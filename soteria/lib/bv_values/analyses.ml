open Soteria_std
module Var = Symex.Var

(** Syntactic analyses over a symbolic value language [L]: the simplification
    knowledge base that records facts learned from the path condition and uses
    them to simplify later constraints. Its [S] signature is what the solvers in
    {!Bv_solver} consume; concrete instances are {{!Make.None}[None]} (no-op),
    {{!Make.Interval}[Interval]}, {{!Make.Equality}[Equality]}, and
    {{!Make.Merge}[Merge]} to combine two of them. *)
module Make (L : Solver_lang.S) = struct
  (* let log = Logs.L.warn *)
  let log _ = ()

  module type S = sig
    include Soteria_std.Reversible.Mutable

    (** Simplifies a constraints using the current knowledge base, without
        updating it. *)
    val simplify : t -> L.t -> L.t

    (** Adds a constraint to the current analysis, updating the currently
        tracked data. *)
    val add_constraint : t -> L.t -> L.t * Var.Set.t

    (** Filters the given iterator of symbolic values, keeping only those
        relevant to the given variable according to the analysis. *)
    val filter : t -> Var.t -> L.ty -> L.t Iter.t -> L.t Iter.t

    (** Encode all the information relevant to the given variables and conjuncts
        them with the given accumulator. *)
    val encode : ?vars:Var.Hashset.t -> t -> L.t Iter.t
  end

  module Merge (A1 : S) (A2 : S) : S = struct
    type t = A1.t * A2.t [@@deriving reversible]

    let simplify (a1, a2) v = v |> A1.simplify a1 |> A2.simplify a2

    let add_constraint (a1, a2) v =
      let v', vars1 = A1.add_constraint a1 v in
      let v'', vars2 = A2.add_constraint a2 v' in
      (v'', Var.Set.union vars1 vars2)

    let filter (a1, a2) var ty vs =
      vs |> A1.filter a1 var ty |> A2.filter a2 var ty

    let encode ?vars (a1, a2) : L.t Iter.t =
      Iter.append (A1.encode ?vars a1) (A2.encode ?vars a2)
  end

  module None : S = struct
    type t = unit

    let init () = ()
    let backtrack_n () _ = ()
    let save () = ()
    let reset () = ()
    let simplify () v = v
    let add_constraint () v = (v, Var.Set.empty)
    let filter () _ _ vs = vs
    let encode ?vars:_ () = Iter.empty
  end

  module Interval : S = struct
    (** An interval analysis for bitvectors inspired by
        https://ceur-ws.org/Vol-1617/paper8.pdf *)

    (* we only include stuff from Z we want *)
    open struct
      let zero = Z.zero
      let pred = Z.pred
      let succ = Z.succ
      let ( < ) = Z.lt
      let ( <= ) = Z.leq
      let ( >= ) = Z.geq
      let ( > ) = Z.gt
      let pow2 n = Z.shift_left Z.one n
    end

    let mk_var n v : L.t = L.mk_var v (L.t_bv n)
    let max_for n = Z.(pred (shift_left one n))

    type sign = L.sign = Pos | Neg

    let pp_sign fmt = function
      | Pos -> Fmt.string fmt "+"
      | Neg -> Fmt.string fmt "-"

    module Range = struct
      (** A range \[m, n\]; both sides are inclusive. Because we deal with
          bitvectors, we always have an upper and lower bound! *)
      type t = Z.t * Z.t

      let pp fmt (m, n) =
        Fmt.pf fmt "[%s; %s]" (Z.format "x" m) (Z.format "x" n)

      let pps fmt (sign, range) = Fmt.pf fmt "%a%a" pp_sign sign pp range
      let is_empty (m, n) : bool = m > n
      let default b = (zero, max_for b)

      (** The intersection of two ranges; always representable *)
      let intersect (m1, n1) (m2, n2) = (Z.max m1 m2, Z.min n1 n2)

      (** The union of two ranges; representable but OX *)
      let union (m1, n1) (m2, n2) = (Z.min m1 m2, Z.max n1 n2)

      (** The exact union of two ranges; may not be representable, if they don't
          overlap *)
      let union_ex ((m1, n1) as r1) ((m2, n2) as r2) =
        if succ n1 < m2 || pred m1 > n2 then None else Some (union r1 r2)

      let eq (m1, n1) (m2, n2) = Z.equal m1 m2 && Z.equal n1 n2

      let cmp (m1, n1) (m2, n2) =
        let c = Z.compare m1 m2 in
        if c <> 0 then c else Z.compare n1 n2
    end

    (** The interval data for a given variable; consists of one positive range,
        and a list of negative ranges that apply to it.

        See https://ceur-ws.org/Vol-1617/paper8.pdf *)
    module Data = struct
      type t = { pos : Range.t; negs : Range.t list; size : int }
      [@@deriving show { with_path = false }]

      let mk n = { pos = Range.default n; negs = []; size = n }

      let apply_negs size pos negs =
        (* First, try filtering out negations that are included in others, and
           join them *)
        let aux_merge_filter negs r =
          let negs, r =
            List.fold_left
              (fun (acc, ra) r ->
                match Range.union_ex r ra with
                | Some merged -> (acc, merged)
                | None -> (r :: acc, ra))
              ([], r) negs
          in
          r :: negs
        in
        let negs = List.fold_left aux_merge_filter [] negs in
        log (fun m ->
            m "negs after: %a" Fmt.(list ~sep:(any ", ") Range.pp) negs);

        (* See [3.1] in https://ceur-ws.org/Vol-1617/paper8.pdf *)
        let pos, negs =
          List.fold_left
            (fun (((l, u) as pos), negs) ((a, b) as neg) ->
              if a > u || b < l then (pos, negs)
              else if a <= l then
                let neg_pos = (succ b, pow2 size) in
                (Range.intersect pos neg_pos, negs)
              else if b >= u then
                let neg_pos = (zero, pred a) in
                (Range.intersect pos neg_pos, negs)
              else (pos, neg :: negs))
            (pos, []) negs
        in
        log (fun m ->
            m "pos/negs after: %a / %a" Range.pp pos
              Fmt.(list ~sep:(any ", ") Range.pp)
              negs);

        (pos, List.sort_uniq Range.cmp negs)

      (** Incorporates a positive range into this data, by using intersection.
          Returns the updated data, and whether the added range is redundant. *)
      let add_pos data r =
        let pos = Range.intersect data.pos r in
        if pos = data.pos then (data, true)
        else
          let pos, negs = apply_negs data.size pos data.negs in
          ({ data with pos; negs }, false)

      (** Incorporates a negative range into this data, by using set difference.
          Returns the updated data, and whether the added range is redundant. *)
      let add_neg data r =
        let pos, negs = apply_negs data.size data.pos (r :: data.negs) in
        if Range.eq pos data.pos && List.equal Range.eq negs data.negs then
          (data, true)
        else ({ data with pos; negs }, false)

      let add data (sign, range) =
        match sign with Pos -> add_pos data range | Neg -> add_neg data range

      (** Whether the interval data represents an empty set. *)
      let is_empty data =
        (* TODO: take into account the negative ranges! Maybe we can do a small
           optimisation where we automatically clear data and set a RangeData to
           be empty when we find it is after an add_pos/add_neg, rather than
           computing it here too. *)
        Range.is_empty data.pos

      (** Whether the data represents a singleton set. *)
      let is_singleton { pos = m, n; _ } = Z.equal m n

      (** [iter_sval_equivalent v d] returns an iterator over the set of
          symbolic values to encode the data [d] for variable [v]. *)
      let iter_sval_equivalent v { pos = m, n; negs; size } f =
        let bv = L.bv_mk size in
        let var = mk_var size v in
        if Z.equal m n then f (L.sem_eq var (bv m))
        else (
          if not (Z.equal m Z.zero) then f (L.bv_uleq (bv m) var);
          if not (Z.equal n (max_for size)) then f (L.bv_uleq var (bv n));

          negs
          |> List.iter @@ fun (m, n) ->
             if Z.equal m n then f (L.not_ (L.sem_eq var (bv m)))
             else
               f (L.not_ (L.and_ (L.bv_uleq (bv m) var) (L.bv_uleq var (bv n)))))
    end

    type st = Data.t Var.Map.t

    include Reversible.Make_mutable (struct
      type t = st

      let default () = Var.Map.empty
      let copy = Fun.id
    end)

    let get n v st =
      match Var.Map.find_opt v st with Some r -> r | None -> Data.mk n

    let pp ft st =
      Fmt.(iter_bindings Var.Map.iter (pair ~sep:(any " -> ") Var.pp Data.pp))
        ft st

    (** [update st var size (sign, range)] Updates state [st] for variable
        [var], with size [size], by adding to it the range [range] (this range
        is positive if [sign = Pos], negative otherwise).

        Returns [(learnt, dirty, st)]: [learnt] is the constraint to be added to
        the PC (e.g. [false] if this constraint is unfeasible), [dirty] is to
        mark variables whose range has changed and for which a new SAT check may
        be needed, and [st] is the new state. *)
    let update st var size new_range =
      let range = get size var st in
      let range', redundant = Data.add range new_range in
      if redundant then (
        log (fun m ->
            m "Useless range  %a: %a %a = %a" Var.pp var Data.pp range Range.pps
              new_range Data.pp range');
        let is_ok = not (Data.is_empty range) in
        (L.of_bool is_ok, Var.Set.empty, st))
      else
        let st = Var.Map.add var range' st in
        log (fun m ->
            m "New range (%b, %b) %a: %a %a@.  = %a" (Data.is_singleton range')
              (Data.is_empty range') Var.pp var Data.pp range Range.pps
              new_range Data.pp range');
        if Data.is_singleton range' then
          (* We narrowed the range to one value! *)
          let const = L.bv_mk size (fst range'.pos) in
          let var = mk_var size var in
          let eq = L.sem_eq const var in
          (eq, Var.Set.empty, st)
        else if Data.is_empty range' then
          (* The range is empty, so this cannot be true *)
          (L.v_false, Var.Set.empty, st)
        else
          (* We could cleanly absorb the range, so the PC doesn't need to store
             it -- however we must mark this variable as dirty, as maybe the
             modified range still renders the branch infeasible, e.g. because of
             some additional PC assertions. *)
          (L.v_true, Var.Set.singleton var, st)

    (** [add_constraint ?sign v st] Adds a constraint [v] to the state [st].
        [sign] is the sign of the constraint (by default [Pos]; [Neg] indicates
        we're in a negation).

        Returns [(simp, learnt, dirty, st)]: [simp] is the simplified constraint
        (which may be [true] if the constraint was entirely absorbed, or [false]
        if it was deemed unfeasible), [learnt] is additional facts learnt from
        the simplified formula, [dirty] is the set of variables whose ranges
        changed, and [st] is the updated state. *)
    let rec add_constraint (v : L.t) st : L.t * L.t * Var.Set.t * st =
      match L.as_and v with
      | Some (v1, v2) ->
          let v1', learnt1, vars1, st' = add_constraint v1 st in
          let v2', learnt2, vars2, st'' = add_constraint v2 st' in

          log (fun m ->
              m "%a && %a => %a && %a" L.pp v1 L.pp v2 L.pp v1' L.pp v2');
          ( L.and_ v1' v2',
            L.and_ learnt1 learnt2,
            Var.Set.union vars1 vars2,
            st'' )
      | None -> (
          match L.as_range v with
          | Some (var, size, srange) ->
              let learnt, vars, st' = update st var size srange in
              (L.v_true, learnt, vars, st')
          | None -> (v, L.v_true, Var.Set.empty, st))

    let rec simplify (v : L.t) st =
      match L.as_or v with
      | Some (v1, v2) ->
          (* [v1 || v2] is valid under [st] iff [¬v1 && ¬v2] is infeasible
             there. Unlike the join of ranges (which over-approximates a union
             and would let us wrongly conclude e.g. [x != 0 || y != 0] is always
             true), intersecting ranges is exact, so [add_constraint] only
             reports infeasibility (a [false] learnt fact) when it genuinely
             holds. *)
          let _, learnt1, _, st1 = add_constraint (L.not_ v1) st in
          let _, learnt2, _, _ = add_constraint (L.not_ v2) st1 in
          log (fun m ->
              m "checking %a || %a:@.¬1. %a@.¬2. %a" L.pp v1 L.pp v2 L.pp
                learnt1 L.pp learnt2);
          if L.equal learnt1 L.v_false || L.equal learnt2 L.v_false then
            L.v_true
          else v
      | None -> (
          let is_lt x = Option.is_some (L.as_lt x) in
          match L.as_eq v with
          | Some (l, r) when is_lt l && is_lt r ->
              let l' = simplify l st in
              let r' = simplify r st in
              if L.equal l l' && L.equal r r' then v else L.sem_eq l' r'
          | _ -> (
              match L.as_range v with
              | Some (var, size, srange) ->
                  let range = get size var st in
                  log (fun m ->
                      m "Simplify range of %a: %a (curr %a) for %a" L.pp v
                        Range.pps srange Data.pp range pp st);
                  let range', redundant = Data.add range srange in
                  log (fun m ->
                      m "Redundant? %b Empty? %b" redundant
                        (Data.is_empty range'));
                  if redundant then L.v_true
                  else if Data.is_empty range' then L.v_false
                  else v
              | None -> v))

    let add_constraint v st =
      log (fun m -> m "Adding constraint: %a" L.pp v);
      let v', learnt, vars, st' = add_constraint v st in
      if v <> v' || not (Var.Set.is_empty vars) then
        log (fun m ->
            m "Change: %a -> %a + %a (%a)@." L.pp v L.pp v' L.pp learnt
              Fmt.(list ~sep:(any ", ") Var.pp)
              (Var.Set.to_list vars))
      else log (fun m -> m "No change.@.");
      ((L.and_ v' learnt, vars), st')

    let filter var ty vs st =
      match L.as_bv_ty ty with
      | Some n -> (
          let range_opt = Var.Map.find_opt var st in
          match range_opt with
          | None -> vs
          | Some range ->
              (* In sparsely populated ranges (e.g. [0, 1000] - [1, 999]),
                 filtering can be very slow since the odds of getting a valid
                 integer is so low. Because of this, we reset the iterator and
                 generate values ourselves. *)
              let l, h = range.Data.pos in
              let rec iter z f =
                f (L.bv_mk n z);
                (* if a negative range exists, update to next value *)
                let z = Z.succ z in
                let neg =
                  List.find_opt
                    (fun (m, n) -> Z.Compare.(m <= z && z <= n))
                    range.Data.negs
                in
                let z' = match neg with None -> z | Some (_, n) -> Z.succ n in
                if Z.Compare.(z' <= h) then iter z' f
              in
              iter l)
      | None -> vs

    let simplify st v = wrap_read (simplify v) st
    let add_constraint st v = wrap (add_constraint v) st
    let filter st var ty vs = wrap_read (filter var ty vs) st

    let encode ?vars st : L.t Iter.t =
      let to_check =
        Option.fold ~none:(fun _ -> true) ~some:Var.Hashset.mem vars
      in
      wrap_read
        (fun m f ->
          Var.Map.iter
            (fun v r -> if to_check v then Data.iter_sval_equivalent v r f)
            m)
        st
  end

  module Equality : S = struct
    module UnionFind = UnionFind.Make (UnionFind.StoreMap)

    module VMap = PatriciaTree.MakeMap (struct
      type t = L.t

      let to_int = L.unique_tag
      let pp = L.pp
    end)

    include Reversible.Make_mutable (struct
      type t = L.t UnionFind.store * L.t UnionFind.rref VMap.t

      let default () = (UnionFind.new_store (), VMap.empty)
      let copy (uf, refs) = (UnionFind.copy uf, refs)
    end)

    let get_or_make v ((uf, refs) as st) =
      match VMap.find_opt v refs with
      | None ->
          let ref = UnionFind.make uf v in
          let refs = VMap.add v ref refs in
          (ref, (uf, refs))
      | Some ref -> (ref, st)

    let merge v1 v2 (uf, _) =
      ignore
      @@ UnionFind.merge uf
           (fun v1 v2 -> if L.cost v1 > L.cost v2 then v2 else v1)
           v1 v2

    let find_cheaper_opt v (uf, refs) =
      VMap.find_opt v refs
      |> Option.bind @@ fun r ->
         let v_repr = UnionFind.get uf r in
         if L.equal v v_repr then None else Some v_repr

    let known_eq v1 v2 (uf, refs) : bool =
      match (VMap.find_opt v1 refs, VMap.find_opt v2 refs) with
      | Some r1, Some r2 -> UnionFind.eq uf r1 r2
      | _ -> false

    let eval_var (uf, refs) var _ _ =
      VMap.find_opt var refs |> Option.fold ~none:var ~some:(UnionFind.get uf)

    let simplify (v : L.t) st =
      let rec simplify ~fuel v =
        if fuel - 1 <= 0 then v
        else
          let simplify = simplify ~fuel:(fuel - 1) in
          match find_cheaper_opt v st with
          | Some v' -> v'
          | None ->
              let known_eq_opt = function
                | Some (l, r) -> known_eq l r st
                | None -> false
              in
              if known_eq_opt (L.as_eq v) || known_eq_opt (L.as_leq v) then
                L.v_true
              else if known_eq_opt (L.as_lt v) then L.v_false
              else L.map_operands simplify v
      in
      L.eval ~eval_var:(eval_var st) v |> simplify ~fuel:3

    let add_vars v s =
      L.iter_vars v |> Iter.fold (fun s (v, _) -> Var.Set.add v s) s

    let add_constraint (v : L.t) st =
      match L.as_eq v with
      | Some (v1, v2) ->
          let vars = Var.Set.empty |> add_vars v1 |> add_vars v2 in
          let v1, st = get_or_make v1 st in
          let v2, st = get_or_make v2 st in
          merge v1 v2 st;
          ((L.v_true, vars), st)
      | None -> (
          match Stdlib.Option.bind (L.as_not v) L.as_distinct with
          | Some (hd :: tl) ->
              let vars = add_vars hd Var.Set.empty in
              let v1, st = get_or_make hd st in
              let rec aux vars st = function
                | [] -> (vars, st)
                | v2 :: rest ->
                    let vars = add_vars v2 vars in
                    let v2, st = get_or_make v2 st in
                    merge v1 v2 st;
                    aux vars st rest
              in
              let vars, st = aux vars st tl in
              ((L.v_true, vars), st)
          | _ -> ((v, Var.Set.empty), st))

    (** In equality analysis we can be certain of the value of a variable, so we
        can entirely replace the set of possible values [vs] with the
        representative value (if any). *)
    let filter var ty vs st =
      let v = L.mk_var var ty in
      match find_cheaper_opt v st with
      | None -> vs
      | Some v_repr -> Iter.singleton v_repr

    let encode ?vars (uf, refs) f =
      let module URefTbl = Hashtbl.Make (struct
        type t = L.t UnionFind.rref

        let equal r1 r2 = UnionFind.eq uf r1 r2
        let hash = Hashtbl.hash
      end) in
      let is_relevant =
        match vars with
        | None -> fun _ -> true
        | Some vars ->
            fun v ->
              L.iter_vars v
              |> Iter.exists (fun (v, _) -> Var.Hashset.mem vars v)
      in
      let relevant_refs = URefTbl.create 8 in
      VMap.iter
        (fun v ufref ->
          if is_relevant v then
            let repr = UnionFind.find uf ufref in
            let repr_v = UnionFind.get uf repr in
            URefTbl.add relevant_refs repr repr_v)
        refs;
      (* When encoding we need to be careful; e.g. if we know A = X and A = Y,
         and X is relevant, we must also encode A = Y, as maybe X != Y; we don't
         have the capacity to check that here, it is discharged to the
         solver. *)
      VMap.iter
        (fun v ufref ->
          let ufref = UnionFind.find uf ufref in
          match URefTbl.find_opt relevant_refs ufref with
          | None -> ()
          | Some repr when L.equal v repr -> ()
          | Some repr -> f (L.sem_eq v repr))
        refs

    let simplify st v = wrap_read (simplify v) st
    let add_constraint st v = wrap (add_constraint v) st
    let filter st var ty vs = wrap_read (filter var ty vs) st
    let encode ?vars st = wrap_read (encode ?vars) st
  end
end
