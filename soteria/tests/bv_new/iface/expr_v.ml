(** Substitution and equational learning over any language {!Value_lang.S}: the
    successor of [expr.ml]. [Subst.apply] ([expr.ml:34-131]) is generic over
    [operands]/[rebuild]/[as_var]/[as_exists]; [Subst.learn] ([expr.ml:140-198])
    over [learn_alts]/[learn_value] ({!View_host.learn_plan}). The [Ext.mk],
    [Ext.apply_subst] and [Ext.learn] hooks of the extensions are the [rebuild],
    [operands] and [learn_*] cases of their [extend fn]. Written by the
    architect as the reference implementation; WP3b owns it from now on.

    Two textual differences with [expr.ml], neither behavioural:
    - the binders of [apply_bound] are compared with [Var.equal] and [equal_ty]
      instead of the polymorphic [List.mem];
    - [learn] reads the inverse of a node in its {!View_host.learn_plan}. *)

open Deps
open Soteria.Soteria_std

module type S = sig
  type value
  type vty

  include
    Symex.Value.Expr
      with type 'a v = value
       and type 'a ty = vty
       and type t = value
end

module Make (V : Value_lang.S) : S with type value = V.t and type vty = V.ty =
struct
  module K = V.K

  type value = V.t
  type vty = V.ty
  type t = V.t
  type 'a v = V.t
  type 'a ty = V.ty

  let pp = V.pp
  let show = Fmt.to_to_string V.pp
  let ty (s : t) : 'a ty = V.type_of s
  let[@inline] of_value v = v

  module Subst = struct
    module Raw_map = PatriciaTree.MakeMap (struct
      type t = V.t

      let to_int = V.unique_tag
      let pp = V.pp
    end)

    type t = V.t Raw_map.t

    let extend s v subst = Raw_map.add_assert_new s v subst
    let pp = Raw_map.pp V.pp
    let empty = Raw_map.empty

    let rec apply ~missing_var (s : t) (v : V.t) =
      match Raw_map.find_opt v s with
      | Some v' -> (v', s)
      | None -> (
          match K.as_var v with
          | Some (x, ty) ->
              let v' = missing_var x ty in
              let s = Raw_map.add v v' s in
              (v', s)
          | None -> (
              match K.as_exists v with
              | Some (vs, sv) ->
                  let (vs, sv), s = apply_bound ~missing_var s vs sv in
                  (K.b_mk_exists vs sv, s)
              | None -> (
                  match K.operands v with
                  | [] -> (v, s)
                  | cs ->
                      let cs, s = apply_list ~missing_var s cs in
                      (K.rebuild v cs, s))))

    and apply_list ~missing_var s vs =
      match vs with
      | [] -> ([], s)
      | v :: vs ->
          let v, s = apply ~missing_var s v in
          let vs, s = apply_list ~missing_var s vs in
          (v :: vs, s)

    and apply_bound ~missing_var s vs sv =
      (* [max_var_ind] returns the index of the freshest semantic variable used
         in [sv], which we use to create new fresh variables for the
         existential. *)
      let max_var_ind sv init =
        V.iter_vars sv
        |> IterLabels.fold ~init ~f:(fun curr (var, _) ->
            let var = Var.to_int var in
            if var > curr then var else curr)
      in
      let is_binder (var, ty) =
        List.exists (fun (v', ty') -> Var.equal var v' && V.equal_ty ty ty') vs
      in
      let max_var_ind, s =
        V.iter_vars sv
        |> Iter.filter (fun var -> not @@ is_binder var)
        |> IterLabels.fold ~init:(0, s) ~f:(fun (curr, s) (var, ty) ->
            let syn_var = V.mk_var var ty in
            match Raw_map.find_opt syn_var s with
            | Some sv -> (max_var_ind sv curr, s)
            | None ->
                (* We call [missing_var] here to ensure that our fresh variables
                   do not clash with other unknown variables and then update [s]
                   so that [missing_var] is only called once. *)
                let sv = missing_var var ty in
                (max_var_ind sv curr, Raw_map.add syn_var sv s))
      in
      (* [subst_with_fresh] is the new substitution which extends [s] by binding
         each variable in [vs] to a fresh semantic variable. [fresh_vs] is a
         list with all the freshly created variables. [old_bindings] is a list
         of pairs [(syn_var, sem_var_opt)] where [sem_var_opt] is an optional
         variable: if [sem_var_opt] holds a value [sem_var], then the binding
         [(syn_var, sem_var)] existed in the original substitution and must be
         reverted at the end. *)
      let _, subst_with_fresh, fresh_vs, old_bindings =
        ListLabels.fold_left vs
          ~init:(max_var_ind + 1, s, [], [])
          ~f:(fun (curr_var_ind, s, vs, bs) (var, ty) ->
            let new_var = Var.of_int curr_var_ind in
            let syn_var, sem_var = (V.mk_var var ty, V.mk_var new_var ty) in
            let bs = (syn_var, Raw_map.find_opt syn_var s) :: bs in
            let s = Raw_map.add syn_var sem_var s in
            (curr_var_ind + 1, s, (new_var, ty) :: vs, bs))
      in
      (* Actually perform substitution *)
      let sv, subst_with_fresh = apply ~missing_var subst_with_fresh sv in
      (* Revert the dummy bindings *)
      let subst_after_pass =
        ListLabels.fold_left old_bindings ~init:subst_with_fresh
          ~f:(fun s -> function
          | syn_var, None -> Raw_map.remove syn_var s
          | syn_var, Some sem_var -> Raw_map.add syn_var sem_var s)
      in
      ((fresh_vs, sv), subst_after_pass)

    let is_known (s : t) (e : V.t) : bool =
      let exception Not_covered in
      try
        let _ = apply ~missing_var:(fun _ _ -> raise_notrace Not_covered) s e in
        true
      with Not_covered -> false

    let rec learn (s : t) (e : V.t) (v : V.t) : t option =
      let open Syntaxes.Option in
      let/ () = if is_known s e then Some s else None in
      match K.as_var e with
      | Some _ -> if Raw_map.mem e s then Some s else Some (extend e v s)
      | None -> (
          match K.learn_alts e with
          | View_host.LNone -> None
          | LAlts alts ->
              let ops = Array.of_list (K.operands e) in
              let rec first = function
                | [] -> None
                | (known, target) :: rest ->
                    let known = Z.to_int known and target = Z.to_int target in
                    if is_known s ops.(known) then
                      let* tv = K.learn_value e (Z.of_int target) v in
                      learn s ops.(target) tv
                    else first rest
              in
              first alts
          | LAll (eager, order) ->
              let ops = Array.of_list (K.operands e) in
              let values = Array.make (Array.length ops) None in
              (* the eager values, in their order, before anything is learned *)
              let* () =
                List.fold_left
                  (fun acc i ->
                    let* () = acc in
                    let i = Z.to_int i in
                    let* tv = K.learn_value e (Z.of_int i) v in
                    values.(i) <- Some tv;
                    Some ())
                  (Some ()) eager
              in
              List.fold_left
                (fun acc i ->
                  let* s = acc in
                  let i = Z.to_int i in
                  let* tv =
                    match values.(i) with
                    | Some tv -> Some tv
                    | None -> K.learn_value e (Z.of_int i) v
                  in
                  learn s ops.(i) tv)
                (Some s) order)
  end

  let subst (f : t -> 'a v) (s : t) : 'b v = f s
end
