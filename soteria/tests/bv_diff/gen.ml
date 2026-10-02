(** Random generation of well-typed [Tm.t] (qcheck-core's [Gen], which is a
    function of a [Random.State.t]: the run is a function of the seed).

    Widths (1, 2, 4, 8, 16, 32, 64, 128) (16 and 128 are rare: they are what
    [BvToFloatRaw] needs), pointers/locations of 8, 32 or 64 bits, 4 variables
    per sort, depth <= 6, size-biased (small roots are the most frequent),
    literals biased to (0, 1, 2, 2^(n-1)-1, 2^(n-1), 2^n-1, random), shared
    subterms (a pool per root, per sort), random [checked] flags, floats biased
    to (+-0, +-inf, NaN, 1, 0.5, -1). Well typedness is by construction;
    divisors are never the literal 0 (the old API types them [nonzero]). *)

open Tm
module G = QCheck.Gen
module F = Soteria.Bv_values.Svalue.F

let widths =
  [ (1, 3); (2, 3); (4, 2); (8, 6); (16, 1); (32, 6); (64, 6); (128, 1) ]

let ptr_widths = [ (8, 2); (32, 2); (64, 3) ]
let precs = [ (F16, 1); (F32, 5); (F64, 5); (F128, 1) ]
let rms = [| RM.NearestTiesToEven; Truncate; Ceil; Floor; NearestTiesToAway |]
let fcs = [| FC.Normal; Subnormal; Zero; Infinite; NaN |]
let wchoice l = G.oneof_weighted (List.map (fun (x, w) -> (w, G.return x)) l)
let gen_width = wchoice widths
let gen_ptr_width = wchoice ptr_widths
let gen_prec = wchoice precs
let var_index : (sort, int) Hashtbl.t = Hashtbl.create 64

let var_id s i =
  let k =
    match Hashtbl.find_opt var_index s with
    | Some k -> k
    | None ->
        let k = Hashtbl.length var_index in
        Hashtbl.add var_index s k;
        k
  in
  1 + (4 * k) + i

let gen_flag rs = G.bool rs
let gen_checked rs : checked = (G.bool rs, G.bool rs)

type st = {
  rs : Random.State.t;
  pool : (sort, Tm.t) Hashtbl.t;
  bound : sort list;  (** enclosing [Exists1] binders, outermost first *)
  mutable budget : int;
}

let chance st pct = G.int_bound 99 st.rs < pct
let pick st l = List.nth l (G.int_bound (List.length l - 1) st.rs)

let weighted st (l : (int * (unit -> 'a)) list) : 'a =
  let total = List.fold_left (fun a (w, _) -> a + w) 0 l in
  let r = G.int_bound (total - 1) st.rs in
  let rec go r = function
    | [] -> assert false
    | (w, f) :: tl -> if r < w then f () else go (r - w) tl
  in
  go r l

let random_bits rs n =
  let rec go acc k =
    if k <= 0 then acc
    else
      go
        (Z.logor (Z.shift_left acc 30) (Z.of_int (Random.State.bits rs)))
        (k - 30)
  in
  Z.extract (go Z.zero n) 0 n

let mask n z = Z.extract z 0 n

let gen_bv_z st n =
  let max_u = Z.pred (Z.shift_left Z.one n) in
  let half = Z.shift_left Z.one (n - 1) in
  mask n
    (weighted st
       [
         (15, fun () -> Z.zero);
         (15, fun () -> Z.one);
         (8, fun () -> Z.of_int 2);
         (10, fun () -> Z.pred half);
         (10, fun () -> half);
         (15, fun () -> max_u);
         (4, fun () -> Z.of_int 3);
         (23, fun () -> random_bits st.rs n);
       ])

let float_specials p =
  let z f = F.to_z f in
  [
    z (F.zero p);
    z (F.neg_zero p);
    z (F.infinity p);
    z (F.neg_infinity p);
    z (F.nan p);
    z (F.one p);
    z (F.of_float p 0.5);
    z (F.of_float p (-1.0));
  ]

let gen_float_z st p =
  if chance st 10 then random_bits st.rs (FP.size p)
  else pick st (float_specials p)

let gen_loc_z st n =
  weighted st
    [
      (45, fun () -> Z.zero);
      (20, fun () -> Z.one);
      (10, fun () -> Z.of_int 2);
      (25, fun () -> random_bits st.rs n);
    ]

let gen_var st s = Var (var_id s (G.int_bound 3 st.rs), s)

let gen_sort_general st =
  weighted st
    [
      (3, fun () -> SBool);
      (9, fun () -> SBv (gen_width st.rs));
      (1, fun () -> SLoc (gen_ptr_width st.rs));
      (2, fun () -> SPtr (gen_ptr_width st.rs));
      (2, fun () -> SFloat (gen_prec st.rs));
      (1, fun () -> SSeq (if chance st 50 then SBv 8 else SBool));
    ]

let rec leaf st s : Tm.t =
  let bound_idx =
    List.mapi (fun i b -> (i, b)) st.bound
    |> List.filter (fun (_, b) -> b = s)
    |> List.map fst
  in
  if bound_idx <> [] && chance st 40 then Bound (pick st bound_idx, s)
  else
    match s with
    | SBool -> if chance st 35 then Bool (G.bool st.rs) else gen_var st s
    | SBv n -> if chance st 60 then Bv (n, gen_bv_z st n) else gen_var st s
    | SLoc n -> if chance st 35 then Loc (n, gen_loc_z st n) else gen_var st s
    | SPtr n ->
        weighted st
          [
            (25, fun () -> Op (PtrNull n, []));
            (15, fun () -> Op (PtrMk, [ leaf st (SLoc n); leaf st (SBv n) ]));
            (60, fun () -> gen_var st s);
          ]
    | SFloat p ->
        if chance st 55 then Float (p, gen_float_z st p) else gen_var st s
    | SSeq e ->
        weighted st
          [
            (35, fun () -> Op (SeqMk s, []));
            (15, fun () -> Op (SeqMk s, [ leaf st e ]));
            (50, fun () -> gen_var st s);
          ]

and term st s d : Tm.t =
  if d <= 0 || st.budget <= 0 then leaf st s
  else
    let pooled = Hashtbl.find_all st.pool s in
    if pooled <> [] && chance st 15 then pick st pooled
    else begin
      st.budget <- st.budget - 1;
      let t = prod st s d in
      Hashtbl.add st.pool s t;
      t
    end

(** A child of a node at depth budget [d]. *)
and sub st s d =
  let d' = if chance st 50 then d - 1 else G.int_bound (d - 1) st.rs in
  term st s d'

and nonzero_divisor st n d =
  let t = sub st (SBv n) d in
  match t with Bv (_, z) when Z.equal z Z.zero -> Bv (n, Z.one) | t -> t

and prod st s d : Tm.t =
  let sb x = sub st x d in
  let op1 o a = Op (o, [ a ]) in
  let op2 o a b = Op (o, [ a; b ]) in
  let ite_ s =
    let c = sb SBool in
    let a = sb s in
    let b = sb s in
    Op (Ite, [ c; a; b ])
  in
  let bin o s () =
    let a = sb s in
    let b = sb s in
    op2 o a b
  in
  match s with
  | SBool ->
      let any_w () = SBv (gen_width st.rs) in
      let bvbin mk () =
        let t = any_w () in
        let o = mk () in
        let a = sb t in
        let b = sb t in
        op2 o a b
      in
      let fbin o () =
        let t = SFloat (gen_prec st.rs) in
        let a = sb t in
        let b = sb t in
        op2 o a b
      in
      let sg () = G.bool st.rs in
      weighted st
        [
          (6, bin And SBool);
          (6, bin Or SBool);
          (5, fun () -> op1 Not (sb SBool));
          (4, fun () -> ite_ SBool);
          ( 10,
            fun () ->
              let t = gen_sort_general st in
              let a = sb t in
              let b = sb t in
              op2 SemEq a b );
          ( 3,
            fun () ->
              let t = gen_sort_general st in
              let t' = if chance st 90 then t else gen_sort_general st in
              let a = sb t in
              let b = sb t' in
              op2 SemEqUntyped a b );
          ( 4,
            fun () ->
              let t = gen_sort_general st in
              let n = G.int_bound 4 st.rs in
              Op (Distinct, List.init n (fun _ -> sb t)) );
          (2, bin AndLazy SBool);
          (2, bin OrLazy SBool);
          ( 2,
            fun () ->
              let n = G.int_bound 4 st.rs in
              Op (Conj, List.init n (fun _ -> sb SBool)) );
          ( 5,
            fun () ->
              let bs =
                weighted st
                  [
                    (2, fun () -> SBool);
                    (6, fun () -> SBv (gen_width st.rs));
                    (1, fun () -> SPtr (gen_ptr_width st.rs));
                    (1, fun () -> SFloat (gen_prec st.rs));
                  ]
              in
              let not_in = term st (gen_sort_general st) 1 in
              let inner = min st.budget 30 in
              let st' =
                {
                  st with
                  pool = Hashtbl.create 8;
                  bound = st.bound @ [ bs ];
                  budget = inner;
                }
              in
              let body = term st' SBool (d - 1) in
              st.budget <- st.budget - (inner - st'.budget);
              op2 (Exists1 bs) not_in body );
          (4, bvbin (fun () -> BvLt (sg ())));
          (4, bvbin (fun () -> BvLeq (sg ())));
          (3, bvbin (fun () -> BvGt (sg ())));
          (3, bvbin (fun () -> BvGeq (sg ())));
          (3, bvbin (fun () -> BvAddOvf (sg ())));
          (2, bvbin (fun () -> BvSubOvf (sg ())));
          (3, bvbin (fun () -> BvMulOvf (sg ())));
          (2, fun () -> op1 BvNegOvf (sb (any_w ())));
          (4, fun () -> op1 BvToBool (sb (any_w ())));
          (3, fbin FEq);
          (2, fbin FLt);
          (2, fbin FLeq);
          (1, fbin FGt);
          (1, fbin FGeq);
          ( 4,
            fun () ->
              let fc = fcs.(G.int_bound 4 st.rs) in
              op1 (FIsFloatClass fc) (sb (SFloat (gen_prec st.rs))) );
          (1, fun () -> op1 FIsNegative (sb (SFloat (gen_prec st.rs))));
          (1, fun () -> op1 FIsPositive (sb (SFloat (gen_prec st.rs))));
          (2, fun () -> op1 PtrIsNullLoc (sb (SLoc (gen_ptr_width st.rs))));
          (2, fun () -> op1 PtrIsNull (sb (SPtr (gen_ptr_width st.rs))));
          (2, fun () -> op1 PtrIsAtNullLoc (sb (SPtr (gen_ptr_width st.rs))));
        ]
  | SBv n ->
      let ck () = gen_checked st.rs in
      let sg () = G.bool st.rs in
      let smaller = List.filter (fun (w, _) -> w < n) widths in
      let bigger = List.filter (fun (w, _) -> w > n) widths in
      let splits =
        List.filter_map
          (fun (a, _) ->
            if a < n && List.mem_assoc (n - a) widths then Some a else None)
          widths
      in
      weighted st
        ([
           ( 4,
             fun () ->
               let o = BvAdd (ck ()) in
               bin o s () );
           ( 4,
             fun () ->
               let o = BvSub (ck ()) in
               bin o s () );
           ( 4,
             fun () ->
               let o = BvMul (ck ()) in
               bin o s () );
           ( 3,
             fun () ->
               let o = BvDiv (sg ()) in
               let a = sb s in
               let b = nonzero_divisor st n d in
               op2 o a b );
           ( 3,
             fun () ->
               let o = BvRem (sg ()) in
               let a = sb s in
               let b = nonzero_divisor st n d in
               op2 o a b );
           (2, bin BvMod s);
           ( 2,
             fun () ->
               let o = BvNeg (sg ()) in
               op1 o (sb s) );
           (4, bin BvAnd s);
           (4, bin BvOr s);
           (3, bin BvXor s);
           (3, bin BvShl s);
           (3, bin BvLShr s);
           (3, bin BvAShr s);
           (3, fun () -> op1 BvNot (sb s));
           (4, fun () -> op1 (BvOfBool n) (sb SBool));
           (2, fun () -> op1 BvNotBool (sb s));
           ( 3,
             fun () ->
               let rm = rms.(G.int_bound 4 st.rs) in
               let o = BvOfFloat (rm, sg (), n) in
               op1 o (sb (SFloat (gen_prec st.rs))) );
           (4, fun () -> ite_ s);
         ]
        @ (if smaller <> [] then
             [
               ( 4,
                 fun () ->
                   let m, _ = pick st smaller in
                   let o = BvExtend (sg (), n - m) in
                   op1 o (sb (SBv m)) );
             ]
           else [])
        @ (if bigger <> [] then
             [
               ( 5,
                 fun () ->
                   let m, _ = pick st bigger in
                   let i = G.int_bound (m - n) st.rs in
                   op1 (BvExtract (i, i + n - 1)) (sb (SBv m)) );
               ( 3,
                 fun () ->
                   (* extract out of a concatenation of two pool widths *)
                   let a, _ = pick st widths in
                   let b, _ = pick st widths in
                   let m = a + b in
                   if m < n then ite_ s
                   else
                     let i = G.int_bound (m - n) st.rs in
                     let x = sb (SBv a) in
                     let y = sb (SBv b) in
                     op1 (BvExtract (i, i + n - 1)) (op2 BvConcat x y) );
             ]
           else [])
        @ (if splits <> [] then
             [
               ( 4,
                 fun () ->
                   let a = pick st splits in
                   let x = sb (SBv a) in
                   let y = sb (SBv (n - a)) in
                   op2 BvConcat x y );
             ]
           else [])
        @
        if List.mem_assoc n ptr_widths then
          [ (3, fun () -> op1 PtrOfs (sb (SPtr n))) ]
        else [])
  | SFloat p ->
      let fb o () = bin o s () in
      let rm () = rms.(G.int_bound 4 st.rs) in
      let tern o () =
        let a = sb s in
        let b = sb s in
        let c = sb s in
        Op (o, [ a; b; c ])
      in
      let size = FP.size p in
      weighted st
        [
          (4, fb FAdd);
          (4, fb FSub);
          (4, fb FMul);
          (3, fb FDiv);
          (2, fb FRem);
          (2, fb FFmod);
          (2, fb FMin);
          (2, fb FMax);
          (2, fb FMinimum);
          (2, fb FMaximum);
          (2, tern FFma);
          (1, tern FFmodOfRem);
          (2, fun () -> op1 FAbs (sb s));
          (2, fun () -> op1 FNeg (sb s));
          (2, fun () -> op1 FSqrt (sb s));
          ( 2,
            fun () ->
              let o = FRound (rm ()) in
              op1 o (sb s) );
          ( 3,
            fun () ->
              let o = FCast (rm (), p) in
              op1 o (sb (SFloat (gen_prec st.rs))) );
          ( 3,
            fun () ->
              let o = BvToFloat (rm (), G.bool st.rs, p) in
              op1 o (sb (SBv (gen_width st.rs))) );
          (2, fun () -> op1 BvToFloatRaw (sb (SBv size)));
          (3, fun () -> ite_ s);
        ]
  | SLoc n ->
      weighted st
        [ (5, fun () -> op1 PtrLoc (sb (SPtr n))); (3, fun () -> ite_ s) ]
  | SPtr n ->
      weighted st
        [
          ( 6,
            fun () ->
              let l = sb (SLoc n) in
              let o = sb (SBv n) in
              op2 PtrMk l o );
          ( 5,
            fun () ->
              let p = sb s in
              let o = sb (SBv n) in
              op2 PtrAddOfs p o );
          (2, fun () -> Op (PtrNull n, []));
          (3, fun () -> ite_ s);
        ]
  | SSeq e ->
      weighted st
        [
          ( 6,
            fun () ->
              let k = G.int_bound 3 st.rs in
              Op (SeqMk s, List.init k (fun _ -> sb e)) );
          (3, fun () -> ite_ s);
        ]

let max_depth = 6

let gen_depth rs =
  wchoice [ (1, 20); (2, 25); (3, 20); (4, 15); (5, 12); (6, 8) ] rs

let gen_root rs : Tm.t =
  let st = { rs; pool = Hashtbl.create 16; bound = []; budget = 250 } in
  let s =
    weighted st
      [
        (45, fun () -> SBool);
        (35, fun () -> SBv (gen_width rs));
        (10, fun () -> SFloat (gen_prec rs));
        (5, fun () -> SPtr (gen_ptr_width rs));
        (2, fun () -> SLoc (gen_ptr_width rs));
        (3, fun () -> SSeq (if G.bool rs then SBv 8 else SBool));
      ]
  in
  term st s (gen_depth rs)
