(** Golden dump of the [Bv_values] public typed API.

    Generates ~2000 well-typed terms from a fixed seed, exercising every
    smart-constructor family, and prints for each one: pp, type, cost, SMT
    encoding (with the order of emitted declarations), [as_range], [iter_vars],
    substitution, [Lang.eval] (forced and with a variable mapping),
    [Expr.Subst.learn], and, on consecutive pairs of boolean facts,
    [implies_or_contradicts] and [sure_neq]. Stdout is the golden output (must
    be byte-identical between runs and between implementations); a coverage
    table goes to stderr.

    Usage: [bv_golden.exe [seed]] (default seed 42). With [BV_GOLDEN_GC] set,
    [Gc.compact] is called between stanzas (stress test: a few stanzas may then
    differ, because hash-consed nodes that die get a higher tag when re-created
    and the printed operand order of commutative operators depends on tags).
    Normal runs enlarge the minor heap and retain every value they create, so
    that the output does not depend on GC parameters.

    Written against the public typed API only, so that it compiles unchanged
    against any implementation of [Typed.S]. The only implementation-specific
    part is the shim below. *)

module Typed = Soteria.Bv_values.Lang.Typed
module Var = Soteria.Symex.Var
module Smt = Soteria.Smt
module Decls = Soteria.Solvers.Decls
module FP = Typed.FloatPrecision
module RM = Typed.RoundingMode
open Typed

(* ------------------------------------------------------------------ *)
(* Shim: everything that is not plain [Typed] API. A port to another
   implementation only has to re-implement these.
   - [Shim.make]: the generative application of [Typed.Make]
     (above: [Typed.Make (Svalue.Dummy_ext) ()]);
   - [Shim.lang_ty_pp]: print a [Lang.ty] (via [type_type] and [ppa_ty]);
   - [Shim.lang]: uses [untyped] / [type_] to move between [Typed.t] and
     [Lang.t].
   Everything else is [Typed.Lang], [Typed.Expr], [Typed.Bool], ... *)
module Shim = struct
  let lang_ty_pp fmt (ty : Lang.ty) = ppa_ty fmt (type_type ty : T.any ty)
  let to_lang (v : _ t) : Lang.t = untyped v
  let of_lang (v : Lang.t) : T.any t = type_ v
end

type v = T.any t

(* Hash-consed nodes live in weak tables: a node that dies and is re-created
   gets a higher tag, which can flip the printed operand order of commutative
   operators. To keep the output independent of GC timing, every value this
   program creates or receives is retained until exit. *)
let keep : Obj.t list ref = ref []

let retain x =
  keep := Obj.repr x :: !keep;
  x

let c x = cast x
let w x : v = cast x
let str pp x = Format.asprintf "%a" pp x
let pp_v fmt (x : v) = ppa fmt x
let show (x : v) = str pp_v x

(* ------------------------------------------------------------------ *)
(* Sorts                                                               *)
(* ------------------------------------------------------------------ *)

type sort = B | V of int | F of FP.t | L of int | P of int | S of sort

let rec ty_of_sort : sort -> T.any ty = function
  | B -> t_bool
  | V n -> t_int n
  | F p -> t_float p
  | L n -> t_loc n
  | P n -> t_ptr n
  | S s -> t_seq (ty_of_sort s)

let fp_size = function FP.F16 -> 16 | F32 -> 32 | F64 -> 64 | F128 -> 128
let all_fps = [| FP.F16; F32; F64; F128 |]
let bv_widths = [| 1; 2; 8; 16; 32; 64; 128 |]

(* ------------------------------------------------------------------ *)
(* Deterministic randomness                                            *)
(* ------------------------------------------------------------------ *)

let seed = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 42
let st = Random.State.make [| seed |]
let ri n = Random.State.int st n
let rb () = Random.State.bool st
let pick a = a.(ri (Array.length a))

let rz n =
  let rec go acc k =
    if k <= 0 then acc
    else
      go Z.(logor (shift_left acc 30) (of_int (Random.State.bits st))) (k - 30)
  in
  Z.extract (go Z.zero n) 0 n

let bv_lit n =
  let top = Z.shift_left Z.one n in
  match ri 9 with
  | 0 -> BitVec.mk n Z.zero
  | 1 -> BitVec.mk n Z.one
  | 2 -> BitVec.mk_masked n (Z.of_int 2)
  | 3 -> BitVec.mk n (Z.pred (Z.shift_left Z.one (n - 1)))
  | 4 -> BitVec.mk n (Z.shift_left Z.one (n - 1))
  | 5 -> BitVec.mk n (Z.pred top)
  | 6 -> BitVec.mk_masked n (Z.neg (Z.of_int (1 + ri 5)))
  | _ -> BitVec.mk_masked n (rz n)

let float_lit p =
  match ri 12 with
  | 0 -> Float.zero p
  | 1 -> Float.neg_zero p
  | 2 -> Float.infinity p
  | 3 -> Float.neg_infinity p
  | 4 -> Float.nan p
  | 5 -> Float.one p
  | 6 -> Float.mk p "0.5"
  | 7 -> Float.mk p "-2.25"
  | 8 -> Float.mk p "3.0"
  | 9 -> Float.of_z p (Z.of_int (ri 100 - 50))
  | _ -> Float.mk_bits p (rz (fp_size p))

let rms = [| RM.NearestTiesToEven; Truncate; Ceil; Floor; NearestTiesToAway |]

let checkeds =
  [| unchecked; checked_both; checked_of_signed true; checked_of_signed false |]

(* ------------------------------------------------------------------ *)
(* Coverage bookkeeping                                                *)
(* ------------------------------------------------------------------ *)

let cov : (string, int ref * (int, unit) Hashtbl.t) Hashtbl.t =
  Hashtbl.create 256

let fam_order = ref []

let rec_ fam (x : v) : v =
  let x = retain x in
  let n, set =
    match Hashtbl.find_opt cov fam with
    | Some e -> e
    | None ->
        let e = (ref 0, Hashtbl.create 64) in
        Hashtbl.replace cov fam e;
        fam_order := fam :: !fam_order;
        e
  in
  incr n;
  Hashtbl.replace set (unique_tag x) ();
  x

(* ------------------------------------------------------------------ *)
(* Generator                                                           *)
(* ------------------------------------------------------------------ *)

(* Retain the obvious intermediate nodes that smart constructors build from a
   variable (see [keep]). *)
let retain_derived s (x : v) =
  let r y = ignore (retain y) in
  match s with
  | B ->
      r (Bool.not (c x));
      List.iter (fun n -> r (BitVec.of_bool n (c x))) [ 1; 8; 32; 64 ]
  | V n ->
      let z = sem_eq (c x) (BitVec.zero n) in
      r z;
      r (BitVec.of_bool n z);
      r (BitVec.not (c x));
      r (BitVec.neg (c x));
      r (BitVec.to_bool (c x));
      r (BitVec.not_bool (c x));
      r (BitVec.of_bool n (BitVec.to_bool (c x)))
  | P _ ->
      r (Ptr.ofs (c x));
      r (Ptr.loc (c x));
      r (Ptr.is_null (c x));
      r (Ptr.is_null_loc (Ptr.loc (c x)))
  | L n ->
      r (Ptr.is_null_loc (c x));
      r (sem_eq (c x) (Ptr.null_loc n))
  | F _ ->
      r (Float.neg (c x));
      r (Float.abs (c x));
      r (Float.is_nan (c x))
  | S _ -> ()

let var_ids : (sort * int, v) Hashtbl.t = Hashtbl.create 64
let var_sorts : (int, sort) Hashtbl.t = Hashtbl.create 64
let next_var = ref 0

let get_var s idx : v =
  match Hashtbl.find_opt var_ids (s, idx) with
  | Some x -> x
  | None ->
      let id = !next_var in
      incr next_var;
      Hashtbl.replace var_sorts id s;
      let x = w (mk_var (Var.of_int id) (ty_of_sort s)) in
      Hashtbl.replace var_ids (s, idx) x;
      retain_derived s x;
      x

let pools : (sort, v list) Hashtbl.t = Hashtbl.create 64

let pool_add s x =
  Hashtbl.replace pools s
    (x :: Option.value ~default:[] (Hashtbl.find_opt pools s))

let pool_get s =
  match Hashtbl.find_opt pools s with
  | None | Some [] -> None
  | Some l -> Some (List.nth l (ri (min 40 (List.length l))))

let () =
  Array.iter
    (fun n ->
      List.iter
        (fun z -> ignore (retain (BitVec.mk_masked n z)))
        [
          Z.zero;
          Z.one;
          Z.of_int 2;
          Z.pred (Z.shift_left Z.one (n - 1));
          Z.shift_left Z.one (n - 1);
          Z.pred (Z.shift_left Z.one n);
        ])
    bv_widths;
  Array.iter
    (fun n ->
      for i = -10 to 20 do
        ignore (retain (BitVec.mki_masked n i))
      done)
    bv_widths;
  Array.iter
    (fun n ->
      List.iter
        (fun i -> ignore (retain (Ptr.loc_of_int n i)))
        [ 0; 1; 2; 3; 7 ];
      ignore (retain (Ptr.null n)))
    [| 32; 64 |]

let rec lit s : v =
  retain
  @@
  match s with
  | B -> w (Bool.of_bool (rb ()))
  | V n -> w (bv_lit n)
  | F p -> w (float_lit p)
  | L n -> (
      match ri 4 with
      | 0 -> w (Ptr.null_loc n)
      | 1 -> w (Ptr.loc_of_int n (1 + ri 3))
      | _ -> w (Ptr.loc_of_z n (Z.extract (rz n) 0 (min n 20))))
  | P n -> (
      match ri 3 with
      | 0 -> w (Ptr.null n)
      | _ -> w (Ptr.mk (c (lit (L n))) (c (lit (V n)))))
  | S e ->
      let k = ri 3 in
      w (SSeq.mk ~seq_ty:(t_seq (ty_of_sort e)) (List.init k (fun _ -> lit e)))

let eq_sorts = [| B; V 1; V 8; V 32; V 64; F F32; F F64; L 64; P 64; S (V 8) |]
let exists_sorts = [| B; V 1; V 8; V 32; V 64; F F32; P 64 |]

let rec gen s d : v =
  if d <= 0 || ri 100 < 18 then leaf s
  else
    match ri 100 with
    | n when n < 15 -> leaf s
    | _ ->
        let r = ops s d in
        if
          Stdlib.not (equal_ty (type_type (get_ty r) : T.any ty) (ty_of_sort s))
        then
          failwith
            (Printf.sprintf "ILL-SORTED generation: %s : %s%s" (show r)
               (str ppa_ty (type_type (get_ty r) : T.any ty))
               (" expected " ^ str ppa_ty (ty_of_sort s)));
        r

and leaf s : v =
  retain
  @@
  match ri 100 with
  | n when n < 40 -> get_var s (ri 4)
  | n when n < 70 -> lit s
  | _ -> ( match pool_get s with Some x -> x | None -> get_var s (ri 4))

and ops s d : v =
  let g s' = gen s' (d - 1) in
  let ite_ fam = rec_ fam (w (ite (c (g B)) (c (g s)) (c (g s)))) in
  match s with
  | B -> bool_ops d g ite_
  | V n -> bv_ops n d g ite_
  | F p -> float_ops p d g ite_
  | L n -> (
      match ri 3 with
      | 0 -> rec_ "ptr_loc" (w (Ptr.loc (c (g (P n)))))
      | 1 -> rec_ "ptr_decompose_loc" (w (fst (Ptr.decompose (c (g (P n))))))
      | _ -> ite_ "ite_loc")
  | P n -> (
      match ri 5 with
      | 0 -> rec_ "ptr_mk" (w (Ptr.mk (c (g (L n))) (c (g (V n)))))
      | 1 -> rec_ "ptr_add_ofs" (w (Ptr.add_ofs (c (g (P n))) (c (g (V n)))))
      | 2 -> rec_ "ptr_null" (w (Ptr.null n))
      | 3 ->
          rec_ "ptr_mk_decomp"
            (let l, o = Ptr.decompose (c (g (P n))) in
             w (Ptr.mk l (c (BitVec.add o (c (g (V n)))))))
      | _ -> ite_ "ite_ptr")
  | S e -> (
      match ri 3 with
      | 0 | 1 ->
          let k = ri 4 in
          rec_ "seq_mk"
            (w
               (SSeq.mk
                  ~seq_ty:(t_seq (ty_of_sort e))
                  (List.init k (fun _ -> g e))))
      | _ -> ite_ "ite_seq")

and bool_ops d g ite_ : v =
  let sb () = c (g B) in
  let cmp_bv () =
    let n = pick [| 1; 2; 8; 32; 64 |] in
    (n, c (g (V n)), c (g (V n)))
  in
  match ri 40 with
  | 0 -> rec_ "bool_not" (w (Bool.not (sb ())))
  | 1 | 2 -> rec_ "bool_and" (w (Bool.and_ (sb ()) (sb ())))
  | 3 | 4 -> rec_ "bool_or" (w (Bool.or_ (sb ()) (sb ())))
  | 5 -> ite_ "bool_ite"
  | 6 | 7 | 8 ->
      let s = pick eq_sorts in
      rec_ "sem_eq" (w (sem_eq (c (g s)) (c (g s))))
  | 9 ->
      let s = pick eq_sorts in
      rec_ "sem_eq_untyped" (w (sem_eq_untyped (c (g s)) (c (g s))))
  | 10 ->
      let s = pick eq_sorts in
      let k = ri 5 in
      rec_ "distinct" (w (Bool.distinct (List.init k (fun _ -> c (g s)))))
  | 11 ->
      let s = pick eq_sorts in
      let k = ri 5 in
      rec_ "distinct_seq"
        (w (Bool.distinct_seq (List.to_seq (List.init k (fun _ -> c (g s))))))
  | 12 ->
      let k = ri 4 in
      rec_ "bool_conj" (w (Bool.conj (List.init k (fun _ -> sb ()))))
  | 13 ->
      let b2 = sb () in
      rec_ "bool_and_lazy" (w (Bool.and_lazy (sb ()) (fun () -> b2)))
  | 14 ->
      let b2 = sb () in
      rec_ "bool_or_lazy" (w (Bool.or_lazy (sb ()) (fun () -> b2)))
  | 15 | 16 ->
      let b = sb () and s = pick exists_sorts in
      let o = c (g s) in
      let body x =
        match ri 3 with
        | 0 -> Bool.and_ b (sem_eq x o)
        | 1 -> Bool.or_ b (sem_eq x o)
        | _ -> Bool.and_ (Bool.not b) (sem_eq o x)
      in
      rec_ "exists_1" (w (Bool.exists_1 ~not_in:b (ty_of_sort s) body))
  | 17 ->
      let b = sb () and s1 = pick exists_sorts and s2 = pick exists_sorts in
      let o1 = c (g s1) and o2 = c (g s2) in
      let body x y = Bool.and_ b (Bool.or_ (sem_eq x o1) (sem_eq y o2)) in
      rec_ "exists_2"
        (w (Bool.exists_2 ~not_in:b (ty_of_sort s1) (ty_of_sort s2) body))
  | 18 ->
      let b = sb () in
      let s1 = pick exists_sorts
      and s2 = pick exists_sorts
      and s3 = pick exists_sorts in
      let o1 = c (g s1) and o2 = c (g s3) in
      let body x y z =
        Bool.and_
          (Bool.or_ b (sem_eq x o1))
          (Bool.and_ (sem_eq z o2) (sem_eq y y))
      in
      rec_ "exists_3"
        (w
           (Bool.exists_3 ~not_in:b (ty_of_sort s1) (ty_of_sort s2)
              (ty_of_sort s3) body))
  | 19 | 20 | 21 ->
      let _, a, b = cmp_bv () in
      let signed = rb () in
      if rb () then rec_ "bv_lt" (w (BitVec.lt ~signed a b))
      else rec_ "bv_leq" (w (BitVec.leq ~signed a b))
  | 22 ->
      let _, a, b = cmp_bv () in
      let signed = rb () in
      if rb () then rec_ "bv_gt" (w (BitVec.gt ~signed a b))
      else rec_ "bv_geq" (w (BitVec.geq ~signed a b))
  | 23 ->
      let _, a, b = cmp_bv () in
      rec_ "bv_add_overflows" (w (BitVec.add_overflows ~signed:(rb ()) a b))
  | 24 ->
      let _, a, b = cmp_bv () in
      rec_ "bv_sub_overflows" (w (BitVec.sub_overflows ~signed:(rb ()) a b))
  | 25 ->
      let _, a, b = cmp_bv () in
      rec_ "bv_mul_overflows" (w (BitVec.mul_overflows ~signed:(rb ()) a b))
  | 26 ->
      let n = pick [| 2; 8; 32; 64 |] in
      rec_ "bv_neg_overflows" (w (BitVec.neg_overflows (c (g (V n)))))
  | 27 ->
      let _, a, b = cmp_bv () in
      let signed = rb () in
      let _, o =
        (match ri 3 with
        | 0 -> BitVec.add_checked
        | 1 -> BitVec.sub_checked
        | _ -> BitVec.mul_checked)
          ~signed a b
      in
      rec_ "bv_checked_ovf" (w o)
  | 28 ->
      let n = pick [| 2; 8; 32 |] in
      let _, o = BitVec.neg_checked (c (g (V n))) in
      rec_ "bv_neg_checked_ovf" (w o)
  | 29 ->
      let n = pick [| 1; 2; 8; 32; 64 |] in
      rec_ "bv_to_bool" (w (BitVec.to_bool (c (g (V n)))))
  | 30 ->
      let n = pick [| 32; 64 |] in
      rec_ "ptr_is_null" (w (Ptr.is_null (c (g (P n)))))
  | 31 ->
      let n = pick [| 32; 64 |] in
      if rb () then rec_ "loc_is_null_loc" (w (Ptr.is_null_loc (c (g (L n)))))
      else rec_ "ptr_is_at_null_loc" (w (Ptr.is_at_null_loc (c (g (P n)))))
  | 32 | 33 -> (
      let p = pick all_fps in
      let a = c (g (F p)) and b = c (g (F p)) in
      match ri 5 with
      | 0 -> rec_ "float_eq" (w (Float.eq a b))
      | 1 -> rec_ "float_geq" (w (Float.geq a b))
      | 2 -> rec_ "float_gt" (w (Float.gt a b))
      | 3 -> rec_ "float_leq" (w (Float.leq a b))
      | _ -> rec_ "float_lt" (w (Float.lt a b)))
  | 34 | 35 -> (
      let a = c (g (F (pick all_fps))) in
      match ri 7 with
      | 0 -> rec_ "float_is_normal" (w (Float.is_normal a))
      | 1 -> rec_ "float_is_subnormal" (w (Float.is_subnormal a))
      | 2 -> rec_ "float_is_zero" (w (Float.is_zero a))
      | 3 -> rec_ "float_is_infinite" (w (Float.is_infinite a))
      | 4 -> rec_ "float_is_nan" (w (Float.is_nan a))
      | 5 -> rec_ "float_is_negative" (w (Float.is_negative a))
      | _ -> rec_ "float_is_positive" (w (Float.is_positive a)))
  | 36 -> (
      let n, a, b = cmp_bv () in
      ignore n;
      let open Infix in
      match ri 10 with
      | 0 -> rec_ "infix_cmp" (w (a ==@ b))
      | 1 -> rec_ "infix_cmp" (w (a <@ b))
      | 2 -> rec_ "infix_cmp" (w (a <=@ b))
      | 3 -> rec_ "infix_cmp" (w (a >@ b))
      | 4 -> rec_ "infix_cmp" (w (a >=@ b))
      | 5 -> rec_ "infix_cmp" (w (a <$@ b))
      | 6 -> rec_ "infix_cmp" (w (a <=$@ b))
      | 7 -> rec_ "infix_cmp" (w (a >$@ b))
      | 8 -> rec_ "infix_cmp" (w (a >=$@ b))
      | _ -> rec_ "infix_cmp" (w (a ==?@ b)))
  | 37 -> (
      let open Infix in
      let p = pick [| FP.F32; F64 |] in
      let a = c (g (F p)) and b = c (g (F p)) in
      match ri 5 with
      | 0 -> rec_ "infix_fcmp" (w (a ==.@ b))
      | 1 -> rec_ "infix_fcmp" (w (a <.@ b))
      | 2 -> rec_ "infix_fcmp" (w (a <=.@ b))
      | 3 -> rec_ "infix_fcmp" (w (a >.@ b))
      | _ -> rec_ "infix_fcmp" (w (a >=.@ b)))
  | 38 ->
      let open Infix in
      rec_ "infix_bool"
        (if rb () then w (sb () &&@ sb ()) else w (sb () ||@ sb ()))
  | _ ->
      (* ordering of operands of commutative ops: reuse of pool terms *)
      let s = pick eq_sorts in
      let a = c (g s) in
      rec_ "sem_eq_sym"
        (w (if rb () then sem_eq a (c (g s)) else sem_eq (c (g s)) a))
      |> fun x ->
      ignore d;
      x

and bv_ops n _d g ite_ : v =
  let a () = c (g (V n)) in
  let pick_ck () = pick checkeds in
  match ri 48 with
  | 0 | 1 -> rec_ "bv_add" (w (BitVec.add ~checked:(pick_ck ()) (a ()) (a ())))
  | 2 | 3 -> rec_ "bv_sub" (w (BitVec.sub ~checked:(pick_ck ()) (a ()) (a ())))
  | 4 | 5 -> rec_ "bv_mul" (w (BitVec.mul ~checked:(pick_ck ()) (a ()) (a ())))
  | 6 ->
      rec_ "bv_div"
        (w (BitVec.div ~signed:(rb ()) (a ()) (BitVec.cast_nonzero (a ()))))
  | 7 ->
      rec_ "bv_rem"
        (w (BitVec.rem ~signed:(rb ()) (a ()) (BitVec.cast_nonzero (a ()))))
  | 8 ->
      rec_ "bv_div_nz" (w (BitVec.div ~signed:(rb ()) (a ()) (c (gen (V n) 0))))
  | 9 -> rec_ "bv_mod" (w (BitVec.mod_ (a ()) (a ())))
  | 10 -> rec_ "bv_neg" (w (BitVec.neg ~checked:(rb ()) (a ())))
  | 11 ->
      let signed = rb () in
      let f =
        match ri 3 with
        | 0 -> BitVec.add_checked
        | 1 -> BitVec.sub_checked
        | _ -> BitVec.mul_checked
      in
      rec_ "bv_checked_val" (w (fst (f ~signed (a ()) (a ()))))
  | 12 -> rec_ "bv_neg_checked_val" (w (fst (BitVec.neg_checked (a ()))))
  | 13 ->
      rec_ "bv_no_ovf_unsafe"
        (w (BitVec.no_ovf_unsafe (BitVec.add (a ()) (a ()))))
  | 14 | 15 -> rec_ "bv_and" (w (BitVec.and_ (a ()) (a ())))
  | 16 | 17 -> rec_ "bv_or" (w (BitVec.or_ (a ()) (a ())))
  | 18 -> rec_ "bv_xor" (w (BitVec.xor (a ()) (a ())))
  | 19 -> rec_ "bv_shl" (w (BitVec.shl (a ()) (a ())))
  | 20 -> rec_ "bv_lshr" (w (BitVec.lshr (a ()) (a ())))
  | 21 -> rec_ "bv_ashr" (w (BitVec.ashr (a ()) (a ())))
  | 22 | 23 -> rec_ "bv_not" (w (BitVec.not (a ())))
  | 24 | 25 | 26 -> (
      (* concat: n = n1 + n2 *)
      let splits =
        match n with
        | 1 -> []
        | 2 -> [ (1, 1) ]
        | 8 -> [ (2, 6); (1, 7); (4, 4); (6, 2) ]
        | 16 -> [ (8, 8); (1, 15) ]
        | 32 -> [ (8, 24); (1, 31); (16, 16); (24, 8) ]
        | 64 -> [ (32, 32); (8, 56); (1, 63); (16, 48) ]
        | 128 -> [ (64, 64) ]
        | _ -> [ (1, n - 1) ]
      in
      match splits with
      | [] -> ite_ "bv_ite"
      | l ->
          let n1, n2 = List.nth l (ri (List.length l)) in
          rec_ "bv_concat" (w (BitVec.concat (c (g (V n1))) (c (g (V n2))))))
  | 27 | 28 -> (
      let smaller = List.filter (fun m -> m < n) (Array.to_list bv_widths) in
      match smaller with
      | [] -> ite_ "bv_ite"
      | l ->
          let m = List.nth l (ri (List.length l)) in
          rec_ "bv_extend"
            (w (BitVec.extend ~signed:(rb ()) (n - m) (c (g (V m))))))
  | 29 | 30 -> (
      let larger = List.filter (fun m -> m > n) (Array.to_list bv_widths) in
      match larger with
      | [] -> ite_ "bv_ite"
      | l ->
          let m = List.nth l (ri (List.length l)) in
          let from_ = ri (m - n + 1) in
          let from_ = if ri 3 = 0 then 0 else from_ in
          rec_ "bv_extract"
            (w (BitVec.extract from_ (from_ + n - 1) (c (g (V m))))))
  | 31 -> rec_ "bv_of_bool" (w (BitVec.of_bool n (c (g B))))
  | 32 -> rec_ "bv_not_bool" (w (BitVec.not_bool (a ())))
  | 33 -> (
      match n with
      | 16 | 32 | 64 | 128 -> (
          let p =
            match n with 16 -> FP.F16 | 32 -> F32 | 64 -> F64 | _ -> F128
          in
          match Float.to_bits_opt (c (g (F p))) with
          | Some x -> rec_ "float_to_bits_opt" (w x)
          | None -> ite_ "bv_ite")
      | _ -> ite_ "bv_ite")
  | 34 | 35 ->
      let p = pick all_fps in
      rec_ "bv_of_float"
        (w
           (BitVec.of_float ~rounding:(pick rms) ~signed:(rb ()) ~size:n
              (c (g (F p)))))
  | 36 -> (
      match n with
      | 64 -> rec_ "ptr_ofs" (w (Ptr.ofs (c (g (P 64)))))
      | 32 -> rec_ "ptr_ofs" (w (Ptr.ofs (c (g (P 32)))))
      | 128 -> ite_ "bv_ite"
      | _ ->
          rec_ "bv_decomp_ofs"
            (w
               ( snd (Ptr.decompose (c (g (P 64)))) |> fun x ->
                 BitVec.extract 0 (n - 1) (c x) )))
  | 37 -> (
      let open Infix in
      let x = a () and y = a () in
      match ri 12 with
      | 0 -> rec_ "infix_arith" (w (x +@ y))
      | 1 -> rec_ "infix_arith" (w (x -@ y))
      | 2 -> rec_ "infix_arith" (w (x *@ y))
      | 3 -> rec_ "infix_arith" (w (x +!@ y))
      | 4 -> rec_ "infix_arith" (w (x -!@ y))
      | 5 -> rec_ "infix_arith" (w (x *!@ y))
      | 6 -> rec_ "infix_arith" (w (x +!!@ y))
      | 7 -> rec_ "infix_arith" (w (x -!!@ y))
      | 8 -> rec_ "infix_arith" (w (x *!!@ y))
      | 9 -> rec_ "infix_arith" (w ~-!x)
      | 10 -> rec_ "infix_arith" (w ~-!!x)
      | _ -> rec_ "infix_arith" (w ~-x))
  | 38 -> (
      let open Infix in
      let x = a () and y = a () in
      match ri 6 with
      | 0 -> rec_ "infix_bit" (w (x <<@ y))
      | 1 -> rec_ "infix_bit" (w (x >>@ y))
      | 2 -> rec_ "infix_bit" (w (x >>>@ y))
      | 3 -> rec_ "infix_bit" (w (x ^@ y))
      | 4 -> rec_ "infix_bit" (w (x &@ y))
      | _ -> rec_ "infix_bit" (w (x |@ y)))
  | 39 -> (
      let open Infix in
      let x = a () and y = c (g (V n)) in
      match ri 4 with
      | 0 -> rec_ "infix_div" (w (x /@ cast_nonzero_ y))
      | 1 -> rec_ "infix_div" (w (x /$@ cast_nonzero_ y))
      | 2 -> rec_ "infix_div" (w (x %@ cast_nonzero_ y))
      | _ -> rec_ "infix_div" (w (x %$@ cast_nonzero_ y)))
  | 40 ->
      let open Infix in
      let x = a () and y = a () in
      let r, _ =
        match ri 6 with
        | 0 -> x +?@ y
        | 1 -> x +$?@ y
        | 2 -> x -?@ y
        | 3 -> x -$?@ y
        | 4 -> x *?@ y
        | _ -> x *$?@ y
      in
      rec_ "infix_checked" (w r)
  | 41 ->
      let open Infix in
      let r, _ = ~-?(a ()) in
      rec_ "infix_checked" (w r)
  | 42 | 43 -> (
      let sizes = [| 8; 32; 64 |] in
      match ri 2 with
      | 0 -> ite_ "bv_ite"
      | _ ->
          ignore sizes;
          rec_ "bv_mki" (w (BitVec.mki_masked n (ri 20 - 10))))
  | _ -> ite_ "bv_ite"

and cast_nonzero_ y = BitVec.cast_nonzero y

and float_ops p d g ite_ : v =
  ignore d;
  let a () = c (g (F p)) in
  let open Infix in
  match ri 32 with
  | 0 -> rec_ "float_add" (w (Float.add (a ()) (a ())))
  | 1 -> rec_ "float_sub" (w (Float.sub (a ()) (a ())))
  | 2 -> rec_ "float_mul" (w (Float.mul (a ()) (a ())))
  | 3 -> rec_ "float_div" (w (Float.div (a ()) (a ())))
  | 4 -> rec_ "float_rem" (w (Float.rem (a ()) (a ())))
  | 5 -> rec_ "float_fmod" (w (Float.fmod (a ()) (a ())))
  | 6 ->
      let x = a () and y = a () in
      rec_ "float_fmod_of_rem" (w (Float.fmod_of_rem (Float.rem x y) x y))
  | 7 -> rec_ "float_fma" (w (Float.fma (a ()) (a ()) (a ())))
  | 8 -> rec_ "float_min" (w (Float.min (a ()) (a ())))
  | 9 -> rec_ "float_max" (w (Float.max (a ()) (a ())))
  | 10 -> rec_ "float_minimum" (w (Float.minimum (a ()) (a ())))
  | 11 -> rec_ "float_maximum" (w (Float.maximum (a ()) (a ())))
  | 12 -> rec_ "float_abs" (w (Float.abs (a ())))
  | 13 -> rec_ "float_neg" (w (Float.neg (a ())))
  | 14 -> rec_ "float_sqrt" (w (Float.sqrt (a ())))
  | 15 | 16 ->
      let q = pick all_fps in
      rec_ "float_cast"
        (w (Float.cast ~rounding:(pick rms) ~fp:p (c (g (F q)))))
  | 17 | 18 -> rec_ "float_round" (w (Float.round (pick rms) (a ())))
  | 19 | 20 ->
      let m = pick [| 8; 32; 64 |] in
      rec_ "bv_to_float"
        (w
           (BitVec.to_float ~rounding:(pick rms) ~signed:(rb ()) ~fp:p
              (c (g (V m)))))
  | 21 | 22 ->
      rec_ "bv_to_float_raw" (w (BitVec.to_float_raw (c (g (V (fp_size p))))))
  | 23 -> rec_ "float_infix" (w (a () +.@ a ()))
  | 24 -> rec_ "float_infix" (w (a () -.@ a ()))
  | 25 -> rec_ "float_infix" (w (a () *.@ a ()))
  | 26 -> rec_ "float_infix" (w (a () /.@ a ()))
  | 27 -> rec_ "float_of_z" (w (Float.of_z p (Z.of_int (ri 40 - 20))))
  | 28 -> (
      let x = a () in
      match Float.approx (fun f -> f *. 2.0) x with
      | Some r -> rec_ "float_approx" (w r)
      | None -> ite_ "float_ite")
  | 29 -> (
      let x = a () and y = a () in
      match Float.approx2 (fun f g -> f +. g) x y with
      | Some r -> rec_ "float_approx2" (w r)
      | None -> ite_ "float_ite")
  | _ -> ite_ "float_ite"

(* ------------------------------------------------------------------ *)
(* Range facts (interval analysis, implication)                        *)
(* ------------------------------------------------------------------ *)

let gen_fact () : v =
  let n = pick [| 2; 8; 8; 32; 64 |] in
  let x = get_var (V n) (ri 3) in
  let k = bv_lit n in
  let k = if ri 3 = 0 then c (BitVec.mki n (ri 6)) else c k in
  let x' =
    match ri 6 with
    | 0 -> w (BitVec.add (c x) (c (bv_lit n)))
    | 1 when n > 2 -> w (BitVec.extract 0 ((n / 2) - 1) (c x))
    | _ -> x
  in
  let k =
    match (n, Typed.size_of_int (c x')) with
    | _, m when m <> n -> BitVec.mk m (Z.extract (rz m) 0 m)
    | _ -> k
  in
  let r =
    match ri 12 with
    | 0 -> BitVec.lt ~signed:false (c x') k
    | 1 -> BitVec.leq ~signed:false (c x') k
    | 2 -> BitVec.lt ~signed:true (c x') k
    | 3 -> BitVec.leq ~signed:true (c x') k
    | 4 -> BitVec.gt ~signed:false (c x') k
    | 5 -> BitVec.geq ~signed:true (c x') k
    | 6 -> sem_eq (c x') k
    | 7 -> Bool.not (sem_eq (c x') k)
    | 8 -> Bool.not (BitVec.lt ~signed:false (c x') k)
    | 9 -> Bool.not (BitVec.leq ~signed:true (c x') k)
    | 10 -> BitVec.lt ~signed:false k (c x')
    | _ ->
        Bool.and_
          (BitVec.leq ~signed:false (c x') k)
          (BitVec.leq ~signed:false
             (BitVec.mki (Typed.size_of_int (c x')) 1)
             (c x'))
  in
  rec_ "fact" (w r)

(* ------------------------------------------------------------------ *)
(* Per-term analyses                                                   *)
(* ------------------------------------------------------------------ *)

let guard f = try f () with e -> "EXN " ^ Printexc.to_string e

(* Memoising recursive encoder; records [Declare] effects in the order they are
   emitted. Fresh memo table per term, so every stanza lists its own
   declarations. *)
let encode (x : v) : string =
  let log = Buffer.create 64 in
  let rec collect : 'a. depth:int -> (unit -> 'a) -> 'a =
   fun ~depth f ->
    try f ()
    with effect Decls.Declare d, k ->
      Buffer.add_string log
        (Printf.sprintf "%sdecl key=%s\n" (String.make depth ' ') d.key);
      let cmds = ref [] in
      collect ~depth:(depth + 2) (fun () ->
          d.commands (fun s -> cmds := s :: !cmds));
      List.iter
        (fun s ->
          Buffer.add_string log
            (Printf.sprintf "%s  cmd %s\n" (String.make depth ' ')
               (str Smt.pp_sexp s)))
        (List.rev !cmds);
      Effect.Deep.continue k ()
  in
  let memo = Lang.Hashtbl.create 16 in
  let rec sort_of_ty ty = Lang.encode_ty ~sort_of_ty ty in
  let rec enc t =
    match Lang.Hashtbl.find_opt memo t with
    | Some k -> k
    | None ->
        let k = Lang.encode_node ~sort_of_ty ~encode_child:enc t in
        Lang.Hashtbl.add memo t k;
        k
  in
  let k = collect ~depth:0 (fun () -> enc (Shim.to_lang x)) in
  Buffer.contents log ^ "sexp " ^ str Smt.pp_sexp k

let pp_lang fmt (l : Lang.t) = pp_v fmt (retain (Shim.of_lang l))

let pp_range = function
  | None -> "None"
  | Some (var, size, (sign, (lo, hi))) ->
      Printf.sprintf "Some (%s, %d, (%s, (%s, %s)))" (str Var.pp var) size
        (match sign with Lang.Pos -> "Pos" | Neg -> "Neg")
        (Z.to_string lo) (Z.to_string hi)

let vars_of (x : v) =
  let l = ref [] in
  Lang.iter_vars (Shim.to_lang x) (fun (var, ty) ->
      l :=
        Printf.sprintf "%s:%s" (str Var.pp var) (str Shim.lang_ty_pp ty) :: !l);
  List.rev !l

let first_var (x : v) =
  let r = ref None in
  Lang.iter_vars (Shim.to_lang x) (fun (var, _) ->
      if !r = None then r := Some var);
  !r

(* A fixed literal for a sort, if one exists (None for sequences). *)
let rec fixed_lit = function
  | B -> Some (w (Bool.of_bool true))
  | V n -> Some (w (BitVec.mki_masked n 5))
  | F p -> Some (w (Float.one p))
  | L n -> Some (w (Ptr.loc_of_int n 7))
  | P n -> Some (w (Ptr.mk (c (Ptr.loc_of_int n 7)) (c (BitVec.mki n 3))))
  | S e -> (
      match fixed_lit e with
      | Some x -> Some (w (SSeq.mk ~seq_ty:(t_seq (ty_of_sort e)) [ x; x ]))
      | None -> None)

let sort_of_var var = Hashtbl.find_opt var_sorts (Var.to_int var)

let eval_var _sv var _ty : Lang.t =
  match sort_of_var var with
  | Some s when Var.to_int var mod 2 = 0 -> (
      match fixed_lit s with
      | Some x -> Shim.to_lang x
      | None -> Shim.to_lang (mk_var var (ty_of_sort s)))
  | Some s -> Shim.to_lang (mk_var var (ty_of_sort s))
  | None -> _sv

let missing_var var ty = mk_var var ty

let subst_first (x : v) sort =
  match (first_var x, sort) with
  | None, _ -> "no var"
  | Some var, _ -> (
      match Option.bind (sort_of_var var) fixed_lit with
      | None -> "no literal"
      | Some l -> (
          let e =
            Expr.of_value
              (mk_var var
                 (ty_of_sort (Hashtbl.find var_sorts (Var.to_int var))))
          in
          match Expr.Subst.learn Expr.Subst.empty e l with
          | None -> "learn-var failed"
          | Some s ->
              let r, s' = Expr.Subst.apply ~missing_var s (Expr.of_value x) in
              Printf.sprintf "%s  [subst %s]"
                (show (retain (w r)))
                (str Expr.Subst.pp s')))

let learn_fixed (x : v) sort =
  match fixed_lit sort with
  | None -> "no literal"
  | Some l -> (
      match Expr.Subst.learn Expr.Subst.empty (Expr.of_value x) l with
      | None -> "None"
      | Some s -> "Some " ^ str Expr.Subst.pp s)

let gc_stress = Sys.getenv_opt "BV_GOLDEN_GC" <> None
let maybe_gc () = if gc_stress then Gc.compact ()

let accessors (x : v) sort =
  let o f = function Some y -> f y | None -> "-" in
  let fl =
    match sort with
    | F _ ->
        Printf.sprintf " to_float_opt=%s sign_bit_opt=%s to_bits_opt=%s"
          (o string_of_float (Float.to_float_opt (c x)))
          (o string_of_bool (Float.sign_bit_opt (c x)))
          (o (fun y -> show (w y)) (Float.to_bits_opt (c x)))
    | _ -> ""
  in
  Printf.sprintf "to_bool=%s to_z=%s%s"
    (o string_of_bool (Bool.to_bool x))
    (o Z.to_string (BitVec.to_z x))
    fl

let stanza idx fam (x : v) sort =
  maybe_gc ();
  let l = Shim.to_lang x in
  Printf.printf "== term %d [%s]\n" idx fam;
  Printf.printf "pp: %s\n" (show x);
  Printf.printf "ty: %s\n"
    (guard (fun () -> str ppa_ty (type_type (get_ty x) : v ty)));
  Printf.printf "cost: %s\n" (guard (fun () -> string_of_int (Lang.cost l)));
  Printf.printf "encode:\n%s\n" (guard (fun () -> encode x));
  Printf.printf "as_range: %s\n" (guard (fun () -> pp_range (Lang.as_range l)));
  Printf.printf "vars: [%s]\n"
    (guard (fun () -> String.concat "; " (vars_of x)));
  Printf.printf "subst: %s\n" (guard (fun () -> subst_first x sort));
  Printf.printf "eval_force: %s\n"
    (guard (fun () -> str pp_lang (Lang.eval ~force:true l)));
  Printf.printf "eval_var: %s\n"
    (guard (fun () -> str pp_lang (Lang.eval ~eval_var l)));
  Printf.printf "learn: %s\n" (guard (fun () -> learn_fixed x sort));
  Printf.printf "accessors: %s\n" (guard (fun () -> accessors x sort));
  Printf.printf "is_literal=%b is_bool=%b\n" (Lang.is_literal l)
    (Lang.is_bool l)

let pair_stanza idx (a : v) (b : v) =
  maybe_gc ();
  let la = Shim.to_lang a and lb = Shim.to_lang b in
  Printf.printf "== pair %d\n" idx;
  Printf.printf "pc: %s\nq: %s\n" (show a) (show b);
  Printf.printf "implies_or_contradicts: %s\n"
    (guard (fun () ->
         match Lang.implies_or_contradicts ~q:lb ~neg_q:(Lang.not_ lb) la with
         | None -> "None"
         | Some b -> "Some " ^ string_of_bool b));
  Printf.printf "sure_neq: %b %b\n"
    (guard (fun () -> string_of_bool (Lang.sure_neq la lb)) = "true")
    (guard (fun () -> string_of_bool (Lang.sure_neq lb la)) = "true")

(* ------------------------------------------------------------------ *)
(* Main                                                                *)
(* ------------------------------------------------------------------ *)

let all_sorts =
  [|
    (B, 24);
    (V 1, 4);
    (V 2, 6);
    (V 8, 14);
    (V 16, 3);
    (V 32, 14);
    (V 64, 12);
    (V 128, 2);
    (F F16, 3);
    (F F32, 5);
    (F F64, 5);
    (F F128, 3);
    (L 64, 2);
    (P 64, 4);
    (P 32, 2);
    (S (V 8), 2);
    (S B, 1);
  |]

let total_w = Array.fold_left (fun a (_, k) -> a + k) 0 all_sorts

let pick_sort () =
  let r = ref (ri total_w) in
  let res = ref B in
  (try
     Array.iter
       (fun (s, k) ->
         if !r < k then (
           res := s;
           raise Exit)
         else r := !r - k)
       all_sorts
   with Exit -> ());
  !res

let n_terms = 2000
let n_facts = 400

let () =
  (* No major cycle should complete during the run (see [keep] above). *)
  if Stdlib.not gc_stress then
    Gc.set
      {
        (Gc.get ()) with
        space_overhead = 1_000_000_000;
        minor_heap_size = 256 * 1024 * 1024;
        custom_major_ratio = 1_000_000;
        custom_minor_ratio = 1_000_000;
        custom_minor_max_size = max_int / 2;
      };
  let minor0 = (Gc.quick_stat ()).minor_collections in
  Printf.printf "bv_golden seed=%d\n" seed;
  let bools = ref [] in
  for i = 0 to n_terms - 1 do
    let s = pick_sort () in
    let d = 1 + ri 6 in
    maybe_gc ();
    let rec bounded d =
      let x = gen s d in
      if d > 1 && String.length (show x) > 2500 then bounded (d - 1) else x
    in
    match bounded d with
    | x ->
        pool_add s x;
        if s = B then bools := x :: !bools;
        stanza i "gen" x s
    | exception e ->
        Printf.printf "== term %d RAISED %s\n" i (Printexc.to_string e);
        Printf.eprintf "RAISED %d: %s\n%s\n" i (Printexc.to_string e)
          (Printexc.get_backtrace ())
  done;
  let bools = Array.of_list (List.rev !bools) in
  (* consecutive pairs of generated booleans *)
  Array.iteri
    (fun i b ->
      if i + 1 < Array.length bools then pair_stanza i b bools.(i + 1))
    bools;
  (* range facts *)
  let facts =
    Array.init n_facts (fun _ ->
        try gen_fact ()
        with e ->
          Printf.printf "fact raised %s\n" (Printexc.to_string e);
          w (Bool.of_bool true))
  in
  Array.iteri (fun i f -> stanza (n_terms + i) "fact" f B) facts;
  Array.iteri
    (fun i f ->
      pair_stanza (10000 + i) f facts.((i + 1) mod n_facts);
      pair_stanza (20000 + i) f facts.(((i * 7) + 3) mod n_facts);
      pair_stanza (30000 + i) f (w (Bool.not (c facts.((i + 5) mod n_facts)))))
    facts;
  (* coverage *)
  let fams = List.sort Stdlib.compare !fam_order in
  Printf.eprintf "%-28s %8s %8s\n" "family" "uses" "distinct";
  List.iter
    (fun f ->
      let n, set = Hashtbl.find cov f in
      Printf.eprintf "%-28s %8d %8d\n" f !n (Hashtbl.length set))
    fams;
  Printf.eprintf "families: %d\n" (List.length fams);
  let gs = Gc.quick_stat () in
  Printf.eprintf "gc: minor_words=%.0f minor_collections_during_run=%d\n"
    gs.minor_words
    (gs.minor_collections - minor0)
