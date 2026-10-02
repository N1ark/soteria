(* Sanity checks of the standalone stack ([Bv_new]) on a handful of terms; the
   comparison with the old simplifier is the job of the differential harness. *)

open Bv_new
open Bv_new.Types
module Old = Soteria.Bv_values.Svalue
module OS = Old.Make (Old.Dummy_ext) ()
module F = Floatml.AnyFloat

(* The old stack is created first, so that its constants are its first nodes (it
   has its own table: the order of creation matters only inside a stack). *)

let term = Alcotest.testable pp equal
let uc : checked = { signed = false; unsigned = false }
let var i ty = mk_var (Soteria.Symex.Var.of_int i) ty
let bv8 = mk_bv 8
let x = var 1 (t_bv 8)
let y = var 2 (t_bv 8)
let p = var 3 t_bool
let q = var 4 t_bool
let z = Z.of_int
let i = Z.of_int

let init_order () =
  (* the same tags as the old functor application: v_true, v_false, the zero
     literals of 1 to 256 bits, then the one literals of 1 to 256 bits *)
  Alcotest.(check int) "v_true" OS.v_true.tag v_true.tag;
  Alcotest.(check int) "v_false" OS.v_false.tag v_false.tag;
  for n = 1 to 256 do
    Alcotest.(check int) "zero" (OS.BitVec.zero n).tag (bv_zero n).tag;
    Alcotest.(check int) "one" (OS.BitVec.one n).tag (bv_one n).tag
  done;
  Alcotest.(check (list int))
    "tags" [ 0; 1; 2; 3; 257; 258 ]
    [
      v_true.tag;
      v_false.tag;
      (bv_zero 1).tag;
      (bv_zero 2).tag;
      (bv_zero 256).tag;
      (bv_one 1).tag;
    ];
  Alcotest.(check int) "one 256" 513 (bv_one 256).tag

let hashcons () =
  Alcotest.(check bool) "physical" true (bv8 (z 5) == bv8 (z 5));
  Alcotest.(check bool) "distinct sorts" false (bv_zero 8 == bv_zero 9)

let bools () =
  let open Rules in
  Alcotest.check term "not not" p (b_not (b_not p));
  Alcotest.check term "and true" p (b_and p v_true);
  Alcotest.check term "and false" v_false (b_and v_false p);
  Alcotest.check term "and not" v_false (b_and p (b_not p));
  Alcotest.check term "or true" v_true (b_or p v_true);
  Alcotest.check term "ite true" x (b_ite v_true x y);
  Alcotest.check term "ite same" x (b_ite p x x);
  Alcotest.check term "ite bool" p (b_ite p v_true v_false);
  Alcotest.check term "eq same" v_true (sem_eq x x);
  Alcotest.check term "eq bools" v_true (sem_eq v_true v_true);
  Alcotest.check term "eq lits" v_false (sem_eq (bv8 (z 1)) (bv8 (z 2)));
  (* commutative operators put the smaller tag first *)
  Alcotest.check term "comm" (b_and p q) (b_and q p);
  Alcotest.(check bool)
    "distinct lits" true
    (equal v_false (b_distinct [ bv8 (z 1); bv8 (z 1) ]))

let bitvecs () =
  let open Rules in
  Alcotest.check term "add wraps"
    (bv8 (z 44))
    (bv_add uc (bv8 (z 200)) (bv8 (z 100)));
  Alcotest.check term "sub wraps"
    (bv8 (z 255))
    (bv_sub uc (bv8 (z 0)) (bv8 (z 1)));
  Alcotest.check term "mul wraps"
    (bv8 (z 32))
    (bv_mul uc (bv8 (z 200)) (bv8 (z 100)));
  Alcotest.check term "not" (bv8 (z 0xF0)) (bv_not (bv8 (z 0x0F)));
  Alcotest.check term "neg" (bv8 (z 255)) (bv_neg false (bv8 (z 1)));
  Alcotest.check term "and"
    (bv8 (z 0x0A))
    (bv_and (bv8 (z 0x0F)) (bv8 (z 0xFA)));
  Alcotest.check term "shl" (bv8 (z 0x80)) (bv_shl (bv8 (z 1)) (bv8 (z 7)));
  Alcotest.check term "shl big" (bv8 (z 0)) (bv_shl (bv8 (z 1)) (bv8 (z 9)));
  Alcotest.check term "ashr" (bv8 (z 0xFF)) (bv_ashr (bv8 (z 0x80)) (bv8 (z 9)));
  Alcotest.check term "extract"
    (mk_bv 4 (z 0xB))
    (bv_extract (i 0) (i 3) (bv8 (z 0xAB)));
  Alcotest.check term "concat"
    (mk_bv 16 (z 0xAB12))
    (bv_concat (bv8 (z 0xAB)) (bv8 (z 0x12)));
  Alcotest.check term "add zero" x (bv_add uc x (bv_zero 8));
  Alcotest.check term "add comm" (bv_add uc x y) (bv_add uc y x);
  Alcotest.check term "lt lits" v_true (bv_lt false (bv8 (z 1)) (bv8 (z 2)));
  Alcotest.check term "add ovf" v_true
    (bv_add_overflows false (bv8 (z 200)) (bv8 (z 100)));
  Alcotest.check term "mul ovf" v_false
    (bv_mul_overflows false (bv8 (z 10)) (bv8 (z 10)));
  Alcotest.check_raises "sorts"
    (Assert_failure ("", 0, 0))
    (fun () ->
      try ignore (bv_add uc x (mk_bv 16 (z 1)))
      with Assert_failure _ -> raise (Assert_failure ("", 0, 0)))

let floats () =
  let open Rules in
  let f v = mk_float (F.of_float F32 v) in
  Alcotest.check term "fadd" (f 3.) (float_add (f 1.) (f 2.));
  Alcotest.check term "fmul" (f 6.) (float_mul (f 2.) (f 3.));
  Alcotest.check term "feq nan" v_false (float_eq (mk_float (F.nan F32)) (f 1.));
  Alcotest.check term "feq lits" v_true (float_eq (f 1.) (f 1.));
  Alcotest.check term "flt" v_true (float_lt (f 1.) (f 2.));
  Alcotest.check term "eq floats" v_true (sem_eq (f 1.) (f 1.));
  Alcotest.check term "eq floats nan" v_true
    (sem_eq (mk_float (F.nan F32)) (mk_float (F.nan F32)));
  let fx = var 5 (t_float F32) in
  Alcotest.check term "abs abs" (float_abs fx) (float_abs (float_abs fx));
  Alcotest.check term "neg neg" fx (float_neg (float_neg fx));
  Alcotest.check term "fabs lit" (f 1.) (float_abs (f (-1.)));
  Alcotest.check term "fmod" (f 1.) (float_fmod (f 7.) (f 3.));
  Alcotest.check term "feq same"
    (b_not (float_is_floatclass NaN fx))
    (float_eq fx fx)

let ptrs () =
  let open Rules in
  let l1 = mk_loc 64 (z 1) and l2 = mk_loc 64 (z 2) in
  let o = var 6 (t_bv 64) in
  let pt = mk_ptr l1 o in
  Alcotest.(check bool) "ptr sort" true (pt.ty = t_ptr 64);
  Alcotest.check term "loc" l1 (ptr_loc pt);
  Alcotest.check term "ofs" o (ptr_ofs pt);
  Alcotest.check term "eq locs" v_false (sem_eq l1 l2);
  Alcotest.check term "eq locs same" v_true (sem_eq l1 (mk_loc 64 (z 1)));
  Alcotest.check term "eq ptrs" v_false (sem_eq pt (mk_ptr l2 o));
  Alcotest.check term "eq ptrs ofs"
    (sem_eq o (var 7 (t_bv 64)))
    (sem_eq pt (mk_ptr l1 (var 7 (t_bv 64))));
  Alcotest.check term "null" v_true
    (sem_eq
       (mk_ptr (null_loc 64) (bv_zero 64))
       (mk_ptr (null_loc 64) (bv_zero 64)));
  let pv = var 8 (t_ptr 64) in
  Alcotest.(check bool)
    "loc of var stays" true
    (match (ptr_loc pv).kind with Op1 (GetPtrLoc, _) -> true | _ -> false)

let exists () =
  let open Rules in
  let v1 = Soteria.Symex.Var.of_int 10 and v2 = Soteria.Symex.Var.of_int 11 in
  let a = var 10 (t_bv 8) in
  let body = sem_eq a x in
  Alcotest.check term "unused binder dropped" body
    (mk_exists [ (v2, t_bv 8) ] body);
  match (mk_exists [ (v1, t_bv 8); (v2, t_bv 8) ] body).kind with
  | Exists ([ (v, _) ], _) ->
      Alcotest.(check int) "kept" 10 (Soteria.Symex.Var.to_int v)
  | _ -> Alcotest.fail "expected an Exists with one binder"

let print () =
  Alcotest.(check string)
    "pp" "(and (var 3 : bool) (var 4 : bool))"
    (show (Rules.b_and p q));
  Alcotest.(check string) "pp bv" "(bv bv8 5)" (show (bv8 (z 5)))

let () =
  Alcotest.run "bv_new"
    [
      ( "bv_new",
        [
          Alcotest.test_case "init order" `Quick init_order;
          Alcotest.test_case "hash-consing" `Quick hashcons;
          Alcotest.test_case "bools" `Quick bools;
          Alcotest.test_case "bitvecs" `Quick bitvecs;
          Alcotest.test_case "floats" `Quick floats;
          Alcotest.test_case "pointers" `Quick ptrs;
          Alcotest.test_case "exists" `Quick exists;
          Alcotest.test_case "print" `Quick print;
        ] );
    ]
