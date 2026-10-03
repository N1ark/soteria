module Sv = Soteria.Bv_values.Lang.L.Svalue
module Eval = Soteria.Bv_values.Lang.L.Eval
open Sv

let ty = Sv.t_bv 8
let var i = mk_var (Soteria.Symex.Var.of_int i) ty
let x = var 1
let y = var 2
let z = var 3
let c n = BitVec.mki 8 n
let b = mk_var (Soteria.Symex.Var.of_int 4) Sv.t_bool
let b' = mk_var (Soteria.Symex.Var.of_int 5) Sv.t_bool
let value = Alcotest.testable Sv.pp Sv.equal

let subst_vars l _ v _ty =
  match List.find_opt (fun (v', _) -> Soteria.Symex.Var.equal v v') l with
  | Some (_, r) -> r
  | None -> mk_var v _ty

let eval_with l =
  Eval.eval ~eval_var:(fun sv v ty ->
      ignore sv;
      subst_vars l () v ty)

let id_of (v : Sv.t) =
  match v.kind with
  | Soteria.Bv_values.Lang.Types.Var i -> i
  | _ -> assert false

let exists_body y x =
  Bool.and_ (BitVec.lt ~signed:false y x) (Bool.sem_eq y (c 5))

let mk_ex y x = Bool.mk_exists [ (id_of y, ty) ] (exists_body y x)

let test_exists_substitutes_free () =
  let t = mk_ex y x in
  (match (t : Sv.t).kind with
  | Soteria.Bv_values.Lang.Types.Exists _ -> ()
  | _ -> Alcotest.fail "not an Exists");
  let res = eval_with [ (id_of x, z) ] t in
  Alcotest.check value "free var substituted, bound var kept" (mk_ex y z) res

let test_exists_bound_not_substituted () =
  let t = mk_ex y x in
  let res = eval_with [ (id_of x, z); (id_of y, c 9) ] t in
  Alcotest.check value "bound var not substituted" (mk_ex y z) res

let test_exists_unchanged () =
  let t = mk_ex y x in
  let res = eval_with [ (id_of y, c 9) ] t in
  Alcotest.(check bool) "physically unchanged" true (res == t)

let test_ite_guard_var_replaced () =
  let t = Bool.ite b x z in
  let res = eval_with [ (id_of b, b') ] t in
  Alcotest.check value "new guard used" (Bool.ite b' x z) res

let test_ite_guard_literal () =
  let t = Bool.ite b x z in
  let res =
    eval_with [ (id_of b, Bool.v_true); (id_of x, c 1); (id_of z, c 2) ] t
  in
  Alcotest.check value "true picks then" (c 1) res;
  let res =
    eval_with [ (id_of b, Bool.v_false); (id_of x, c 1); (id_of z, c 2) ] t
  in
  Alcotest.check value "false picks else" (c 2) res

let test_ite_lazy () =
  let t = Bool.ite b x z in
  let eval_var _ v ty =
    if Soteria.Symex.Var.equal v (id_of b) then Bool.v_true
    else if Soteria.Symex.Var.equal v (id_of z) then
      Alcotest.fail "else branch evaluated"
    else mk_var v ty
  in
  let res = Eval.eval ~eval_var t in
  Alcotest.check value "lazy" x res

let test_ite_unchanged () =
  let t = Bool.ite b x z in
  Alcotest.(check bool) "physically unchanged" true (eval_with [] t == t)

let () =
  Alcotest.run "bv_values_eval"
    [
      ( "exists",
        [
          Alcotest.test_case "substitutes free variables" `Quick
            test_exists_substitutes_free;
          Alcotest.test_case "does not substitute bound variables" `Quick
            test_exists_bound_not_substituted;
          Alcotest.test_case "unchanged" `Quick test_exists_unchanged;
        ] );
      ( "ite",
        [
          Alcotest.test_case "guard replaced by variable" `Quick
            test_ite_guard_var_replaced;
          Alcotest.test_case "guard becomes literal" `Quick
            test_ite_guard_literal;
          Alcotest.test_case "lazy branch evaluation" `Quick test_ite_lazy;
          Alcotest.test_case "unchanged" `Quick test_ite_unchanged;
        ] );
    ]
