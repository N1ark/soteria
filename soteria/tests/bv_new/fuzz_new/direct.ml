(** Non-simplifying ("direct") constructors for the Svalue expressions of the
    NEW stack ({!New_stack}).

    Each function here corresponds 1:1 to a smart constructor of the new
    language, but builds the raw node ([Bv_new.Types.node]) without any
    simplification. This serves as the semantic ground truth when fuzz-testing
    that the simplifications of the generated rules are correct. *)

open Bv_new.Types
module Typed = New_stack.Typed
module Sv = Typed.Svalue
open Sv

let ( <| ) = node

(* ------------------------------------------------------------------ *)
(* Boolean operations                                                  *)
(* ------------------------------------------------------------------ *)

module Var_pool = struct
  let max_var_per_ty = 5

  let get_next_name =
    let name_counter = ref 0 in
    fun () ->
      let res = !name_counter in
      incr name_counter;
      Var.of_int res

  (* We want to generate at most [max_var_per_ty] variables per type. This
     avoids generating expressions with only different variables, which cannot
     be reduced interestingly. *)
  let var_pool : (int * ty, t) Stdlib.Hashtbl.t = Stdlib.Hashtbl.create 1024

  let get_from_pool idx ty =
    let key = (idx, ty) in
    match Stdlib.Hashtbl.find_opt var_pool key with
    | None ->
        let name = get_next_name () in
        let v = mk_var name ty in
        Stdlib.Hashtbl.replace var_pool key v;
        v
    | Some v -> v
end

module Bool = struct
  let v_true = Bool true <| t_bool
  let v_false = Bool false <| t_bool
  let bool b = if b then v_true else v_false
  let not_ v = Op1 (Not, v) <| t_bool
  let and_ v1 v2 = Op2 (And, v1, v2) <| t_bool
  let or_ v1 v2 = Op2 (Or, v1, v2) <| t_bool
  let ite c t e = Op3 (Ite, c, t, e) <| t.ty

  let eq v1 v2 =
    (* Eq always returns TBool *)
    Op2 (Eq, v1, v2) <| t_bool

  let distinct vs = OpN (Distinct, vs) <| t_bool
end

(* ------------------------------------------------------------------ *)
(* BitVector operations                                                *)
(* ------------------------------------------------------------------ *)

module BitVec = struct
  (* Constructors *)
  let mk n z = BitVec z <| t_bv n
  let zero n = BitVec Z.zero <| t_bv n
  let one n = BitVec Z.one <| t_bv n

  (* Arithmetic *)
  let add ?(checked = unchecked) v1 v2 = Op2 (Add checked, v1, v2) <| v1.ty
  let sub ?(checked = unchecked) v1 v2 = Op2 (Sub checked, v1, v2) <| v1.ty
  let mul ?(checked = unchecked) v1 v2 = Op2 (Mul checked, v1, v2) <| v1.ty
  let div ~signed v1 v2 = Op2 (Div signed, v1, v2) <| v1.ty
  let rem ~signed v1 v2 = Op2 (Rem signed, v1, v2) <| v1.ty
  let mod_ v1 v2 = Op2 (Mod, v1, v2) <| v1.ty
  let neg ?(checked = false) v = Op1 (Neg checked, v) <| v.ty

  (* Bitwise *)
  let not_ v = Op1 (BvNot, v) <| v.ty
  let and_ v1 v2 = Op2 (BitAnd, v1, v2) <| v1.ty
  let or_ v1 v2 = Op2 (BitOr, v1, v2) <| v1.ty
  let xor v1 v2 = Op2 (BitXor, v1, v2) <| v1.ty
  let shl v1 v2 = Op2 (Shl, v1, v2) <| v1.ty
  let lshr v1 v2 = Op2 (LShr, v1, v2) <| v1.ty
  let ashr v1 v2 = Op2 (AShr, v1, v2) <| v1.ty

  (* Bitvector manipulation *)
  let concat v1 v2 =
    let n1 = size_of v1.ty in
    let n2 = size_of v2.ty in
    Op2 (BvConcat, v1, v2) <| t_bv (n1 + n2)

  let extract from_ to_ v =
    Op1 (BvExtract (from_, to_), v) <| t_bv (to_ - from_ + 1)

  let extend ~signed by v =
    let n = size_of v.ty in
    Op1 (BvExtend (signed, by), v) <| t_bv (n + by)

  (* Comparisons *)
  let lt ~signed v1 v2 = Op2 (Lt signed, v1, v2) <| t_bool
  let leq ~signed v1 v2 = Op2 (Leq signed, v1, v2) <| t_bool
  let gt ~signed v1 v2 = lt ~signed v2 v1
  let geq ~signed v1 v2 = leq ~signed v2 v1

  (* Overflow checks *)
  let add_overflows ~signed v1 v2 = Op2 (AddOvf signed, v1, v2) <| t_bool
  let sub_overflows ~signed v1 v2 = Op2 (SubOvf signed, v1, v2) <| t_bool
  let mul_overflows ~signed v1 v2 = Op2 (MulOvf signed, v1, v2) <| t_bool

  let neg_overflows (v : t) =
    let n = size_of v.ty in
    let min = Z.(neg (one lsl Stdlib.( - ) n 1)) in
    Op2 (Eq, v, BitVec.mk_masked n min) <| t_bool

  (* Bool-bv conversions *)
  let of_bool n v = Op1 (BvOfBool n, v) <| t_bv n

  let to_bool v =
    (* not(v == 0) *)
    let n = size_of v.ty in
    Bool.not_ (Bool.eq v (zero n))

  let not_bool v =
    (* v == 0 *)
    let n = size_of v.ty in
    Bool.eq v (zero n)

  (* Float-bv conversions *)
  let of_float ~rounding ~signed ~size v =
    Op1 (BvOfFloat (rounding, signed, size), v) <| t_bv size

  let to_float ~rounding ~signed ~fp v =
    Op1 (FloatOfBv (rounding, signed, fp), v) <| t_float fp

  let to_float_raw v =
    let n = size_of v.ty in
    let fp = FloatPrecision.of_size n in
    Op1 (FloatOfBvRaw fp, v) <| t_float fp
end

let checked_has ~signed (c : checked) = if signed then c.signed else c.unsigned

(* A checked operation only promises no overflow in the signedness(es) recorded
   by its [checked] flag, so we only assume those. *)
let checked_assumptions assumptions checked v1 v2 overflows =
  Iter.bools @@ fun signed ->
  if checked_has ~signed checked then
    Dynarray.add_last assumptions (Bool.not_ (overflows ~signed v1 v2))

let collect_checked_assumptions (v : t) : t list =
  let assumptions = Dynarray.create () in

  let rec go v =
    match v.kind with
    | Op1 (Neg true, v') ->
        Dynarray.add_last assumptions (Bool.not_ (BitVec.neg_overflows v'));
        go v'
    | Op1 (_, v) -> go v
    | Op3 (_, a, b, c) ->
        go a;
        go b;
        go c
    | Op2 (Add checked, v1, v2) ->
        checked_assumptions assumptions checked v1 v2 BitVec.add_overflows;
        go v1;
        go v2
    | Op2 (Sub checked, v1, v2) ->
        checked_assumptions assumptions checked v1 v2 BitVec.sub_overflows;
        go v1;
        go v2
    | Op2 (Mul checked, v1, v2) ->
        checked_assumptions assumptions checked v1 v2 BitVec.mul_overflows;
        go v1;
        go v2
    | Op2 (_, v1, v2) ->
        go v1;
        go v2
    | Seq vs | OpN (_, vs) -> List.iter go vs
    | Var _ | Bool _ | BitVec _ | LocLit _ | Float _ -> ()
    | Exists _ ->
        failwith
          "collect_checked_assumptions: not implemented for quantifiers (we \
           don't generate quantifiers for fuzzing yet)"
  in
  go v;
  Dynarray.to_list assumptions |> List.sort_uniq compare

module Shrink = struct
  let ( @ ) = Seq.append
  let ( ++ ) = Seq.cons

  let small_of_ty ty =
    match ty with
    | TBool -> Seq.cons Bool.v_false (Seq.singleton Bool.v_true)
    | TBitVector n -> Seq.cons (BitVec.zero n) (Seq.singleton (BitVec.one n))
    | _ -> Seq.empty

  let just_var ty = Var_pool.get_from_pool 0 ty

  let rec children_of_ty ~ty v =
    let return v = v ++ shrink v in
    let if_ty v = if equal_ty ty v.ty then return v else children_of_ty ~ty v in
    match v.kind with
    | Op1 (_, v) -> if_ty v
    | Op2 (_, v1, v2) ->
        let left = if_ty v1 in
        let right = if_ty v2 in
        left @ right
    | Op3 (Ite, c, t, e) ->
        if equal c Bool.v_true then return t
        else if equal c Bool.v_false then return e
        else return t @ return e
    | _ -> Seq.empty

  and shrink v =
    match v.kind with
    | Var _ -> small_of_ty v.ty
    | Bool _ -> Seq.empty
    | BitVec n ->
        let size = size_of v.ty in
        if Z.gt n Z.one then List.to_seq [ BitVec.zero size; BitVec.one size ]
        else if Z.gt n Z.zero then Seq.singleton (BitVec.zero size)
        else Seq.empty
    | _ ->
        let ty = v.ty in
        (just_var ty ++ small_of_ty ty) @ children_of_ty ~ty:v.ty v
end
