(** [Make (R)] is [R] with the bug selected by {!Config.mutation} (read at call
    time) injected in one rule function; with [No_mutation] it is [R]. *)

open Tm

module Make (R : Side.RAW) : Side.RAW with type t = R.t = struct
  include R

  let m () = !Config.mutation

  let bv_sub ck a b =
    if m () = Config.Sub_swap then R.bv_sub ck b a else R.bv_sub ck a b

  let bv_add ck a b =
    if m () = Config.Add_ck_ignored then R.bv_add (false, false) a b
    else R.bv_add ck a b

  let bv_mul ck a b =
    if m () = Config.Mul_ck_forced then R.bv_mul (true, true) a b
    else R.bv_mul ck a b

  let b_ite c a b =
    if m () = Config.Ite_swap then R.b_ite c b a else R.b_ite c a b

  let bv_lt s a b =
    if m () = Config.Lt_sign_flip then R.bv_lt (not s) a b else R.bv_lt s a b

  let bv_extend s k a =
    if m () = Config.Extend_sign_flip then R.bv_extend (not s) k a
    else R.bv_extend s k a

  let float_min a b =
    if m () = Config.Float_min_is_max then R.float_max a b else R.float_min a b

  let sem_eq a b =
    match (m (), R.sort_of a) with
    | Config.Eq_to_false_on_ptr, SPtr _ -> R.mk_bool false
    | _ -> R.sem_eq a b

  let view x =
    match (m (), R.view x) with
    | Config.View_swap_add, VNode ((N_add _ as n), [ a; b ]) ->
        VNode (n, [ b; a ])
    | _, v -> v
end
