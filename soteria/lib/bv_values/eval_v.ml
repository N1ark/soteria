(** The generic normaliser: replaces [Eval.eval] ([eval.ml:73-125], at HEAD
    f52223c: it substitutes under [Exists] and compares the guard of [Ite]) with
    the per-node dispatch [eval_binop/unop/triop/nop] ([eval.ml:12-71]),
    [Ptr.mk], [SSeq.mk] and [Ext.eval]/[Ext.mk] replaced by
    {!Kanon_fns.Kanon_fns.operands} and [rebuild]. It keeps [force], the
    [eval_var] closure, the laziness of [Ite] and the [Division_by_zero] catch.
    Written by the architect as the reference implementation; WP3b owns it from
    now on. *)

open Deps

module type S = sig
  type t
  type ty

  val eval : ?force:bool -> ?eval_var:(t -> Var.t -> ty -> t) -> t -> t
end

module Make (V : Value_lang.Base) : S with type t = V.t and type ty = V.ty =
struct
  open V

  type nonrec t = t
  type nonrec ty = ty

  let rec eval ~force ~eval_var (x : t) : t =
    let eval' = eval ~force in
    let eval = eval ~force ~eval_var in
    match K.as_var x with
    | Some (v, ty) -> eval_var x v ty
    | None -> (
        match K.as_exists x with
        | Some (vs, sv) ->
            let eval_var' sv v ty =
              if List.exists (fun (v', _) -> Var.equal v v') vs then sv
              else eval_var sv v ty
            in
            let nsv = eval' ~eval_var:eval_var' sv in
            if (not force) && sv == nsv then x else K.b_mk_exists vs nsv
        | None -> (
            match K.as_ite x with
            | Some (guard, then_, else_) ->
                (* eval this separately, to have lazy evaluation *)
                let old_guard = guard in
                let guard = eval guard in
                if equal guard v_true then eval then_
                else if equal guard v_false then eval else_
                else
                  let nthen = eval then_ in
                  let nelse = eval else_ in
                  if
                    (not force)
                    && guard == old_guard
                    && then_ == nthen
                    && else_ == nelse
                  then x
                  else K.b_ite guard nthen nelse
            | None -> (
                match K.operands x with
                | [] -> x
                | cs ->
                    let cs', changed = Soteria_std.List.map_changed eval cs in
                    if (not force) && not changed then x else K.rebuild x cs')))

  let eval ?(force = false) ?(eval_var : t -> Var.t -> ty -> t = fun x _ _ -> x)
      (x : t) : t =
    try eval ~force ~eval_var x with Division_by_zero -> x
end
