(** The generic pretty-printer of terms: replaces [Svalue.pp]
    ([svalue.ml:101-143]) and the [Ext.pp] of extensions by one renderer of the
    {!View_host.pp_style} of {!Kanon_fns.Kanon_fns.pp_style}. The formats are
    exactly those of the old printer, break hints included: see
    {!View_host.pp_style}. Written by the architect as the reference
    implementation; WP3b owns it from now on. *)

module type S = sig
  type t

  val pp : t Fmt.t
end

module Make (V : Value_lang.Base) : S with type t = V.t = struct
  open View_host

  type t = V.t

  let pp_head ft (h : pphead) = h ft

  let nth_operand (t : t) i =
    match List.nth_opt (V.K.operands t) (Z.to_int i) with
    | Some o -> o
    | None -> failwith "Pp: operand out of range"

  let rec pp ft (t : t) =
    let operands () = V.K.operands t in
    match V.K.pp_style t with
    | PAtom h -> h ft
    | PCall h ->
        Fmt.pf ft "%a(%a)" pp_head h (Fmt.list ~sep:Fmt.comma pp) (operands ())
    | PCallPlain h ->
        Fmt.pf ft "%a(%a)" pp_head h
          (Fmt.list ~sep:(Fmt.any ", ") pp)
          (operands ())
    | PIn h -> (
        match operands () with
        | [ a; b ] -> Fmt.pf ft "(%a %a %a)" pp a pp_head h pp b
        | _ -> failwith "Pp: PIn needs two operands")
    | PIte -> (
        match operands () with
        | [ c; a; b ] -> Fmt.pf ft "(%a ? %a : %a)" pp c pp a pp b
        | _ -> failwith "Pp: PIte needs three operands")
    | PBrackets ->
        Fmt.pf ft "%a" (Fmt.brackets (Fmt.list ~sep:Fmt.comma pp)) (operands ())
    | PSeq pieces ->
        List.iter
          (function
            | PText h -> h ft
            | PArg i -> pp ft (nth_operand t i)
            | PArgOf (i, j) -> pp ft (nth_operand (nth_operand t i) j)
            | PArgs h -> Fmt.list ~sep:(fun ft () -> h ft) pp ft (operands ()))
          pieces
end
