(** Rule-level exhaustive mode: for every public entry point and every parameter
    value, ALL shallow arguments over a small pool.

    Pool: widths 1 to 3 (every literal of the width), 2 variables per sort,
    floats (F32; F16 and F64 for the conversions) from the special values (+-0,
    +-inf, NaN, 1, 0.5, -1) and 2 variables, pointers and locations of 2 bits,
    [bv8]/[bv16]/[bv32] from the biased literals (they are only operands of
    conversions).

    [leaves s] is level 0. [level1 s] is level 0 plus one application of every
    operator (every parameter value) to level-0 arguments. For each operator the
    argument tuples enumerated are: all of level 0 (the full product), and, for
    each position, level 1 at that position and level 0 at the others. *)

open Tm

let var s i = Var (Gen.var_id s i, s)

let all_lits n =
  let rec go i =
    if i >= 1 lsl n then [] else Bv (n, Z.of_int i) :: go (i + 1)
  in
  go 0

let biased_lits n =
  let max_u = Z.pred (Z.shift_left Z.one n) in
  let half = Z.shift_left Z.one (n - 1) in
  List.sort_uniq compare [ Z.zero; Z.one; Z.pred half; half; max_u ]
  |> List.map (fun z -> Bv (n, z))

let specials p =
  List.map
    (fun z -> Float (p, z))
    (let z f = Soteria.Bv_values.Svalue.F.to_z f in
     let module F = Soteria.Bv_values.Svalue.F in
     [
       z (F.zero p);
       z (F.neg_zero p);
       z (F.infinity p);
       z (F.neg_infinity p);
       z (F.nan p);
       z (F.one p);
       z (F.of_float p 0.5);
       z (F.of_float p (-1.0));
     ])

let rec leaves0 s : Tm.t list =
  match s with
  | SBool -> [ Bool true; Bool false; var s 0; var s 1 ]
  | SBv n ->
      (if n <= 3 then all_lits n else biased_lits n) @ [ var s 0; var s 1 ]
  | SLoc n ->
      List.init (1 lsl n) (fun i -> Loc (n, Z.of_int i)) @ [ var s 0; var s 1 ]
  | SPtr n ->
      [
        Op (PtrNull n, []);
        var s 0;
        var s 1;
        Op (PtrMk, [ Loc (n, Z.one); Bv (n, Z.of_int 2) ]);
      ]
  | SFloat p -> specials p @ [ var s 0; var s 1 ]
  | SSeq e ->
      [
        Op (SeqMk s, []); var s 0; var s 1; Op (SeqMk s, [ List.hd (leaves0 e) ]);
      ]

let bools = [ true; false ]
let rms = [ RM.NearestTiesToEven; Truncate; Ceil; Floor; NearestTiesToAway ]
let fcs = [ FC.Normal; Subnormal; Zero; Infinite; NaN ]
let checkeds = [ (false, false); (true, false); (false, true); (true, true) ]
let bvw = [ 1; 2; 3 ]

(** Operator, argument sorts. *)
let catalogue : (op * sort list) list Lazy.t =
  lazy
    (let l = ref [] in
     let add o a = l := (o, a) :: !l in
     (* bool *)
     let b = SBool in
     add And [ b; b ];
     add Or [ b; b ];
     add Not [ b ];
     add Ite [ b; b; b ];
     add SemEq [ b; b ];
     add SemEqUntyped [ b; b ];
     add AndLazy [ b; b ];
     add OrLazy [ b; b ];
     add Distinct [ b; b ];
     add Distinct [ b; b; b ];
     add Distinct [ b ];
     add Distinct [];
     add Conj [];
     add Conj [ b ];
     add Conj [ b; b ];
     add Conj [ b; b; b ];
     (* bitvec *)
     List.iter
       (fun w ->
         let v = SBv w in
         List.iter
           (fun c ->
             add (BvAdd c) [ v; v ];
             add (BvSub c) [ v; v ];
             add (BvMul c) [ v; v ])
           checkeds;
         List.iter
           (fun s ->
             add (BvDiv s) [ v; v ];
             add (BvRem s) [ v; v ];
             add (BvAddOvf s) [ v; v ];
             add (BvSubOvf s) [ v; v ];
             add (BvMulOvf s) [ v; v ];
             add (BvLt s) [ v; v ];
             add (BvLeq s) [ v; v ];
             add (BvGt s) [ v; v ];
             add (BvGeq s) [ v; v ];
             for k = 0 to 3 do
               add (BvExtend (s, k)) [ v ]
             done)
           bools;
         add BvMod [ v; v ];
         List.iter (fun c -> add (BvNeg c) [ v ]) bools;
         add BvNegOvf [ v ];
         List.iter (fun w' -> add BvConcat [ v; SBv w' ]) bvw;
         for i = 0 to w - 1 do
           for j = i to w - 1 do
             add (BvExtract (i, j)) [ v ]
           done
         done;
         List.iter
           (fun o -> add o [ v; v ])
           [ BvAnd; BvOr; BvXor; BvShl; BvLShr; BvAShr ];
         add BvNot [ v ];
         add (BvOfBool w) [ b ];
         add BvToBool [ v ];
         add BvNotBool [ v ];
         add SemEq [ v; v ];
         add SemEqUntyped [ v; v ];
         add Ite [ b; v; v ];
         add Distinct [ v; v ];
         add Distinct [ v; v; v ];
         add Distinct [ v ];
         List.iter
           (fun rm ->
             List.iter
               (fun s ->
                 List.iter
                   (fun p -> add (BvToFloat (rm, s, p)) [ v ])
                   [ F16; F32 ])
               bools)
           rms)
       bvw;
     add SemEqUntyped [ SBv 1; SBv 2 ];
     add SemEqUntyped [ SBv 2; SBool ];
     add (BvOfBool 8) [ b ];
     add (BvOfBool 32) [ b ];
     add BvToFloatRaw [ SBv 16 ];
     add BvToFloatRaw [ SBv 32 ];
     (* floats *)
     let f = SFloat F32 in
     List.iter
       (fun o -> add o [ f; f ])
       [
         FEq;
         FLt;
         FLeq;
         FGt;
         FGeq;
         FAdd;
         FSub;
         FMul;
         FDiv;
         FRem;
         FFmod;
         FMin;
         FMax;
         FMinimum;
         FMaximum;
       ];
     add FFmodOfRem [ f; f; f ];
     add FFma [ f; f; f ];
     List.iter
       (fun o -> add o [ f ])
       [ FAbs; FNeg; FSqrt; FIsNegative; FIsPositive ];
     List.iter (fun fc -> add (FIsFloatClass fc) [ f ]) fcs;
     add SemEq [ f; f ];
     add Ite [ b; f; f ];
     add Distinct [ f; f ];
     List.iter
       (fun rm ->
         add (FRound rm) [ f ];
         List.iter (fun p -> add (FCast (rm, p)) [ f ]) [ F16; F32; F64 ];
         add (FCast (rm, F32)) [ SFloat F16 ];
         add (FCast (rm, F32)) [ SFloat F64 ];
         List.iter
           (fun s ->
             List.iter (fun n -> add (BvOfFloat (rm, s, n)) [ f ]) [ 2; 8; 32 ])
           bools)
       rms;
     (* pointers, locations *)
     let n = 2 in
     let loc = SLoc n and ptr = SPtr n and bv = SBv n in
     add PtrMk [ loc; bv ];
     add PtrLoc [ ptr ];
     add PtrOfs [ ptr ];
     add PtrAddOfs [ ptr; bv ];
     add (PtrNull n) [];
     add PtrIsNullLoc [ loc ];
     add PtrIsNull [ ptr ];
     add PtrIsAtNullLoc [ ptr ];
     add SemEq [ ptr; ptr ];
     add SemEq [ loc; loc ];
     add Ite [ b; ptr; ptr ];
     add Ite [ b; loc; loc ];
     add Distinct [ ptr; ptr ];
     add Distinct [ loc; loc ];
     (* sequences *)
     let sq = SSeq bv in
     add (SeqMk sq) [];
     add (SeqMk sq) [ bv ];
     add (SeqMk sq) [ bv; bv ];
     add SemEq [ sq; sq ];
     add Ite [ b; sq; sq ];
     List.rev !l)

let is_zero_lit = function Bv (_, z) -> Z.equal z Z.zero | _ -> false

let valid op (args : Tm.t list) =
  match (op, args) with
  | (BvDiv _ | BvRem _), [ _; d ] -> not (is_zero_lit d)
  | _ -> true

let result_sort_of op args = result_sort op args

let product (pools : Tm.t list list) (f : Tm.t list -> unit) =
  let rec go acc = function
    | [] -> f (List.rev acc)
    | p :: rest -> List.iter (fun x -> go (x :: acc) rest) p
  in
  go [] pools

let level1_tbl : (sort, Tm.t list) Hashtbl.t = Hashtbl.create 32

let level1 s =
  match Hashtbl.find_opt level1_tbl s with
  | Some l -> l
  | None ->
      let seen = Hashtbl.create 1024 in
      let out = ref [] in
      let push t =
        if not (Hashtbl.mem seen t) then (
          Hashtbl.add seen t ();
          out := t :: !out)
      in
      List.iter push (leaves0 s);
      List.iter
        (fun (op, asorts) ->
          if
            (match op with Distinct | Conj | SeqMk _ -> false | _ -> true)
            && try result_sort_of op asorts = s with _ -> false
          then
            product (List.map leaves0 asorts) (fun args ->
                if valid op args then push (Op (op, args))))
        (Lazy.force catalogue);
      let l = List.rev !out in
      Hashtbl.add level1_tbl s l;
      l

(** [iter f] calls [f] on every term of the exhaustive set. *)
let iter (f : Tm.t -> unit) =
  List.iter
    (fun (op, asorts) ->
      let l0 = List.map leaves0 asorts in
      let emit args = if valid op args then f (Op (op, args)) in
      product l0 emit;
      let nary =
        match op with Distinct | Conj | SeqMk _ -> true | _ -> false
      in
      if not nary then
        List.iteri
          (fun i s ->
            let l0i = leaves0 s in
            let extra =
              List.filter (fun t -> not (List.mem t l0i)) (level1 s)
            in
            let pools = List.mapi (fun j p -> if j = i then extra else p) l0 in
            product pools emit)
          asorts)
    (Lazy.force catalogue);
  (* exists_1: binder of sort bv2 or bool; not_in a leaf; body: level 0 and
     level 1 over the leaves extended with the bound variable *)
  List.iter
    (fun bs ->
      let leaves_b s =
        if s = bs then Bound (0, s) :: leaves0 s else leaves0 s
      in
      let bodies =
        let acc = ref [] in
        List.iter
          (fun (op, asorts) ->
            if
              (match op with
                | Distinct | Conj | SeqMk _ | Exists1 _ -> false
                | _ -> true)
              && try result_sort_of op asorts = SBool with _ -> false
            then
              product (List.map leaves_b asorts) (fun args ->
                  let t = Op (op, args) in
                  if
                    valid op args
                    && List.exists (fun a -> a = Bound (0, bs)) args
                  then acc := t :: !acc))
          (Lazy.force catalogue);
        Bound (0, bs) :: !acc |> List.filter (fun t -> sort_of t = SBool)
        |> fun l -> Bool true :: Bool false :: var SBool 0 :: l
      in
      List.iter
        (fun not_in ->
          List.iter (fun body -> f (Op (Exists1 bs, [ not_in; body ]))) bodies)
        (leaves0 (SBv 2) @ leaves0 SBool))
    [ SBv 2; SBool ]

let count () =
  let n = ref 0 in
  iter (fun _ -> incr n);
  !n
