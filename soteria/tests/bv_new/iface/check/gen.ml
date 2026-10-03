(* A generator of well-typed terms through the sugar of
   {!Bv_iface.Svalue_sugar_v} (so through the smart constructors), over every
   node family. *)

module Make (S : Bv_iface.Svalue_sugar_v.S) = struct
  open S

  type sort = B | V of int | F | L of int | P of int | Sq of sort

  let sorts = [| B; V 8; V 16; F; L 16; P 16; Sq (V 8) |]

  let rec code = function
    | B -> 0
    | V 8 -> 1
    | V _ -> 2
    | F -> 3
    | L _ -> 4
    | P _ -> 5
    | Sq _ -> 6

  let rec ty_of = function
    | B -> t_bool
    | V n -> t_bv n
    | F -> t_f32
    | L n -> t_loc n
    | P n -> t_ptr n
    | Sq s -> t_seq (ty_of s)

  let var s k = mk_var (Var.of_int ((code s * 10) + k)) (ty_of s)
  let pick rng l = List.nth l (Random.State.int rng (List.length l))

  let rms : RoundingMode.t list =
    [ NearestTiesToEven; Truncate; Ceil; Floor; NearestTiesToAway ]

  let fcs : FloatClass.t list = [ Normal; Subnormal; Zero; Infinite; NaN ]

  let checkeds =
    [ unchecked; checked_both; checked_of_signed true; checked_of_signed false ]

  let bv_lits n =
    let m = Z.pred (Z.shift_left Z.one n) in
    [
      Z.zero;
      Z.one;
      Z.of_int 2;
      Z.of_int 3;
      Z.shift_left Z.one (n - 1);
      Z.pred (Z.shift_left Z.one (n - 1));
      m;
      Z.pred m;
      Z.of_int 5;
      Z.of_int 0xf0;
    ]

  let float_bits =
    [
      0;
      0x3f800000;
      0x7fc00000;
      0x80000000;
      0xff800000;
      0x7f800000;
      0xbf000000;
      0x40490fdb;
    ]

  let rec gen rng depth (s : sort) : t =
    let r n = Random.State.int rng n in
    let g = gen rng (depth - 1) in
    let leaf () =
      match s with
      | B ->
          if r 4 = 0 then Bool.of_bool (Random.State.bool rng) else var s (r 3)
      | V n ->
          if r 3 = 0 then BitVec.mk_masked n (pick rng (bv_lits n))
          else var s (r 3)
      | F ->
          if r 3 = 0 then
            Float.mk_bits FloatPrecision.F32 (Z.of_int (pick rng float_bits))
          else var s (r 3)
      | L n -> if r 2 = 0 then Ptr.loc_of_int n (r 4) else var s (r 3)
      | P n -> var s (r 3)
      | Sq e -> var s (r 2)
    in
    if depth <= 0 || r 6 = 0 then leaf ()
    else
      match s with
      | B -> (
          match r 22 with
          | 0 -> Bool.and_ (g B) (g B)
          | 1 -> Bool.or_ (g B) (g B)
          | 2 -> Bool.not (g B)
          | 3 -> Bool.ite (g B) (g B) (g B)
          | 4 ->
              let s' = pick rng (Array.to_list sorts) in
              Bool.sem_eq (g s') (g s')
          | 5 -> BitVec.lt ~signed:(r 2 = 0) (g (V 8)) (g (V 8))
          | 6 -> BitVec.leq ~signed:(r 2 = 0) (g (V 16)) (g (V 16))
          | 7 -> BitVec.add_overflows ~signed:(r 2 = 0) (g (V 8)) (g (V 8))
          | 8 -> BitVec.sub_overflows ~signed:(r 2 = 0) (g (V 8)) (g (V 8))
          | 9 -> BitVec.mul_overflows ~signed:(r 2 = 0) (g (V 8)) (g (V 8))
          | 10 -> Float.eq (g F) (g F)
          | 11 -> Float.lt (g F) (g F)
          | 12 -> Float.leq (g F) (g F)
          | 13 -> Float.is_floatclass (pick rng fcs) (g F)
          | 14 -> Float.is_negative (g F)
          | 15 -> Bool.distinct [ g (V 8); g (V 8); g (V 8) ]
          | 16 -> BitVec.to_bool (g (V 8))
          | 17 ->
              let not_in = g (V 8) in
              Bool.exists_1 ~not_in (t_bv 8) (fun x -> Bool.sem_eq x (g (V 8)))
          | 18 -> Ptr.is_null (g (P 16))
          | 19 -> (
              (* the shapes of [as_range]: [c <u x + k] etc. *)
              let x = var (V 8) (r 3) in
              let c k = BitVec.mk_masked 8 (Z.of_int k) in
              match r 4 with
              | 0 ->
                  BitVec.lt ~signed:false (c (r 256)) (BitVec.add x (c (r 256)))
              | 1 ->
                  BitVec.leq ~signed:false
                    (BitVec.add (c (r 256)) x)
                    (c (r 256))
              | 2 -> BitVec.leq ~signed:true x (c (r 256))
              | _ -> BitVec.lt ~signed:true (c (r 256)) x)
          | 20 -> Bool.not (Bool.sem_eq (g (V 8)) (g (V 8)))
          | _ -> Bool.and_ (g B) (Bool.not (g B)))
      | V n -> (
          match r 22 with
          | 0 -> BitVec.add ~checked:(pick rng checkeds) (g s) (g s)
          | 1 -> BitVec.sub ~checked:(pick rng checkeds) (g s) (g s)
          | 2 -> BitVec.mul ~checked:(pick rng checkeds) (g s) (g s)
          | 3 -> BitVec.div ~signed:(r 2 = 0) (g s) (g s)
          | 4 -> BitVec.rem ~signed:(r 2 = 0) (g s) (g s)
          | 5 -> BitVec.mod_ (g s) (g s)
          | 6 -> BitVec.neg ~checked:(r 2 = 0) (g s)
          | 7 -> BitVec.not (g s)
          | 8 -> BitVec.and_ (g s) (g s)
          | 9 -> BitVec.or_ (g s) (g s)
          | 10 -> BitVec.xor (g s) (g s)
          | 11 -> BitVec.shl (g s) (g s)
          | 12 -> BitVec.lshr (g s) (g s)
          | 13 -> BitVec.ashr (g s) (g s)
          | 14 -> Bool.ite (g B) (g s) (g s)
          | 15 -> BitVec.of_bool n (g B)
          | 16 ->
              if n = 8 then BitVec.extract 0 7 (g (V 16))
              else BitVec.extend ~signed:(r 2 = 0) 8 (g (V 8))
          | 17 ->
              if n = 16 then BitVec.concat (g (V 8)) (g (V 8))
              else BitVec.not_bool (g s)
          | 18 ->
              BitVec.of_float ~rounding:(pick rng rms)
                ~signed:(r 2 = 0)
                ~size:n (g F)
          | 19 -> if n = 16 then Ptr.ofs (g (P 16)) else BitVec.add (g s) (g s)
          | 20 -> BitVec.not_bool (g s)
          | _ -> BitVec.neg_overflows (g s) |> fun b -> BitVec.of_bool n b)
      | F -> (
          match r 18 with
          | 0 -> Float.add (g F) (g F)
          | 1 -> Float.sub (g F) (g F)
          | 2 -> Float.mul (g F) (g F)
          | 3 -> Float.div (g F) (g F)
          | 4 -> Float.rem (g F) (g F)
          | 5 -> Float.fmod (g F) (g F)
          | 6 -> Float.min (g F) (g F)
          | 7 -> Float.max (g F) (g F)
          | 8 -> Float.abs (g F)
          | 9 -> Float.neg (g F)
          | 10 -> Float.sqrt (g F)
          | 11 -> Float.round (pick rng rms) (g F)
          | 12 -> Float.fma (g F) (g F) (g F)
          | 13 ->
              Float.cast ~rounding:(pick rng rms) ~fp:FloatPrecision.F32 (g F)
          | 14 ->
              BitVec.to_float ~rounding:(pick rng rms)
                ~signed:(r 2 = 0)
                ~fp:FloatPrecision.F32 (g (V 16))
          | 15 -> Float.minimum (g F) (g F)
          | 16 -> Bool.ite (g B) (g F) (g F)
          | _ -> Float.neg (Float.neg (g F)))
      | L n -> if r 2 = 0 then Ptr.loc (g (P n)) else Bool.ite (g B) (g s) (g s)
      | P n ->
          if r 4 = 0 then Bool.ite (g B) (g s) (g s)
          else Ptr.mk (g (L n)) (g (V n))
      | Sq e -> SSeq.mk ~seq_ty:(ty_of s) [ g e; g e ]
end
