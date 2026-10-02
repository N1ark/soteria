(** Deliberate bugs injected on the new side by [--mutate], to prove that the
    harness detects them. *)
type mutation =
  | No_mutation
  | Sub_swap  (** [bv_sub] with its operands swapped *)
  | Add_ck_ignored  (** [bv_add] ignores its [checked] flag *)
  | Mul_ck_forced  (** [bv_mul] always claims [checked_both] *)
  | Ite_swap  (** [b_ite] with its branches swapped *)
  | Lt_sign_flip  (** [bv_lt] flips its signedness *)
  | Extend_sign_flip  (** [bv_extend] flips its signedness *)
  | Float_min_is_max  (** [float_min] computes [float_max] *)
  | Eq_to_false_on_ptr  (** [sem_eq] on pointers is [false] *)
  | View_swap_add
      (** the [view] of an [Add] node lists its operands in the other order: an
          order-only difference, not a wrong rule *)

let all =
  [
    ("sub-swap", Sub_swap);
    ("add-ck-ignored", Add_ck_ignored);
    ("mul-ck-forced", Mul_ck_forced);
    ("ite-swap", Ite_swap);
    ("lt-sign-flip", Lt_sign_flip);
    ("extend-sign-flip", Extend_sign_flip);
    ("float-min-is-max", Float_min_is_max);
    ("eq-ptr-false", Eq_to_false_on_ptr);
    ("view-swap-add", View_swap_add);
  ]

let mutation = ref No_mutation
