module type Rust_symex = Soteria.Symex.Base with module Value = Rustsymex.Value

module M (Symex : Rust_symex) = struct
  module type S = sig
    (** {2 Tree Borrows trees (the general structure)} *)

    type tag
    type access = Read | Write

    type state =
      | Reserved of bool
      | Unique
      | Frozen
      | ReservedIM
      | Cell
      | Disabled
      | UB

    type protector = Strong | Weak
    type t

    val pp : Format.formatter -> t -> unit
    val pp_tag : Format.formatter -> tag -> unit
    val pp_state : Format.formatter -> state -> unit

    module SM :
      Soteria.Sym_states.State_monad.S
        with type 'a Symex.t = 'a Symex.t
         and type st = t option

    (** {2 Tree Borrows state (the per-byte information)} *)

    type tb_state

    val pp_tb_state : Format.formatter -> tb_state -> unit

    (* Compositionality *)

    type syn [@@deriving show]

    val to_syn : t -> syn list
    val ins_outs : syn -> Symex.Value.Expr.(t list * t list)
    val consume : syn -> t option -> (t option, syn list) Symex.Consumer.t
    val produce : syn -> t option -> t option Symex.Producer.t

    type syn_state [@@deriving show]

    val to_syn_state : tb_state -> syn_state list
    val ins_outs_state : syn_state -> Symex.Value.Expr.(t list * t list)

    val consume_state :
      syn_state ->
      tb_state option ->
      (tb_state option, syn_state list) Symex.Consumer.t

    val produce_state :
      syn_state -> tb_state option -> tb_state option Symex.Producer.t

    type syn_full = Structure of syn | State of syn_state

    (** {2 Operations on the structure} *)

    (** Generates a nondeterministic tag, for a nondeterministic pointer. May
        return [None] if this tree borrows implementation doesn't support
        symbolic tags. *)
    val nondet_tag : unit -> tag option Symex.t

    val init : unit -> (t * tag) Symex.t

    val borrow :
      ?protector:protector ->
      tag ->
      state:state ->
      (tag, 'e, syn list) SM.Result.t

    val unprotect : tag -> (unit, 'e, syn list) SM.Result.t
    val strong_protector_exists : t option -> bool

    (** {2 Operations on the state} *)

    val fix_empty_state : unit -> syn_state list
    val init_st : unit -> tb_state Symex.t
    val equal_state : tb_state option -> tb_state option -> bool

    val set_protector :
      protected:bool ->
      tag ->
      t option ->
      tb_state option ->
      (tb_state option, 'e, syn_full list) Symex.Result.t

    (** [access root accessed e state]: Update all nodes in the mapping [state]
        for the tree rooted at [root] with an event [e], that happened at
        [accessed]. *)
    val access :
      tag ->
      access ->
      t option ->
      tb_state option ->
      (tb_state option, [> `AliasingError ], syn_full list) Symex.Result.t

    val merge : tb_state -> tb_state -> tb_state Symex.t
  end
end

module type T = (Symex : Rust_symex) -> M(Symex).S
