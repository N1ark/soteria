import CoreMod.Node
import CoreMod.FBits
import KanonCore.Embed
import KanonCore.ProofAttr

/-!
# The meaning of the nodes of the core module

A variable is the value that the environment gives it, if it is of the sort of
the variable, and poison otherwise; a sequence is the list of the values of its
elements, poison if one is. `Values.Of` says which values a sort has, for the
variables and the elements of sequences.
-/

noncomputable section

namespace CoreMod

open Classical Kanon
open Kanon.Sem (OLe FLe)

/-- What the core module needs of a language: the values of the variables, the
values of each sort, and the sequences. -/
class Values (D : Kanon.Dom) where
  lookup : D.Env → Int → Option D.Val
  Of : D.Val → D.Ty → Prop
  vseq : Embed (List D.Val) D.Val

/-- The invariant of sequences: their elements have the sort of the elements of
their sort. -/
@[kanon_wt] def seq_wt {T Ty : Type} (sCore : Srt Ty → Ty) (ty : T → Ty) : Node T → Ty → Prop
  | .Seq l, t => ∃ e, t = sCore (.TSeq e) ∧ ∀ x ∈ l, ty x = e
  | _, _ => True

section
variable {D : Kanon.Dom} [Values D]

/-- A sequence of the values of terms, given in every environment. -/
def seqV (ρ : D.Env) (l : List (D.Env → Option D.Val)) : Option D.Val :=
  ((l.map fun (a : D.Env → Option D.Val) => a ρ).mapM id).map Values.vseq.inj

theorem seqV_mono {ρ : D.Env} {l l' : List (D.Env → Option D.Val)} (h : Forall₂ FLe l l') :
    OLe (seqV ρ l) (seqV ρ l') := by
  intro v e
  unfold seqV at e ⊢
  obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.1 e
  rw [Sem.FLe.mapM h ρ vs hvs]; rfl
end

/-- The evaluation of a node in the environment `ρ`, at the sort `t`. -/
def Node.eval {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty) :
    Node (D.Env → Option D.Val) → Option D.Val
  | .Var x => (Values.lookup ρ x).bind fun v => if Values.Of v t then some v else none
  | .Seq l => seqV ρ l

theorem Node.eval_mono {D : Kanon.Dom} [Values D] (ρ : D.Env) (t : D.Ty)
    {n n' : Node (D.Env → Option D.Val)} (h : n.Rel FLe n') :
    OLe (n.eval ρ t) (n'.eval ρ t) := by
  cases n <;> cases n' <;> simp only [Node.Rel] at h <;> (try contradiction)
  · subst h; exact OLe.refl _
  · exact seqV_mono h

/-- The values of the sorts of the module: sequences of values of the sort of
their elements. -/
def Srt.val {D : Kanon.Dom} [Values D] : Srt D.Ty → D.Val → Prop
  | .TSeq e, v => ∃ vs, v = Values.vseq.inj vs ∧ ∀ x ∈ vs, Values.Of x e

end CoreMod
