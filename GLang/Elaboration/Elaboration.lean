import GLang.Elaboration.ContextFormation
import GLang.Elaboration.BasisUniqueness

/-!
# The complete surface-elaboration statement

This file states the six existence results together. Their joint proof is
`SurfaceElaboration.complete` in `SurfaceBasisElaboration`; `Goals` is never
postulated as an axiom or added as a public premise. Context reconstruction
is derived below from the two formation results. Uniqueness is proved
independently of existence.
-/
namespace GLang.SurfaceElaboration

def SpaceLift (ε : NLCtx) (s : Surface.Space) (s' : Space) : Prop :=
  s'.erase = s ∧ Nonempty (SValid ε s')

/-- Kind-preserving annotated type reconstruction. -/
def TypeLift (ε : NLCtx) (t : Surface.Ty) (k : Kind) (t' : Ty) : Prop :=
  t'.erase = t ∧ Nonempty (TValid ε t' k)

/-- Reconstruct both endpoints of the same subspace judgment. -/
def SubspaceLift (ε : NLCtx) (s t : Surface.Space) (p : Space × Space) : Prop :=
  p.1.erase = s ∧ p.2.erase = t ∧ Nonempty (SubType ε p.1 p.2)

/-- Reconstruct the term and its result type together. -/
def TermLift (Δ : LCtx) (ε : NLCtx) (e : Surface.Term) (t : Surface.Ty)
    (p : Term × Ty) : Prop :=
  p.1.erase = e ∧ p.2.erase = t ∧ Nonempty (HasType Δ ε p.1 p.2)

/-- Reconstruct every component of a basis, including frame bodies. -/
def BasisLift (ε : NLCtx) (b : Surface.Basis) (b' : Basis) : Prop :=
  b'.erase = b ∧ Basis.BasisValid ε b'

/-- Reconstruct well-formed contexts, preserving their keys and visible entries. -/
def ContextLift (Δ : Surface.LCtx) (ε : Surface.NLCtx) (p : LCtx × NLCtx) : Prop :=
  p.1.erase = Δ ∧ p.2.erase = ε ∧ InductiveCtxWF p.1 p.2

/-- Space-existence obligation relative to any well-formed annotated context. -/
def SpaceExists : Prop :=
  ∀ {Δ ε}, InductiveCtxWF Δ ε → ∀ {s}, Surface.SValid ε.erase s →
    ∃ s', SpaceLift ε s s'

/-- Type-existence obligation, preserving the surface kind. -/
def TypeExists : Prop :=
  ∀ {Δ ε}, InductiveCtxWF Δ ε → ∀ {t k}, Surface.TValid ε.erase t k →
    ∃ t', TypeLift ε t k t'

/-- Subspace-existence obligation. -/
def SubspaceExists : Prop :=
  ∀ {Δ ε}, InductiveCtxWF Δ ε → ∀ {s t}, Surface.SubType ε.erase s t →
    ∃ p, SubspaceLift ε s t p

/-- Term-existence obligation, with no annotated derivation among its premises. -/
def TermExists : Prop :=
  ∀ {Δ ε}, InductiveCtxWF Δ ε → ∀ {e t}, Surface.HasType Δ.erase ε.erase e t →
    ∃ p, TermLift Δ ε e t p

/-- Basis-existence obligation. -/
def BasisExists : Prop :=
  ∀ {Δ ε}, InductiveCtxWF Δ ε → ∀ {b}, Surface.Basis.BasisValid ε.erase b →
    ∃ b', BasisLift ε b b'

def ContextExists : Prop :=
  ∀ {Δ ε}, Surface.InductiveCtxWF Δ ε → ∃ p, ContextLift Δ ε p

/-- All requested existence statements, inhabited by `complete` in
`SurfaceBasisElaboration`. -/
structure Goals : Prop where
  space : SpaceExists
  type : TypeExists
  subspace : SubspaceExists
  term : TermExists
  basis : BasisExists
  context : ContextExists

/-- Context lifting is a consequence of space/type lifting. Annotated scoping
comes from formation itself, so no reverse free-variable-erasure assumption is
needed. `complete` supplies both formation proofs. -/
theorem context_of_formation (hs : SpaceExists) (ht : TypeExists) : ContextExists := by
  intro Δ ε h
  induction h with
  | empty => exact ⟨(∅, ∅), by simp [LCtx.erase], by simp [NLCtx.erase], .empty⟩
  | @linear Δ ε x s h hx hy hscope hv ih =>
    obtain ⟨⟨D,E⟩, hD, hE, hwf⟩ := ih
    obtain ⟨s', hes, ⟨hvalid⟩⟩ := hs hwf (by simpa only [hE] using hv)
    refine ⟨(Finmap.insert x s' D, E), ?_, hE, ?_⟩
    · simpa only [LCtx.erase, sourceMap_insert, hes] using
        congrArg (Finmap.insert x s) hD
    · exact .linear hwf (by simpa only [← hD, sourceMap_mem] using hx)
        (by simpa only [← hE, sourceMap_mem] using hy)
        (fun y hy => Finmap.mem_keys.mp (hvalid.fv_closure hy)) hvalid
  | @nonlinear Δ ε x t k h hx hy hscope hv ih =>
    obtain ⟨⟨D,E⟩, hD, hE, hwf⟩ := ih
    obtain ⟨t', het, ⟨hvalid⟩⟩ := ht hwf (by simpa only [hE] using hv)
    refine ⟨(D, Finmap.insert x t' E), hD, ?_, ?_⟩
    · simpa only [NLCtx.erase, sourceMap_insert, het] using
        congrArg (Finmap.insert x t) hE
    · exact .nonlinear hwf (by simpa only [← hD, sourceMap_mem] using hx)
        (by simpa only [← hE, sourceMap_mem] using hy)
        (fun y hy => Finmap.mem_keys.mp (hvalid.fv_closure hy)) hvalid

/-- It suffices to solve the five judgment goals; the sixth is derived. -/
theorem goals_of_judgments (hs : SpaceExists) (ht : TypeExists)
    (hsub : SubspaceExists) (he : TermExists) (hb : BasisExists) : Goals :=
  ⟨hs, ht, hsub, he, hb, context_of_formation hs ht⟩

/-- Space lifts are unique even before the existence goal is solved. -/
theorem spaceLift_unique {ε s a b} (ha : SpaceLift ε s a) (hb : SpaceLift ε s b) :
    a = b := SValid.annotation_unique ha.2.some hb.2.some (ha.1.trans hb.1.symm)

/-- Type lifts preserve a unique annotated type. -/
theorem typeLift_unique {ε t k a b} (ha : TypeLift ε t k a) (hb : TypeLift ε t k b) :
    a = b := TValid.annotation_unique ha.2.some hb.2.some (ha.1.trans hb.1.symm)

/-- Subspace lifts determine both annotated endpoints. -/
theorem subspaceLift_unique {ε s t a b}
    (ha : SubspaceLift ε s t a) (hb : SubspaceLift ε s t b) : a = b := by
  obtain ⟨h₁,h₂⟩ := SubType.annotation_unique ha.2.2.some hb.2.2.some
    (ha.1.trans hb.1.symm)
  exact Prod.ext h₁ h₂

/-- Term lifts determine both annotated syntax and its result type. -/
theorem termLift_unique {Δ ε e t a b} (hwf : InductiveCtxWF Δ ε)
    (ha : TermLift Δ ε e t a) (hb : TermLift Δ ε e t b) : a = b := by
  obtain ⟨h₁,h₂⟩ := HasType.annotation_unique hwf ha.2.2.some hb.2.2.some
    (ha.1.trans hb.1.symm)
  exact Prod.ext h₁ h₂

/-- Basis lifts are unique, including beneath frames. -/
theorem basisLift_unique {ε b a c} (ha : BasisLift ε b a) (hc : BasisLift ε b c) :
    a = c := Basis.BasisValid.annotation_unique ha.2 hc.2 (ha.1.trans hc.1.symm)

end GLang.SurfaceElaboration
