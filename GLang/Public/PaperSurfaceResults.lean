import GLang.Elaboration.PaperRules
import GLang.Elaboration.Supporting.SurfaceBasisSubstitution

namespace GLang.PaperSurfaceResults

open SurfaceElaboration

theorem spaceElaborationUnique (hw : InductiveCtxWF Δ ε)
    (h : Surface.SValid ε.erase s) : ∃! S, SpaceLift ε s S := by
  obtain ⟨S,hS⟩ := spaceExists hw h
  exact ⟨S,hS,fun _ hT => spaceLift_unique hT hS⟩

/-- Reconstruct a unique annotated type while preserving its stated kind. -/
theorem typeElaborationUnique (hw : InductiveCtxWF Δ ε)
    (h : Surface.TValid ε.erase t k) : ∃! T, TypeLift ε t k T := by
  obtain ⟨T,hT⟩ := typeExists hw h
  exact ⟨T,hT,fun _ hU => typeLift_unique hU hT⟩

theorem subspaceElaborationUnique (hw : InductiveCtxWF Δ ε)
    (h : Surface.SubType ε.erase s t) : ∃! p, SubspaceLift ε s t p := by
  obtain ⟨p,hp⟩ := subspaceExists hw h
  exact ⟨p,hp,fun _ hq => subspaceLift_unique hq hp⟩

/-- The shortened term rules reconstruct a unique term/result-type pair. -/
theorem termElaborationUnique (hw : InductiveCtxWF Δ ε)
    (h : Surface.HasType Δ.erase ε.erase e t) : ∃! p, TermLift Δ ε e t p :=
  SurfacePaper.elaborate_unique hw h

/-- Basis validity reconstructs a unique fully annotated basis or frame. -/
theorem basisElaborationUnique (hw : InductiveCtxWF Δ ε)
    (h : Surface.Basis.BasisValid ε.erase b) : ∃! B, BasisLift ε b B := by
  obtain ⟨B,hB⟩ := basisExists hw h
  exact ⟨B,hB,fun _ hC => basisLift_unique hC hB⟩

/-- Start entirely with surface context formation and basis validity.
Uniqueness is within the reconstructed context, as for term elaboration. -/
theorem basisValidityUnique (hw : Surface.InductiveCtxWF d g)
    (h : Surface.Basis.BasisValid g b) :
    ∃ (D : LCtx) (E : NLCtx), D.erase = d ∧ E.erase = g ∧
      InductiveCtxWF D E ∧ ∃! B, BasisLift E b B := by
  obtain ⟨⟨D,E⟩,hD,hE,hw'⟩ := contextExists hw
  exact ⟨D,E,hD,hE,hw',basisElaborationUnique hw' (by simpa only [hE] using h)⟩

theorem basisDenotation_eq (hA : BasisLift ε b A) (hB : BasisLift ε b B)
    (σ : DEnv) : denotBasis σ A = denotBasis σ B :=
  congrArg (denotBasis σ) (basisLift_unique hA hB)

end GLang.PaperSurfaceResults
