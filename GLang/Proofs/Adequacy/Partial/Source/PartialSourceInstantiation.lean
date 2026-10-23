import GLang.Proofs.Adequacy.Agreement
import GLang.Proofs.Source.Substitution

/-!
# Source instantiation for raw agreement

Closed source substitution commutes with raw agreement and exact-basis raw
dimensions.  This module contains no consistency or adequacy-master state.
-/

namespace GLang.PartialAdequacy

/-! ## Source instantiation transport -/

/-- Reading raw agreement below a source-stack entry for a closed term is
equivalent to syntactically instantiating the source type at that index.  The
raw value and the value-side stacks are unchanged. -/
theorem Agree.openRec_src {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {u : Term} (hu : Term.lc u) :
    ∀ (τ : Ty) (Ds : List DVal) (Gv : List ValTy)
      (Dv : List ValValSem) (τv : ValTy) (B : BasisDenot)
      (x : DVal) (y : ValValSem),
      Agree orc σ ρ (Ds ++ [denotTerm σ u]) Gv Dv τ τv B x y ↔
        Agree orc σ ρ Ds Gv Dv
          (Ty.openRec Ds.length u τ) τv B x y
  | .space s, Ds, Gv, Dv, .space sv, B, x, y => by
      have hV : denotSpaceAux σ Ds (Space.openRec Ds.length u s) =
          denotSpaceAux σ (Ds ++ [denotTerm σ u]) s := by
        rw [denotSpaceAux_inst hu σ Ds s,
          denotTermAux_lc_irrel hu σ Ds []]
      cases y with
      | array a =>
          simp only [Ty.openRec, Agree]
          rw [hV]
      | fn T f => simp only [Ty.openRec, Agree]
  | .space _, _, _, _, .piTy _ _, _, _, _ => by
      simp only [Ty.openRec, Agree]
  | .piTy _ _, _, _, _, .space _, _, _, _ => by
      simp only [Ty.openRec, Agree]
  | .piTy τ₀ τ₁, Ds, Gv, Dv, .piTy τv₀ τv₁, B, x, y => by
      have hT : denotTyAux σ Ds (Ty.openRec Ds.length u τ₀) =
          denotTyAux σ (Ds ++ [denotTerm σ u]) τ₀ := by
        rw [denotTyAux_inst hu σ Ds τ₀,
          denotTermAux_lc_irrel hu σ Ds []]
      simp only [Ty.openRec, Agree]
      rw [hT]
      constructor
      · rintro ⟨D,hD,f,rfl,hf⟩
        refine ⟨D,hD,f,rfl,?_⟩
        intro x' argVal arg hto harg
        obtain ⟨out, hout, houtAgree⟩ := hf x' argVal arg hto
          ((Agree.openRec_src hu τ₀ Ds Gv Dv τv₀ B.domainBasis _ _).mpr harg)
        exact ⟨out, hout,
          (Agree.openRec_src hu τ₁
            ((denotTyAux σ (Ds ++ [denotTerm σ u]) τ₀).embed x' :: Ds)
            (τv₀ :: Gv) (argVal :: Dv) τv₁
            (B.applyEl x') (x.applyEl x') out).mp houtAgree⟩
      · rintro ⟨D,hD,f,rfl,hf⟩
        refine ⟨D,hD,f,rfl,?_⟩
        intro x' argVal arg hto harg
        obtain ⟨out, hout, houtAgree⟩ := hf x' argVal arg hto
          ((Agree.openRec_src hu τ₀ Ds Gv Dv τv₀ B.domainBasis _ _).mp harg)
        exact ⟨out, hout,
          (Agree.openRec_src hu τ₁
            ((denotTyAux σ (Ds ++ [denotTerm σ u]) τ₀).embed x' :: Ds)
            (τv₀ :: Gv) (argVal :: Dv) τv₁
            (B.applyEl x') (x.applyEl x') out).mpr houtAgree⟩
  termination_by τ _ _ _ _ _ _ _ => Ty.size τ
  decreasing_by all_goals simp only [Ty.size]; omega

/-- Source shape follows the same closed-term stack/instantiation bridge. -/
private theorem srcShp_openRec_src {σ : DEnv} {u : Term} (hu : Term.lc u) :
    ∀ (s : Space) (Ds : List DVal),
      srcShp σ (Ds ++ [denotTerm σ u]) s =
        srcShp σ Ds (Space.openRec Ds.length u s)
  | .empty, _ => rfl
  | .real, _ => rfl
  | .dual s, Ds => by
      simpa only [srcShp, Space.openRec] using srcShp_openRec_src hu s Ds
  | .dsum s₀ s₁, Ds => by
      have h₀ : denotSpaceAux σ Ds (Space.openRec Ds.length u s₀) =
          denotSpaceAux σ (Ds ++ [denotTerm σ u]) s₀ := by
        rw [denotSpaceAux_inst hu σ Ds s₀,
          denotTermAux_lc_irrel hu σ Ds []]
      have h₁ : denotSpaceAux σ Ds (Space.openRec Ds.length u s₁) =
          denotSpaceAux σ (Ds ++ [denotTerm σ u]) s₁ := by
        rw [denotSpaceAux_inst hu σ Ds s₁,
          denotTermAux_lc_irrel hu σ Ds []]
      simp only [srcShp, Space.openRec]
      rw [h₀, h₁]
  | .tprod s₀ s₁, Ds => by
      have h₀ : denotSpaceAux σ Ds (Space.openRec Ds.length u s₀) =
          denotSpaceAux σ (Ds ++ [denotTerm σ u]) s₀ := by
        rw [denotSpaceAux_inst hu σ Ds s₀,
          denotTermAux_lc_irrel hu σ Ds []]
      have h₁ : denotSpaceAux σ Ds (Space.openRec Ds.length u s₁) =
          denotSpaceAux σ (Ds ++ [denotTerm σ u]) s₁ := by
        rw [denotSpaceAux_inst hu σ Ds s₁,
          denotTermAux_lc_irrel hu σ Ds []]
      simp only [srcShp, Space.openRec]
      rw [h₀, h₁]
  | .ker s₀ s₁ e, Ds => by
      have hV : denotSpaceAux σ Ds
            (Space.openRec Ds.length u (.ker s₀ s₁ e)) =
          denotSpaceAux σ (Ds ++ [denotTerm σ u]) (.ker s₀ s₁ e) := by
        rw [denotSpaceAux_inst hu σ Ds (.ker s₀ s₁ e),
          denotTermAux_lc_irrel hu σ Ds []]
      simp only [srcShp]
      exact congrArg (fun V : HSpace => [Module.finrank ℝ V.carrier]) hV.symm
  | .coker s₀ s₁ e, Ds => by
      have hV : denotSpaceAux σ Ds
            (Space.openRec Ds.length u (.coker s₀ s₁ e)) =
          denotSpaceAux σ (Ds ++ [denotTerm σ u]) (.coker s₀ s₁ e) := by
        rw [denotSpaceAux_inst hu σ Ds (.coker s₀ s₁ e),
          denotTermAux_lc_irrel hu σ Ds []]
      simp only [srcShp]
      exact congrArg (fun V : HSpace => [Module.finrank ℝ V.carrier]) hV.symm
  | .img s₀ s₁ e, Ds => by
      have hV : denotSpaceAux σ Ds
            (Space.openRec Ds.length u (.img s₀ s₁ e)) =
          denotSpaceAux σ (Ds ++ [denotTerm σ u]) (.img s₀ s₁ e) := by
        rw [denotSpaceAux_inst hu σ Ds (.img s₀ s₁ e),
          denotTermAux_lc_irrel hu σ Ds []]
      simp only [srcShp]
      exact congrArg (fun V : HSpace => [Module.finrank ℝ V.carrier]) hV.symm
  | .coimg s₀ s₁ e, Ds => by
      have hV : denotSpaceAux σ Ds
            (Space.openRec Ds.length u (.coimg s₀ s₁ e)) =
          denotSpaceAux σ (Ds ++ [denotTerm σ u]) (.coimg s₀ s₁ e) := by
        rw [denotSpaceAux_inst hu σ Ds (.coimg s₀ s₁ e),
          denotTermAux_lc_irrel hu σ Ds []]
      simp only [srcShp]
      exact congrArg (fun V : HSpace => [Module.finrank ℝ V.carrier]) hV.symm
  termination_by s _ => Space.size s
  decreasing_by all_goals simp only [Space.size]; omega

/-- Basis-indexed raw dimensions obey source instantiation as well. -/
theorem DimsAt.openRec_src
    {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {u : Term} (hu : Term.lc u) :
    ∀ (τ : Ty) (Ds : List DVal) (Gv : List ValTy)
      (Dv : List ValValSem) (τv : ValTy) (B : BasisDenot),
      DimsAt orc σ ρ (Ds ++ [denotTerm σ u]) Gv Dv τ τv B ↔
        DimsAt orc σ ρ Ds Gv Dv
          (Ty.openRec Ds.length u τ) τv B
  | .space s, Ds, Gv, Dv, .space sv, B => by
      simp only [Ty.openRec, DimsAt]
      rw [srcShp_openRec_src hu s Ds]
  | .space _, _, _, _, .piTy _ _, _ => by
      simp only [Ty.openRec, DimsAt]
  | .piTy _ _, _, _, _, .space _, _ => by
      simp only [Ty.openRec, DimsAt]
  | .piTy τ₀ τ₁, Ds, Gv, Dv, .piTy τv₀ τv₁, B => by
      have hT : denotTyAux σ Ds (Ty.openRec Ds.length u τ₀) =
          denotTyAux σ (Ds ++ [denotTerm σ u]) τ₀ := by
        rw [denotTyAux_inst hu σ Ds τ₀,
          denotTermAux_lc_irrel hu σ Ds []]
      simp only [Ty.openRec, DimsAt]
      rw [hT]
      constructor
      · rintro ⟨hdom, hcod⟩
        refine ⟨(DimsAt.openRec_src hu τ₀ Ds Gv Dv τv₀
          B.domainBasis).mp hdom, ?_⟩
        intro x' argVal arg hto harg
        have hargLeft := (Agree.openRec_src hu τ₀ Ds Gv Dv τv₀
          B.domainBasis _ _).mpr harg
        have hcodLeft := hcod x' argVal arg hto hargLeft
        exact (DimsAt.openRec_src hu τ₁
          ((denotTyAux σ (Ds ++ [denotTerm σ u]) τ₀).embed x' :: Ds)
          (τv₀ :: Gv) (argVal :: Dv) τv₁ (B.applyEl x')).mp hcodLeft
      · rintro ⟨hdom, hcod⟩
        refine ⟨(DimsAt.openRec_src hu τ₀ Ds Gv Dv τv₀
          B.domainBasis).mpr hdom, ?_⟩
        intro x' argVal arg hto harg
        have hargRight := (Agree.openRec_src hu τ₀ Ds Gv Dv τv₀
          B.domainBasis _ _).mp harg
        have hcodRight := hcod x' argVal arg hto hargRight
        exact (DimsAt.openRec_src hu τ₁
          ((denotTyAux σ (Ds ++ [denotTerm σ u]) τ₀).embed x' :: Ds)
          (τv₀ :: Gv) (argVal :: Dv) τv₁ (B.applyEl x')).mpr hcodRight
  termination_by τ _ _ _ _ _ => Ty.size τ
  decreasing_by all_goals simp only [Ty.size]; omega

/-- Root-stack specialization of `Agree.openRec_src`, in the vocabulary
used by nonlinear application. -/
theorem Agree.instantiate_src
    {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {u : Term} (hu : Term.lc u) (τ : Ty) (Gv : List ValTy)
    (Dv : List ValValSem) (τv : ValTy) (B : BasisDenot)
    (x : DVal) (y : ValValSem) :
    Agree orc σ ρ [denotTerm σ u] Gv Dv τ τv B x y ↔
      Agree orc σ ρ [] Gv Dv (Ty.instantiate u τ) τv B x y := by
  simpa only [Ty.instantiate, List.nil_append] using
    (Agree.openRec_src hu τ [] Gv Dv τv B x y)

/-- Root-stack specialization of `DimsAt.openRec_src`. -/
theorem DimsAt.instantiate_src
    {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {u : Term} (hu : Term.lc u) (τ : Ty) (Gv : List ValTy)
    (Dv : List ValValSem) (τv : ValTy) (B : BasisDenot) :
    DimsAt orc σ ρ [denotTerm σ u] Gv Dv τ τv B ↔
      DimsAt orc σ ρ [] Gv Dv
        (Ty.instantiate u τ) τv B := by
  simpa only [Ty.instantiate, List.nil_append] using
    (DimsAt.openRec_src hu τ [] Gv Dv τv B)

/-! ## Named source-binder transport -/

end GLang.PartialAdequacy
