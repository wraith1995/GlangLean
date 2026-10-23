import GLang.Proofs.Adequacy.Foundations.Agree
import GLang.Proofs.Basis.BasisSoundnessLive
import GLang.Proofs.Source.Substitution

/-!
# Adequacy v3 — named/source binder bridges

This file isolates the locally-nameless bookkeeping which is independent of the
environment-aware FFS oracle.  It transports the *source* half of `LegacyAgree` and
`LegacyAgreeDims` between an opened body under `σ.bind` and the corresponding body with
its de Bruijn source stack left in place.  The value type, value environment, and
both value stacks are deliberately held fixed: their analogous transport is the
separate oracle-coherence obligation.
-/

namespace GLang

/-! ## Frame/lambda fiber identities -/

/-- Reading a denoted frame at an argument may use any fresh opening name,
not only `Basis.freshFor` chosen internally by `denotBasis`. -/
theorem denotBasis_frame_applyEl_openVar {σ : DEnv} {b₀ b₁ : Basis}
    (y : Name) (hy : y ∉ Basis.fv b₁)
    (x' : (denotTy σ (Basis.tof b₀)).El) :
    (denotBasis σ (.frame b₀ b₁)).applyEl x' =
      denotBasis (σ.bind y ((denotTy σ (Basis.tof b₀)).embed x'))
        (Basis.openVar y b₁) := by
  rw [denotBasis]
  simp only [BasisDenot.applyEl_frame]
  exact denotBasisOpenIrrel σ b₁ (Basis.freshFor b₁) y
    ((denotTy σ (Basis.tof b₀)).embed x') (Basis.freshFor_spec b₁) hy

/-- Applying the source denotation of a nonlinear lambda exposes its body
under the corresponding de Bruijn source stack. -/
theorem denotTerm_nllam_applyEl {σ : DEnv} {τ₀ : Ty} {e : Term}
    (x' : (denotTy σ τ₀).El) :
    (denotTerm σ (.nllam τ₀ e)).applyEl x' =
      denotTermAux σ [((denotTy σ τ₀).embed x')] e := by
  rw [denotTerm]
  simp only [denotTermAux, DVal.applyEl_pi]

/-! ## `srcShp` follows source opening and local-stack irrelevance -/

theorem srcShp_openRec_bind {z : Name} (σ : DEnv) :
    ∀ (Δs : List DVal) (k : Nat) (s : Space), z ∉ Space.fv s →
      srcShp (σ.bind z (Δs.getD k DVal.default)) Δs
          (Space.openRec k (.var z) s) = srcShp σ Δs s
  | _, _, .empty, _ => rfl
  | _, _, .real, _ => rfl
  | Δs, k, .dual s, hz => by
      simp only [Space.fv] at hz
      simp only [Space.openRec, srcShp]
      exact srcShp_openRec_bind σ Δs k s hz
  | Δs, k, .dsum s₀ s₁, hz => by
      simp only [Space.fv, Finset.mem_union, not_or] at hz
      simp only [Space.openRec, srcShp]
      rw [denotSpaceAux_openRec_bind σ Δs k s₀ hz.1,
        denotSpaceAux_openRec_bind σ Δs k s₁ hz.2]
  | Δs, k, .tprod s₀ s₁, hz => by
      simp only [Space.fv, Finset.mem_union, not_or] at hz
      simp only [Space.openRec, srcShp]
      rw [denotSpaceAux_openRec_bind σ Δs k s₀ hz.1,
        denotSpaceAux_openRec_bind σ Δs k s₁ hz.2]
  | Δs, k, .ker s₀ s₁ e, hz => by
      have h := denotSpaceAux_openRec_bind (x := z) σ Δs k (.ker s₀ s₁ e) hz
      simp only [Space.openRec] at h
      simp only [Space.openRec, srcShp]
      rw [h]
  | Δs, k, .coker s₀ s₁ e, hz => by
      have h := denotSpaceAux_openRec_bind (x := z) σ Δs k (.coker s₀ s₁ e) hz
      simp only [Space.openRec] at h
      simp only [Space.openRec, srcShp]
      rw [h]
  | Δs, k, .img s₀ s₁ e, hz => by
      have h := denotSpaceAux_openRec_bind (x := z) σ Δs k (.img s₀ s₁ e) hz
      simp only [Space.openRec] at h
      simp only [Space.openRec, srcShp]
      rw [h]
  | Δs, k, .coimg s₀ s₁ e, hz => by
      have h := denotSpaceAux_openRec_bind (x := z) σ Δs k (.coimg s₀ s₁ e) hz
      simp only [Space.openRec] at h
      simp only [Space.openRec, srcShp]
      rw [h]

/-- A locally closed source space has the same source shape at every local
source stack. -/
theorem srcShp_lc_irrel :
    ∀ {s : Space}, Space.lc s → ∀ (σ : DEnv) (Δs₁ Δs₂ : List DVal),
      srcShp σ Δs₁ s = srcShp σ Δs₂ s
  | _, .empty => fun _ _ _ => rfl
  | _, .real => fun _ _ _ => rfl
  | _, .dual hs => fun σ Δs₁ Δs₂ => by
      simp only [srcShp]
      exact srcShp_lc_irrel hs σ Δs₁ Δs₂
  | _, .dsum h₀ h₁ => fun σ Δs₁ Δs₂ => by
      simp only [srcShp]
      rw [denotSpaceAux_lc_irrel h₀ σ Δs₁ Δs₂,
        denotSpaceAux_lc_irrel h₁ σ Δs₁ Δs₂]
  | _, .tprod h₀ h₁ => fun σ Δs₁ Δs₂ => by
      simp only [srcShp]
      rw [denotSpaceAux_lc_irrel h₀ σ Δs₁ Δs₂,
        denotSpaceAux_lc_irrel h₁ σ Δs₁ Δs₂]
  | _, .ker hs₀ hs₁ he => fun σ Δs₁ Δs₂ => by
      simp only [srcShp]
      rw [denotSpaceAux_lc_irrel (Space.lc.ker hs₀ hs₁ he) σ Δs₁ Δs₂]
  | _, .coker hs₀ hs₁ he => fun σ Δs₁ Δs₂ => by
      simp only [srcShp]
      rw [denotSpaceAux_lc_irrel (Space.lc.coker hs₀ hs₁ he) σ Δs₁ Δs₂]
  | _, .img hs₀ hs₁ he => fun σ Δs₁ Δs₂ => by
      simp only [srcShp]
      rw [denotSpaceAux_lc_irrel (Space.lc.img hs₀ hs₁ he) σ Δs₁ Δs₂]
  | _, .coimg hs₀ hs₁ he => fun σ Δs₁ Δs₂ => by
      simp only [srcShp]
      rw [denotSpaceAux_lc_irrel (Space.lc.coimg hs₀ hs₁ he) σ Δs₁ Δs₂]

/-! ## Source-side opening for agreement -/

/-- Source opening under a matching named `σ` binding.  All value-side data is
fixed, so this theorem imposes no law on the FFS oracle. -/
theorem LegacyAgree.openRec_bind_src (orc : FFSOracleSem) {z : Name} (σ : DEnv)
    (ρ : ValEnvSem) :
    ∀ (τ : Ty) (τv : ValTy) (Δs : List DVal) (Γv : List ValTy)
      (Δv : List ValValSem) (k : Nat) (B : BasisDenot) (x : DVal)
      (y : ValValSem), z ∉ Ty.fv τ →
      (LegacyAgree orc (σ.bind z (Δs.getD k DVal.default)) ρ Δs Γv Δv
          (Ty.openRec k (.var z) τ) τv B x y ↔
        LegacyAgree orc σ ρ Δs Γv Δv τ τv B x y)
  | .space s, .space sv, Δs, Γv, Δv, k, B, x, y, hz => by
      simp only [Ty.fv] at hz
      cases y with
      | array a =>
          simp only [Ty.openRec, LegacyAgree.eq_def]
          rw [denotSpaceAux_openRec_bind σ Δs k s hz]
      | fn T f => simp only [Ty.openRec, LegacyAgree.eq_def]
  | .space _, .piTy _ _, _, _, _, _, _, _, _, _ => Iff.rfl
  | .piTy _ _, .space _, _, _, _, _, _, _, _, _ => Iff.rfl
  | .piTy τ₀ τ₁, .piTy τv₀ τv₁, Δs, Γv, Δv, k, B, x, y, hz => by
      simp only [Ty.fv, Finset.mem_union, not_or] at hz
      have hT₀ :
          denotTyAux (σ.bind z (Δs.getD k DVal.default)) Δs
              (Ty.openRec k (.var z) τ₀) = denotTyAux σ Δs τ₀ :=
        denotTyAux_openRec_bind σ Δs k τ₀ hz.1
      simp only [Ty.openRec]
      rw [LegacyAgree, LegacyAgree]
      revert hT₀
      generalize denotTyAux (σ.bind z (Δs.getD k DVal.default)) Δs
          (Ty.openRec k (.var z) τ₀) = T₁
      generalize denotTyAux σ Δs τ₀ = T₂
      intro hT₀
      subst hT₀
      refine forall_congr' fun x' => forall_congr' fun y' =>
        imp_congr
          (LegacyAgree.openRec_bind_src orc σ ρ τ₀ τv₀ Δs Γv Δv k
            B.domainBasis _ _ hz.1) ?_
      refine exists_congr fun y'' => and_congr Iff.rfl ?_
      have ih := LegacyAgree.openRec_bind_src orc σ ρ τ₁ τv₁
        (T₁.embed x' :: Δs) (τv₀ :: Γv)
        (ValValSem.fromEl (denotValTyS orc ρ Γv Δv τv₀) y' :: Δv) (k + 1)
        (B.applyEl x') (x.applyEl x') y'' hz.2
      simpa only [List.getD_cons_succ] using ih

/-- Dimension agreement version of `LegacyAgree.openRec_bind_src`. -/
theorem LegacyAgreeDims.openRec_bind_src (orc : FFSOracleSem) {z : Name} (σ : DEnv)
    (ρ : ValEnvSem) :
    ∀ (τ : Ty) (τv : ValTy) (Δs : List DVal) (Γv : List ValTy)
      (Δv : List ValValSem) (k : Nat), z ∉ Ty.fv τ →
      (LegacyAgreeDims orc (σ.bind z (Δs.getD k DVal.default)) ρ Δs Γv Δv
          (Ty.openRec k (.var z) τ) τv ↔
        LegacyAgreeDims orc σ ρ Δs Γv Δv τ τv)
  | .space s, .space sv, Δs, Γv, Δv, k, hz => by
      simp only [Ty.fv] at hz
      simp only [Ty.openRec]
      rw [LegacyAgreeDims, LegacyAgreeDims]
      rw [srcShp_openRec_bind σ Δs k s hz]
  | .space _, .piTy _ _, _, _, _, _, _ => Iff.rfl
  | .piTy _ _, .space _, _, _, _, _, _ => Iff.rfl
  | .piTy τ₀ τ₁, .piTy τv₀ τv₁, Δs, Γv, Δv, k, hz => by
      simp only [Ty.fv, Finset.mem_union, not_or] at hz
      have hT₀ :
          denotTyAux (σ.bind z (Δs.getD k DVal.default)) Δs
              (Ty.openRec k (.var z) τ₀) = denotTyAux σ Δs τ₀ :=
        denotTyAux_openRec_bind σ Δs k τ₀ hz.1
      simp only [Ty.openRec]
      rw [LegacyAgreeDims, LegacyAgreeDims]
      refine and_congr
        (LegacyAgreeDims.openRec_bind_src orc σ ρ τ₀ τv₀ Δs Γv Δv k hz.1) ?_
      revert hT₀
      generalize denotTyAux (σ.bind z (Δs.getD k DVal.default)) Δs
          (Ty.openRec k (.var z) τ₀) = T₁
      generalize denotTyAux σ Δs τ₀ = T₂
      intro hT₀
      subst hT₀
      refine exists_congr fun B => forall_congr' fun x' =>
        forall_congr' fun y' =>
          imp_congr
            (LegacyAgree.openRec_bind_src orc σ ρ τ₀ τv₀ Δs Γv Δv k B _ _ hz.1) ?_
      have ih := LegacyAgreeDims.openRec_bind_src orc σ ρ τ₁ τv₁
        (T₁.embed x' :: Δs) (τv₀ :: Γv)
        (ValValSem.fromEl (denotValTyS orc ρ Γv Δv τv₀) y' :: Δv) (k + 1) hz.2
      simpa only [List.getD_cons_succ] using ih

/-! ## Locally closed source types ignore the source stack -/

/-- Changing only the local *source* stack does not affect agreement at a
locally closed source type.  The value environment and both value stacks stay
fixed, so no oracle invariance is used. -/
theorem LegacyAgree.lc_irrel_src (orc : FFSOracleSem) :
    ∀ {τ : Ty}, Ty.lc τ → ∀ (τv : ValTy) (σ : DEnv) (ρ : ValEnvSem)
      (Δs₁ Δs₂ : List DVal) (Γv : List ValTy) (Δv : List ValValSem)
      (B : BasisDenot) (x : DVal) (y : ValValSem),
      LegacyAgree orc σ ρ Δs₁ Γv Δv τ τv B x y ↔
        LegacyAgree orc σ ρ Δs₂ Γv Δv τ τv B x y
  | _, .space hs => fun τv σ ρ Δs₁ Δs₂ Γv Δv B x y => by
      cases τv with
      | space sv =>
          cases y with
          | array a =>
              simp only [LegacyAgree.eq_def]
              rw [denotSpaceAux_lc_irrel hs σ Δs₁ Δs₂]
          | fn T f => simp only [LegacyAgree.eq_def]
      | piTy _ _ => exact Iff.rfl
  | .piTy τ₀ τ₁, .piTy L hτ₀ hbody =>
      fun τv σ ρ Δs₁ Δs₂ Γv Δv B x y => by
      cases τv with
      | space _ => exact Iff.rfl
      | piTy τv₀ τv₁ =>
          have hT₀ : denotTyAux σ Δs₁ τ₀ = denotTyAux σ Δs₂ τ₀ :=
            denotTyAux_lc_irrel hτ₀ σ Δs₁ Δs₂
          rw [LegacyAgree, LegacyAgree]
          revert hT₀
          generalize denotTyAux σ Δs₁ τ₀ = T₁
          generalize denotTyAux σ Δs₂ τ₀ = T₂
          intro hT₀
          subst hT₀
          refine forall_congr' fun x' => forall_congr' fun y' =>
            imp_congr
              (LegacyAgree.lc_irrel_src orc hτ₀ τv₀ σ ρ Δs₁ Δs₂ Γv Δv
                B.domainBasis _ _) ?_
          refine exists_congr fun y'' => and_congr Iff.rfl ?_
          obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv τ₁)
          simp only [Finset.mem_union, not_or] at hw
          have B₁ := LegacyAgree.openRec_bind_src orc (z := w) σ ρ τ₁ τv₁
            (T₁.embed x' :: Δs₁) (τv₀ :: Γv)
            (ValValSem.fromEl (denotValTyS orc ρ Γv Δv τv₀) y' :: Δv) 0
            (B.applyEl x') (x.applyEl x') y'' hw.2
          have B₂ := LegacyAgree.openRec_bind_src orc (z := w) σ ρ τ₁ τv₁
            (T₁.embed x' :: Δs₂) (τv₀ :: Γv)
            (ValValSem.fromEl (denotValTyS orc ρ Γv Δv τv₀) y' :: Δv) 0
            (B.applyEl x') (x.applyEl x') y'' hw.2
          simp only [List.getD_cons_zero] at B₁ B₂
          rw [← B₁, ← B₂]
          exact LegacyAgree.lc_irrel_src orc (hbody w hw.1) τv₁
            (σ.bind w (T₁.embed x')) ρ
            (T₁.embed x' :: Δs₁) (T₁.embed x' :: Δs₂)
            (τv₀ :: Γv)
            (ValValSem.fromEl (denotValTyS orc ρ Γv Δv τv₀) y' :: Δv)
            _ _ _

/-- Dimension-agreement version of `LegacyAgree.lc_irrel_src`. -/
theorem LegacyAgreeDims.lc_irrel_src (orc : FFSOracleSem) :
    ∀ {τ : Ty}, Ty.lc τ → ∀ (τv : ValTy) (σ : DEnv) (ρ : ValEnvSem)
      (Δs₁ Δs₂ : List DVal) (Γv : List ValTy) (Δv : List ValValSem),
      LegacyAgreeDims orc σ ρ Δs₁ Γv Δv τ τv ↔
        LegacyAgreeDims orc σ ρ Δs₂ Γv Δv τ τv
  | _, .space hs => fun τv σ ρ Δs₁ Δs₂ Γv Δv => by
      cases τv with
      | space sv =>
          rw [LegacyAgreeDims, LegacyAgreeDims, srcShp_lc_irrel hs σ Δs₁ Δs₂]
      | piTy _ _ => exact Iff.rfl
  | .piTy τ₀ τ₁, .piTy L hτ₀ hbody =>
      fun τv σ ρ Δs₁ Δs₂ Γv Δv => by
      cases τv with
      | space _ => exact Iff.rfl
      | piTy τv₀ τv₁ =>
          have hT₀ : denotTyAux σ Δs₁ τ₀ = denotTyAux σ Δs₂ τ₀ :=
            denotTyAux_lc_irrel hτ₀ σ Δs₁ Δs₂
          rw [LegacyAgreeDims, LegacyAgreeDims]
          refine and_congr
            (LegacyAgreeDims.lc_irrel_src orc hτ₀ τv₀ σ ρ Δs₁ Δs₂ Γv Δv) ?_
          revert hT₀
          generalize denotTyAux σ Δs₁ τ₀ = T₁
          generalize denotTyAux σ Δs₂ τ₀ = T₂
          intro hT₀
          subst hT₀
          refine exists_congr fun B => forall_congr' fun x' =>
            forall_congr' fun y' =>
              imp_congr
                (LegacyAgree.lc_irrel_src orc hτ₀ τv₀ σ ρ Δs₁ Δs₂ Γv Δv B _ _) ?_
          obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv τ₁)
          simp only [Finset.mem_union, not_or] at hw
          have B₁ := LegacyAgreeDims.openRec_bind_src orc (z := w) σ ρ τ₁ τv₁
            (T₁.embed x' :: Δs₁) (τv₀ :: Γv)
            (ValValSem.fromEl (denotValTyS orc ρ Γv Δv τv₀) y' :: Δv) 0 hw.2
          have B₂ := LegacyAgreeDims.openRec_bind_src orc (z := w) σ ρ τ₁ τv₁
            (T₁.embed x' :: Δs₂) (τv₀ :: Γv)
            (ValValSem.fromEl (denotValTyS orc ρ Γv Δv τv₀) y' :: Δv) 0 hw.2
          simp only [List.getD_cons_zero] at B₁ B₂
          rw [← B₁, ← B₂]
          exact LegacyAgreeDims.lc_irrel_src orc (hbody w hw.1) τv₁
            (σ.bind w (T₁.embed x')) ρ
            (T₁.embed x' :: Δs₁) (T₁.embed x' :: Δs₂)
            (τv₀ :: Γv)
            (ValValSem.fromEl (denotValTyS orc ρ Γv Δv τv₀) y' :: Δv)

end GLang
