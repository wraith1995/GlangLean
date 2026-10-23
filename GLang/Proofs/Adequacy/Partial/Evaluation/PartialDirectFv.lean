import GLang.Proofs.Value.Partial.PartialValueRuntimeTransport
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectLocality
import GLang.Proofs.Adequacy.Foundations.FvIrrel

/-! Fresh-name transport for the error-aware evaluator and its recursive oracle.
Both successful results and failures are preserved. -/
namespace GLang.PartialDirectFv

/-- Updating a name absent from the query and local type context preserves the
entire partial answer, including errors. -/
def OracleFresh (orc : PartialFFSOracleSem) : Prop :=
  ∀ (ρ : ValEnvSem) (y : VName) (w : ValValSem) (Γ : List ValTy) (Δ : List ValValSem)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr),
    ValTyCtxFresh y Γ → y ∉ ValSpace.fv s → y ∉ ValExpr.fv e →
    orc (ρ.update y w) Γ Δ p s e = orc ρ Γ Δ p s e

theorem numbers_fresh {orc : PartialFFSOracleSem} (h : OracleFresh orc) :
    OracleFvIrrel (fun ρ Γ Δ => PartialValueEval.numbers (orc ρ Γ Δ)) := by
  intro ρ y w Γ Δ p s e hΓ hs he
  simp only [PartialValueEval.numbers, h ρ y w Γ Δ p s e hΓ hs he]

theorem observations {orc : PartialFFSOracleSem} (h : OracleFresh orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) (Γ : List ValTy) (Δ : List ValValSem)
    (hΓ : ValTyCtxFresh y Γ) : ∀ s : ValSpace, y ∉ s.fv →
      s.dofPartial (orc (ρ.update y w) Γ Δ) = s.dofPartial (orc ρ Γ Δ) ∧
      s.shpOfPartial (orc (ρ.update y w) Γ Δ) = s.shpOfPartial (orc ρ Γ Δ)
  | .empty, _ => by simp [ValSpace.dofPartial, ValSpace.shpOfPartial]
  | .real, _ => by simp [ValSpace.dofPartial, ValSpace.shpOfPartial]
  | .dsum a b, hs => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hs
      have ha := (observations h ρ y w Γ Δ hΓ a hs.1).1
      have hb := (observations h ρ y w Γ Δ hΓ b hs.2).1
      have he : (ValSpace.dsum a b).shpOfPartial (orc (ρ.update y w) Γ Δ) =
          (ValSpace.dsum a b).shpOfPartial (orc ρ Γ Δ) := by
        simp only [ValSpace.shpOfPartial, ha, hb]
      exact ⟨by simp only [ValSpace.dofPartial, he], he⟩
  | .tprod a b, hs => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hs
      have ha := (observations h ρ y w Γ Δ hΓ a hs.1).1
      have hb := (observations h ρ y w Γ Δ hΓ b hs.2).1
      have he : (ValSpace.tprod a b).shpOfPartial (orc (ρ.update y w) Γ Δ) =
          (ValSpace.tprod a b).shpOfPartial (orc ρ Γ Δ) := by
        simp only [ValSpace.shpOfPartial, ha, hb]
      exact ⟨by simp only [ValSpace.dofPartial, he], he⟩
  | .ffs p s e, hs => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hs
      have he := h ρ y w Γ Δ p s e hΓ hs.1 hs.2
      constructor <;> simp only [ValSpace.dofPartial, ValSpace.shpOfPartial, he]
termination_by s => sizeOf s

theorem dimensions_eq {orc : PartialFFSOracleSem} (h : OracleFresh orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) (Γ : List ValTy) (Δ : List ValValSem)
    (hΓ : ValTyCtxFresh y Γ) (ss : List ValSpace) (hs : ∀ s ∈ ss, y ∉ s.fv) :
    PartialValueEval.dimensions (orc (ρ.update y w) Γ Δ) ss =
      PartialValueEval.dimensions (orc ρ Γ Δ) ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      simp only [PartialValueEval.dimensions,
        (observations h ρ y w Γ Δ hΓ s (hs s (by simp))).1,
        ih (fun t ht => hs t (by simp [ht]))]

theorem withDimensions_congr {orc : PartialFFSOracleSem} (h : OracleFresh orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) (Γ : List ValTy) (Δ : List ValValSem)
    (hΓ : ValTyCtxFresh y Γ) (ss : List ValSpace) (hs : ∀ s ∈ ss, y ∉ s.fv)
    (f g : FFSOracle → Except DimError ValValSem)
    (he : f (PartialValueEval.numbers (orc (ρ.update y w) Γ Δ)) =
      g (PartialValueEval.numbers (orc ρ Γ Δ))) :
    PartialValueEval.withDimensions (orc (ρ.update y w) Γ Δ) ss f =
      PartialValueEval.withDimensions (orc ρ Γ Δ) ss g := by
  simp only [PartialValueEval.withDimensions, dimensions_eq h ρ y w Γ Δ hΓ ss hs, he]

theorem type_eq {orc : PartialFFSOracleSem} (h : OracleFresh orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) :
    ∀ (τ : ValTy) (Γ : List ValTy) (Δ : List ValValSem),
      ValTyCtxFresh y Γ → y ∉ τ.fv →
      denotValTyPartial orc (ρ.update y w) Γ Δ τ = denotValTyPartial orc ρ Γ Δ τ
  | .space s, Γ, Δ, hΓ, hs => by
      simp only [denotValTyPartial, (observations h ρ y w Γ Δ hΓ s hs).1]
  | .piTy d c, Γ, Δ, hΓ, hs => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hs
      rw [denotValTyPartial, denotValTyPartial, type_eq h ρ y w d Γ Δ hΓ hs.1]
      cases ht : denotValTyPartial orc ρ Γ Δ d with
      | error e => rfl
      | ok domain =>
          apply congrArg Except.ok
          apply congrArg (PartialValType.piTy domain)
          funext a
          exact type_eq h ρ y w c (d :: Γ) (d.carrierToVal a :: Δ)
            (hΓ.cons hs.1) hs.2

theorem reshape_eq {orc : PartialFFSOracleSem} (h : OracleFresh orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) :
    ∀ (v : ValValSem) (t s : ValTy)
      (Γt : List ValTy) (Δt : List ValValSem) (Γs : List ValTy) (Δs : List ValValSem),
      ValTyCtxFresh y Γt → ValTyCtxFresh y Γs → y ∉ t.fv → y ∉ s.fv →
      PartialValueEval.reshapeBetween orc (ρ.update y w) Γt Δt Γs Δs v t s =
        PartialValueEval.reshapeBetween orc ρ Γt Δt Γs Δs v t s
  | .array a, .space t, .space s, Γt, Δt, Γs, Δs, hΓt, hΓs, ht, hs => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at ht hs
      simp only [PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray,
        (observations h ρ y w Γt Δt hΓt t ht).1, (observations h ρ y w Γs Δs hΓs s hs).1]
  | .fn _ _, .space _, _, _, _, _, _, _, _, _, _ => by
      simp only [PartialValueEval.reshapeBetween]
  | .array _, .space _, .piTy _ _, _, _, _, _, _, _, _, _ => by
      simp only [PartialValueEval.reshapeBetween]
  | v, .piTy dt ct, .piTy ds cs, Γt, Δt, Γs, Δs, hΓt, hΓs, ht, hs => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at ht hs
      rw [PartialValueEval.reshapeBetween, PartialValueEval.reshapeBetween,
        type_eq h ρ y w dt Γt Δt hΓt ht.1, type_eq h ρ y w ds Γs Δs hΓs hs.1]
      cases hdt : denotValTyPartial orc ρ Γt Δt dt with
      | error e => rfl
      | ok target =>
        cases hds : denotValTyPartial orc ρ Γs Δs ds with
        | error e => rfl
        | ok source =>
          apply congrArg Except.ok
          apply congrArg (ValValSem.fn dt.carrierEl)
          funext a
          cases hc : target.check a with
          | error e => rfl
          | ok checked =>
            simp only []
            rw [reshape_eq h ρ y w (dt.carrierToVal checked) ds dt Γs Δs Γt Δt hΓs hΓt hs.1 ht.1]
            cases ha : PartialValueEval.reshapeBetween orc ρ Γs Δs Γt Δt (dt.carrierToVal checked) ds dt with
            | error e => rfl
            | ok argS =>
              simp only []
              cases hb : ds.carrierFromVal argS with
              | error e => rfl
              | ok arg =>
                simp only []
                cases hr : v.applyTyped arg with
                | error e => rfl
                | ok result =>
                  exact reshape_eq h ρ y w result ct cs
                    (dt :: Γt) (dt.carrierToVal checked :: Δt) (ds :: Γs) (argS :: Δs)
                    (hΓt.cons ht.1) (hΓs.cons hs.1) ht.2 hs.2
  | _, .piTy _ _, .space _, _, _, _, _, _, _, _, _ => by
      simp only [PartialValueEval.reshapeBetween]
termination_by _ t s _ _ _ _ _ _ _ _ => ValTy.kindSize t + ValTy.kindSize s
decreasing_by all_goals (simp only [ValTy.kindSize_piTy]; omega)

theorem eval_eq {orc : PartialFFSOracleSem} (hirr : OracleFresh orc)
    (ρ : ValEnvSem) (y : VName) (w : ValValSem) :
    ∀ (e : ValExpr) (Γ : List ValTy) (Δ : List ValValSem),
      y ∉ ValExpr.fv e → (∀ τ ∈ Γ, y ∉ ValTy.fv τ) →
      denotValB_partial orc (ρ.update y w) Γ Δ e = denotValB_partial orc ρ Γ Δ e
  | .bvar n, Γ, Δ, _, _ => by rw [denotValB_partial, denotValB_partial]
  | .var x τ, Γ, Δ, hy, _ => by
      simp only [ValExpr.fv, Finset.mem_insert, not_or] at hy
      rw [denotValB_partial, denotValB_partial, ValEnvSem.update_other _ _ _ _ (Ne.symm hy.1)]
  | .rlit r, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.rlit r) Γ hy hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole]
  | .zero s, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.zero s) Γ hy hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole]
  | .scale e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.scale e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e₀ Γ Δ hy.1 hΓ,
          eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
        simp only [ValueShape.scale, hdof _
          (ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ)]
  | .vadd s e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hy.1.1,
          eval_eq hirr ρ y w e₀ Γ Δ hy.1.2 hΓ,
          eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
  | .delta n s, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.delta n s) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole, hdof _ hy]
  | .idelta s, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.idelta s) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole, hdof _ hy]
  | .tprodE e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.tprodE e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole, hdof _ h1,
          eval_eq hirr ρ y w e₀ Γ Δ hy.1 hΓ,
          eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
        simp only [ValueShape.pair, hdof _ h1, hdof _
          (ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ)]
  | .dsumE e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.dsumE e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole, hdof _ h0,
          eval_eq hirr ρ y w e₀ Γ Δ hy.1 hΓ,
          eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
        simp only [ValueShape.pair, hdof _ h0, hdof _
          (ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ)]
  | .vtrans e, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.vtrans e) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy hΓ]
        simp only [ValueShape.tensor]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish_strict hdof h0
  | .ttv s e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.ttv s e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1.2 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole, hdof _ hy.1.1,
          eval_eq hirr ρ y w e₀ Γ Δ hy.1.2 hΓ,
          eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
        simp only [ValueShape.ttv, ValueShape.pair, hdof _ h0, hdof _ hy.1.1,
          hdof _ (ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ)]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e₀ <;> intro h0 <;> (try dsimp only) <;>
          simp only [hdof _ hy.1.1, hdof _
            (ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ)] <;>
          fv_dof_finish_strict hdof h0
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.mtm n₀ n₁ s₀ s₁ e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1.2 hΓ
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole, hdof _ hy.1.1.1,
          eval_eq hirr ρ y w e₀ Γ Δ hy.1.2 hΓ,
          eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
        simp only [ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, hdof _ hy.1.1.1]
        congr 1; funext i
        revert h0 h1
        cases ValExpr.inferSpaceCtx Γ e₀ <;> cases ValExpr.inferSpaceCtx Γ e₁ <;>
          intro h0 h1 <;> (try simp only [ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, false_and, and_false, if_false]) <;> (try rfl)
        simp only [ValSpace.fv, Finset.mem_union, not_or] at h0 h1
        simp only [hdof _ hy.1.1.1, hdof _ h0.1, hdof _ h0.2, hdof _ h1.1, hdof _ h1.2]
  | .vkrn e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.vkrn e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e₀ Γ Δ hy.1 hΓ,
          eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
        simp only [ValueShape.matrices, ValueShape.tensor]
        congr 1; funext i
        revert h0 h1
        cases ValExpr.inferSpaceCtx Γ e₀ <;> cases ValExpr.inferSpaceCtx Γ e₁ <;>
          intro h0 h1 <;> (try simp only [ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, false_and, and_false, if_false]) <;> (try rfl)
        simp only [ValSpace.fv, Finset.mem_union, not_or] at h0 h1
        simp only [hdof _ h0.1, hdof _ h0.2, hdof _ h1.1, hdof _ h1.2]
  | .vblk e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.vblk e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e₀ Γ Δ hy.1 hΓ,
          eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
        simp only [ValueShape.matrices, ValueShape.tensor]
        congr 1; funext i
        revert h0 h1
        cases ValExpr.inferSpaceCtx Γ e₀ <;> cases ValExpr.inferSpaceCtx Γ e₁ <;>
          intro h0 h1 <;> (try simp only [ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, false_and, and_false, if_false]) <;> (try rfl)
        simp only [ValSpace.fv, Finset.mem_union, not_or] at h0 h1
        simp only [hdof _ h0.1, hdof _ h0.2, hdof _ h1.1, hdof _ h1.2]
  | .vsum s es, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.vsum s es) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole, hdof _ hy.1]
        have hm : ((es.take (ValSpace.dof (PartialValueEval.numbers (orc ρ Γ Δ)) s)).attach.map
            (fun e => denotValB_partial orc (ρ.update y w) Γ Δ e.val)) =
            ((es.take (ValSpace.dof (PartialValueEval.numbers (orc ρ Γ Δ)) s)).attach.map
            (fun e => denotValB_partial orc ρ Γ Δ e.val)) := by
          apply List.map_congr_left
          intro e _
          have hmem : (e : ValExpr) ∈ es := List.mem_of_mem_take e.property
          have hfve : y ∉ ValExpr.fv (e : ValExpr) := fun hc =>
            hy.2 (ValExpr.mem_fvList.mpr ⟨e, hmem, hc⟩)
          exact eval_eq hirr ρ y w e Γ Δ hfve hΓ
        simp only [hm]
  | .reshap e τ τ₀, Γ, Δ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_partial, denotValB_partial,
        eval_eq hirr ρ y w e Γ Δ hy.1.1 hΓ]
      cases hden : denotValB_partial orc ρ Γ Δ e with
      | error err => rfl
      | ok v =>
          have hf := ValExpr.notMem_fv_inferTypeCtx y e Γ hy.1.1 hΓ
          cases τ₀ with
          | space s => exact reshape_eq hirr ρ y w v τ (.space s) Γ Δ Γ Δ hΓ hΓ hy.1.2 hy.2
          | piTy d c =>
            cases hi : ValExpr.inferTypeCtx Γ e with
            | space s => rfl
            | piTy di ci =>
              simp only [hi] at hf
              exact reshape_eq hirr ρ y w v τ (.piTy di ci) Γ Δ Γ Δ hΓ hΓ hy.1.2 hf
  | .pinv e, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.pinv e) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy hΓ]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish hdof h0
  | .inv e, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.inv e) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy hΓ]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish hdof h0
  | .svds e, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.svds e) Γ hy hΓ
      simp only [ValExpr.fv] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy hΓ]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish hdof h0
  | .gsvdS e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdS e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy.1.1 hΓ,
          eval_eq hirr ρ y w a Γ Δ hy.1.2 hΓ,
          eval_eq hirr ρ y w b Γ Δ hy.2 hΓ]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish hdof h0
  | .gsvdU e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdU e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy.1.1 hΓ,
          eval_eq hirr ρ y w a Γ Δ hy.1.2 hΓ,
          eval_eq hirr ρ y w b Γ Δ hy.2 hΓ]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish hdof h0
  | .gsvdUI e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdUI e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy.1.1 hΓ,
          eval_eq hirr ρ y w a Γ Δ hy.1.2 hΓ,
          eval_eq hirr ρ y w b Γ Δ hy.2 hΓ]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish hdof h0
  | .gsvdV e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdV e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy.1.1 hΓ,
          eval_eq hirr ρ y w a Γ Δ hy.1.2 hΓ,
          eval_eq hirr ρ y w b Γ Δ hy.2 hΓ]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish hdof h0
  | .gsvdVI e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gsvdVI e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy.1.1 hΓ,
          eval_eq hirr ρ y w a Γ Δ hy.1.2 hΓ,
          eval_eq hirr ρ y w b Γ Δ hy.2 hΓ]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish hdof h0
  | .gpinv e a b, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.gpinv e a b) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e Γ hy.1.1 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl | rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e Γ Δ hy.1.1 hΓ,
          eval_eq hirr ρ y w a Γ Δ hy.1.2 hΓ,
          eval_eq hirr ρ y w b Γ Δ hy.2 hΓ]
        congr 1; funext i
        revert h0; cases ValExpr.inferSpaceCtx Γ e <;> intro h0 <;> (try dsimp only) <;>
          fv_dof_finish hdof h0
  | .rrefRep e₀ e₁, Γ, Δ, hy, hΓ => by
      have hdof := ValSpace.dof_update_of_not_mem_fv (numbers_fresh hirr) ρ y w Γ Δ hΓ
      have hwhole := ValExpr.notMem_fv_inferSpaceCtx y (.rrefRep e₀ e₁) Γ hy hΓ
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have h0 := ValExpr.notMem_fv_inferSpaceCtx y e₀ Γ hy.1 hΓ
      have h1 := ValExpr.notMem_fv_inferSpaceCtx y e₁ Γ hy.2 hΓ
      rw [denotValB_partial, denotValB_partial]
      apply withDimensions_congr hirr ρ y w Γ Δ hΓ
      · intro sp hsp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
        rcases hsp with rfl | rfl
        all_goals first
          | assumption
          | (apply ValExpr.notMem_fv_inferSpaceCtx y _ Γ _ hΓ; tauto)
          | tauto
      · dsimp only
        rw [ hdof _ hwhole,
          eval_eq hirr ρ y w e₀ Γ Δ hy.1 hΓ,
          eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
        congr 1; funext i
        revert h1; cases ValExpr.inferSpaceCtx Γ e₁ <;> intro h1 <;> (try dsimp only) <;>
          fv_dof_finish hdof h1
  | .vlam τ₀ τ₁ body, Γ, Δ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      rw [denotValB_partial, denotValB_partial,
        type_eq hirr ρ y w τ₀ Γ Δ hΓ hy.1.1]
      cases hd : denotValTyPartial orc ρ Γ Δ τ₀ with
      | error e => rfl
      | ok d =>
          apply congrArg Except.ok
          apply congrArg (ValValSem.fn τ₀.carrierEl)
          funext a
          exact eval_eq hirr ρ y w body (τ₀ :: Γ) _ hy.2 (ValTyCtxFresh.cons hy.1.1 hΓ)
  | .appV e₀ e₁, Γ, Δ, hy, hΓ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
      have hff := ValExpr.notMem_fv_inferTypeCtx y e₀ Γ hy.1 hΓ
      rw [denotValB_partial, denotValB_partial,
        eval_eq hirr ρ y w e₀ Γ Δ hy.1 hΓ,
        eval_eq hirr ρ y w e₁ Γ Δ hy.2 hΓ]
      cases hft : ValExpr.inferTypeCtx Γ e₀ with
      | space s => rfl
      | piTy d c =>
        rw [hft] at hff
        simp only [ValTy.fv, Finset.mem_union, not_or] at hff
        exact PartialValueEval.applyDomainChecked_congr _ _ _ _ _ _ _ _ _ _
          (ValSoundOfDenot.ValTy.SameShape.refl d)
          (heq_of_eq (type_eq hirr ρ y w d Γ Δ hΓ hff.1)) _ _

  termination_by e _ _ => ValExpr.size e
  decreasing_by
    all_goals
      first
      | (have hmem : _ ∈ _ := List.mem_of_getElem? ‹_[_]? = some _›
         have hle := ValExpr.size_le_sizeList hmem
         simp only [ValExpr.size]
         omega)
      | (have hle := ValExpr.size_le_sizeList ‹_ ∈ _›
         simp only [ValExpr.size]
         omega)
      | (simp [ValExpr.size]; omega)
      | (simp only [ValExpr.size]; omega)

open DirectOracleWF

private theorem query_fresh (root : Query) :
    forall (y : VName) (value : ValValSem),
      ValTyCtxFresh y root.Gamma ->
      y ∉ ValSpace.fv root.parent ->
      y ∉ ValExpr.fv root.witness ->
      PartialDirectOracle.query
          { root with rho := root.rho.update y value } =
        PartialDirectOracle.query root := by
  generalize hn : Query.certifiedMeasure root = n
  induction n using Nat.strong_induction_on generalizing root with
  | h n ih =>
      intro y value hGamma hparent hwitness
      let guarded : PartialFFSOracleSem :=
        PartialDirectOracle.smallerOracle root
          (fun query _ => PartialDirectOracle.query query)
      have guarded_fv : OracleFresh guarded := by
        intro rho name replacement Gamma Delta property parent witness
          hGamma' hparent' hwitness'
        simp only [guarded, PartialDirectOracle.smallerOracle]
        let updated : Query :=
          ⟨rho.update name replacement, Gamma, Delta,
            property, parent, witness⟩
        let plain : Query :=
          ⟨rho, Gamma, Delta, property, parent, witness⟩
        change
          (if _ : Query.certifiedMeasure updated < Query.certifiedMeasure root then
              PartialDirectOracle.query updated
            else .error .mismatch) =
          (if _ : Query.certifiedMeasure plain < Query.certifiedMeasure root then
              PartialDirectOracle.query plain
            else .error .mismatch)
        have hmeasure : Query.certifiedMeasure updated =
            Query.certifiedMeasure plain := by
          rfl
        by_cases hlt : Query.certifiedMeasure plain <
            Query.certifiedMeasure root
        · have hlt' : Query.certifiedMeasure updated <
              Query.certifiedMeasure root := by
            simpa only [hmeasure] using hlt
          rw [dif_pos hlt, dif_pos hlt']
          have hrec := ih (Query.certifiedMeasure plain)
            (by simpa only [hn] using hlt) plain rfl name replacement
            hGamma' hparent' hwitness'
          simpa only [updated, plain] using hrec
        · have hlt' : ¬ Query.certifiedMeasure updated <
              Query.certifiedMeasure root := by
            simpa only [hmeasure] using hlt
          rw [dif_neg hlt, dif_neg hlt']
      let updatedRoot : Query :=
        { root with rho := root.rho.update y value }
      have hrootMeasure : Query.certifiedMeasure updatedRoot =
          Query.certifiedMeasure root := by
        rfl
      have hguardedRoot :
          PartialDirectOracle.smallerOracle updatedRoot
              (fun query _ => PartialDirectOracle.query query) = guarded := by
        funext rho Gamma Delta property parent witness
        simp only [guarded, PartialDirectOracle.smallerOracle]
        rw [hrootMeasure]
      rw [PartialDirectOracle.query_eq updatedRoot, PartialDirectOracle.query_eq root]
      simp only [PartialDirectOracle.step, hrootMeasure]
      split
      · rfl
      rw [hguardedRoot]
      rw [(observations guarded_fv root.rho y value root.Gamma root.Delta hGamma
        root.parent hparent).2]
      rw [eval_eq guarded_fv root.rho y value root.witness root.Gamma root.Delta
        hwitness hGamma]

/-- The direct oracle satisfies the current context-aware FV contract without
passing through any finite approximation or eventual-value fallback. -/
theorem oracle_fresh :
    OracleFresh PartialDirectOracle.oracle := by
  intro rho y value Gamma Delta property parent witness
    hGamma hparent hwitness
  exact query_fresh
    ⟨rho, Gamma, Delta, property, parent, witness⟩
    y value hGamma hparent hwitness

/-- The actual partial evaluator preserves the entire result under fresh updates. -/
theorem eval_fresh (ρ : ValEnvSem) (y : VName) (w : ValValSem)
    (e : ValExpr) (Γ : List ValTy) (Δ : List ValValSem)
    (he : y ∉ e.fv) (hΓ : ValTyCtxFresh y Γ) :
    Adequacy.Partial.evalVal (ρ.update y w) Γ Δ e =
      Adequacy.Partial.evalVal ρ Γ Δ e :=
  eval_eq oracle_fresh ρ y w e Γ Δ he hΓ

/-- Checking a result at a fresh type also preserves failures and functions. -/
theorem checked_fresh (ρ : ValEnvSem) (y : VName) (w : ValValSem)
    (τ : ValTy) (e : ValExpr) (Γ : List ValTy) (Δ : List ValValSem)
    (hτ : y ∉ τ.fv) (he : y ∉ e.fv) (hΓ : ValTyCtxFresh y Γ) :
    Adequacy.Partial.evalValCheckedAt (ρ.update y w) Γ Δ τ e =
      Adequacy.Partial.evalValCheckedAt ρ Γ Δ τ e := by
  simp only [Adequacy.Partial.evalValCheckedAt, denotValB_partialCheckedAt,
    eval_eq oracle_fresh ρ y w e Γ Δ he hΓ, checkValTyPartial,
    type_eq oracle_fresh ρ y w τ Γ Δ hΓ hτ]

end GLang.PartialDirectFv
