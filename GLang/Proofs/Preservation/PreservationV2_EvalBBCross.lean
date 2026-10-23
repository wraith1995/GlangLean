/- GLang.PreservationV2_EvalBBCross — gen-4 standalone helpers for the structural
`EvalBB` (change-of-basis) arms of `preservation_joint` (motive_3 / part 2). -/
import GLang.Proofs.Preservation.PreservationV2Helpers
import GLang.Operational.Ordinary

namespace GLang

/-- A CobShape triple over a witness `env`: its type is a matrix `sv₀ ⊗ sv₁` whose
    factors are genuine realizations of SOME source spaces `s₀`, `s₁`. -/
abbrev CobShapeT (Ψ : EvalCtx) (env : ValExpr) (ρ' : Finset VName) : Prop :=
    (∃ s₀ s₁ sv₀ sv₁, ValExpr.inferType env = .space (.tprod sv₀ sv₁)
              ∧ ValSpace.EvalS Ψ s₀ sv₀ ∧ ValSpace.EvalS Ψ s₁ sv₁)
  ∧ ValTyOk (ValExpr.inferType env)
  ∧ ValExpr.fv env ⊆ ρ'

/-- **`trans` arm** (`EvalBB.trans`). `mtm 0 0 sv sv env₁ (reshap env₀ (sv⊗sv))`;
    `inferType` = `.space (sv ⊗ t)` where `t` is `env₁`'s second factor. -/
theorem term_bb_trans_v2 {Ψ : EvalCtx} {ρ' : Finset VName}
    {env₀ env₁ : ValExpr} {sv : ValSpace} {s : Space}
    (hsv : ValSpace.EvalS Ψ s sv)
    (hsvval : Nonempty (ValSValidC sv))
    (hfvsv : ValSpace.fv sv ⊆ ρ')
    (ih₀ : CobShapeT Ψ env₀ ρ')
    (ih₁ : CobShapeT Ψ env₁ ρ') :
    CobShapeT Ψ (.mtm 0 0 sv sv env₁ (ValExpr.reshapBase env₀ (.tprod sv sv))) ρ' := by
  obtain ⟨_, _, hfvenv₀⟩ := ih₀
  obtain ⟨⟨_s₂, s₃, _r, t, hinf₁, _hr, ht⟩, hok₁, hfvenv₁⟩ := ih₁
  obtain ⟨vsv⟩ := hsvval
  have hinfer : ValExpr.inferType
      (ValExpr.mtm 0 0 sv sv env₁ (ValExpr.reshapBase env₀ (.tprod sv sv)))
        = .space (.tprod sv t) := by
    simp only [ValExpr.reshapBase, ValExpr.inferType, hinf₁]
  obtain ⟨_, ⟨hk₁⟩⟩ := hok₁
  rw [hinf₁] at hk₁
  have htval : ValSValidC t := (valSValidC_tprod_inv (valTValidC_space_inv hk₁)).2
  refine ⟨⟨s, s₃, sv, t, hinfer, hsv, ht⟩, ?_, ?_⟩
  · rw [hinfer]; exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod vsv htval)⟩⟩
  · simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
    repeat' apply Finset.union_subset
    all_goals first | exact hfvsv | exact hfvenv₀ | exact hfvenv₁

/-- **`tprod` arm** (`EvalBB.tprod`). `vkrn env₀ env₁`; the four factors realize the
    `.tprod` of the two operands' source spaces (`EvalS.tprod`). -/
theorem term_bb_tprod_v2 {Ψ : EvalCtx} {ρ' : Finset VName} {env₀ env₁ : ValExpr}
    (ih₀ : CobShapeT Ψ env₀ ρ') (ih₁ : CobShapeT Ψ env₁ ρ') :
    CobShapeT Ψ (.vkrn env₀ env₁) ρ' := by
  obtain ⟨⟨s₀, s₁, p, q, hinf₀, hp, hq⟩, hok₀, hfv₀⟩ := ih₀
  obtain ⟨⟨s₂, s₃, r, t, hinf₁, hr, ht⟩, hok₁, hfv₁⟩ := ih₁
  have hinfer : ValExpr.inferType (.vkrn env₀ env₁)
      = .space (.tprod (.tprod p r) (.tprod q t)) := by
    simp only [ValExpr.inferType, hinf₀, hinf₁]
  obtain ⟨_, ⟨hk₀⟩⟩ := hok₀; rw [hinf₀] at hk₀
  obtain ⟨hpv, hqv⟩ := valSValidC_tprod_inv (valTValidC_space_inv hk₀)
  obtain ⟨_, ⟨hk₁⟩⟩ := hok₁; rw [hinf₁] at hk₁
  obtain ⟨hrv, htv⟩ := valSValidC_tprod_inv (valTValidC_space_inv hk₁)
  refine ⟨⟨.tprod s₀ s₂, .tprod s₁ s₃, .tprod p r, .tprod q t, hinfer,
      ValSpace.EvalS.tprod hp hr, ValSpace.EvalS.tprod hq ht⟩, ?_, ?_⟩
  · rw [hinfer]
    exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod
      (ValSValidC.tprod hpv hrv) (ValSValidC.tprod hqv htv))⟩⟩
  · simp only [ValExpr.fv]; exact Finset.union_subset hfv₀ hfv₁

/-- **`dsum` arm** (`EvalBB.dsum`). `vblk env₀ env₁`; factors realize the `.dsum`
    of the operands' source spaces (`EvalS.dsum`). -/
theorem term_bb_dsum_v2 {Ψ : EvalCtx} {ρ' : Finset VName} {env₀ env₁ : ValExpr}
    (ih₀ : CobShapeT Ψ env₀ ρ') (ih₁ : CobShapeT Ψ env₁ ρ') :
    CobShapeT Ψ (.vblk env₀ env₁) ρ' := by
  obtain ⟨⟨s₀, s₁, p, q, hinf₀, hp, hq⟩, hok₀, hfv₀⟩ := ih₀
  obtain ⟨⟨s₂, s₃, r, t, hinf₁, hr, ht⟩, hok₁, hfv₁⟩ := ih₁
  have hinfer : ValExpr.inferType (.vblk env₀ env₁)
      = .space (.tprod (.dsum p r) (.dsum q t)) := by
    simp only [ValExpr.inferType, hinf₀, hinf₁]
  obtain ⟨_, ⟨hk₀⟩⟩ := hok₀; rw [hinf₀] at hk₀
  obtain ⟨hpv, hqv⟩ := valSValidC_tprod_inv (valTValidC_space_inv hk₀)
  obtain ⟨_, ⟨hk₁⟩⟩ := hok₁; rw [hinf₁] at hk₁
  obtain ⟨hrv, htv⟩ := valSValidC_tprod_inv (valTValidC_space_inv hk₁)
  refine ⟨⟨.dsum s₀ s₂, .dsum s₁ s₃, .dsum p r, .dsum q t, hinfer,
      ValSpace.EvalS.dsum hp hr, ValSpace.EvalS.dsum hq ht⟩, ?_, ?_⟩
  · rw [hinfer]
    exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod
      (ValSValidC.dsum hpv hrv) (ValSValidC.dsum hqv htv))⟩⟩
  · simp only [ValExpr.fv]; exact Finset.union_subset hfv₀ hfv₁

/-- **`proj_ker_coker` arm** (`EvalBB.proj_ker_coker`). The produced COB witness is
    the nested `mtm`
    `mtm 0 0 sv₀' sv₀' (reshap env₁ (sv₀'⊗sv')) (mtm 0 0 sv₀ sv₀ (reshap env₂ (sv₀⊗sv₀')) (reshap env₃ (sv⊗sv₀)))`.
    Computing `inferType` over the corrected edges (§9.18): the inner `mtm` has type
    `sv ⊗ sv₀'` (contracting `sv₀`), the outer has type `sv ⊗ sv'` (contracting `sv₀'`).
    Both factors `sv`, `sv'` are genuine realizations of the SAME ambient space `s`
    (`hsv`, `hsv'`), so `CobShapeT` holds with `s₀ = s₁ = s`. -/
theorem term_bb_proj_ker_coker_v2 {Ψ : EvalCtx} {ρ' : Finset VName}
    {env₁ env₂ env₃ : ValExpr} {sv₀ sv sv' sv₀' : ValSpace} {s : Space}
    (hsv  : ValSpace.EvalS Ψ s sv)
    (hsv' : ValSpace.EvalS Ψ s sv')
    (hsvval  : Nonempty (ValSValidC sv))
    (hsv'val : Nonempty (ValSValidC sv'))
    (hfvsv₀  : ValSpace.fv sv₀ ⊆ ρ') (hfvsv₀' : ValSpace.fv sv₀' ⊆ ρ')
    (hfvsv   : ValSpace.fv sv ⊆ ρ')  (hfvsv'  : ValSpace.fv sv' ⊆ ρ')
    (hfvenv₁ : ValExpr.fv env₁ ⊆ ρ') (hfvenv₂ : ValExpr.fv env₂ ⊆ ρ')
    (hfvenv₃ : ValExpr.fv env₃ ⊆ ρ') :
    CobShapeT Ψ
      (.mtm 0 0 sv₀' sv₀'
        (.reshap env₁ (.space (.tprod sv₀' sv')) (.space (.tprod sv₀' sv')))
        (.mtm 0 0 sv₀ sv₀ (ValExpr.reshapBase env₂ (.tprod sv₀ sv₀'))
          (.reshap env₃ (.space (.tprod sv sv₀)) (.space (.tprod sv sv₀))))) ρ' := by
  obtain ⟨vsv⟩ := hsvval
  obtain ⟨vsv'⟩ := hsv'val
  have hinfer : ValExpr.inferType
      (.mtm 0 0 sv₀' sv₀'
        (.reshap env₁ (.space (.tprod sv₀' sv')) (.space (.tprod sv₀' sv')))
        (.mtm 0 0 sv₀ sv₀ (ValExpr.reshapBase env₂ (.tprod sv₀ sv₀'))
          (.reshap env₃ (.space (.tprod sv sv₀)) (.space (.tprod sv sv₀)))))
        = .space (.tprod sv sv') := by
    simp only [ValExpr.reshapBase, ValExpr.inferType]
  refine ⟨⟨s, s, sv, sv', hinfer, hsv, hsv'⟩, ?_, ?_⟩
  · rw [hinfer]; exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod vsv vsv')⟩⟩
  · simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
    repeat' apply Finset.union_subset
    all_goals first
      | exact hfvsv₀ | exact hfvsv₀' | exact hfvsv | exact hfvsv'
      | exact hfvenv₁ | exact hfvenv₂ | exact hfvenv₃

/-- **`proj_img_coimg` arm** (`EvalBB.proj_img_coimg`). Codomain mirror of
    `proj_ker_coker`: the witness uses the codomain edges `sv₁`/`sv₁'` but its
    `inferType` is identically `sv ⊗ sv'` (both realizations of `s`). -/
theorem term_bb_proj_img_coimg_v2 {Ψ : EvalCtx} {ρ' : Finset VName}
    {env₁ env₂ env₃ : ValExpr} {sv₁ sv sv' sv₁' : ValSpace} {s : Space}
    (hsv  : ValSpace.EvalS Ψ s sv)
    (hsv' : ValSpace.EvalS Ψ s sv')
    (hsvval  : Nonempty (ValSValidC sv))
    (hsv'val : Nonempty (ValSValidC sv'))
    (hfvsv₁  : ValSpace.fv sv₁ ⊆ ρ') (hfvsv₁' : ValSpace.fv sv₁' ⊆ ρ')
    (hfvsv   : ValSpace.fv sv ⊆ ρ')  (hfvsv'  : ValSpace.fv sv' ⊆ ρ')
    (hfvenv₁ : ValExpr.fv env₁ ⊆ ρ') (hfvenv₂ : ValExpr.fv env₂ ⊆ ρ')
    (hfvenv₃ : ValExpr.fv env₃ ⊆ ρ') :
    CobShapeT Ψ
      (.mtm 0 0 sv₁' sv₁'
        (.reshap env₁ (.space (.tprod sv₁' sv')) (.space (.tprod sv₁' sv')))
        (.mtm 0 0 sv₁ sv₁ (ValExpr.reshapBase env₂ (.tprod sv₁ sv₁'))
          (.reshap env₃ (.space (.tprod sv sv₁)) (.space (.tprod sv sv₁))))) ρ' := by
  obtain ⟨vsv⟩ := hsvval
  obtain ⟨vsv'⟩ := hsv'val
  have hinfer : ValExpr.inferType
      (.mtm 0 0 sv₁' sv₁'
        (.reshap env₁ (.space (.tprod sv₁' sv')) (.space (.tprod sv₁' sv')))
        (.mtm 0 0 sv₁ sv₁ (ValExpr.reshapBase env₂ (.tprod sv₁ sv₁'))
          (.reshap env₃ (.space (.tprod sv sv₁)) (.space (.tprod sv sv₁)))))
        = .space (.tprod sv sv') := by
    simp only [ValExpr.reshapBase, ValExpr.inferType]
  refine ⟨⟨s, s, sv, sv', hinfer, hsv, hsv'⟩, ?_, ?_⟩
  · rw [hinfer]; exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod vsv vsv')⟩⟩
  · simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
    repeat' apply Finset.union_subset
    all_goals first
      | exact hfvsv₁ | exact hfvsv₁' | exact hfvsv | exact hfvsv'
      | exact hfvenv₁ | exact hfvenv₂ | exact hfvenv₃

/-- **`dual_std` arm** (`EvalBB.dual_std`). The produced witness is
    `.vtrans (.inv leev)`: `inv` flips the tprod (`sv₀⊗sv₁ ↦ sv₁⊗sv₀`) and `vtrans`
    flips it back, so `inferType (vtrans (inv leev)) = inferType leev`. CobShapeT is
    therefore inherited verbatim from the sub-derivation's CobShape on `leev`. -/
theorem term_bb_dual_std_v2 {Ψ : EvalCtx} {ρ' : Finset VName} {leev : ValExpr}
    (ih : CobShapeT Ψ leev ρ') :
    CobShapeT Ψ (.vtrans (.inv leev)) ρ' := by
  obtain ⟨⟨s₀, s₁, sv₀, sv₁, hinf, hes0, hes1⟩, hok, hfv⟩ := ih
  have hinfer : ValExpr.inferType (.vtrans (.inv leev)) = .space (.tprod sv₀ sv₁) := by
    simp only [ValExpr.inferType, hinf]
  obtain ⟨_, ⟨hokv⟩⟩ := hok; rw [hinf] at hokv
  obtain ⟨hsv0v, hsv1v⟩ := valSValidC_tprod_inv (valTValidC_space_inv hokv)
  refine ⟨⟨s₀, s₁, sv₀, sv₁, hinfer, hes0, hes1⟩, ?_, ?_⟩
  · rw [hinfer]; exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod hsv0v hsv1v)⟩⟩
  · simpa only [ValExpr.fv] using hfv

/-- **`image` arm** (`EvalBB.image`). The produced witness is the SAME `leev` as the
    sub-derivation `b₀ ⟷_{leev} b₀'`, so CobShapeT is inherited verbatim. -/
theorem term_bb_image_v2 {Ψ : EvalCtx} {ρ' : Finset VName} {leev : ValExpr}
    (ih : CobShapeT Ψ leev ρ') :
    CobShapeT Ψ leev ρ' := ih

end GLang
