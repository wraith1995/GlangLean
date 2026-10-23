import GLang.Proofs.Value.Typing.ValueInferenceFv

import GLang.Proofs.Value.Typing.ValueValidC
import GLang.Proofs.Preservation.EvalTKind

namespace GLang

/-- Context-free analogue of `ValTValid.kind_eq_structural`: the kind in a
    `ValTValidC` derivation is exactly the type's structural kind. -/
theorem ValTValidC.kind_eq_structural {τ : ValTy} {k : ValKind}
    (h : ValTValidC τ k) : k = τ.structuralKind :=
  match h with
  | .space _ => rfl
  | .piTy L h₀ h₁ => by
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset L
      have hc := ValTValidC.kind_eq_structural (h₁ y hy)
      rw [ValTy.openVar, ValTy.structuralKind_openRec] at hc
      simp only [ValTy.structuralKind, ValTValidC.kind_eq_structural h₀, hc]
  termination_by ValTy.kindSize τ
  decreasing_by
    all_goals simp only [ValTy.kindSize_piTy, ValTy.openVar, ValTy.kindSize_openRec]; omega

/-- `ReshapEq` from two valid types whose structural kinds agree. -/
theorem ReshapEq.of_valid_eqStructKind {τ τ' : ValTy} {k k' : ValKind}
    (h : ValTValidC τ k) (h' : ValTValidC τ' k')
    (hk : τ.structuralKind = τ'.structuralKind) : ReshapEq τ τ' := by
  have e : k = k' := by
    rw [ValTValidC.kind_eq_structural h, ValTValidC.kind_eq_structural h', hk]
  exact ⟨k, ⟨h⟩, ⟨by rw [e]; exact h'⟩⟩

/-- **The gen-4 bridge discharge.** Two `ValTValidC` realizations of the SAME
    source type `τ` are `ReshapEq` — no FFS witness equality needed. -/
theorem reshapEq_of_evalT {Ψ : EvalCtx} {τ : Ty} {τv τv' : ValTy} {k k' : ValKind}
    (hev : ValTy.EvalT Ψ τ τv) (hev' : ValTy.EvalT Ψ τ τv')
    (h : ValTValidC τv k) (h' : ValTValidC τv' k') : ReshapEq τv τv' :=
  ReshapEq.of_valid_eqStructKind h h'
    (by rw [hev.structuralKind_eq_sourceKind, hev'.structuralKind_eq_sourceKind])

/-- Self-`ReshapEq` (the non-FFS arms, where `inferType v` IS the realization):
    a valid type is reshape-equivalent to itself. -/
theorem ReshapEq.refl {τ : ValTy} {k : ValKind} (h : ValTValidC τ k) :
    ReshapEq τ τ := ⟨k, ⟨h⟩, ⟨h⟩⟩

/-- The canonical base-reshape constructor commutes definitionally with value
substitution. -/
@[simp] theorem ValExpr.subst_reshapBase (x : VName) (u e : ValExpr)
    (target : ValSpace) :
    ValExpr.subst x u (ValExpr.reshapBase e target) =
      ValExpr.reshapBase (ValExpr.subst x u e) (ValSpace.subst x u target) := rfl

/-- `spaceOf` only drops structure (it returns `.empty` on a `.piTy`), so its free
    variables are contained in the type's. Unconditional. -/
theorem ValSpace.fv_spaceOf_subset :
    (τ : ValTy) → ValSpace.fv (ValTy.spaceOf τ) ⊆ ValTy.fv τ
  | .space _    => Finset.Subset.refl _
  | .piTy _ _   => Finset.empty_subset _

/-- A `.space`-type realization reveals the value space. -/
theorem evalT_space_inv {Ψ : EvalCtx} {s : Space} {τv : ValTy}
    (h : ValTy.EvalT Ψ (.space s) τv) : ∃ sv, ValSpace.EvalS Ψ s sv ∧ τv = .space sv := by
  cases h with | space hsv => exact ⟨_, hsv, rfl⟩

/-- `ℝ` realizes only to `ℝ`. -/
theorem evalS_real_eq {Ψ : EvalCtx} {sv : ValSpace}
    (h : ValSpace.EvalS Ψ .real sv) : sv = .real := by
  cases h with | real => rfl

/-- A `.tprod`-space realization is itself a `.tprod`. -/
theorem evalS_tprod_inv {Ψ : EvalCtx} {a b : Space} {sv : ValSpace}
    (h : ValSpace.EvalS Ψ (.tprod a b) sv) : ∃ sva svb, sv = .tprod sva svb := by
  cases h with | tprod _ _ => exact ⟨_, _, rfl⟩

/-- Context-free `ValTValid`-of-`.space` inversion. -/
def valTValidC_space_inv {s : ValSpace} {k : ValKind}
    (h : ValTValidC (.space s) k) : ValSValidC s :=
  match h with | .space hsv => hsv

/-- Context-free `ValSValid`-of-`.tprod` inversion. -/
def valSValidC_tprod_inv {a b : ValSpace}
    (h : ValSValidC (.tprod a b)) : ValSValidC a × ValSValidC b :=
  match h with | .tprod ha hb => ⟨ha, hb⟩

/-- `ReshapEq τ τ'` gives `τ` is a valid type. -/
theorem ReshapEq.fst_ok {τ τ' : ValTy} (h : ReshapEq τ τ') : ValTyOk τ := by
  obtain ⟨k, ⟨hk⟩, _⟩ := h; exact ⟨k, ⟨hk⟩⟩

/-- `ReshapEq τ (.space sv)` gives the space `sv` is valid. -/
theorem ReshapEq.snd_space {τ : ValTy} {sv : ValSpace}
    (h : ReshapEq τ (.space sv)) : Nonempty (ValSValidC sv) := by
  obtain ⟨_, _, ⟨hk⟩⟩ := h; exact ⟨valTValidC_space_inv hk⟩

/-- A `.base`-kind valid type IS a valid space. -/
theorem valTValidC_base_space {τ : ValTy} (h : ValTValidC τ .base) :
    ∃ s, τ = .space s ∧ Nonempty (ValSValidC s) := by
  cases h with | space hsv => exact ⟨_, rfl, ⟨hsv⟩⟩

/-- `ReshapEq τ (.space sv)`: the LHS is a `.space` of a valid space. -/
theorem ReshapEq.fst_base_space {τ : ValTy} {sv : ValSpace}
    (h : ReshapEq τ (.space sv)) : ∃ s, τ = .space s ∧ Nonempty (ValSValidC s) := by
  obtain ⟨k, ⟨hk⟩, ⟨hk'⟩⟩ := h
  -- the RHS `.space sv` forces k = .base, so the LHS is also `.base`.
  cases hk' with | space _ => exact valTValidC_base_space hk

theorem Basis.EvalBB.sof_eq {Ψ : EvalCtx} {b₀ b₁ : Basis} {env : ValExpr}
    (h : Basis.EvalBB Ψ b₀ env b₁) : Basis.sof b₀ = Basis.sof b₁ := by
  refine Basis.EvalBB.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ bsrc _ btgt _ => Basis.sof bsrc = Basis.sof btgt)
    (motive_4 := fun _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    ?bInv ?bTrans ?bTprod ?bDsum ?_ ?bImage ?_ ?_ ?_ ?bTermsRref ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    h
  case bInv => intro _ _ _ _ _ ih; exact ih.symm
  case bTrans => intro _ _ _ _ _ _ _ _ _ _ ih₀ ih₁ _; exact ih₀.trans ih₁
  case bTprod => intro _ _ _ _ _ _ _ _ _ ih₀ ih₁; simp only [Basis.sof, ih₀, ih₁]
  case bDsum => intro _ _ _ _ _ _ _ _ _ ih₀ ih₁; simp only [Basis.sof, ih₀, ih₁]
  case bImage => intro _ _ _ _ _ _ ih; simp only [Basis.sof, ih]
  case bTermsRref =>
    -- `sof (.terms (sof b') (e::es) b') = sof b'`; the `hbb` sub-IH closes.
    intros; rename_i ih_bb _ih_ch _ih_sv
    simpa only [Basis.sof] using ih_bb
  all_goals first
    | (intros; exact trivial)
    | (intros; simp [Basis.sof, Basis.tof, Basis.std, Basis.stdSpace, Basis.sof_stdSpace])

/-- **`cob` arm (change-of-basis during evaluation).** The produced value is a
    `ttv` whose type is `.space sv` (`sv` from the part-3 realization of `sof b₀`,
    pinned by the rule's reshaps). Only the `fv ⊆ ρ` parts of the part-1/part-2
    IHs are needed (the `ttv` type is determined by `sv`). -/
theorem term_cob_v2 {Ψ : EvalCtx} {ρ' : Finset VName} {b₀ : Basis} {env₀ v : ValExpr}
    {sv : ValSpace}
    (htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
    (hes : ValSpace.EvalS Ψ (Basis.sof b₀) sv)
    (hsvval : Nonempty (ValSValidC sv))
    (hfvsv : ValSpace.fv sv ⊆ ρ')
    (hfvenv : ValExpr.fv env₀ ⊆ ρ')
    (hfvv : ValExpr.fv v ⊆ ρ') :
    (∃ τv, ValTy.EvalT Ψ (Basis.tof b₀) τv
          ∧ ReshapEq (ValExpr.inferType
              (.ttv sv (ValExpr.reshapBase env₀ (.tprod sv sv))
                (ValExpr.reshapBase v sv))) τv)
    ∧ ValTyOk (ValExpr.inferType
        (.ttv sv (ValExpr.reshapBase env₀ (.tprod sv sv))
          (ValExpr.reshapBase v sv)))
    ∧ (ValTy.fv (ValExpr.inferType
          (.ttv sv (ValExpr.reshapBase env₀ (.tprod sv sv))
            (ValExpr.reshapBase v sv)))
        ∪ ValExpr.fv (.ttv sv (ValExpr.reshapBase env₀ (.tprod sv sv))
          (ValExpr.reshapBase v sv))
        ⊆ ρ') := by
  obtain ⟨vsv⟩ := hsvval
  have hinfer : ValExpr.inferType
      (.ttv sv (ValExpr.reshapBase env₀ (.tprod sv sv))
        (ValExpr.reshapBase v sv))
        = .space sv := rfl
  refine ⟨⟨.space sv, ?_, ?_⟩, ?_, ?_⟩
  · rw [htof₀]; exact ValTy.EvalT.space hes
  · rw [hinfer]; exact ReshapEq.refl (ValTValidC.space vsv)
  · rw [hinfer]; exact ⟨.base, ⟨ValTValidC.space vsv⟩⟩
  · rw [hinfer]
    simp only [ValTy.fv, ValSpace.fv, ValExpr.fv]
    refine Finset.union_subset hfvsv ?_
    repeat' apply Finset.union_subset
    all_goals first | exact hfvsv | exact hfvenv | exact hfvv

/-! ## Operational regularity — `EvalS → ValSValidC` / `EvalT → ValTValidC`.

A realized value space / value type is VALID — purely operationally, with NO source
typing and NO `OpStep`/`ValExprValidC` regularity. The key is that `ValSValidC.ffs`
requires only the witness's `inferType` SHAPE (`= .space (.tprod …)`), which is
structural (`reshap`'s `inferType` is its annotation), not the witness's validity. So
the FFS arms recurse only on the witness-space `EvalS` (`hsvb`), never on the embedded
term's `OpStep`. The `EvalS`/`EvalT` recursion is closed (does not touch `EvalBB`/
`OpStep`), so it independently supplies operational realization regularity.

`ValSValidC`/`ValTValidC` are `Type`-valued; the eval judgments are `Prop`, so we
eliminate into `Nonempty (…)` (a `Prop`) and rewrap via `.some`/`Classical`. -/

/-- A realized value space is valid (operational regularity). -/
theorem evalS_valid {Ψ : EvalCtx} {s : Space} {sv : ValSpace}
    (h : ValSpace.EvalS Ψ s sv) : Nonempty (ValSValidC sv) := by
  refine ValSpace.EvalS.rec
    (motive_1 := fun _ _ sv' _ => Nonempty (ValSValidC sv'))
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    ?eReal ?eEmpty ?eDual ?eKer ?eCoker ?eImg ?eCoimg ?eTprod ?eDsum
    ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    h
  case eReal => exact ⟨.real⟩
  case eEmpty => exact ⟨.empty⟩
  case eDual => intro _ _ _ _ ih; exact ih
  case eKer =>
    intro _ _ _ _ b leev svb _he hb _hcompat _hsvb _ih_he ih_svb
    obtain ⟨sva, svb1, rfl⟩ := evalS_tprod_inv (hb ▸ _hsvb)
    obtain ⟨hsva, hsvb1⟩ := valSValidC_tprod_inv ih_svb.some
    exact ⟨ValSValidC.ffs hsva hsvb1 rfl⟩
  case eCoker =>
    intro _ _ _ _ b leev svb _he hb _hcompat _hsvb _ih_he ih_svb
    obtain ⟨sva, svb1, rfl⟩ := evalS_tprod_inv (hb ▸ _hsvb)
    obtain ⟨hsva, hsvb1⟩ := valSValidC_tprod_inv ih_svb.some
    exact ⟨ValSValidC.ffs hsva hsvb1 rfl⟩
  case eImg =>
    intro _ _ _ _ b leev svb _he hb _hcompat _hsvb _ih_he ih_svb
    obtain ⟨sva, svb1, rfl⟩ := evalS_tprod_inv (hb ▸ _hsvb)
    obtain ⟨hsva, hsvb1⟩ := valSValidC_tprod_inv ih_svb.some
    exact ⟨ValSValidC.ffs hsva hsvb1 rfl⟩
  case eCoimg =>
    intro _ _ _ _ b leev svb _he hb _hcompat _hsvb _ih_he ih_svb
    obtain ⟨sva, svb1, rfl⟩ := evalS_tprod_inv (hb ▸ _hsvb)
    obtain ⟨hsva, hsvb1⟩ := valSValidC_tprod_inv ih_svb.some
    exact ⟨ValSValidC.ffs hsva hsvb1 rfl⟩
  case eTprod =>
    intro _ _ _ _ _ _ _ ih₀ ih₁; exact ⟨.tprod ih₀.some ih₁.some⟩
  case eDsum =>
    intro _ _ _ _ _ _ _ ih₀ ih₁; exact ⟨.dsum ih₀.some ih₁.some⟩
  all_goals (intros; exact trivial)

/-- A realized value type is valid at its structural kind (operational regularity);
    the `.space` arm reuses `evalS_valid`, the `.piTy` arm assembles the cofinite
    codomain at the `openRec`-invariant uniform kind `τv₁.structuralKind`. -/
theorem evalT_valid {Ψ : EvalCtx} {τ : Ty} {τv : ValTy}
    (h : ValTy.EvalT Ψ τ τv) : Nonempty (ValTValidC τv τv.structuralKind) := by
  refine ValTy.EvalT.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ τv' _ => Nonempty (ValTValidC τv' τv'.structuralKind))
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?tSpace ?tPiTy
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    h
  case tSpace =>
    intro _ _ _ hes _
    exact ⟨ValTValidC.space (evalS_valid hes).some⟩
  case tPiTy =>
    intro _ _ _ _ τv₀ τv₁ _ _ L _ ih₀ ih₁
    refine ⟨ValTValidC.piTy L ih₀.some (fun y hy => ?_)⟩
    have hc := (ih₁ y hy).some
    simpa only [ValTy.openVar, ValTy.structuralKind_openRec] using hc
  all_goals (intros; exact trivial)

/-- `inferSpace`'s output draws its free names from the value's own: annotation
    arms project sub-fvs, match fallbacks are closed (`.empty`/`.real`), and the
    `gsvd*`/`svds` ffs factors embed the operand itself. -/
theorem ValExpr.fv_inferSpace_subset :
    ∀ v : ValExpr, ValSpace.fv (ValExpr.inferSpace v) ⊆ ValExpr.fv v
  | .zero _ => Finset.Subset.refl _
  | .rlit _ => Finset.Subset.refl _
  | .scale _ e₁ => (ValExpr.fv_inferSpace_subset e₁).trans Finset.subset_union_right
  | .vadd s _ _ => by
      simp only [ValExpr.inferSpace, ValExpr.fv]
      exact Finset.subset_union_left.trans Finset.subset_union_left
  | .dsumE e₀ e₁ => by
      simp only [ValExpr.inferSpace, ValExpr.fv, ValSpace.fv]
      exact Finset.union_subset
        ((ValExpr.fv_inferSpace_subset e₀).trans Finset.subset_union_left)
        ((ValExpr.fv_inferSpace_subset e₁).trans Finset.subset_union_right)
  | .tprodE e₀ e₁ => by
      simp only [ValExpr.inferSpace, ValExpr.fv, ValSpace.fv]
      exact Finset.union_subset
        ((ValExpr.fv_inferSpace_subset e₀).trans Finset.subset_union_left)
        ((ValExpr.fv_inferSpace_subset e₁).trans Finset.subset_union_right)
  | .delta _ _ => Finset.Subset.refl _
  | .idelta s => by
      simp only [ValExpr.inferSpace, ValExpr.fv, ValSpace.fv]
      exact Finset.union_subset (Finset.Subset.refl _) (Finset.Subset.refl _)
  | .vsum _ [] => Finset.empty_subset _
  | .vsum s (e :: es) => by
      simp only [ValExpr.inferSpace, ValExpr.fv, ValExpr.fvList]
      exact (ValExpr.fv_inferSpace_subset e).trans
        (Finset.subset_union_left.trans Finset.subset_union_right)
  | .vlam _ _ _ => Finset.empty_subset _
  | .bvar _ => Finset.empty_subset _
  | .var _ τ => (ValSpace.fv_spaceOf_subset τ).trans (Finset.subset_insert _ _)
  | .appV f a => (ValSpace.fv_spaceOf_subset _).trans
      (ValExpr.fv_inferType_subset (.appV f a))
  | .reshap _ τ _ => (ValSpace.fv_spaceOf_subset τ).trans
      (Finset.subset_union_right.trans Finset.subset_union_left)
  | .ttv s e₀ e₁ => by
      cases h : ValExpr.inferSpace e₀ with
      | tprod a b =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have hb : w ∈ ValSpace.fv b → w ∈ ValExpr.fv e₀ := fun hm =>
            ValExpr.fv_inferSpace_subset e₀ (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [Finset.mem_union] at hw ⊢
          tauto
      | empty => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | real => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | dsum _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | ffs _ _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
  | .mtm _ _ _ _ e₀ e₁ => by
      cases h₀ : ValExpr.inferSpace e₀ <;> cases h₁ : ValExpr.inferSpace e₁ <;>
        simp only [ValExpr.inferSpace, h₀, h₁, ValSpace.fv, ValExpr.fv] <;>
        try exact Finset.empty_subset _
      rename_i a b c d
      intro w hw
      have hb : w ∈ ValSpace.fv b → w ∈ ValExpr.fv e₀ := fun hm =>
        ValExpr.fv_inferSpace_subset e₀ (by rw [h₀]; exact Finset.mem_union_right _ hm)
      have hc : w ∈ ValSpace.fv c → w ∈ ValExpr.fv e₁ := fun hm =>
        ValExpr.fv_inferSpace_subset e₁ (by rw [h₁]; exact Finset.mem_union_left _ hm)
      simp only [Finset.mem_union] at hw ⊢
      tauto
  | .vkrn e₀ e₁ => by
      cases h₀ : ValExpr.inferSpace e₀ <;> cases h₁ : ValExpr.inferSpace e₁ <;>
        simp only [ValExpr.inferSpace, h₀, h₁, ValSpace.fv, ValExpr.fv] <;>
        try exact Finset.empty_subset _
      rename_i a b c d
      intro w hw
      have ha : w ∈ ValSpace.fv a → w ∈ ValExpr.fv e₀ := fun hm =>
        ValExpr.fv_inferSpace_subset e₀ (by rw [h₀]; exact Finset.mem_union_left _ hm)
      have hb : w ∈ ValSpace.fv b → w ∈ ValExpr.fv e₀ := fun hm =>
        ValExpr.fv_inferSpace_subset e₀ (by rw [h₀]; exact Finset.mem_union_right _ hm)
      have hc : w ∈ ValSpace.fv c → w ∈ ValExpr.fv e₁ := fun hm =>
        ValExpr.fv_inferSpace_subset e₁ (by rw [h₁]; exact Finset.mem_union_left _ hm)
      have hd : w ∈ ValSpace.fv d → w ∈ ValExpr.fv e₁ := fun hm =>
        ValExpr.fv_inferSpace_subset e₁ (by rw [h₁]; exact Finset.mem_union_right _ hm)
      simp only [Finset.mem_union] at hw ⊢
      tauto
  | .vblk e₀ e₁ => by
      cases h₀ : ValExpr.inferSpace e₀ <;> cases h₁ : ValExpr.inferSpace e₁ <;>
        simp only [ValExpr.inferSpace, h₀, h₁, ValSpace.fv, ValExpr.fv] <;>
        try exact Finset.empty_subset _
      rename_i a b c d
      intro w hw
      have ha : w ∈ ValSpace.fv a → w ∈ ValExpr.fv e₀ := fun hm =>
        ValExpr.fv_inferSpace_subset e₀ (by rw [h₀]; exact Finset.mem_union_left _ hm)
      have hb : w ∈ ValSpace.fv b → w ∈ ValExpr.fv e₀ := fun hm =>
        ValExpr.fv_inferSpace_subset e₀ (by rw [h₀]; exact Finset.mem_union_right _ hm)
      have hc : w ∈ ValSpace.fv c → w ∈ ValExpr.fv e₁ := fun hm =>
        ValExpr.fv_inferSpace_subset e₁ (by rw [h₁]; exact Finset.mem_union_left _ hm)
      have hd : w ∈ ValSpace.fv d → w ∈ ValExpr.fv e₁ := fun hm =>
        ValExpr.fv_inferSpace_subset e₁ (by rw [h₁]; exact Finset.mem_union_right _ hm)
      simp only [Finset.mem_union] at hw ⊢
      tauto
  | .vtrans e => by
      cases h : ValExpr.inferSpace e with
      | tprod a b =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have ha : w ∈ ValSpace.fv a → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_left _ hm)
          have hb : w ∈ ValSpace.fv b → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw
          tauto
      | empty => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | real => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | dsum _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | ffs _ _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
  | .gsvdS e a b => by
      simp only [ValExpr.inferSpace, ValSpace.fv, ValExpr.fv]
      intro w hw
      have he : w ∈ ValSpace.fv (ValExpr.inferSpace e) → w ∈ ValExpr.fv e :=
        fun hm => ValExpr.fv_inferSpace_subset e hm
      simp only [Finset.mem_union] at hw ⊢
      tauto
  | .gsvdU e a b => by
      cases h : ValExpr.inferSpace e with
      | tprod c d =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have hc : w ∈ ValSpace.fv c → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_left _ hm)
          have hd : w ∈ ValSpace.fv d → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw ⊢
          tauto
      | empty => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | real => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | dsum _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | ffs _ _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
  | .gsvdUI e a b => by
      cases h : ValExpr.inferSpace e with
      | tprod c d =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have hc : w ∈ ValSpace.fv c → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_left _ hm)
          have hd : w ∈ ValSpace.fv d → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw ⊢
          tauto
      | empty => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | real => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | dsum _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | ffs _ _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
  | .gsvdV e a b => by
      cases h : ValExpr.inferSpace e with
      | tprod c d =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have hc : w ∈ ValSpace.fv c → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_left _ hm)
          have hd : w ∈ ValSpace.fv d → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw ⊢
          tauto
      | empty => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | real => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | dsum _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | ffs _ _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
  | .gsvdVI e a b => by
      cases h : ValExpr.inferSpace e with
      | tprod c d =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have hc : w ∈ ValSpace.fv c → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_left _ hm)
          have hd : w ∈ ValSpace.fv d → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw ⊢
          tauto
      | empty => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | real => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | dsum _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | ffs _ _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
  | .pinv e => by
      cases h : ValExpr.inferSpace e with
      | tprod a b =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have ha : w ∈ ValSpace.fv a → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_left _ hm)
          have hb : w ∈ ValSpace.fv b → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw
          tauto
      | empty =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have he : w ∈ ValSpace.fv ValSpace.empty → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw
          tauto
      | real =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have he : w ∈ ValSpace.fv ValSpace.real → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw
          tauto
      | dsum s₀ s₁ =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have he : w ∈ ValSpace.fv (.dsum s₀ s₁) → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw he
          tauto
      | ffs p sp wt =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have he : w ∈ ValSpace.fv (.ffs p sp wt) → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw he
          tauto
  | .gpinv e a b => by
      cases h : ValExpr.inferSpace e with
      | tprod c d =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have hc : w ∈ ValSpace.fv c → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_left _ hm)
          have hd : w ∈ ValSpace.fv d → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw ⊢
          tauto
      | empty => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | real => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | dsum _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | ffs _ _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
  | .rrefRep e₀ e₁ => by
      cases h : ValExpr.inferSpace e₁ with
      | tprod a b =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have ha : w ∈ ValSpace.fv a → w ∈ ValExpr.fv e₁ := fun hm =>
            ValExpr.fv_inferSpace_subset e₁ (by rw [h]; exact Finset.mem_union_left _ hm)
          have hb : w ∈ ValSpace.fv b → w ∈ ValExpr.fv e₁ := fun hm =>
            ValExpr.fv_inferSpace_subset e₁ (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw ⊢
          tauto
      | empty => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | real => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | dsum _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
      | ffs _ _ _ => simp only [ValExpr.inferSpace, h, ValSpace.fv]; exact Finset.empty_subset _
  | .inv e => by
      cases h : ValExpr.inferSpace e with
      | tprod a b =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have ha : w ∈ ValSpace.fv a → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_left _ hm)
          have hb : w ∈ ValSpace.fv b → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact Finset.mem_union_right _ hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw
          tauto
      | empty =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have he : w ∈ ValSpace.fv ValSpace.empty → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw
          tauto
      | real =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have he : w ∈ ValSpace.fv ValSpace.real → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw
          tauto
      | dsum s₀ s₁ =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have he : w ∈ ValSpace.fv (.dsum s₀ s₁) → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw he
          tauto
      | ffs p sp wt =>
          simp only [ValExpr.inferSpace, h, ValExpr.fv]
          intro w hw
          have he : w ∈ ValSpace.fv (.ffs p sp wt) → w ∈ ValExpr.fv e := fun hm =>
            ValExpr.fv_inferSpace_subset e (by rw [h]; exact hm)
          simp only [ValSpace.fv, Finset.mem_union] at hw he
          tauto
  | .svds e => by
      simp only [ValExpr.inferSpace, ValSpace.fv, ValExpr.fv]
      intro w hw
      have he : w ∈ ValSpace.fv (ValExpr.inferSpace e) → w ∈ ValExpr.fv e :=
        fun hm => ValExpr.fv_inferSpace_subset e hm
      simp only [Finset.mem_union] at hw ⊢
      tauto

/-- `.pinv`'s structural type, given the operand's `inferType` is a valid `.space`:
    valid at `.base`, fvs ⊆ the operand type's (covers all `match` branches of
    `inferType (.pinv v)` — tprod swap and the degenerate `ℝ⊗s`). -/
theorem pinv_inferType_valid {v : ValExpr} {sv : ValSpace}
    (hshape : ValExpr.inferType v = .space sv) (hval : ValSValidC sv) :
    Nonempty (ValTValidC (ValExpr.inferType (.pinv v)) .base)
    ∧ ValTy.fv (ValExpr.inferType (.pinv v)) ⊆ ValTy.fv (ValExpr.inferType v) := by
  cases sv with
  | tprod a b =>
      obtain ⟨ha, hb⟩ := valSValidC_tprod_inv hval
      refine ⟨⟨?_⟩, ?_⟩
      · simp only [ValExpr.inferType, hshape]
        exact .space (.tprod hb ha)
      · simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]
        exact Finset.union_subset Finset.subset_union_right Finset.subset_union_left
  | empty =>
      exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space (.tprod .real hval)⟩,
        by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | real =>
      exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space (.tprod .real hval)⟩,
        by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | dsum s₀ s₁ =>
      exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space (.tprod .real hval)⟩,
        by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | ffs p sp w =>
      exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space (.tprod .real hval)⟩,
        by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩

/-! ### GSVD-factor values (`gsvdU`/`gsvdUI`/`gsvdV`/`gsvdVI`, the `embed_*` arms).
Same skeleton: operand's inferType a valid `.space` ⟹ the factor value's
inferType is base-valid; its fvs are bounded by the operand TYPE's ∪ the operand
VALUE's (the ffs component carries the operand itself). -/

/-- `.gsvdU`'s structural type. -/
theorem gsvdU_inferType_valid {v env₀ env₁ : ValExpr} {sv : ValSpace}
    (hshape : ValExpr.inferType v = .space sv) (hval : ValSValidC sv) :
    Nonempty (ValTValidC (ValExpr.inferType (.gsvdU v env₀ env₁)) .base)
    ∧ ValTy.fv (ValExpr.inferType (.gsvdU v env₀ env₁))
        ⊆ ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v := by
  cases sv with
  | tprod a b =>
      obtain ⟨ha, hb⟩ := valSValidC_tprod_inv hval
      refine ⟨⟨?_⟩, ?_⟩
      · simp only [ValExpr.inferType, hshape]
        exact .space (.tprod ha (.ffs ha hb hshape))
      · simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]
        intro w hw; simp only [Finset.mem_union] at hw ⊢; tauto
  | empty => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | real => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | dsum s₀ s₁ => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | ffs p sp w => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩

/-- `.gsvdUI`'s structural type. -/
theorem gsvdUI_inferType_valid {v env₀ env₁ : ValExpr} {sv : ValSpace}
    (hshape : ValExpr.inferType v = .space sv) (hval : ValSValidC sv) :
    Nonempty (ValTValidC (ValExpr.inferType (.gsvdUI v env₀ env₁)) .base)
    ∧ ValTy.fv (ValExpr.inferType (.gsvdUI v env₀ env₁))
        ⊆ ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v := by
  cases sv with
  | tprod a b =>
      obtain ⟨ha, hb⟩ := valSValidC_tprod_inv hval
      refine ⟨⟨?_⟩, ?_⟩
      · simp only [ValExpr.inferType, hshape]
        exact .space (.tprod ha (.ffs ha hb hshape))
      · simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]
        intro w hw; simp only [Finset.mem_union] at hw ⊢; tauto
  | empty => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | real => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | dsum s₀ s₁ => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | ffs p sp w => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩

/-- `.gsvdV`'s structural type (E5: left factor = codomain factor `b`). -/
theorem gsvdV_inferType_valid {v env₀ env₁ : ValExpr} {sv : ValSpace}
    (hshape : ValExpr.inferType v = .space sv) (hval : ValSValidC sv) :
    Nonempty (ValTValidC (ValExpr.inferType (.gsvdV v env₀ env₁)) .base)
    ∧ ValTy.fv (ValExpr.inferType (.gsvdV v env₀ env₁))
        ⊆ ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v := by
  cases sv with
  | tprod a b =>
      obtain ⟨ha, hb⟩ := valSValidC_tprod_inv hval
      refine ⟨⟨?_⟩, ?_⟩
      · simp only [ValExpr.inferType, hshape]
        exact .space (.tprod hb (.ffs ha hb hshape))
      · simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]
        intro w hw; simp only [Finset.mem_union] at hw ⊢; tauto
  | empty => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | real => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | dsum s₀ s₁ => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | ffs p sp w => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩

/-- `.gsvdVI`'s structural type (E5: left factor = codomain factor `b`). -/
theorem gsvdVI_inferType_valid {v env₀ env₁ : ValExpr} {sv : ValSpace}
    (hshape : ValExpr.inferType v = .space sv) (hval : ValSValidC sv) :
    Nonempty (ValTValidC (ValExpr.inferType (.gsvdVI v env₀ env₁)) .base)
    ∧ ValTy.fv (ValExpr.inferType (.gsvdVI v env₀ env₁))
        ⊆ ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v := by
  cases sv with
  | tprod a b =>
      obtain ⟨ha, hb⟩ := valSValidC_tprod_inv hval
      refine ⟨⟨?_⟩, ?_⟩
      · simp only [ValExpr.inferType, hshape]
        exact .space (.tprod hb (.ffs ha hb hshape))
      · simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]
        intro w hw; simp only [Finset.mem_union] at hw ⊢; tauto
  | empty => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | real => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | dsum s₀ s₁ => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | ffs p sp w => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩

/-- `.vtrans`'s structural type (the `embed_*` arms, erratum E2: the GSVD block is
    transposed to the conclusion's subspace-major layout): a base-valid operand type
    ⟹ the transpose's inferType (tprod swap; fallback `.space .empty`) is base-valid
    with fvs bounded by the operand type's. -/
theorem vtrans_inferType_valid {x : ValExpr}
    (hx : Nonempty (ValTValidC (ValExpr.inferType x) .base)) :
    Nonempty (ValTValidC (ValExpr.inferType (.vtrans x)) .base)
    ∧ ValTy.fv (ValExpr.inferType (.vtrans x)) ⊆ ValTy.fv (ValExpr.inferType x) := by
  cases h : ValExpr.inferType x with
  | piTy τa τb =>
      exact ⟨⟨by simp only [ValExpr.inferType, h]; exact .space .empty⟩,
        by simp only [ValExpr.inferType, h, ValTy.fv, ValSpace.fv]; simp⟩
  | space sv =>
      rw [h] at hx
      obtain ⟨hx⟩ := hx
      cases sv with
      | tprod a b =>
          obtain ⟨ha, hb⟩ := valSValidC_tprod_inv (valTValidC_space_inv hx)
          refine ⟨⟨?_⟩, ?_⟩
          · simp only [ValExpr.inferType, h]
            exact .space (.tprod hb ha)
          · simp only [ValExpr.inferType, h, ValTy.fv, ValSpace.fv]
            exact Finset.union_subset Finset.subset_union_right Finset.subset_union_left
      | empty => exact ⟨⟨by simp only [ValExpr.inferType, h]; exact .space .empty⟩,
          by simp only [ValExpr.inferType, h, ValTy.fv, ValSpace.fv]; simp⟩
      | real => exact ⟨⟨by simp only [ValExpr.inferType, h]; exact .space .empty⟩,
          by simp only [ValExpr.inferType, h, ValTy.fv, ValSpace.fv]; simp⟩
      | dsum s₀ s₁ => exact ⟨⟨by simp only [ValExpr.inferType, h]; exact .space .empty⟩,
          by simp only [ValExpr.inferType, h, ValTy.fv, ValSpace.fv]; simp⟩
      | ffs p sp w => exact ⟨⟨by simp only [ValExpr.inferType, h]; exact .space .empty⟩,
          by simp only [ValExpr.inferType, h, ValTy.fv, ValSpace.fv]; simp⟩

/-- `.ttv`'s structural type (the linear-application arms): the matrix operand's
    inferType a valid `.space` ⟹ the contraction's inferType (`s_out` of a tprod;
    fallback ℝ) is base-valid with fvs bounded by the matrix type's. -/
theorem ttv_inferType_valid {sv : ValSpace} {e₀ e₁ : ValExpr} {svw : ValSpace}
    (hshape : ValExpr.inferType e₀ = .space svw) (hval : ValSValidC svw) :
    Nonempty (ValTValidC (ValExpr.inferType (.ttv sv e₀ e₁)) .base)
    ∧ ValTy.fv (ValExpr.inferType (.ttv sv e₀ e₁)) ⊆ ValTy.fv (ValExpr.inferType e₀) := by
  cases svw with
  | tprod a b =>
      obtain ⟨_, hb⟩ := valSValidC_tprod_inv hval
      refine ⟨⟨?_⟩, ?_⟩
      · simp only [ValExpr.inferType, hshape]
        exact .space hb
      · simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]
        exact Finset.subset_union_right
  | empty => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .real⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | real => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .real⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | dsum s₀ s₁ => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .real⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | ffs p sp w => exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .real⟩,
      by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩

/-- `.gpinv`'s structural type (same shape as `pinv_inferType_valid`; the
    non-tprod fallback is `.space .empty`). -/
theorem gpinv_inferType_valid {v env₀ env₁ : ValExpr} {sv : ValSpace}
    (hshape : ValExpr.inferType v = .space sv) (hval : ValSValidC sv) :
    Nonempty (ValTValidC (ValExpr.inferType (.gpinv v env₀ env₁)) .base)
    ∧ ValTy.fv (ValExpr.inferType (.gpinv v env₀ env₁)) ⊆ ValTy.fv (ValExpr.inferType v) := by
  cases sv with
  | tprod a b =>
      obtain ⟨ha, hb⟩ := valSValidC_tprod_inv hval
      refine ⟨⟨?_⟩, ?_⟩
      · simp only [ValExpr.inferType, hshape]
        exact .space (.tprod hb ha)
      · simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]
        exact Finset.union_subset Finset.subset_union_right Finset.subset_union_left
  | empty =>
      exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
        by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | real =>
      exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
        by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | dsum s₀ s₁ =>
      exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
        by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩
  | ffs p sp w =>
      exact ⟨⟨by simp only [ValExpr.inferType, hshape]; exact .space .empty⟩,
        by simp only [ValExpr.inferType, hshape, ValTy.fv, ValSpace.fv]; simp⟩

end GLang
