import GLang.Proofs.Value.Binding.ValueInferenceSubstitution

import GLang.Proofs.Value.Binding.ValueWeakening
import GLang.Proofs.Source.SourceSubstCommute
import GLang.Proofs.Preservation.PreservationV2Helpers
import GLang.Proofs.Value.Typing.ValueRealizeLc

namespace GLang

/-- `tof b = .space (sof b)` (a space-basis premise) survives substitution. -/
private theorem tof_space_subst (x : VName) (n₁ : Term) {b : Basis}
    (h : Basis.tof b = .space (Basis.sof b)) :
    Basis.tof (Basis.subst x n₁ b) = .space (Basis.sof (Basis.subst x n₁ b)) := by
  simp only [Basis.tof_subst, h, Ty.subst, Basis.sof_subst]

/-- `isStd` is shape-only, so it survives substitution. -/
private theorem isStd_subst (x : VName) (n₁ : Term) (b : Basis) :
    Basis.isStd (Basis.subst x n₁ b) = Basis.isStd b := by
  induction b with
  | empty => rfl
  | one => rfl
  | dual b ih => simp only [Basis.subst, Basis.isStd, ih]
  | dsum _ _ ih₀ ih₁ => simp only [Basis.subst, Basis.isStd, ih₀, ih₁]
  | tprod _ _ ih₀ ih₁ => simp only [Basis.subst, Basis.isStd, ih₀, ih₁]
  | proj _ _ _ ih₀ ih₁ => simp only [Basis.subst, Basis.isStd, ih₀, ih₁]
  | image _ _ => simp only [Basis.subst, Basis.isStd]
  | terms _ _ _ _ => simp only [Basis.subst, Basis.isStd]
  | frame _ _ ih₀ ih₁ =>
      simp only [Basis.subst, Basis.isStd, ih₀, ih₁]

/-- The standard basis of a space commutes with substitution. -/
private theorem stdSpace_subst (x : VName) (u : Term) :
    ∀ s : Space, Basis.subst x u (Basis.stdSpace s) = Basis.stdSpace (Space.subst x u s)
  | .empty => rfl
  | .real => rfl
  | .dual s => by simp only [Basis.stdSpace, Space.subst, Basis.subst, stdSpace_subst x u s]
  | .dsum s₀ s₁ => by
      simp only [Basis.stdSpace, Space.subst, Basis.subst,
        stdSpace_subst x u s₀, stdSpace_subst x u s₁]
  | .tprod s₀ s₁ => by
      simp only [Basis.stdSpace, Space.subst, Basis.subst,
        stdSpace_subst x u s₀, stdSpace_subst x u s₁]
  | .ker s₀ s₁ e => by
      simp only [Basis.stdSpace, Space.subst, Basis.subst,
        stdSpace_subst x u s₀, stdSpace_subst x u s₁]
  | .coker s₀ s₁ e => by
      simp only [Basis.stdSpace, Space.subst, Basis.subst,
        stdSpace_subst x u s₀, stdSpace_subst x u s₁]
  | .img s₀ s₁ e => by
      simp only [Basis.stdSpace, Space.subst, Basis.subst,
        stdSpace_subst x u s₀, stdSpace_subst x u s₁]
  | .coimg s₀ s₁ e => by
      simp only [Basis.stdSpace, Space.subst, Basis.subst,
        stdSpace_subst x u s₀, stdSpace_subst x u s₁]

/-- The standard basis of a type commutes with substitution. -/
private theorem std_subst (x : VName) (u : Term) :
    ∀ τ : Ty, Basis.subst x u (Basis.std τ) = Basis.std (Ty.subst x u τ)
  | .space s => by simp only [Basis.std, Ty.subst, stdSpace_subst x u s]
  | .piTy τ₀ τ₁ => by
      simp only [Basis.std, Ty.subst, Basis.subst, std_subst x u τ₀, std_subst x u τ₁]

/-! ## `inferSpace`/`subst` commutation (the `add` arm's `inferSpace` side condition).

`ValSpace.subst` is HEAD-PRESERVING — `ValSpace` has no variable constructor
(`empty/real/dsum/tprod/ffs`), so `ValSpace.subst x arg` never changes a
`ValSpace`'s outer constructor. Consequently `inferSpace` commutes with
`ValExpr.subst` in EVERY structural case (including the nested-`match` cases
`ttv`/`mtm`/`vkrn`/`vblk`/`vtrans`/`gsvd*`, whose scrutinee `inferSpace e` keeps
its `.tprod` head under `subst`). The SOLE exception is `.var x τ`: there
`subst` yields `arg` (whence `inferSpace arg`) while the structural answer is
`ValSpace.subst x arg (spaceOf τ)`. The two agree precisely when `arg` is
normalized so its space matches the placeholder annotation — the FFS/L1
realization invariant. `inferSpace_subst_comm` below makes that the ONLY
hypothesis (`hvarx`), proving every other case, which pins the obstruction. -/

/-- `spaceOf` commutes with substitution (structural; `ValSpace.subst` is
    head-preserving and `spaceOf` is a head-projection). -/
private theorem spaceOf_subst (x : VName) (arg : ValExpr) :
    ∀ τ : ValTy, ValTy.spaceOf (ValTy.subst x arg τ) = ValSpace.subst x arg (ValTy.spaceOf τ)
  | .space _ => rfl
  | .piTy _ _ => rfl

/-- The context invariant feeding the `add` arm's side condition: every stored
    value's `inferSpace` commutes with the substitution. The `.var x` placeholder
    case is anchored by `ESubst.xbind`/`xonly` (the realization invariant);
    binder placeholders commute via `spaceOf_subst`; the boundary's `x`-free
    bindings via `subst_fresh` + `fv_inferSpace_subset`. -/
def InferSpaceSubstCtx (x : VName) (arg : ValExpr) (Ψ : EvalCtx) : Prop :=
  ∀ z b v, EvalCtx.lookup Ψ (z, b) = some v →
    ValExpr.inferSpace (ValExpr.subst x arg v) = ValSpace.subst x arg (ValExpr.inferSpace v)

/-! ### Head-match commutation helpers: `ValSpace.subst` is head-preserving, so
each `match inferSpace e` site fires the SAME branch after substitution, given
the operand's commutation. One helper per match-headed value constructor that
the eval rules produce. -/

private theorem inferSpace_subst_pinv {x : VName} {arg : ValExpr} {e : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e)
        = ValSpace.subst x arg (ValExpr.inferSpace e)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.pinv e))
      = ValSpace.subst x arg (ValExpr.inferSpace (.pinv e)) := by
  cases h : ValExpr.inferSpace e <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he, h, ValSpace.subst]

private theorem inferSpace_subst_gpinv {x : VName} {arg : ValExpr} {e a b : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e)
        = ValSpace.subst x arg (ValExpr.inferSpace e)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.gpinv e a b))
      = ValSpace.subst x arg (ValExpr.inferSpace (.gpinv e a b)) := by
  cases h : ValExpr.inferSpace e <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he, h, ValSpace.subst]

private theorem inferSpace_subst_ttv {x : VName} {arg : ValExpr} {s : ValSpace}
    {e₀ e₁ : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e₀)
        = ValSpace.subst x arg (ValExpr.inferSpace e₀)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.ttv s e₀ e₁))
      = ValSpace.subst x arg (ValExpr.inferSpace (.ttv s e₀ e₁)) := by
  cases h : ValExpr.inferSpace e₀ <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he, h, ValSpace.subst]

private theorem inferSpace_subst_gsvdU {x : VName} {arg : ValExpr} {e a b : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e)
        = ValSpace.subst x arg (ValExpr.inferSpace e)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.gsvdU e a b))
      = ValSpace.subst x arg (ValExpr.inferSpace (.gsvdU e a b)) := by
  cases h : ValExpr.inferSpace e <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he, h, ValSpace.subst]

private theorem inferSpace_subst_gsvdUI {x : VName} {arg : ValExpr} {e a b : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e)
        = ValSpace.subst x arg (ValExpr.inferSpace e)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.gsvdUI e a b))
      = ValSpace.subst x arg (ValExpr.inferSpace (.gsvdUI e a b)) := by
  cases h : ValExpr.inferSpace e <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he, h, ValSpace.subst]

private theorem inferSpace_subst_gsvdV {x : VName} {arg : ValExpr} {e a b : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e)
        = ValSpace.subst x arg (ValExpr.inferSpace e)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.gsvdV e a b))
      = ValSpace.subst x arg (ValExpr.inferSpace (.gsvdV e a b)) := by
  cases h : ValExpr.inferSpace e <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he, h, ValSpace.subst]

private theorem inferSpace_subst_gsvdVI {x : VName} {arg : ValExpr} {e a b : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e)
        = ValSpace.subst x arg (ValExpr.inferSpace e)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.gsvdVI e a b))
      = ValSpace.subst x arg (ValExpr.inferSpace (.gsvdVI e a b)) := by
  cases h : ValExpr.inferSpace e <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he, h, ValSpace.subst]

private theorem inferSpace_subst_inv {x : VName} {arg : ValExpr} {e : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e)
        = ValSpace.subst x arg (ValExpr.inferSpace e)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.inv e))
      = ValSpace.subst x arg (ValExpr.inferSpace (.inv e)) := by
  cases h : ValExpr.inferSpace e <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he, h, ValSpace.subst]

/-- The SVD-space constructor commutes with substitution whenever its matrix
operand's inferred space does. -/
private theorem inferSpace_subst_svds {x : VName} {arg e : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e)
        = ValSpace.subst x arg (ValExpr.inferSpace e)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.svds e))
      = ValSpace.subst x arg (ValExpr.inferSpace (.svds e)) := by
  simp only [ValExpr.subst, ValExpr.inferSpace, he, ValSpace.subst]

private theorem inferSpace_subst_vtrans {x : VName} {arg : ValExpr} {e : ValExpr}
    (he : ValExpr.inferSpace (ValExpr.subst x arg e)
        = ValSpace.subst x arg (ValExpr.inferSpace e)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.vtrans e))
      = ValSpace.subst x arg (ValExpr.inferSpace (.vtrans e)) := by
  cases h : ValExpr.inferSpace e <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he, h, ValSpace.subst]

private theorem inferSpace_subst_vkrn {x : VName} {arg : ValExpr} {e₀ e₁ : ValExpr}
    (he₀ : ValExpr.inferSpace (ValExpr.subst x arg e₀)
        = ValSpace.subst x arg (ValExpr.inferSpace e₀))
    (he₁ : ValExpr.inferSpace (ValExpr.subst x arg e₁)
        = ValSpace.subst x arg (ValExpr.inferSpace e₁)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.vkrn e₀ e₁))
      = ValSpace.subst x arg (ValExpr.inferSpace (.vkrn e₀ e₁)) := by
  cases h₀ : ValExpr.inferSpace e₀ <;> cases h₁ : ValExpr.inferSpace e₁ <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he₀, he₁, h₀, h₁, ValSpace.subst]

private theorem inferSpace_subst_vblk {x : VName} {arg : ValExpr} {e₀ e₁ : ValExpr}
    (he₀ : ValExpr.inferSpace (ValExpr.subst x arg e₀)
        = ValSpace.subst x arg (ValExpr.inferSpace e₀))
    (he₁ : ValExpr.inferSpace (ValExpr.subst x arg e₁)
        = ValSpace.subst x arg (ValExpr.inferSpace e₁)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.vblk e₀ e₁))
      = ValSpace.subst x arg (ValExpr.inferSpace (.vblk e₀ e₁)) := by
  cases h₀ : ValExpr.inferSpace e₀ <;> cases h₁ : ValExpr.inferSpace e₁ <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he₀, he₁, h₀, h₁, ValSpace.subst]

private theorem inferSpace_subst_mtm {x : VName} {arg : ValExpr} {i j : Nat}
    {s₀ s₁ : ValSpace} {e₀ e₁ : ValExpr}
    (he₀ : ValExpr.inferSpace (ValExpr.subst x arg e₀)
        = ValSpace.subst x arg (ValExpr.inferSpace e₀))
    (he₁ : ValExpr.inferSpace (ValExpr.subst x arg e₁)
        = ValSpace.subst x arg (ValExpr.inferSpace e₁)) :
    ValExpr.inferSpace (ValExpr.subst x arg (.mtm i j s₀ s₁ e₀ e₁))
      = ValSpace.subst x arg (ValExpr.inferSpace (.mtm i j s₀ s₁ e₀ e₁)) := by
  cases h₀ : ValExpr.inferSpace e₀ <;> cases h₁ : ValExpr.inferSpace e₁ <;>
    simp only [ValExpr.subst, ValExpr.inferSpace, he₀, he₁, h₀, h₁, ValSpace.subst]

/-- The `.reshap`-headed values' commutation (annotation-pinned; no IH). -/
private theorem inferSpace_subst_reshap {x : VName} {arg : ValExpr} {e : ValExpr}
    {τ τ₀ : ValTy} :
    ValExpr.inferSpace (ValExpr.subst x arg (.reshap e τ τ₀))
      = ValSpace.subst x arg (ValExpr.inferSpace (.reshap e τ τ₀)) := by
  simp only [ValExpr.subst, ValExpr.inferSpace, spaceOf_subst]

/-- Internal substitution also retains full function codomains. -/
def InferTypeSubstCtx (x : VName) (arg : ValExpr) (Ψ : EvalCtx) : Prop :=
  ∀ z b v, EvalCtx.lookup Ψ (z, b) = some v → InferTypeSubstAt x arg v

theorem opStep_inferType_subst {x : VName} {arg : ValExpr}
    (hlcarg : ValExpr.lc arg) {Ψ : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e b v) (hctx : InferTypeSubstCtx x arg Ψ) :
    ValExpr.inferType (ValExpr.subst x arg v)
      = ValTy.subst x arg (ValExpr.inferType v) := by
  refine ValExpr.OpStep.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun Ψ' _ _ v' _ => InferTypeSubstCtx x arg Ψ' →
      ValExpr.inferType (ValExpr.subst x arg v')
        = ValTy.subst x arg (ValExpr.inferType v'))
    -- 9 EvalS arms + 2 EvalT arms + 13 EvalBB arms: trivial motives.
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial)
    -- var: the context invariant.
    (by intros; rename_i hlk; intro hc; exact hc _ _ _ hlk)
    -- cob: `.ttv sv (.reshap …) (.reshap …)` — annotation-pinned.
    (by intros; intro _hc
        simp only [ValExpr.reshapBase,
          ValExpr.subst, ValTy.subst, ValTy.spaceOf, ValTy.subst, ValSpace.subst,
          ValExpr.inferType])
    -- scale: `.scale v₀ v₁` reads v₁.
    (by intros; rename_i ih₀ ih₁; intro hc
        simp only [ValExpr.subst, ValExpr.inferType]; exact ih₁ hc)
    -- add: the explicit result-space annotation is substitution-structural.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.inferType, ValTy.subst])
    -- dsumE.
    (by intros; rename_i ih₀ ih₁; intro hc
        simp only [ValExpr.subst, ValExpr.inferType, ValTy.subst, ValSpace.subst, ih₀ hc, ih₁ hc, spaceOf_subst])
    -- tprodE.
    (by intros; rename_i ih₀ ih₁; intro hc
        simp only [ValExpr.subst, ValExpr.inferType, ValTy.subst, ValSpace.subst, ih₀ hc, ih₁ hc, spaceOf_subst])
    -- pinvT_std: `.pinv v`.
    (by intros; rename_i ih; intro hc; exact inferType_subst_pinv hlcarg (ih hc))
    -- pinvT_gpinv: `.gpinv v env₁ env₀` (E3).
    (by intros; rename_i ih_he ih_hi₀ ih_hi₁; intro hc
        exact inferType_subst_gpinv hlcarg (ih_he hc))
    -- pinvD_std: `.pinv (.reshap v (sv₁ ⊗ ℝ))` (E4/E7) — annotation-pinned.
    (by intros; rename_i ih _ih_hsv; intro _hc
        exact inferType_subst_pinv hlcarg (inferType_subst_reshap hlcarg))
    -- pinvD_gpinv: `.gpinv (.reshap v (sv₁ ⊗ ℝ)) env₁ env₀`.
    (by intros; rename_i ih_he ih_hi₀ ih_hi₁ _ih_hsv; intro _hc
        exact inferType_subst_gpinv hlcarg (inferType_subst_reshap hlcarg))
    -- inner_std: `.idelta sv` — annotations only.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValTy.subst, ValSpace.subst, ValExpr.inferType])
    -- embed_ker..coimg: `.vtrans (.gsvdUI/U/V/VI v env₀ env₁)` (E1/E2).
    (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hc
        exact inferType_subst_vtrans hlcarg (inferType_subst_gsvdUI hlcarg (ih_he hc)))
    (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hc
        exact inferType_subst_vtrans hlcarg (inferType_subst_gsvdU hlcarg (ih_he hc)))
    (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hc
        exact inferType_subst_vtrans hlcarg (inferType_subst_gsvdV hlcarg (ih_he hc)))
    (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hc
        exact inferType_subst_vtrans hlcarg (inferType_subst_gsvdVI hlcarg (ih_he hc)))
    -- appL_lin: the result reshape pins the inferred space to its codomain
    -- annotation, independently of the matrix operand's inferred space.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.reshapBase, ValExpr.inferType,
          ValTy.subst, ValTy.spaceOf])
    -- appI_lin: `.ttv sv (.reshap env₀ (sv ⊗ ℝ)) env₁` (E7) — annotation-pinned.
    (by intros; rename_i ih_h₀ ih_hsv ih_h₁; intro _hc
        exact inferType_subst_ttv hlcarg (inferType_subst_reshap hlcarg))
    -- nllam: `.vlam …` — constant `.empty`.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.inferType, ValTy.subst, ValSpace.subst])
    -- The compiler's explicit result conversion selects its realized type.
    (by intros; intro _hc; exact inferType_subst_reshap hlcarg)
    -- frame_reanchor / frame_eta: `.vlam …` — constant `.empty`.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.inferType, ValTy.subst, ValSpace.subst])
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.inferType, ValTy.subst, ValSpace.subst])
    -- reshape_cob: `.reshap v τv` — annotation-pinned.
    (by intros; intro _hc; exact inferType_subst_reshap hlcarg)
    -- llam_assemble / llam_assemble_real: after S1 the assembled sum is wrapped in the
    -- identity reshape to its space (`.reshap (.vsum …) (.space …)`) — annotation-pinned
    -- for every `n` (before S1 the `n = 0` corner was the constant `.empty`).
    (by intros; intro _hc; exact inferType_subst_reshap hlcarg)
    (by intros; intro _hc; exact inferType_subst_reshap hlcarg)
    -- zero: `.zero sv` — head-structural (`ValSpace.subst` is head-preserving).
    (by intros; intro _hc; simp only [ValExpr.subst, ValExpr.inferType, ValTy.subst])
    -- rlit: constant `.real`.
    (by intros; intro _hc; simp only [ValExpr.subst, ValExpr.inferType, ValTy.subst, ValSpace.subst])
    h hctx

private theorem opStep_inferSpace_subst {x : VName} {arg : ValExpr}
    (hlcarg : ValExpr.lc arg) {Ψ : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e b v) (hctx : InferSpaceSubstCtx x arg Ψ ∧ InferTypeSubstCtx x arg Ψ) :
    ValExpr.inferSpace (ValExpr.subst x arg v)
      = ValSpace.subst x arg (ValExpr.inferSpace v) := by
  refine ValExpr.OpStep.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun Ψ' _ _ v' _ => (InferSpaceSubstCtx x arg Ψ' ∧ InferTypeSubstCtx x arg Ψ') →
      ValExpr.inferSpace (ValExpr.subst x arg v')
        = ValSpace.subst x arg (ValExpr.inferSpace v'))
    -- 9 EvalS arms + 2 EvalT arms + 13 EvalBB arms: trivial motives.
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial) (by intros; exact trivial) (by intros; exact trivial)
    (by intros; exact trivial)
    -- var: the context invariant.
    (by intros; rename_i hlk; intro hc; exact hc.1 _ _ _ hlk)
    -- cob: `.ttv sv (.reshap …) (.reshap …)` — annotation-pinned.
    (by intros; intro _hc
        simp only [ValExpr.reshapBase,
          ValExpr.subst, ValTy.subst, ValTy.spaceOf, ValSpace.subst,
          ValExpr.inferSpace])
    -- scale: `.scale v₀ v₁` reads v₁.
    (by intros; rename_i ih₀ ih₁; intro hc
        simp only [ValExpr.subst, ValExpr.inferSpace]; exact ih₁ hc)
    -- add: the explicit result-space annotation is substitution-structural.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.inferSpace])
    -- dsumE.
    (by intros; rename_i ih₀ ih₁; intro hc
        simp only [ValExpr.subst, ValExpr.inferSpace, ValSpace.subst, ih₀ hc, ih₁ hc])
    -- tprodE.
    (by intros; rename_i ih₀ ih₁; intro hc
        simp only [ValExpr.subst, ValExpr.inferSpace, ValSpace.subst, ih₀ hc, ih₁ hc])
    -- pinvT_std: `.pinv v`.
    (by intros; rename_i ih; intro hc; exact inferSpace_subst_pinv (ih hc))
    -- pinvT_gpinv: `.gpinv v env₁ env₀` (E3).
    (by intros; rename_i ih_he ih_hi₀ ih_hi₁; intro hc
        exact inferSpace_subst_gpinv (ih_he hc))
    -- pinvD_std: `.pinv (.reshap v (sv₁ ⊗ ℝ))` (E4/E7) — annotation-pinned.
    (by intros; rename_i ih _ih_hsv; intro _hc
        exact inferSpace_subst_pinv inferSpace_subst_reshap)
    -- pinvD_gpinv: `.gpinv (.reshap v (sv₁ ⊗ ℝ)) env₁ env₀`.
    (by intros; rename_i ih_he ih_hi₀ ih_hi₁ _ih_hsv; intro _hc
        exact inferSpace_subst_gpinv inferSpace_subst_reshap)
    -- inner_std: `.idelta sv` — annotations only.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValSpace.subst, ValExpr.inferSpace])
    -- embed_ker..coimg: `.vtrans (.gsvdUI/U/V/VI v env₀ env₁)` (E1/E2).
    (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hc
        exact inferSpace_subst_vtrans (inferSpace_subst_gsvdUI (ih_he hc)))
    (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hc
        exact inferSpace_subst_vtrans (inferSpace_subst_gsvdU (ih_he hc)))
    (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hc
        exact inferSpace_subst_vtrans (inferSpace_subst_gsvdV (ih_he hc)))
    (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hc
        exact inferSpace_subst_vtrans (inferSpace_subst_gsvdVI (ih_he hc)))
    -- appL_lin: the result reshape pins the inferred space to its codomain
    -- annotation, independently of the matrix operand's inferred space.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.reshapBase, ValExpr.inferSpace,
          ValTy.subst, ValTy.spaceOf])
    -- appI_lin: `.ttv sv (.reshap env₀ (sv ⊗ ℝ)) env₁` (E7) — annotation-pinned.
    (by intros; rename_i ih_h₀ ih_hsv ih_h₁; intro _hc
        exact inferSpace_subst_ttv inferSpace_subst_reshap)
    -- nllam: `.vlam …` — constant `.empty`.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.inferSpace, ValSpace.subst])
    -- The explicit result conversion selects its realized space.
    (by intros; intro _hc; exact inferSpace_subst_reshap)
    -- frame_reanchor / frame_eta: `.vlam …` — constant `.empty`.
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.inferSpace, ValSpace.subst])
    (by intros; intro _hc
        simp only [ValExpr.subst, ValExpr.inferSpace, ValSpace.subst])
    -- reshape_cob: `.reshap v τv` — annotation-pinned.
    (by intros; intro _hc; exact inferSpace_subst_reshap)
    -- llam_assemble / llam_assemble_real: after S1 the assembled sum is wrapped in the
    -- identity reshape to its space (`.reshap (.vsum …) (.space …)`) — annotation-pinned
    -- for every `n` (before S1 the `n = 0` corner was the constant `.empty`).
    (by intros; intro _hc; exact inferSpace_subst_reshap)
    (by intros; intro _hc; exact inferSpace_subst_reshap)
    -- zero: `.zero sv` — head-structural (`ValSpace.subst` is head-preserving).
    (by intros; intro _hc; simp only [ValExpr.subst, ValExpr.inferSpace])
    -- rlit: constant `.real`.
    (by intros; intro _hc; simp only [ValExpr.subst, ValExpr.inferSpace, ValSpace.subst])
    h hctx

/-! ## The `ESubst` relation (context substitution). -/

/-- `Ψ'` is `Ψ` with the placeholder `(x,b₀)↦.var x τv₀` discharged and `x` substituted
    (`x↦n₁` source / `x↦arg` value) through the remaining bindings. -/
structure ESubst (x : VName) (b₀ : Basis) (τv₀ : ValTy) (n₁ : Term) (arg : ValExpr)
    (Ψ Ψ' : EvalCtx) : Prop where
  /-- the discharged placeholder is present in `Ψ`. -/
  xbind : EvalCtx.lookup Ψ (x, b₀) = some (.var x τv₀)
  /-- `x` is bound only at `b₀` in `Ψ` (a var-lookup of `x` is the placeholder). -/
  xonly : ∀ b' v', EvalCtx.lookup Ψ (x, b') = some v' → b' = b₀
  /-- the argument realizes in `Ψ'` at the substituted domain basis — the variable cut. -/
  hcut  : ValExpr.OpStep Ψ' n₁ (Basis.subst x n₁ b₀) arg
  /-- every non-`x` binding maps to its substitution in `Ψ'`. -/
  fwd   : ∀ z b v, z ≠ x → EvalCtx.lookup Ψ (z, b) = some v →
            EvalCtx.lookup Ψ' (z, Basis.subst x n₁ b) = some (ValExpr.subst x arg v)
  /-- the substituted source term is locally closed (drives the source
      `subst_openRec` commutation in the binder arms). -/
  lcn   : Term.lc n₁
  /-- the substituted value is locally closed (drives the value `subst_openRec`
      commutation in the binder arms). -/
  lcarg : ValExpr.lc arg

  hinfer : InferSpaceSubstCtx x arg Ψ
  /-- Full inferred types, including dependent codomains, commute with substitution. -/
  htype : InferTypeSubstCtx x arg Ψ

/-- The exact empty-context SVD source annotation commutes with an environment
substitution along any operationally realized operand.  This packages the
context invariant carried by `ESubst` for certified/strengthened transports
that must preserve the `image_svds` result literally. -/
theorem ESubst.inferSpaceCtx_svds
    {x : VName} {b₀ : Basis} {τv₀ : ValTy} {n₁ : Term} {arg : ValExpr}
    {Ψ Ψ' : EvalCtx} (hes : ESubst x b₀ τv₀ n₁ arg Ψ Ψ')
    {e : Term} {b : Basis} {v : ValExpr} (h : ValExpr.OpStep Ψ e b v) :
    ValExpr.inferSpaceCtx [] (.svds (ValExpr.subst x arg v)) =
      ValSpace.subst x arg (ValExpr.inferSpaceCtx [] (.svds v)) := by
  rw [ValExpr.inferSpaceCtx_nil, ValExpr.inferSpaceCtx_nil]
  exact inferSpace_subst_svds
    (opStep_inferSpace_subst hes.lcarg h ⟨hes.hinfer, hes.htype⟩)

/-- `ESubst` extends under a fresh inner binder `y` — the binder arms' workhorse (cf.
    `SRen.extendΓ`): the inner domain `tv0z`/`bz` get substituted in `Ψ'`. -/
theorem ESubst.extend {x : VName} {b₀ : Basis} {τv₀ : ValTy} {n₁ : Term} {arg : ValExpr}
    {Ψ Ψ' : EvalCtx} (hes : ESubst x b₀ τv₀ n₁ arg Ψ Ψ')
    {y : VName} {bz : Basis} {tv0z : ValTy}
    (hyx : y ≠ x) (hyΨ : ∀ b', (y, b') ∉ Ψ) (hyΨ' : (y, Basis.subst x n₁ bz) ∉ Ψ') :
    ESubst x b₀ τv₀ n₁ arg
      (EvalCtx.extend Ψ y bz (.var y tv0z))
      (EvalCtx.extend Ψ' y (Basis.subst x n₁ bz) (.var y (ValTy.subst x arg tv0z))) := by
  have hxy : (x, b₀) ≠ (y, bz) := fun h => hyx ((congrArg Prod.fst h).symm)
  refine ⟨?_, ?_, ?_, ?_, hes.lcn, hes.lcarg, ?_, ?_⟩
  · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hxy]; exact hes.xbind
  · intro b' v' hl
    by_cases hk : (x, b') = (y, bz)
    · exact absurd (congrArg Prod.fst hk).symm hyx
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      exact hes.xonly b' v' hl
  · rw [EvalCtx.extend]; exact opStep_wk hes.hcut hyΨ'
  · intro z b v hzx hl
    by_cases hk : (z, b) = (y, bz)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert]
      simp only [ValExpr.subst, if_neg hzx]
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      have hzy : z ≠ y := fun h => hyΨ b (h ▸ Finmap.mem_of_lookup_eq_some hl)
      have hk' : (z, Basis.subst x n₁ b) ≠ (y, Basis.subst x n₁ bz) :=
        fun h => hzy (congrArg Prod.fst h)
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk']
      exact hes.fwd z b v hzx hl
  ·
    intro z b v hl
    by_cases hk : (z, b) = (y, bz)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      simp only [ValExpr.subst, if_neg hyx, ValExpr.inferSpace, spaceOf_subst]
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      exact hes.hinfer z b v hl

  · intro z b v hl
    by_cases hk : (z, b) = (y, bz)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      simp only [InferTypeSubstAt, ValExpr.subst, if_neg hyx, ValExpr.inferType]
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      exact hes.htype z b v hl

theorem ESubst.extend_val {x : VName} {b₀ : Basis} {τv₀ : ValTy} {n₁ : Term} {arg : ValExpr}
    {Ψ Ψ' : EvalCtx} (hes : ESubst x b₀ τv₀ n₁ arg Ψ Ψ')
    {y : VName} {bz : Basis} {w : ValExpr}
    (hyx : y ≠ x) (hyΨ : ∀ b', (y, b') ∉ Ψ) (hyΨ' : (y, Basis.subst x n₁ bz) ∉ Ψ')
    (hwinfer : ValExpr.inferSpace (ValExpr.subst x arg w)
        = ValSpace.subst x arg (ValExpr.inferSpace w))
    (hwtype : InferTypeSubstAt x arg w) :
    ESubst x b₀ τv₀ n₁ arg
      (EvalCtx.extend Ψ y bz w)
      (EvalCtx.extend Ψ' y (Basis.subst x n₁ bz) (ValExpr.subst x arg w)) := by
  have hxy : (x, b₀) ≠ (y, bz) := fun h => hyx ((congrArg Prod.fst h).symm)
  refine ⟨?_, ?_, ?_, ?_, hes.lcn, hes.lcarg, ?_, ?_⟩
  · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hxy]; exact hes.xbind
  · intro b' v' hl
    by_cases hk : (x, b') = (y, bz)
    · exact absurd (congrArg Prod.fst hk).symm hyx
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      exact hes.xonly b' v' hl
  · rw [EvalCtx.extend]; exact opStep_wk hes.hcut hyΨ'
  · intro z b v hzx hl
    by_cases hk : (z, b) = (y, bz)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert]
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      have hzy : z ≠ y := fun h => hyΨ b (h ▸ Finmap.mem_of_lookup_eq_some hl)
      have hk' : (z, Basis.subst x n₁ b) ≠ (y, Basis.subst x n₁ bz) :=
        fun h => hzy (congrArg Prod.fst h)
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk']
      exact hes.fwd z b v hzx hl
  · intro z b v hl
    by_cases hk : (z, b) = (y, bz)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      exact hwinfer
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      exact hes.hinfer z b v hl

  · intro z b v hl
    by_cases hk : (z, b) = (y, bz)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      exact hwtype
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      exact hes.htype z b v hl

set_option maxHeartbeats 1600000 in
mutual

/-- **(EvalS substitution).** All arms structural — port verbatim. -/
theorem evalS_substC {x : VName} {b₀ : Basis} {τv₀ : ValTy} {n₁ : Term} {arg : ValExpr}
    {Ψ Ψ' : EvalCtx} {s : Space} {sv : ValSpace}
    (h : ValSpace.EvalS Ψ s sv) (hes : ESubst x b₀ τv₀ n₁ arg Ψ Ψ') :
    ValSpace.EvalS Ψ' (Space.subst x n₁ s) (ValSpace.subst x arg sv) := by
  match h with
  | .real => exact .real
  | .empty => exact .empty
  | .dual h' => exact .dual (evalS_substC h' hes)
  | .dsum h₀ h₁ => exact .dsum (evalS_substC h₀ hes) (evalS_substC h₁ hes)
  | .tprod h₀ h₁ => exact .tprod (evalS_substC h₀ hes) (evalS_substC h₁ hes)
  | .ker he hb hcompat hsvb =>
      refine .ker (opStep_substC he hes) ?_ ?_ ?_
      · rw [Basis.sof_subst, hb]; rfl
      · obtain ⟨c₀, c₁, rfl⟩ := hcompat
        exact ⟨Basis.subst x n₁ c₀, Basis.subst x n₁ c₁, rfl⟩
      · rw [Basis.sof_subst]; exact evalS_substC hsvb hes
  | .coker he hb hcompat hsvb =>
      refine .coker (opStep_substC he hes) ?_ ?_ ?_
      · rw [Basis.sof_subst, hb]; rfl
      · obtain ⟨c₀, c₁, rfl⟩ := hcompat
        exact ⟨Basis.subst x n₁ c₀, Basis.subst x n₁ c₁, rfl⟩
      · rw [Basis.sof_subst]; exact evalS_substC hsvb hes
  | .img he hb hcompat hsvb =>
      refine .img (opStep_substC he hes) ?_ ?_ ?_
      · rw [Basis.sof_subst, hb]; rfl
      · obtain ⟨c₀, c₁, rfl⟩ := hcompat
        exact ⟨Basis.subst x n₁ c₀, Basis.subst x n₁ c₁, rfl⟩
      · rw [Basis.sof_subst]; exact evalS_substC hsvb hes
  | .coimg he hb hcompat hsvb =>
      refine .coimg (opStep_substC he hes) ?_ ?_ ?_
      · rw [Basis.sof_subst, hb]; rfl
      · obtain ⟨c₀, c₁, rfl⟩ := hcompat
        exact ⟨Basis.subst x n₁ c₀, Basis.subst x n₁ c₁, rfl⟩
      · rw [Basis.sof_subst]; exact evalS_substC hsvb hes

/-- **EvalT substitution.** `space` arm done;
    `piTy` (binder) STUBBED (LN: needs `ESubst.extend` + value `subst_openRec` + source
    `subst_comm`; see binder-arm task). -/
theorem evalT_substC {x : VName} {b₀ : Basis} {τv₀ : ValTy} {n₁ : Term} {arg : ValExpr}
    {Ψ Ψ' : EvalCtx} {τ : Ty} {τv : ValTy}
    (h : ValTy.EvalT Ψ τ τv) (hes : ESubst x b₀ τv₀ n₁ arg Ψ Ψ') :
    ValTy.EvalT Ψ' (Ty.subst x n₁ τ) (ValTy.subst x arg τv) := by
  match h with
  | .space h' => exact .space (evalS_substC h' hes)
  | @ValTy.EvalT.piTy _ bz τ₀ τ₁ τv₀' τv₁' h₀ hb L h₁ =>
      -- LN binder arm: build the substituted `EvalT.piTy`. Domain by recursion;
      -- the cofinite codomain at a fresh `y` via the extended `ESubst` (`ESubst.extend`),
      -- commuting `subst` past `openVar` by `Ty.subst_openRec` (source) and
      -- `ValTy.subst_openRec` (value), both gated on the `lc` fields of `hes`.
      refine ValTy.EvalT.piTy (evalT_substC h₀ hes)
        ((Basis.tof_subst x n₁ bz).trans (congrArg (Ty.subst x n₁) hb))
        (L ∪ {x} ∪ EvalCtx.avoid Ψ ∪ EvalCtx.avoid Ψ') (fun y hy => ?_)
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
      obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
      have hes' := ESubst.extend (bz := bz) (tv0z := τv₀') hes hyx
        (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
      have hrec := evalT_substC (h₁ y hyL) hes'
      have hsrc : Ty.subst x n₁ (Ty.openVar y τ₁) = Ty.openVar y (Ty.subst x n₁ τ₁) := by
        simp only [Ty.openVar, Ty.subst_openRec x n₁ hes.lcn τ₁ 0 (.var y),
          Term.subst, if_neg (Ne.symm hyx)]
      have hval : ValTy.subst x arg (ValTy.openVar y τv₀' τv₁')
          = ValTy.openVar y (ValTy.subst x arg τv₀') (ValTy.subst x arg τv₁') := by
        simp only [ValTy.openVar, ValTy.subst_openRec x arg hes.lcarg τv₁' 0 (.var y τv₀'),
          ValExpr.subst, if_neg hyx]
      rw [hsrc, hval] at hrec
      exact hrec

/-- **(EvalBB substitution).** Structural + image arms done; `dual_std`/`proj_*` STUBBED. -/
theorem evalBB_substC {x : VName} {b₀ : Basis} {τv₀ : ValTy} {n₁ : Term} {arg : ValExpr}
    {Ψ Ψ' : EvalCtx} {bb : Basis} {leev : ValExpr} {bb' : Basis}
    (h : Basis.EvalBB Ψ bb leev bb') (hes : ESubst x b₀ τv₀ n₁ arg Ψ Ψ') :
    Basis.EvalBB Ψ' (Basis.subst x n₁ bb) (ValExpr.subst x arg leev) (Basis.subst x n₁ bb') := by
  match h with
  | .inverse h' => exact .inverse (evalBB_substC h' hes)
  | .trans h₀ h₁ hsv =>
      refine .trans (evalBB_substC h₀ hes) (evalBB_substC h₁ hes) ?_
      rw [Basis.sof_subst]; exact evalS_substC hsv hes
  | .tprod h₀ h₁ => exact .tprod (evalBB_substC h₀ hes) (evalBB_substC h₁ hes)
  | .dsum h₀ h₁ => exact .dsum (evalBB_substC h₀ hes) (evalBB_substC h₁ hes)
  | .image hcoker h =>
      obtain ⟨s₀, s₁, e, hc⟩ := hcoker
      refine .image ⟨Space.subst x n₁ s₀, Space.subst x n₁ s₁, Term.subst x n₁ e, ?_⟩
        (evalBB_substC h hes)
      rw [Basis.sof_subst, hc]; rfl
  | @Basis.EvalBB.image_svds _ bL bR e₀ leev₀ sL sR svb hs₀ hs₁ hb₀ hb₁ he hsvb =>
      have hs₀' : Basis.sof (Basis.subst x n₁ bL) = Space.subst x n₁ sL := by
        rw [Basis.sof_subst, hs₀]
      have hs₁' : Basis.sof (Basis.subst x n₁ bR) = Space.subst x n₁ sR := by
        rw [Basis.sof_subst, hs₁]
      have hsvb' := evalS_substC hsvb hes
      have hsource := ValExpr.imageCoords_inferSpaceCtx_subst x arg leev₀ svb
      have hres := Basis.EvalBB.image_svds hs₀' hs₁'
        ((isStd_subst x n₁ _).symm ▸ hb₀)
        ((isStd_subst x n₁ _).symm ▸ hb₁) (opStep_substC he hes)
        (by
          simpa only [Basis.sof, Space.subst, Basis.sof_subst] using hsvb')
      simpa only [ValExpr.subst, ValTy.subst, hsource, ValExpr.imageCoords_subst] using hres
  | @Basis.EvalBB.dual_std _ b₀' leev htof hb₁ =>
      -- `dual b₀' ⟷ std (tof (dual b₀'))`: recurse on the body COB, commute the
      -- standard-basis-of-`tof` codomain via `std_subst` + `Basis.tof_subst`.
      have hrec := evalBB_substC hb₁ hes
      rw [std_subst, ← Basis.tof_subst] at hrec
      have hres := Basis.EvalBB.dual_std (tof_space_subst x n₁ htof) hrec
      simpa only [Basis.subst, ValExpr.subst, std_subst, ← Basis.tof_subst] using hres
  | @Basis.EvalBB.proj_ker_coker _ s₀ s₁ e s b₀ b₁ b₀' env₁ env₂ env₃
        sv₀ sv₁ sv sv' sv₀' hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₀' hcob hembd hproj =>
      -- domain-side projected-basis conversion. Recurse on every sub-derivation and
      -- align the `sof`/`lembd`/`lproj` premises; the nested `mtm`/`reshap` witness
      -- commutes structurally with `ValExpr.subst`.
      have hs' : Space.subst x n₁ s = .ker (Space.subst x n₁ s₀) (Space.subst x n₁ s₁) (Term.subst x n₁ e)
          ∨ Space.subst x n₁ s = .coker (Space.subst x n₁ s₀) (Space.subst x n₁ s₁) (Term.subst x n₁ e) :=
        hs.imp (fun h => by simp only [h, Space.subst]) (fun h => by simp only [h, Space.subst])
      have hsofb₀' : Basis.sof (Basis.subst x n₁ b₀) = Space.subst x n₁ s₀ := by
        rw [Basis.sof_subst, hsofb₀]
      have hsofb₁' : Basis.sof (Basis.subst x n₁ b₁) = Space.subst x n₁ s₁ := by
        rw [Basis.sof_subst, hsofb₁]
      have hsv₀'' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ b₀)) (ValSpace.subst x arg sv₀) := by
        rw [Basis.sof_subst]; exact evalS_substC hsv₀ hes
      have hsv₁'' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ b₁)) (ValSpace.subst x arg sv₁) := by
        rw [Basis.sof_subst]; exact evalS_substC hsv₁ hes
      have hsv'' : ValSpace.EvalS Ψ' (Space.subst x n₁ s) (ValSpace.subst x arg sv) :=
        evalS_substC hsv hes
      have hsv''' : ValSpace.EvalS Ψ' (Space.subst x n₁ s) (ValSpace.subst x arg sv') :=
        evalS_substC hsv' hes
      have hsv₀''' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ b₀')) (ValSpace.subst x arg sv₀') := by
        rw [Basis.sof_subst]; exact evalS_substC hsv₀' hes
      have hcob' := evalBB_substC hcob hes
      have hembd' := opStep_substC hembd hes
      have hproj' := opStep_substC hproj hes
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst] at hembd' hproj'
      have hres := Basis.EvalBB.proj_ker_coker hs' hsofb₀' hsofb₁'
        hsv₀'' hsv₁'' hsv'' hsv''' hsv₀''' hcob' hembd' hproj'
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst] using hres
  | @Basis.EvalBB.proj_img_coimg _ s₀ s₁ e s b₀ b₁ b₁' env₁ env₂ env₃
        sv₀ sv₁ sv sv' sv₁' hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₁' hcob hembd hproj =>
      -- codomain-side projected-basis conversion (symmetric to `proj_ker_coker`,
      -- the change-of-basis/embedding act on `b₁`/`b₁'`).
      have hs' : Space.subst x n₁ s = .img (Space.subst x n₁ s₀) (Space.subst x n₁ s₁) (Term.subst x n₁ e)
          ∨ Space.subst x n₁ s = .coimg (Space.subst x n₁ s₀) (Space.subst x n₁ s₁) (Term.subst x n₁ e) :=
        hs.imp (fun h => by simp only [h, Space.subst]) (fun h => by simp only [h, Space.subst])
      have hsofb₀' : Basis.sof (Basis.subst x n₁ b₀) = Space.subst x n₁ s₀ := by
        rw [Basis.sof_subst, hsofb₀]
      have hsofb₁' : Basis.sof (Basis.subst x n₁ b₁) = Space.subst x n₁ s₁ := by
        rw [Basis.sof_subst, hsofb₁]
      have hsv₀'' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ b₀)) (ValSpace.subst x arg sv₀) := by
        rw [Basis.sof_subst]; exact evalS_substC hsv₀ hes
      have hsv₁'' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ b₁)) (ValSpace.subst x arg sv₁) := by
        rw [Basis.sof_subst]; exact evalS_substC hsv₁ hes
      have hsv'' : ValSpace.EvalS Ψ' (Space.subst x n₁ s) (ValSpace.subst x arg sv) :=
        evalS_substC hsv hes
      have hsv''' : ValSpace.EvalS Ψ' (Space.subst x n₁ s) (ValSpace.subst x arg sv') :=
        evalS_substC hsv' hes
      have hsv₁''' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ b₁')) (ValSpace.subst x arg sv₁') := by
        rw [Basis.sof_subst]; exact evalS_substC hsv₁' hes
      have hcob' := evalBB_substC hcob hes
      have hembd' := opStep_substC hembd hes
      have hproj' := opStep_substC hproj hes
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst] at hembd' hproj'
      have hres := Basis.EvalBB.proj_img_coimg hs' hsofb₀' hsofb₁'
        hsv₀'' hsv₁'' hsv'' hsv''' hsv₁''' hcob' hembd' hproj'
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst] using hres
  | @Basis.EvalBB.terms_rref _ bsrc b' e es env₀ env₁ sv hbb hch hsv =>
      -- terms-basis RREFRep conversion: COB + chain OpStep + realization recurse
      -- structurally; the chain term/basis commute with `subst` via the
      -- `dsumChain` commutation lemmas (`Syntax.lean`).
      have hbb' := evalBB_substC hbb hes
      have hch' := opStep_substC hch hes
      rw [Term.subst_dsumChain, Basis.subst_dsumChain] at hch'
      have hch'' : ValExpr.OpStep Ψ'
          (Term.dsumChain (Term.subst x n₁ e) (es.map (Term.subst x n₁)))
          (Basis.dsumChain (Basis.subst x n₁ b') (es.map (Term.subst x n₁)).length)
          (ValExpr.subst x arg env₀) := by
        rw [List.length_map]; exact hch'
      have hsv' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ bsrc))
          (ValSpace.subst x arg sv) := by
        rw [Basis.sof_subst]; exact evalS_substC hsv hes
      have hres := Basis.EvalBB.terms_rref hbb' hch'' hsv'
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst, ValSpace.subst,
        Basis.sof_subst, List.map_cons] using hres
  | @Basis.EvalBB.refl _ bsrc sv htof hsv =>
      -- erratum-fix reflexivity: source = target = bsrc; the `idelta`/reshape
      -- witness commutes structurally; the realization recurses.
      have hsv' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ bsrc))
          (ValSpace.subst x arg sv) := by
        rw [Basis.sof_subst]; exact evalS_substC hsv hes
      have hres := Basis.EvalBB.refl (tof_space_subst x n₁ htof) hsv'
      simpa only [ValExpr.subst, ValTy.subst, ValSpace.subst] using hres
  | @Basis.EvalBB.proj_ker_coker_cod _ s₀ s₁ e s b₀ b₁ b₁' env₁ env₃
        sv₀ sv sv' hs hsofb₀ hsofb₁ hsofb₁' hsv₀ hsv hsv' hembd hproj =>
      -- codomain-annotation projected-basis conversion (P6a): same pattern as
      -- `proj_ker_coker` minus the COB factor; `Term.lembd`/`Term.lproj` are
      -- reducible abbreviations, so their subst behavior is the existing one.
      have hs' : Space.subst x n₁ s = .ker (Space.subst x n₁ s₀) (Space.subst x n₁ s₁) (Term.subst x n₁ e)
          ∨ Space.subst x n₁ s = .coker (Space.subst x n₁ s₀) (Space.subst x n₁ s₁) (Term.subst x n₁ e) :=
        hs.imp (fun h => by simp only [h, Space.subst]) (fun h => by simp only [h, Space.subst])
      have hsofb₀' : Basis.sof (Basis.subst x n₁ b₀) = Space.subst x n₁ s₀ := by
        rw [Basis.sof_subst, hsofb₀]
      have hsofb₁'' : Basis.sof (Basis.subst x n₁ b₁) = Space.subst x n₁ s₁ := by
        rw [Basis.sof_subst, hsofb₁]
      have hsofb₁''' : Basis.sof (Basis.subst x n₁ b₁') = Space.subst x n₁ s₁ := by
        rw [Basis.sof_subst, hsofb₁']
      have hsv₀'' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ b₀)) (ValSpace.subst x arg sv₀) := by
        rw [Basis.sof_subst]; exact evalS_substC hsv₀ hes
      have hsv'' : ValSpace.EvalS Ψ' (Space.subst x n₁ s) (ValSpace.subst x arg sv) :=
        evalS_substC hsv hes
      have hsv''' : ValSpace.EvalS Ψ' (Space.subst x n₁ s) (ValSpace.subst x arg sv') :=
        evalS_substC hsv' hes
      have hembd' := opStep_substC hembd hes
      have hproj' := opStep_substC hproj hes
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst] at hembd' hproj'
      have hres := Basis.EvalBB.proj_ker_coker_cod hs' hsofb₀' hsofb₁'' hsofb₁'''
        hsv₀'' hsv'' hsv''' hembd' hproj'
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst] using hres
  | @Basis.EvalBB.proj_img_coimg_dom _ s₀ s₁ e s b₀ b₁ b₀' env₁ env₃
        sv₁ sv sv' hs hsofb₀ hsofb₁ hsofb₀' hsv₁ hsv hsv' hembd hproj =>
      -- domain-annotation projected-basis conversion (P6a): mirror of
      -- `proj_ker_coker_cod` through the codomain ambient `b₁`.
      have hs' : Space.subst x n₁ s = .img (Space.subst x n₁ s₀) (Space.subst x n₁ s₁) (Term.subst x n₁ e)
          ∨ Space.subst x n₁ s = .coimg (Space.subst x n₁ s₀) (Space.subst x n₁ s₁) (Term.subst x n₁ e) :=
        hs.imp (fun h => by simp only [h, Space.subst]) (fun h => by simp only [h, Space.subst])
      have hsofb₀'' : Basis.sof (Basis.subst x n₁ b₀) = Space.subst x n₁ s₀ := by
        rw [Basis.sof_subst, hsofb₀]
      have hsofb₁'' : Basis.sof (Basis.subst x n₁ b₁) = Space.subst x n₁ s₁ := by
        rw [Basis.sof_subst, hsofb₁]
      have hsofb₀''' : Basis.sof (Basis.subst x n₁ b₀') = Space.subst x n₁ s₀ := by
        rw [Basis.sof_subst, hsofb₀']
      have hsv₁'' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ b₁)) (ValSpace.subst x arg sv₁) := by
        rw [Basis.sof_subst]; exact evalS_substC hsv₁ hes
      have hsv'' : ValSpace.EvalS Ψ' (Space.subst x n₁ s) (ValSpace.subst x arg sv) :=
        evalS_substC hsv hes
      have hsv''' : ValSpace.EvalS Ψ' (Space.subst x n₁ s) (ValSpace.subst x arg sv') :=
        evalS_substC hsv' hes
      have hembd' := opStep_substC hembd hes
      have hproj' := opStep_substC hproj hes
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst] at hembd' hproj'
      have hres := Basis.EvalBB.proj_img_coimg_dom hs' hsofb₀'' hsofb₁'' hsofb₀'''
        hsv₁'' hsv'' hsv''' hembd' hproj'
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst] using hres

/-- **OpStep substitution.** The variable cut and all structural/binder arms. -/
theorem opStep_substC {x : VName} {b₀ : Basis} {τv₀ : ValTy} {n₁ : Term} {arg : ValExpr}
    {Ψ Ψ' : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e b v) (hes : ESubst x b₀ τv₀ n₁ arg Ψ Ψ') :
    ValExpr.OpStep Ψ' (Term.subst x n₁ e) (Basis.subst x n₁ b) (ValExpr.subst x arg v) := by
  match h with
  | @ValExpr.OpStep.var _ z b v hlk =>
      by_cases hzx : z = x
      · subst hzx
        have hbb₀ : b = b₀ := hes.xonly b v hlk
        subst hbb₀
        obtain rfl : v = .var z τv₀ := (Option.some_inj.mp (hes.xbind.symm.trans hlk)).symm
        simp only [Term.subst, if_pos rfl, ValExpr.subst, if_pos rfl]
        exact hes.hcut
      · simp only [Term.subst, if_neg (Ne.symm hzx)]
        exact .var (hes.fwd z b v hzx hlk)
  | .scale he₀ he₁ => exact .scale (opStep_substC he₀ hes) (opStep_substC he₁ hes)
  | .dsumE he₀ he₁ htof₀ htof₁ =>
      exact .dsumE (opStep_substC he₀ hes) (opStep_substC he₁ hes)
        (tof_space_subst x n₁ htof₀) (tof_space_subst x n₁ htof₁)
  | .tprodE he₀ he₁ htof₀ htof₁ =>
      exact .tprodE (opStep_substC he₀ hes) (opStep_substC he₁ hes)
        (tof_space_subst x n₁ htof₀) (tof_space_subst x n₁ htof₁)
  | .cob htof₀ htof₁ he hbb hes' =>
      refine .cob (tof_space_subst x n₁ htof₀) (tof_space_subst x n₁ htof₁)
        (opStep_substC he hes) (evalBB_substC hbb hes) ?_
      rw [Basis.sof_subst]; exact evalS_substC hes' hes
  | .reshape_cob he hsrc htgt =>
      exact .reshape_cob (opStep_substC he hes)
        (by rw [Basis.tof_subst]; exact evalT_substC hsrc hes)
        (by rw [Basis.tof_subst]; exact evalT_substC htgt hes)
  | .appL_lin h₀ hsv₀ h₁ hsv₁ htof₁ =>
      simp only [Term.subst, ← Basis.sof_subst]
      refine .appL_lin (opStep_substC h₀ hes) ?_ (opStep_substC h₁ hes) ?_ (tof_space_subst x n₁ htof₁)
      · rw [Basis.sof_subst]; exact evalS_substC hsv₀ hes
      · rw [Basis.sof_subst]; exact evalS_substC hsv₁ hes
  | .appI_lin h₀ hsv h₁ =>
      simp only [Term.subst, ← Basis.sof_subst]
      refine .appI_lin (opStep_substC h₀ hes) ?_ (opStep_substC h₁ hes)
      rw [Basis.sof_subst]; exact evalS_substC hsv hes
  | .inner_std hb₀ hsv hsof =>
      simp only [Term.subst]
      refine .inner_std ((isStd_subst x n₁ _).symm ▸ hb₀) (evalS_substC hsv hes) ?_
      rw [Basis.sof_subst, hsof]
  | .pinvT_std he hb₀ hb₁ =>
      simp only [Term.subst, ← Basis.sof_subst]
      exact .pinvT_std (opStep_substC he hes)
        ((isStd_subst x n₁ _).symm ▸ hb₀) ((isStd_subst x n₁ _).symm ▸ hb₁)
  | .pinvD_std he hsofb₀ hb₀ hb₁ hsv₁ =>
      simp only [Term.subst, ← Basis.sof_subst]
      refine .pinvD_std (opStep_substC he hes) ?_
        ((isStd_subst x n₁ _).symm ▸ hb₀) ((isStd_subst x n₁ _).symm ▸ hb₁)
        (by rw [Basis.sof_subst]; exact evalS_substC hsv₁ hes)
      rw [Basis.sof_subst, hsofb₀]; rfl
  | .embed_ker hs₀ hs₁ hi₀ hi₁ he =>
      refine .embed_ker ?_ ?_ (opStep_substC hi₀ hes)
        (opStep_substC hi₁ hes) (opStep_substC he hes)
      · rw [Basis.sof_subst, hs₀]
      · rw [Basis.sof_subst, hs₁]
  | .embed_coker hs₀ hs₁ hi₀ hi₁ he =>
      refine .embed_coker ?_ ?_ (opStep_substC hi₀ hes)
        (opStep_substC hi₁ hes) (opStep_substC he hes)
      · rw [Basis.sof_subst, hs₀]
      · rw [Basis.sof_subst, hs₁]
  | .embed_img hs₀ hs₁ hi₀ hi₁ he =>
      refine .embed_img ?_ ?_ (opStep_substC hi₀ hes)
        (opStep_substC hi₁ hes) (opStep_substC he hes)
      · rw [Basis.sof_subst, hs₀]
      · rw [Basis.sof_subst, hs₁]
  | .embed_coimg hs₀ hs₁ hi₀ hi₁ he =>
      refine .embed_coimg ?_ ?_ (opStep_substC hi₀ hes)
        (opStep_substC hi₁ hes) (opStep_substC he hes)
      · rw [Basis.sof_subst, hs₀]
      · rw [Basis.sof_subst, hs₁]
  | .pinvT_gpinv he hi₀ hi₁ =>
      have hi₀' := opStep_substC hi₀ hes
      have hi₁' := opStep_substC hi₁ hes
      simp only [Term.subst, ← Basis.sof_subst] at hi₀' hi₁'
      simp only [Term.subst, ← Basis.sof_subst]
      exact .pinvT_gpinv (opStep_substC he hes) hi₀' hi₁'
  | .pinvD_gpinv he hsofb₀ hb₀ hi₀ hi₁ hsv₁ =>
      have hi₀' := opStep_substC hi₀ hes
      have hi₁' := opStep_substC hi₁ hes
      simp only [Term.subst, ← Basis.sof_subst] at hi₀' hi₁'
      simp only [Term.subst, ← Basis.sof_subst]
      refine .pinvD_gpinv (opStep_substC he hes) ?_
        ((isStd_subst x n₁ _).symm ▸ hb₀) hi₀' hi₁'
        (by rw [Basis.sof_subst]; exact evalS_substC hsv₁ hes)
      rw [Basis.sof_subst, hsofb₀]; rfl
  | @ValExpr.OpStep.nllam _ bz₀ bz₁ τ₀ τ₁ e' τv₀' τv₁' env hb₀ hb₁ h₀ L he h₁ =>
      -- LN binder arm: assemble the substituted `OpStep.nllam`. Domain `EvalT` by
      -- recursion; the cofinite body `OpStep` (he) and codomain `EvalT` (h₁) at a
      -- fresh `y` via the extended `ESubst`, commuting `subst` past `openVar` on
      -- the source term/basis (`Term`/`Basis.subst_openRec`), the value body
      -- (`ValExpr.subst_openRec`) and the codomain type (`ValTy.subst_openRec`).
      refine ValExpr.OpStep.nllam
        ((Basis.tof_subst x n₁ bz₀).trans (congrArg (Ty.subst x n₁) hb₀))
        ((Basis.tof_subst x n₁ bz₁).trans (congrArg (Ty.subst x n₁) hb₁))
        (evalT_substC h₀ hes)
        (L ∪ {x} ∪ EvalCtx.avoid Ψ ∪ EvalCtx.avoid Ψ') (fun y hy => ?_) (fun y hy => ?_)
      · -- body `OpStep`.
        simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
        obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
        have hes' := ESubst.extend (bz := bz₀) (tv0z := τv₀') hes hyx
          (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
        have hrec := opStep_substC (he y hyL) hes'
        have hsrcT : Term.subst x n₁ (Term.openVar y e') = Term.openVar y (Term.subst x n₁ e') := by
          simp only [Term.openVar, Term.subst_openRec x n₁ hes.lcn e' 0 (.var y),
            Term.subst, if_neg (Ne.symm hyx)]
        have hsrcB : Basis.subst x n₁ (Basis.openVar y bz₁) = Basis.openVar y (Basis.subst x n₁ bz₁) := by
          simp only [Basis.openVar, Basis.subst_openRec x n₁ hes.lcn bz₁ 0 (.var y),
            Term.subst, if_neg (Ne.symm hyx)]
        have hvalE : ValExpr.subst x arg (ValExpr.openVar y τv₀' env)
            = ValExpr.openVar y (ValTy.subst x arg τv₀') (ValExpr.subst x arg env) := by
          simp only [ValExpr.openVar, ValExpr.subst_openRec x arg hes.lcarg env 0 (.var y τv₀'),
            ValExpr.subst, if_neg hyx]
        rw [hsrcT, hsrcB, hvalE] at hrec
        exact hrec
      · -- codomain `EvalT` (identical to the evalT_substC piTy body).
        simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
        obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
        have hes' := ESubst.extend (bz := bz₀) (tv0z := τv₀') hes hyx
          (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
        have hrec := evalT_substC (h₁ y hyL) hes'
        have hsrc : Ty.subst x n₁ (Ty.openVar y τ₁) = Ty.openVar y (Ty.subst x n₁ τ₁) := by
          simp only [Ty.openVar, Ty.subst_openRec x n₁ hes.lcn τ₁ 0 (.var y),
            Term.subst, if_neg (Ne.symm hyx)]
        have hval : ValTy.subst x arg (ValTy.openVar y τv₀' τv₁')
            = ValTy.openVar y (ValTy.subst x arg τv₀') (ValTy.subst x arg τv₁') := by
          simp only [ValTy.openVar, ValTy.subst_openRec x arg hes.lcarg τv₁' 0 (.var y τv₀'),
            ValExpr.subst, if_neg hyx]
        rw [hsrc, hval] at hrec
        exact hrec
  | @ValExpr.OpStep.appN_val _ bb₀ bb₁ m₀ m₁ ev₀ ev₁ tvout h₀ h₁ hout =>
      -- plain function eval: function/argument OpSteps recurse structurally; the
      -- result basis is an `instantiate`, commuted by `Basis.subst_openRec` (lcn);
      -- the result-type premise recurses via `evalT_substC`, re-aligned through
      -- `Basis.tof_subst` + the same instantiate-commutation.
      have h₀' := opStep_substC h₀ hes
      have h₁' := opStep_substC h₁ hes
      have hb : Basis.subst x n₁ (Basis.instantiate m₁ bb₁)
          = Basis.instantiate (Term.subst x n₁ m₁) (Basis.subst x n₁ bb₁) :=
        Basis.subst_openRec x n₁ hes.lcn bb₁ 0 m₁
      have hout' := evalT_substC hout hes
      rw [← Basis.tof_subst, hb] at hout'
      simp only [Term.subst, Basis.subst, ValExpr.subst] at h₀' h₁' ⊢
      rw [hb, ValExpr.subst_applyAt hes.lcarg
        (opStep_inferType_subst hes.lcarg h₀ hes.htype)
        (opStep_inferType_subst hes.lcarg h₁ hes.htype)]
      exact ValExpr.OpStep.appN_val h₀' h₁' hout'
  | @ValExpr.OpStep.frame_reanchor _ bz₀ bz₀' bz₁ m₀ leev env₁ tv0 tvd tv1
        h₀ htof hfn hdom L hx hcod =>
      -- frame re-anchoring: structural premises recurse (the `tof` equalities
      -- transport via `Basis.tof_subst`); the two under-binder premises follow
      -- the `nllam` binder template (`ESubst.extend` at fresh `y` + the LN
      -- subst/open commutations).
      have hfn' := opStep_substC hfn hes
      simp only [ValExpr.subst, ValExpr.subst_applyValue
        (opStep_inferType_subst hes.lcarg hfn hes.htype)
        (inferType_subst_reshap hes.lcarg)]
      refine ValExpr.OpStep.frame_reanchor
        (by rw [Basis.tof_subst]; exact evalT_substC h₀ hes)
        (by rw [Basis.tof_subst, Basis.tof_subst, htof])
        hfn'
        (by rw [Basis.tof_subst]; exact evalT_substC hdom hes)
        (L ∪ {x} ∪ EvalCtx.avoid Ψ ∪ EvalCtx.avoid Ψ') (fun y hy => ?_) (fun y hy => ?_)
      · -- placeholder realization `hx`.
        simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
        obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
        have hes' := ESubst.extend (bz := bz₀) (tv0z := tv0) hes hyx
          (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
        have hrec := opStep_substC (hx y hyL) hes'
        have hsrcT : Term.subst x n₁ (Term.var y) = Term.var y := by
          simp only [Term.subst, if_neg (Ne.symm hyx)]
        have hvalE : ValExpr.subst x arg (ValExpr.openVar y tv0 env₁)
            = ValExpr.openVar y (ValTy.subst x arg tv0) (ValExpr.subst x arg env₁) := by
          simp only [ValExpr.openVar, ValExpr.subst_openRec x arg hes.lcarg env₁ 0 (.var y tv0),
            ValExpr.subst, if_neg hyx]
        rw [hsrcT, hvalE] at hrec
        exact hrec
      · -- anchored codomain `hcod`.
        simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
        obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
        have hes' := ESubst.extend (bz := bz₀) (tv0z := tv0) hes hyx
          (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
        have hrec := evalT_substC (hcod y hyL) hes'
        have hsrc : Ty.subst x n₁ (Ty.openVar y (Basis.tof bz₁))
            = Ty.openVar y (Basis.tof (Basis.subst x n₁ bz₁)) := by
          simp only [Ty.openVar, Ty.subst_openRec x n₁ hes.lcn (Basis.tof bz₁) 0 (.var y),
            Term.subst, if_neg (Ne.symm hyx), Basis.tof_subst]
        have hval : ValTy.subst x arg (ValTy.openVar y tv0 tv1)
            = ValTy.openVar y (ValTy.subst x arg tv0) (ValTy.subst x arg tv1) := by
          simp only [ValTy.openVar, ValTy.subst_openRec x arg hes.lcarg tv1 0 (.var y tv0),
            ValExpr.subst, if_neg hyx]
        rw [hsrc, hval] at hrec
        exact hrec
  | @ValExpr.OpStep.frame_eta _ bz₀ bz₁ m₀ tv0 tv1 env h₀ L he h₁ =>
      -- frame η-reconstruction: the `nllam` binder template, with the body
      -- premise's source `.appN m₀ (.var y)` and basis `openVar y bz₁`.
      refine ValExpr.OpStep.frame_eta
        (by rw [Basis.tof_subst]; exact evalT_substC h₀ hes)
        (L ∪ {x} ∪ EvalCtx.avoid Ψ ∪ EvalCtx.avoid Ψ') (fun y hy => ?_) (fun y hy => ?_)
      · -- body application `he`.
        simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
        obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
        have hes' := ESubst.extend (bz := bz₀) (tv0z := tv0) hes hyx
          (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
        have hrec := opStep_substC (he y hyL) hes'
        have hsrcT : Term.subst x n₁ (Term.appN m₀ (.var y))
            = Term.appN (Term.subst x n₁ m₀) (.var y) := by
          simp only [Term.subst, if_neg (Ne.symm hyx)]
        have hsrcB : Basis.subst x n₁ (Basis.openVar y bz₁)
            = Basis.openVar y (Basis.subst x n₁ bz₁) := by
          simp only [Basis.openVar, Basis.subst_openRec x n₁ hes.lcn bz₁ 0 (.var y),
            Term.subst, if_neg (Ne.symm hyx)]
        have hvalE : ValExpr.subst x arg (ValExpr.openVar y tv0 env)
            = ValExpr.openVar y (ValTy.subst x arg tv0) (ValExpr.subst x arg env) := by
          simp only [ValExpr.openVar, ValExpr.subst_openRec x arg hes.lcarg env 0 (.var y tv0),
            ValExpr.subst, if_neg hyx]
        rw [hsrcT, hsrcB, hvalE] at hrec
        exact hrec
      · -- anchored codomain `h₁` (identical to the `frame_reanchor` hcod arm).
        simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
        obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
        have hes' := ESubst.extend (bz := bz₀) (tv0z := tv0) hes hyx
          (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
        have hrec := evalT_substC (h₁ y hyL) hes'
        have hsrc : Ty.subst x n₁ (Ty.openVar y (Basis.tof bz₁))
            = Ty.openVar y (Basis.tof (Basis.subst x n₁ bz₁)) := by
          simp only [Ty.openVar, Ty.subst_openRec x n₁ hes.lcn (Basis.tof bz₁) 0 (.var y),
            Term.subst, if_neg (Ne.symm hyx), Basis.tof_subst]
        have hval : ValTy.subst x arg (ValTy.openVar y tv0 tv1)
            = ValTy.openVar y (ValTy.subst x arg tv0) (ValTy.subst x arg tv1) := by
          simp only [ValTy.openVar, ValTy.subst_openRec x arg hes.lcarg tv1 0 (.var y tv0),
            ValExpr.subst, if_neg hyx]
        rw [hsrc, hval] at hrec
        exact hrec
  | @ValExpr.OpStep.add _ e₀ e₁ b sv v₀ v₁ htof hsv he₀ he₁ =>
      have hsv' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ b))
          (ValSpace.subst x arg sv) := by
        rw [Basis.sof_subst]
        exact evalS_substC hsv hes
      exact ValExpr.OpStep.add (tof_space_subst x n₁ htof) hsv'
        (opStep_substC he₀ hes) (opStep_substC he₁ hes)
  | @ValExpr.OpStep.llam_assemble _ bz' bz e' sv' sv env htof' hsv' hsv L hfam =>
      -- linear-λ assembly: the family premise recurses under the GENERALIZED
      -- `ESubst.extend_val` (the binder stores `.delta i sv'`, not a `.var`
      -- placeholder); the vsum value's list distributes via
      -- `substList_eq_map` + `List.map_ofFn`.
      have hsv'' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ bz'))
          (ValSpace.subst x arg sv') := by
        rw [Basis.sof_subst]; exact evalS_substC hsv' hes
      have hsvr : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ bz))
          (ValSpace.subst x arg sv) := by
        rw [Basis.sof_subst]; exact evalS_substC hsv hes
      have hdof : ValSpace.dofUB (ValSpace.subst x arg sv') =
          ValSpace.dofUB sv' := ValSpace.dofUB_subst x arg sv'
      let envT : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')) → ValExpr :=
        fun i => ValExpr.subst x arg (env (Fin.cast hdof i))
      have hfamT : ∀ y,
          y ∉ (L ∪ {x} ∪ EvalCtx.avoid Ψ ∪ EvalCtx.avoid Ψ') →
          ∀ i : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')),
            ValExpr.OpStep
              (Ψ'.extend y (Basis.subst x n₁ bz')
                (.delta i.val (ValSpace.subst x arg sv')))
              (Term.openVar y (Term.subst x n₁ e'))
              (Basis.subst x n₁ bz) (envT i) := by
        intro y hy i
        simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
        obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
        let j : Fin (ValSpace.dofUB sv') := Fin.cast hdof i
        have hes' := ESubst.extend_val (bz := bz') (w := .delta j.val sv') hes hyx
          (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
          (by simp only [ValExpr.subst, ValExpr.inferSpace])
          (by simp only [InferTypeSubstAt, ValExpr.subst, ValExpr.inferType, ValTy.subst])
        have hrec := opStep_substC (hfam y hyL j) hes'
        have hsrcT : Term.subst x n₁ (Term.openVar y e')
            = Term.openVar y (Term.subst x n₁ e') := by
          simp only [Term.openVar, Term.subst_openRec x n₁ hes.lcn e' 0 (.var y),
            Term.subst, if_neg (Ne.symm hyx)]
        rw [hsrcT] at hrec
        simpa only [envT, j, Fin.cast, ValExpr.subst] using hrec
      have hres := ValExpr.OpStep.llam_assemble (Ψ := Ψ')
        (sv' := ValSpace.subst x arg sv') (env := envT)
        (tof_space_subst x n₁ htof') hsv'' hsvr
        (L ∪ {x} ∪ EvalCtx.avoid Ψ ∪ EvalCtx.avoid Ψ')
        hfamT
      have hlist :
          List.ofFn (fun i : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')) =>
            ValExpr.tprodE (.delta i.val (ValSpace.subst x arg sv'))
              (.reshap (envT i) (.space (ValSpace.subst x arg sv))
                (.space (ValSpace.subst x arg sv)))) =
          List.ofFn (fun i : Fin (ValSpace.dofUB sv') =>
            ValExpr.tprodE (.delta i.val (ValSpace.subst x arg sv'))
              (.reshap (ValExpr.subst x arg (env i)) (.space (ValSpace.subst x arg sv))
                (.space (ValSpace.subst x arg sv)))) := by
        rw [List.ofFn_congr hdof]
        congr 1
      rw [hlist] at hres
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst]
      simpa only [envT, ValSpace.dofUB_subst, Function.comp_def, ValExpr.subst_reshapBase, ValExpr.subst_sumAt,
        ValExpr.subst, ValExpr.substList_eq_map, List.map_ofFn,
        ValSpace.subst, ValTy.subst]
        using hres
  | @ValExpr.OpStep.llam_assemble_real _ bz' e' sv' env htof' hsv' L hfam =>
      -- ℝ/dual variant: identical structure (basis `.one` and the scalar
      -- reshape annotation are subst-invariant).
      have hsv'' : ValSpace.EvalS Ψ' (Basis.sof (Basis.subst x n₁ bz'))
          (ValSpace.subst x arg sv') := by
        rw [Basis.sof_subst]; exact evalS_substC hsv' hes
      have hdof : ValSpace.dofUB (ValSpace.subst x arg sv') =
          ValSpace.dofUB sv' := ValSpace.dofUB_subst x arg sv'
      let envT : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')) → ValExpr :=
        fun i => ValExpr.subst x arg (env (Fin.cast hdof i))
      have hfamT : ∀ y,
          y ∉ (L ∪ {x} ∪ EvalCtx.avoid Ψ ∪ EvalCtx.avoid Ψ') →
          ∀ i : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')),
            ValExpr.OpStep
              (Ψ'.extend y (Basis.subst x n₁ bz')
                (.delta i.val (ValSpace.subst x arg sv')))
              (Term.openVar y (Term.subst x n₁ e')) .one (envT i) := by
        intro y hy i
        simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
        obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
        let j : Fin (ValSpace.dofUB sv') := Fin.cast hdof i
        have hes' := ESubst.extend_val (bz := bz') (w := .delta j.val sv') hes hyx
          (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
          (by simp only [ValExpr.subst, ValExpr.inferSpace])
          (by simp only [InferTypeSubstAt, ValExpr.subst, ValExpr.inferType, ValTy.subst])
        have hrec := opStep_substC (hfam y hyL j) hes'
        have hsrcT : Term.subst x n₁ (Term.openVar y e')
            = Term.openVar y (Term.subst x n₁ e') := by
          simp only [Term.openVar, Term.subst_openRec x n₁ hes.lcn e' 0 (.var y),
            Term.subst, if_neg (Ne.symm hyx)]
        rw [hsrcT] at hrec
        simpa only [envT, j, Fin.cast, ValExpr.subst, Basis.subst] using hrec
      have hres := ValExpr.OpStep.llam_assemble_real (Ψ := Ψ')
        (sv' := ValSpace.subst x arg sv') (env := envT)
        (tof_space_subst x n₁ htof') hsv''
        (L ∪ {x} ∪ EvalCtx.avoid Ψ ∪ EvalCtx.avoid Ψ')
        hfamT
      have hlist :
          List.ofFn (fun i : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')) =>
            ValExpr.scale
              (.reshap (envT i) (.space .real) (.space .real))
              (.delta i.val (ValSpace.subst x arg sv'))) =
          List.ofFn (fun i : Fin (ValSpace.dofUB sv') =>
            ValExpr.scale
              (.reshap (ValExpr.subst x arg (env i)) (.space .real) (.space .real))
              (.delta i.val (ValSpace.subst x arg sv'))) := by
        rw [List.ofFn_congr hdof]
        congr 1
      rw [hlist] at hres
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst, Space.subst]
      simpa only [envT, ValSpace.dofUB_subst, Function.comp_def, ValExpr.subst_reshapBase, ValExpr.subst_sumAt,
        ValExpr.subst, ValExpr.substList_eq_map, List.map_ofFn,
        ValSpace.subst, ValTy.subst]
        using hres
  | .zero htof hsv =>
      -- erratum-fix zero literal: `Term.subst` maps `.zero s ↦ .zero (subst s)`,
      -- so the source-side space substitutes and re-aligns via `Basis.sof_subst`;
      -- the realization recurses.
      simp only [Term.subst, ValExpr.subst, ← Basis.sof_subst]
      exact .zero (tof_space_subst x n₁ htof)
        (by rw [Basis.sof_subst]; exact evalS_substC hsv hes)
  | .rlit r =>
      -- erratum-fix real literal: source/basis/value are all subst-invariant.
      simp only [Term.subst, ValExpr.subst, Basis.subst]
      exact .rlit r

end

end GLang
