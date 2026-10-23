/-
Regularity: a well-typed term / well-formed space / type is locally closed.

  • `SValid ε s   → Space.lc s`
  • `TValid ε τ k → Ty.lc τ`
  • `SubType ε s₀ s₁ → Space.lc s₀`  (lc of the FFS subspace)
  • `HasType Δ ε e τ → Term.lc e`

Mutual recursion over the four `Type`-valued typing judgments (defined as one
mutual block in `Typing.lean`). The binder rules (`TValid.piTy`,
`HasType.llam_real`/`llam_tensor`/`nllam`) are cofinite, so their `lc` witnesses
reuse the cofinite premise pointwise (`fun y hy => … (hbody y hy)`), exactly
mirroring `SourceLN`'s `openRec_lc`.

Used by `Soundness.lean`: the denotation `subst`/`bridge` lemmas
(`Substitution.lean`) need `Term.lc` of the substituted argument (`app_nonlinear`)
and of the opened binder bodies. -/

import GLang.Annotated.Binding
import GLang.Annotated.Judgments
import GLang.Proofs.Source.SourceLN

namespace GLang

mutual

theorem SValid.lc {ε : NLCtx} {s : Space} : SValid ε s → Space.lc s
  | .empty => .empty
  | .real  => .real
  | .dual d => .dual (SValid.lc d)
  | .dsum d₀ d₁ => .dsum (SValid.lc d₀) (SValid.lc d₁)
  | .tprod d₀ d₁ => .tprod (SValid.lc d₀) (SValid.lc d₁)
  | .ker hs₀ hs₁ he => .ker (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc he)
  | .coker hs₀ hs₁ he => .coker (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc he)
  | .img hs₀ hs₁ he => .img (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc he)
  | .coimg hs₀ hs₁ he => .coimg (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc he)

theorem TValid.lc {ε : NLCtx} {τ : Ty} {k : Kind} : TValid ε τ k → Ty.lc τ
  | .space hs => .space (SValid.lc hs)
  | .piTy L hτ₀ hbody => .piTy L (TValid.lc hτ₀) (fun y hy => TValid.lc (hbody y hy))

theorem SubType.lc {ε : NLCtx} {s₀ s₁ : Space} : SubType ε s₀ s₁ → Space.lc s₀
  | .sub_ker hs₀ hs₁ he => .ker (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc he)
  | .sub_coker hs₀ hs₁ he => .coker (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc he)
  | .sub_img hs₀ hs₁ he => .img (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc he)
  | .sub_coimg hs₀ hs₁ he => .coimg (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc he)

theorem HasType.lc {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty} : HasType Δ ε e τ → Term.lc e
  | .zero hs => .zero (SValid.lc hs)
  | .smul _ _ h₀ h₁ => .smul (HasType.lc h₀) (HasType.lc h₁)
  | .add _ h₀ h₁ => .add (HasType.lc h₀) (HasType.lc h₁)
  | .inner hs => .inner (SValid.lc hs)
  | .real_lit _ => .real
  | .app_linear hs₀ hs₁ _ h₀ h₁ =>
      .appL (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc h₀) (HasType.lc h₁)
  | .app_inner hs _ h₀ h₁ => .appI (SValid.lc hs) (HasType.lc h₀) (HasType.lc h₁)
  | .app_nonlinear h₀ h₁ => .appN (HasType.lc h₀) (HasType.lc h₁)
  | .var_lin => .var
  | .var_nlin _ => .var
  | .pinv_tensor hs₀ hs₁ he => .pinvT (SValid.lc hs₀) (SValid.lc hs₁) (HasType.lc he)
  | .pinv_dual hs he => .pinvD (SValid.lc hs) (HasType.lc he)
  | .promote _ _ _ _ he => HasType.lc he
  | .dsumE _ _ h₀ h₁ => .dsumE (HasType.lc h₀) (HasType.lc h₁)
  | .tprodE _ _ _ h₀ h₁ => .tprodE (HasType.lc h₀) (HasType.lc h₁)
  | .llam_real L hs hbody =>
      .llam L (SValid.lc hs) Space.lc.real (fun y hy => HasType.lc (hbody y hy))
  | .llam_tensor L _ hs₀ hs hbody =>
      .llam L (SValid.lc hs₀) (SValid.lc hs) (fun y hy => HasType.lc (hbody y hy))
  | .embed hsub => .embed (SubType.lc hsub)
  | .nllam L hτ hbody =>
      .nllam L (match TValid.lc hτ with | .piTy _ h₀ _ => h₀)
        (fun y hy => HasType.lc (hbody y hy))

end

end GLang
