import GLang.Graded.Regularity

namespace GLang.Graded

open GLang

noncomputable def tvalid_instantiate {ε : NLCtx} {τ₀ τ₁ : Ty} {k₀ k₁ : Kind} {e₁ : Term}
    (hpi : TValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁)) (harg : HasType ∅ ε e₁ τ₀) :
    TValid ε (Ty.instantiate e₁ τ₁) k₁ :=
  tvalidBwd (gtvInst (tvalidBridge hpi) (hasTypeBridge (CtxDisj.empty ε) harg))
    (fun _ _ hh => hh)

end GLang.Graded
