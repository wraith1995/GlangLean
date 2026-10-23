import GLang.Surface.Judgments

namespace GLang.Surface

inductive InductiveCtxWF : LCtx → NLCtx → Prop where
  | empty : InductiveCtxWF ∅ ∅
  | linear {Δ ε x s} (ctx : InductiveCtxWF Δ ε)
      (freshLin : x ∉ Δ) (freshNL : x ∉ ε)
      (scope : ∀ y ∈ Space.fv s, y ∈ ε) (valid : SValid ε s) :
      InductiveCtxWF (Finmap.insert x s Δ) ε
  | nonlinear {Δ ε x τ k} (ctx : InductiveCtxWF Δ ε)
      (freshLin : x ∉ Δ) (freshNL : x ∉ ε)
      (scope : ∀ y ∈ Ty.fv τ, y ∈ ε) (valid : TValid ε τ k) :
      InductiveCtxWF Δ (Finmap.insert x τ ε)

end GLang.Surface
