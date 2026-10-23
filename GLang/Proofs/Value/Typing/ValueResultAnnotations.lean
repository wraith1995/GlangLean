import GLang.Proofs.Value.Runtime.RuntimeValueEmbedding
import GLang.Proofs.Value.Runtime.RuntimeValueResultAnnotations

namespace GLang
open ValueDependency

/-- Strict typing has the same annotation-support property as runtime typing. -/
theorem ValHasType.resultAnnotations {ε : ValCtx} (hc : ValCtxValid ε)
    {e : ValExpr} {t : ValTy} (h : ValHasType ε e t) :
    typeAnnotations t ⊆ exprAnnotations e :=
  h.runtime.resultAnnotations hc.runtime

end GLang
