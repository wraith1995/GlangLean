import GLang.Proofs.Value.Presentation.PaperValueDependentCoherence

namespace GLang.PaperValueDomains

def World.rawPush (w : World) (τ : ValTy) (v : ValValSem) : World :=
  ⟨w.env, τ :: w.types, v :: w.values⟩

end GLang.PaperValueDomains
