import GLang.Proofs.Value.Runtime.RuntimeValueEmbedding
import GLang.Proofs.Value.Runtime.RuntimeValueCorrespondence
import GLang.Proofs.Value.Partial.PartialValueCorrespondence

namespace GLang

theorem PartialValueDomains.PartialEnvWF.runtime
    (h : PartialValueDomains.PartialEnvWF orc ε ρ) : RuntimeValue.PartialEnvWF orc ε ρ :=
  ⟨⟨h.1.some.runtime⟩,h.2⟩

end GLang
