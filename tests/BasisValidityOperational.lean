import GLang.Artifact
import Lean

/-! Basis validity is the only hereditary condition exposed by checked type
realization. Space-only progress uses the ordinary type-of-basis equality. -/
open GLang GLang.RawCertifiedOperational

example {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {sv : ValSpace}
    (valid : Basis.BasisValid Gamma b)
    (space : Basis.tof b = .space (Basis.sof b))
    (step : C.Space Gamma Psi (Basis.sof b) sv) :
    C.TyAt Gamma Psi b (.space sv) :=
  .space space valid step

example {Gamma : NLCtx} {b : Basis} (valid : Basis.BasisValid Gamma b) :
    Basis.IsSpaceBasis b ↔ Basis.tof b = .space (Basis.sof b) :=
  ⟨Basis.IsSpaceBasis.tof_eq, valid.isTyBasis.toIsSpaceBasis_of_tof_eq⟩

example {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (history : Operational.ContextHistory Delta Gamma GammaV Psi)
    (valid : Basis.BasisValid Gamma b)
    (space : Basis.tof b = .space (Basis.sof b)) :
    ∃ env, Operational.Cob Gamma Psi b env (Basis.std (Basis.tof b)) :=
  Metatheory.checkedBasisProgress history valid space

#print axioms Metatheory.progress
#print axioms Metatheory.checkedProgressAdequacy
#print axioms Metatheory.termAdequacy
#print axioms Metatheory.checkedCobProgress
