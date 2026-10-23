import GLang.Operational.Supporting.Operational

namespace GLang
namespace Operational.Unchecked

/-- Preservation for the literal result of a supplied ordinary space
evaluation.  A semantic-free context creation history supplies the runtime
invariants needed by the shared preservation induction. -/
theorem EvalS.preservation
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {s : GLang.Space} {sv : ValSpace}
    (hhistory : V2.CtxTele Delta Gamma Psi)
    (hsource : SValid Gamma s)
    (hstep : Operational.Unchecked.EvalS Psi s sv) :
    Nonempty (ValSValidC sv) /\
      ValSpace.fv sv ⊆ Psi.keyNames := by
  have hplus : V2.EvalCtxValidPlus Psi := hhistory.evalCtxValidPlus
  have hrho : V2.RhoValid Psi Psi.keyNames := hplus.rhoValid_keyNames
  have hkeys : V2.KeyScope Psi Psi.keyNames := V2.keyScope_keyNames Psi
  exact V2.preservation_master.1 hstep Delta Gamma Psi.keyNames
    hplus hrho hkeys hsource

end Operational.Unchecked
end GLang
