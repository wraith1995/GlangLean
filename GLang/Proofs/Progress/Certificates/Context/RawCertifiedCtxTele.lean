import GLang.Proofs.Adequacy.Raw.Context.RawConsistent
import GLang.Proofs.Progress.Supporting.ProgressTele

/-!
# Raw consistency projects to the operational telescope

The joint `V2.CtxTele` is the semantic-free operational creation history
already used by ordinary progress.  Its value-FV premise permits the newly
created key, so the explicit self-placeholder accepted by `RawConsistent`
fits without a second history relation.

`RawConsistent` forgets to `V2.CtxTele`.  Only the
operational/static constructor fields are inspected; all denotational and
oracle-indexed fields are discarded.
-/

namespace GLang
namespace RawCertifiedCtxTele

theorem RawConsistent.ctxTele
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    V2.CtxTele Delta Gamma Psi := by
  induction h with
  | empty => exact .empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hprefix hx htof hb hTy hinfer hinferSpace hfvv hlc hnr
      hxs hden hagree hdims ih =>
      refine .extend_lin ih ⟨hx.1, hx.2⟩ (.ofSpace ?_ htof) hb htof
      refine {
        typeRealized := ?_
        valueScoped := hfvv
        locallyClosed := hlc }
      · rw [hinfer]
        exact hTy
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hprefix hx hb hTy hinfer hinferSpace hfvv hlc hnr
      hxs hden hagree hdims hcreation ih =>
      exact .extend_nlin ih ⟨hx.1, hx.2⟩ hcreation hb
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hprefix hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc
      hxs hden hagree hdims hcreation ih =>
      exact .extend_rep ih hsource hkey hcreation hb

end RawCertifiedCtxTele
end GLang
