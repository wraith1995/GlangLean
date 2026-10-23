import GLang.Proofs.Progress.Supporting.CategoryProgress
import GLang.Proofs.Progress.Certificates.RawCertifiedFrameApplicationReanchor

/-!
# Deriving the nonlinear-application codomain premise

The instantiated codomain realization is an output of progress, not an
independent existence assumption. These derived rules keep the supplied
function and argument values literally, choosing the target of the explicit result reshape.
The primitive `appN_val` still checks that chosen annotation; removing that
check while universally quantifying its annotation would be unsound.
-/

namespace GLang
namespace Operational

/-- Source argument typing and frame validity imply existence of a realized
substituted codomain under the ordinary public context-history assumption. -/
theorem applicationCodomain_of_typing
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {n1 : GLang.Term}
    (history : V2.CtxTele Delta Gamma Psi)
    (frameValid : Basis.BasisValid Gamma (.frame b0 b1))
    (argumentTyped : HasType ∅ Gamma n1 (Basis.tof b0)) :
    ∃ tauOut, Unchecked.EvalT Psi (Basis.instantiate n1 b1).tof tauOut := by
  obtain ⟨_, _, k0, k1, ⟨hpi⟩⟩ := frameValid.frame_inv
  have hinst := Graded.tvalid_instantiate hpi argumentTyped
  obtain ⟨tauOut, hout⟩ := Ty.progress history hinst
  refine ⟨tauOut, ?_⟩
  simpa only [Basis.instantiate, Basis.tof_openRec, GLang.Ty.instantiate] using
    hout.toUnchecked

/-- A derived ordinary application rule with no codomain-evaluation premise.
Only the result reshape target is chosen; the supplied operands are retained. -/
theorem Unchecked.OpStep.appN_of_typing
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {n0 n1 : GLang.Term}
    {vFun vArg : ValExpr}
    (history : V2.CtxTele Delta Gamma Psi)
    (frameValid : Basis.BasisValid Gamma (.frame b0 b1))
    (argumentTyped : HasType ∅ Gamma n1 (Basis.tof b0))
    (hfun : Unchecked.OpStep Psi n0 (.frame b0 b1) vFun)
    (harg : Unchecked.OpStep Psi n1 b0 vArg) :
    ∃ tauOut, Unchecked.OpStep Psi (.appN n0 n1)
      (Basis.instantiate n1 b1) (.applyAt vFun vArg tauOut) := by
  obtain ⟨tauOut, hout⟩ := applicationCodomain_of_typing history frameValid argumentTyped
  exact ⟨tauOut, .appN_val hfun harg hout⟩

/-- The checked version derives an exact-basis codomain certificate by
substitution. -/
theorem Term.appN_of_history
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {n0 n1 : GLang.Term}
    {vFun vArg : ValExpr} {tauFun tauArg : ValTy}
    (history : V2.CtxTele Delta Gamma Psi)
    (hfun : Operational.Term ∅ Gamma Psi n0 (.frame b0 b1) vFun tauFun)
    (harg : Operational.Term ∅ Gamma Psi n1 b0 vArg tauArg) :
    ∃ tauOut, Operational.Term ∅ Gamma Psi (.appN n0 n1)
      (Basis.instantiate n1 b1) (.applyAt vFun vArg tauOut) tauOut := by
  obtain ⟨tauV0, tauV1, rfl, hdom, L, hcod⟩ :=
    RawCertifiedProgressScratch.checkedTyAt_frame_inv_full hfun.tyAt
  obtain ⟨_, tauOut, _, hout⟩ :=
    RawCertifiedPiBasisTransport.checkedCodomainCut
      RawCertifiedOperational.checkedTyAtAppCut
      (history.pCarrier V2.pi_entry_transport) history.varsCovered.drop_lin
      (RawCertifiedWorldBinderProgress.ctxWF_dropLin
        (RawCertifiedCtxTeleProgress.ctxWFPrime history)) harg hdom L hcod
  have htyped : Nonempty (HasType ∅ Gamma (.appN n0 n1)
      (Basis.tof (Basis.instantiate n1 b1))) := by
    refine ⟨?_⟩
    simpa only [Basis.tof, Basis.instantiate, Basis.tof_openRec, GLang.Ty.instantiate]
      using HasType.app_nonlinear hfun.hasType.some harg.hasType.some
  exact ⟨tauOut, RawCertifiedOperational.C.Term.appN_val
    htyped hout.basisValid hout hfun harg⟩

/-- An ordinary application constructed with its internally selected reshape target.
The source and the two operand values remain parameters, so this package cannot
silently replace either operand or change the requested result basis. -/
structure Unchecked.ApplicationResult
    (Psi : EvalCtx) (n0 n1 : GLang.Term) (b0 b1 : Basis)
    (vFun vArg : ValExpr) where
  resultType : ValTy
  derivation : Unchecked.OpStep Psi (.appN n0 n1)
    (Basis.instantiate n1 b1) (.applyAt vFun vArg resultType)

/-- Value expression produced by the ordinary application constructor. -/
def Unchecked.ApplicationResult.value
    {Psi : EvalCtx} {n0 n1 : GLang.Term} {b0 b1 : Basis} {vFun vArg : ValExpr}
    (result : Unchecked.ApplicationResult Psi n0 n1 b0 b1 vFun vArg) : ValExpr :=
  .applyAt vFun vArg result.resultType

/-- Construct an ordinary application without supplying its annotation or a
codomain-evaluation derivation. History may contain a nonempty linear context;
only the nonlinear argument's typing uses the empty linear context. -/
noncomputable def Unchecked.OpStep.appN
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {n0 n1 : GLang.Term} {vFun vArg : ValExpr}
    (history : V2.CtxTele Delta Gamma Psi)
    (frameValid : Basis.BasisValid Gamma (.frame b0 b1))
    (argumentTyped : HasType ∅ Gamma n1 (Basis.tof b0))
    (hfun : Unchecked.OpStep Psi n0 (.frame b0 b1) vFun)
    (harg : Unchecked.OpStep Psi n1 b0 vArg) :
    Unchecked.ApplicationResult Psi n0 n1 b0 b1 vFun vArg := by
  let h := Unchecked.OpStep.appN_of_typing history frameValid argumentTyped hfun harg
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- A checked application at the literal instantiated basis, retaining both
supplied operand values and the internally selected reshape target. -/
structure ApplicationResult
    (Gamma : NLCtx) (Psi : EvalCtx) (n0 n1 : GLang.Term) (b0 b1 : Basis)
    (vFun vArg : ValExpr) where
  resultType : ValTy
  derivation : Operational.Term ∅ Gamma Psi (.appN n0 n1)
    (Basis.instantiate n1 b1) (.applyAt vFun vArg resultType) resultType

/-- Value expression produced by the checked application constructor. -/
def ApplicationResult.value
    {Gamma : NLCtx} {Psi : EvalCtx} {n0 n1 : GLang.Term} {b0 b1 : Basis}
    {vFun vArg : ValExpr}
    (result : ApplicationResult Gamma Psi n0 n1 b0 b1 vFun vArg) : ValExpr :=
  .applyAt vFun vArg result.resultType

/-- The caller-facing checked application constructor. Only history and the
two operand derivations are supplied; the result reshape target and its exact
basis certificate are constructed internally. The proof-kernel constructor
`C.Term.appN_val` continues recording the certificate for induction. -/
noncomputable def Term.appN
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {n0 n1 : GLang.Term}
    {vFun vArg : ValExpr} {tauFun tauArg : ValTy}
    (history : V2.CtxTele Delta Gamma Psi)
    (hfun : Operational.Term ∅ Gamma Psi n0 (.frame b0 b1) vFun tauFun)
    (harg : Operational.Term ∅ Gamma Psi n1 b0 vArg tauArg) :
    ApplicationResult Gamma Psi n0 n1 b0 b1 vFun vArg := by
  let h := Term.appN_of_history history hfun harg
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

end Operational
end GLang
