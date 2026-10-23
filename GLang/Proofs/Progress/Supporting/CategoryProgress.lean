import GLang.Operational.Supporting.Operational
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedCtxTeleCategoryProgress

/-!
# Canonical checked progress for non-term operational categories

These wrappers align space, type, exact-basis type, and change-of-basis
progress with `Operational.Term.progress`: callers provide the semantic-free
creation history plus the category's ordinary source validity evidence, and
receive the context-indexed checked judgment used by adequacy.
-/

namespace GLang
namespace Operational

/-- Checked progress for source-space evaluation. -/
theorem Space.progress
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (history : V2.CtxTele Delta Gamma Psi)
    {s : GLang.Space} (valid : SValid Gamma s) :
    exists sv, Operational.Space Gamma Psi s sv :=
  RawCertifiedCtxTeleCategoryProgress.checkedSpace history valid

/-- Checked progress for source-type evaluation, using the canonical standard
basis to choose dependent-frame representations. -/
theorem Ty.progress
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (history : V2.CtxTele Delta Gamma Psi)
    {tau : GLang.Ty} {kind : Kind} (valid : TValid Gamma tau kind) :
    exists tauV, Operational.Ty Gamma Psi tau tauV :=
  RawCertifiedCtxTeleCategoryProgress.checkedTy history valid

/-- Checked progress for type evaluation at one literal requested basis. -/
theorem TyAt.progress
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (history : V2.CtxTele Delta Gamma Psi)
    {b : Basis} (valid : Basis.BasisValid Gamma b) :
    exists tauV, Operational.TyAt Gamma Psi b tauV :=
  RawCertifiedCtxTeleCategoryProgress.checkedTyAt history valid

/-- Checked progress for a source type at one literal requested basis.  The
result exposes both the exact-basis and ordinary checked type views. -/
theorem TyAt.progressSource
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (history : V2.CtxTele Delta Gamma Psi)
    {tau : GLang.Ty} {b : Basis}
    (valid : Basis.BasisValid Gamma b)
    (tof_eq : Basis.tof b = tau) :
    exists tauV,
      Operational.TyAt Gamma Psi b tauV /\
      Operational.Ty Gamma Psi tau tauV :=
  RawCertifiedCtxTeleCategoryProgress.checkedTyAtSource
    history valid tof_eq

/-- Checked change-of-basis progress from a valid hereditary space basis to
the literal standard basis of its source type. -/
theorem Cob.progressToStandard
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    (history : V2.CtxTele Delta Gamma Psi)
    {b : Basis} (valid : Basis.BasisValid Gamma b)
    (isSpace : Basis.tof b = .space (Basis.sof b)) :
    exists env,
      Operational.Cob Gamma Psi b env (Basis.std (Basis.tof b)) :=
  RawCertifiedCtxTeleCategoryProgress.checkedCobToStandard
    history valid isSpace

end Operational
end GLang
