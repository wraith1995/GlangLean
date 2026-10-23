import GLang.Proofs.Progress.Certificates.RawCertifiedPiBasisTransport

/-!
# Checked frame application after root reanchoring

This module isolates the application-specific consequence of a checked
higher-order reanchoring boundary.  Once the function has been reanchored at
the literal frame `frame b0 b1` and its argument at the contravariant domain
`b0`, the existing checked dependent cut constructs the exact instantiated
codomain.  No recursive certificate for `instantiate argument b1` is needed.

The second theorem accepts the two reanchoring operations directly.  It is
deliberately independent of the public/root boundary record so that the
boundary layer can use it without introducing an import cycle.
-/

namespace GLang
namespace RawCertifiedFrameApplicationReanchor

open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedPiBasisTransport

/-- Apply a function already checked at a non-standard frame to an argument
already checked at that frame's domain.

`checkedCodomainCut` substitutes the checked argument into the opened
codomain certificate obtained by frame inversion.  Consequently the result
is checked at the literal instantiated codomain `Basis.instantiate e1 b1`;
there is no result-basis transport premise. -/
theorem checkedAppN_at_frame
    (happCut : CheckedTyAtAppCut)
    {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b0 b1 : Basis}
    {vFun vArg : ValExpr} {tauVFun tauVArg : ValTy}
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hfun : C.Term (∅ : LCtx) Gamma Psi e0 (.frame b0 b1) vFun tauVFun)
    (harg : C.Term (∅ : LCtx) Gamma Psi e1 b0 vArg tauVArg) :
    exists arg' tauVArg' vOut tauVOut,
      C.Term (∅ : LCtx) Gamma Psi e1 b0 arg' tauVArg' /\
      C.Term (∅ : LCtx) Gamma Psi (.appN e0 e1)
        (Basis.instantiate e1 b1) vOut tauVOut := by
  obtain ⟨tauV0, tauV1, rfl, hdom, L, hcod⟩ :=
    checkedTyAt_frame_inv_full hfun.tyAt
  obtain ⟨arg', tauVOut, harg', hout⟩ :=
    checkedCodomainCut (Gamma := Gamma) (Psi := Psi) happCut hP hcov hwf
      harg hdom L hcod
  have htyped : Nonempty (HasType (∅ : LCtx) Gamma (.appN e0 e1)
      (Basis.tof (Basis.instantiate e1 b1))) := by
    obtain ⟨htFun⟩ := hfun.hasType
    obtain ⟨htArg⟩ := harg'.hasType
    refine ⟨?_⟩
    simpa only [Basis.tof, Basis.instantiate, Basis.tof_openRec,
      Ty.instantiate] using HasType.app_nonlinear htFun htArg
  exact ⟨arg', tauV0, .applyAt vFun arg' tauVOut, tauVOut, harg',
    C.Term.appN_val htyped hout.basisValid hout hfun harg'⟩

/-- Application closure for two already-available root reanchoring
operations: one for the requested frame and one for its contravariant
domain.  The codomain needs no analogous operation; checked substitution
constructs its instantiated exact certificate directly. -/
theorem checkedAppN_of_root_reanchors
    (happCut : CheckedTyAtAppCut)
    {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b0 b1 : Basis}
    {vFunStd vArgStd : ValExpr} {tauVFunStd tauVArgStd : ValTy}
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (frameReanchor : forall {v : ValExpr} {tauV : ValTy},
      C.Term (∅ : LCtx) Gamma Psi e0
          (Basis.std (Basis.tof (.frame b0 b1))) v tauV ->
        exists w tauW,
          C.Term (∅ : LCtx) Gamma Psi e0 (.frame b0 b1) w tauW)
    (domainReanchor : forall {v : ValExpr} {tauV : ValTy},
      C.Term (∅ : LCtx) Gamma Psi e1
          (Basis.std (Basis.tof b0)) v tauV ->
        exists w tauW, C.Term (∅ : LCtx) Gamma Psi e1 b0 w tauW)
    (hfunStd : C.Term (∅ : LCtx) Gamma Psi e0
      (Basis.std (Basis.tof (.frame b0 b1))) vFunStd tauVFunStd)
    (hargStd : C.Term (∅ : LCtx) Gamma Psi e1
      (Basis.std (Basis.tof b0)) vArgStd tauVArgStd) :
    exists vOut tauVOut,
      C.Term (∅ : LCtx) Gamma Psi (.appN e0 e1)
        (Basis.instantiate e1 b1) vOut tauVOut := by
  obtain ⟨vFun, tauVFun, hfun⟩ := frameReanchor hfunStd
  obtain ⟨vArg, tauVArg, harg⟩ := domainReanchor hargStd
  obtain ⟨_arg', _tauVArg', vOut, tauVOut, _harg', hout⟩ :=
    checkedAppN_at_frame happCut hP hcov hwf hfun harg
  exact ⟨vOut, tauVOut, hout⟩

end RawCertifiedFrameApplicationReanchor
end GLang
