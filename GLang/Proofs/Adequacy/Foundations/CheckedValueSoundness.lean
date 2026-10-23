import GLang.Proofs.Adequacy.Foundations.ValueSoundnessSemS
import GLang.Proofs.Adequacy.Raw.RawNonBetaValueKernel
import GLang.Proofs.Adequacy.Raw.RawReification

/-!
# Checked value-denotation soundness

The raw evaluator intentionally exposes flat runtime representations and may
return a successful value whose representation is malformed for its claimed
type.  `denotValB_semSCheckedAt` is the public validation boundary: it runs the
raw evaluator unchanged, decodes the result at the requested type, and
checked-reifies it without padding or truncation.

Consequently successful checked evaluation is hereditarily canonical for an
arbitrary (including non-constant or malformed) semantic environment.  This
is partial correctness: `DimError` remains an allowed result.  Adequacy proves
separately that the added check succeeds for compiled values and preserves
their exact source/value agreement.
-/

namespace GLang

noncomputable section

namespace CheckedValue

/-- Decode a raw runtime value at `T`, then checked-reify it.  Base arrays of
the wrong length produce `DimError`; they are never silently resized. -/
noncomputable def recheck (T : ValTypeSem) (v : ValValSem) :
    Except DimError ValValSem :=
  (ValValSem.toEl T v).bind (ValValSem.fromElChecked T)

/-- Checked reification is hereditarily canonical whenever it succeeds. -/
theorem fromElChecked_canonical (orc : FFSOracleSem) :
    forall (tau : ValTy) (rho : ValEnvSem) (Gamma : List ValTy)
      (Delta : List ValValSem)
      (a : (denotValTyS orc rho Gamma Delta tau).El),
      ValCanonicalResultSoundOfDenotSemS orc rho Gamma Delta tau
        (ValValSem.fromElChecked
          (denotValTyS orc rho Gamma Delta tau) a)
  | .space s, rho, Gamma, Delta, a => by
      simp only [denotValTyS, ValValSem.fromElChecked]
      by_cases hlen : a.length = ValSpace.dof (orc rho Gamma Delta) s
      · rw [if_pos hlen]
        apply ValCanonicalResultSoundOfDenotSemS.ok
        exact hlen
      · rw [if_neg hlen]
        exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | .piTy tau0 tau1, rho, Gamma, Delta, f => by
      simp only [denotValTyS, ValValSem.fromElChecked]
      apply ValCanonicalResultSoundOfDenotSemS.ok
      refine ⟨rfl, ?_⟩
      intro arg out hout
      cases hfa : f arg with
      | error err =>
          simp only [hfa, Except.bind] at hout
          cases hout
      | ok value =>
          simp only [hfa, Except.bind] at hout
          exact fromElChecked_canonical orc tau1 rho (tau0 :: Gamma)
            (ValValSem.fromEl (denotValTyS orc rho Gamma Delta tau0) arg :: Delta)
            value out hout
  termination_by tau _ _ _ _ => ValTy.kindSize tau
  decreasing_by
    all_goals simp_wf

/-- A successful recheck is hereditarily canonical, with no precondition on
the raw input. -/
theorem recheck_canonical
    (orc : FFSOracleSem) (rho : ValEnvSem) (Gamma : List ValTy)
    (Delta : List ValValSem) (tau : ValTy) (v : ValValSem) :
    ValCanonicalResultSoundOfDenotSemS orc rho Gamma Delta tau
      (recheck (denotValTyS orc rho Gamma Delta tau) v) := by
  unfold recheck
  cases hto : ValValSem.toEl (denotValTyS orc rho Gamma Delta tau) v with
  | error err =>
      simp only [Except.bind]
      exact ValCanonicalResultSoundOfDenotSemS.error err
  | ok a =>
      simp only [Except.bind]
      exact fromElChecked_canonical orc tau rho Gamma Delta a

/-- The familiar weak, out-of-bounds-zero result follows from canonical
checked reification. -/
theorem recheck_sound
    (orc : FFSOracleSem) (rho : ValEnvSem) (Gamma : List ValTy)
    (Delta : List ValValSem) (tau : ValTy) (v : ValValSem) :
    ValResultSoundOfDenotSemS orc rho Gamma Delta tau
      (recheck (denotValTyS orc rho Gamma Delta tau) v) := by
  intro out hout
  exact ValCanonicalSoundOfDenotSemS.implies_sound
    orc tau rho Gamma Delta out
      (recheck_canonical orc rho Gamma Delta tau v out hout)

/-- Raw agreement plus the matching dimension witness proves that validation
succeeds and preserves the same source/value agreement. -/
theorem recheck_preserves_agree
    (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot} {source : DVal}
    {value : ValValSem}
    (hdims : RawAgreeDimsAt orc sigma rho Ds Gv Dv tau tauv B)
    (hagree : Agree orc sigma rho Ds Gv Dv tau tauv B source value) :
    exists canon,
      recheck (denotValTyS orc rho Gv Dv tauv) value = .ok canon /\
      Agree orc sigma rho Ds Gv Dv tau tauv B source canon := by
  obtain ⟨a, hto⟩ := hagree.toEl
  obtain ⟨canon, hchecked, hcanon⟩ :=
    RawAgree.fromElChecked_of_toEl orc sigma rho hdims hagree hto
  refine ⟨canon, ?_, hcanon⟩
  unfold recheck
  rw [hto]
  exact hchecked

end CheckedValue

/-- Evaluate with the existing raw semantics and validate the successful
payload at the caller-supplied result type. -/
noncomputable def denotValB_semSCheckedAt (orc : FFSOracleSem)
    (rho : ValEnvSem) (Gamma : List ValTy) (Delta : List ValValSem)
    (tau : ValTy) (e : ValExpr) : Except DimError ValValSem :=
  (denotValB_semS orc rho Gamma Delta e).bind fun value =>
    CheckedValue.recheck (denotValTyS orc rho Gamma Delta tau) value

/-- Inferred-type convenience wrapper for standalone typed value programs. -/
noncomputable def denotValB_semSChecked (orc : FFSOracleSem)
    (rho : ValEnvSem) (Gamma : List ValTy) (Delta : List ValValSem)
    (e : ValExpr) : Except DimError ValValSem :=
  denotValB_semSCheckedAt orc rho Gamma Delta
    (ValExpr.inferTypeCtx Gamma e) e

/-- Successful checked evaluation is canonical at the requested type.  No
typing, closure, environment-validity, or oracle-law premise is required. -/
theorem denotValB_semSCheckedAt_canonical
    (orc : FFSOracleSem) (rho : ValEnvSem) (Gamma : List ValTy)
    (Delta : List ValValSem) (tau : ValTy) (e : ValExpr) :
    ValCanonicalResultSoundOfDenotSemS orc rho Gamma Delta tau
      (denotValB_semSCheckedAt orc rho Gamma Delta tau e) := by
  unfold denotValB_semSCheckedAt
  cases heval : denotValB_semS orc rho Gamma Delta e with
  | error err =>
      simp only [Except.bind]
      exact ValCanonicalResultSoundOfDenotSemS.error err
  | ok value =>
      simp only [Except.bind]
      exact CheckedValue.recheck_canonical orc rho Gamma Delta tau value

/-- The inferred convenience wrapper is canonical at its inferred type. -/
theorem denotValB_semSChecked_canonical
    (orc : FFSOracleSem) (rho : ValEnvSem) (Gamma : List ValTy)
    (Delta : List ValValSem) (e : ValExpr) :
    ValCanonicalResultSoundOfDenotSemS orc rho Gamma Delta
      (ValExpr.inferTypeCtx Gamma e)
      (denotValB_semSChecked orc rho Gamma Delta e) := by
  unfold denotValB_semSChecked
  exact denotValB_semSCheckedAt_canonical orc rho Gamma Delta
    (ValExpr.inferTypeCtx Gamma e) e

/-- Premise-free weak soundness at the inferred result type. -/
theorem denotValB_semSChecked_sound
    (orc : FFSOracleSem) (rho : ValEnvSem) (Gamma : List ValTy)
    (Delta : List ValValSem) (e : ValExpr) :
    ValResultSoundOfDenotSemS orc rho Gamma Delta
      (ValExpr.inferTypeCtx Gamma e)
      (denotValB_semSChecked orc rho Gamma Delta e) := by
  intro out hout
  exact ValCanonicalSoundOfDenotSemS.implies_sound
    orc (ValExpr.inferTypeCtx Gamma e) rho Gamma Delta out
      (denotValB_semSChecked_canonical
        orc rho Gamma Delta e out hout)

/-- Explicit-type weak value soundness.  This theorem does not need typing;
the supplied type is enforced dynamically by the checked boundary. -/
theorem denotValB_semSCheckedAt_sound
    (orc : FFSOracleSem) (rho : ValEnvSem) (Gamma : List ValTy)
    (Delta : List ValValSem) (tau : ValTy) (e : ValExpr) :
    ValResultSoundOfDenotSemS orc rho Gamma Delta tau
      (denotValB_semSCheckedAt orc rho Gamma Delta tau e) := by
  intro out hout
  exact ValCanonicalSoundOfDenotSemS.implies_sound
    orc tau rho Gamma Delta out
      (denotValB_semSCheckedAt_canonical
        orc rho Gamma Delta tau e out hout)

/-- Weak public value-soundness theorem.  `rho` may be any non-constant
environment, and a `DimError` is allowed; every successful payload is sound.
Typing is used only to identify the inferred result type. -/
theorem valHasType_denotValB_semSChecked_sound
    (orc : FFSOracleSem) (rho : ValEnvSem) (Gamma : List ValTy)
    (Delta : List ValValSem) {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (htype : ValHasType epsilon e tau) :
    ValResultSoundOfDenotSemS orc rho Gamma Delta tau
      (denotValB_semSChecked orc rho Gamma Delta e) := by
  rw [← ValExpr.inferTypeCtx_eq_of_typed (Gamma := Gamma) htype]
  exact denotValB_semSChecked_sound orc rho Gamma Delta e

/-- Canonical public value soundness.  Like the weaker theorem above, this is
partial correctness: the checked evaluator may return `DimError`.  Whenever it
succeeds, however, base arrays have exactly the semantic dimension and the
same exact-storage property holds hereditarily through dependent callbacks.
No environment-validity or oracle-law premise is required. -/
theorem valHasType_denotValB_semSChecked_canonical
    (orc : FFSOracleSem) (rho : ValEnvSem) (Gamma : List ValTy)
    (Delta : List ValValSem) {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (htype : ValHasType epsilon e tau) :
    ValCanonicalResultSoundOfDenotSemS orc rho Gamma Delta tau
      (denotValB_semSChecked orc rho Gamma Delta e) := by
  rw [← ValExpr.inferTypeCtx_eq_of_typed (Gamma := Gamma) htype]
  exact denotValB_semSChecked_canonical orc rho Gamma Delta e

/-- Existing adequacy lifts through the checked boundary.  The exact value
type is explicit, so this needs no equality with the value syntax's inferred
type. -/
theorem ResultAgree.checkedAt_of_raw
    (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {e : ValExpr} {tau : Ty} {tauv : ValTy} {B : BasisDenot}
    {source : DVal}
    (hdims : AgreeDims orc sigma rho Ds Gv Dv tau tauv B)
    (hraw : ResultAgree orc sigma rho Ds Gv Dv tau tauv B source
      (denotValB_semS orc rho Gv Dv e)) :
    ResultAgree orc sigma rho Ds Gv Dv tau tauv B source
      (denotValB_semSCheckedAt orc rho Gv Dv tauv e) := by
  obtain ⟨value, heval, hagree⟩ := hraw
  obtain ⟨canon, hcheck, hcanon⟩ :=
    CheckedValue.recheck_preserves_agree orc sigma rho hdims.raw hagree
  refine ⟨canon, ?_, hcanon⟩
  unfold denotValB_semSCheckedAt
  rw [heval]
  exact hcheck

end

end GLang
