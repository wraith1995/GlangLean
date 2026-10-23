import GLang.Proofs.Adequacy.Total.DirectOracle
import GLang.Proofs.Adequacy.Foundations.CheckedValueSoundness
import GLang.Operational.Supporting.Operational

/-!
# Public adequacy specialized to the constructive direct oracle

The generic adequacy and operational APIs quantify over an FFS oracle and a
proof of its semantic contract.  This facade discharges exactly those two
parameters with `directOracle` and `directApplicationOracle_spec`.  Semantic consistency
remains explicit, and is consequently indexed by the same concrete oracle.
-/

namespace GLang

namespace Adequacy.Direct

/-! ## Oracle-free public vocabulary

The public vocabulary fixes the constructive oracle once. Public theorem
statements consequently talk only about the direct semantics; callers do
not pass an oracle or an oracle-specification proof.  Unfolding an alias still
reveals the exact `directOracle` instance, so this hides no hypothesis.
-/

/-- Source consistency retains only the operational semantic history. -/
structure Consistent (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (rho : ValEnvSem) : Prop where
  raw : GLang.Consistent directOracle Delta Gamma Psi GammaV sigma rho

/-- Empty consistency constrains no undeclared runtime entries. -/
theorem Consistent.empty (rho : ValEnvSem) :
    Consistent ∅ ∅ ∅ ∅ ⟨∅⟩ rho :=
  ⟨⟨RawConsistent.empty, .empty⟩⟩

/-- Forget semantic data for the public operational progress input. -/
theorem Consistent.contextHistory
    (h : Consistent Delta Gamma Psi GammaV sigma rho) :
    V2.CtxTele Delta Gamma Psi :=
  h.raw.context.erase

/-- Recursive exact-basis soundness, specialized only in namespace (the
relation itself is oracle-independent). -/
noncomputable abbrev BasisAt (sigma : DEnv) (Ds : List DVal)
    (tau : Ty) (B : BasisDenot) : Prop :=
  Adequacy.BasisAt sigma Ds tau B

/-- Result agreement for the supplied constructive oracle. -/
abbrev ResultAgree (sigma : DEnv) (rho : ValEnvSem)
    (Ds : List DVal) (Gv : List ValTy) (Dv : List ValValSem)
    (tau : Ty) (tauV : ValTy) (B : BasisDenot) (source : DVal)
    (result : Except DimError ValValSem) : Prop :=
  GLang.ResultAgree directOracle sigma rho Ds Gv Dv tau tauV B source result

/-- Dimension agreement for the supplied constructive oracle. -/
noncomputable abbrev AgreeDims (sigma : DEnv) (rho : ValEnvSem)
    (Ds : List DVal) (Gv : List ValTy) (Dv : List ValValSem)
    (tau : Ty) (tauV : ValTy) (B : BasisDenot) : Prop :=
  GLang.AgreeDims directOracle sigma rho Ds Gv Dv tau tauV B

/-- Change-of-basis agreement for the supplied constructive oracle. -/
abbrev CobAgree (sigma : DEnv) (rho : ValEnvSem)
    (bSrc bTgt : Basis) (env : ValExpr) : Prop :=
  GLang.CobAgree directOracle sigma rho bSrc bTgt env

/-- Raw value evaluation with the supplied constructive oracle. -/
noncomputable abbrev evalVal (rho : ValEnvSem) (Gv : List ValTy)
    (Dv : List ValValSem) (v : ValExpr) : Except DimError ValValSem :=
  denotValB_semS directOracle rho Gv Dv v

/-- Checked value evaluation with the supplied constructive oracle. -/
noncomputable abbrev evalValCheckedAt (rho : ValEnvSem)
    (Gv : List ValTy) (Dv : List ValValSem) (tauV : ValTy)
    (v : ValExpr) : Except DimError ValValSem :=
  denotValB_semSCheckedAt directOracle rho Gv Dv tauV v

/-- Every valid syntactic basis denotes a recursively sound exact semantic
basis.  No oracle-specific premise is needed. -/
theorem basisAt
    {sigma : DEnv} {Gamma : NLCtx} {b : Basis}
    (hvalid : Basis.BasisValid Gamma b)
    (hctx : CtxWF ∅ Gamma)
    (henv : EnvWF sigma ∅ Gamma) :
    BasisAt sigma [] (Basis.tof b) (denotBasis sigma b) :=
  Adequacy.basisAt hvalid hctx henv

/-- Strengthened-space adequacy for the constructive direct oracle. -/
theorem space
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {sv : ValSpace}
    (h : S.Space Gamma Psi s sv) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent Delta Gamma Psi GammaV sigma rho ->
      ValSpace.shpOf (directOracle rho [] []) sv = srcShp sigma [] s :=
  fun Delta sigma GammaV hc => Adequacy.space directOracle directApplicationOracle_spec h Delta sigma GammaV hc.raw

/-- Canonical strengthened-term adequacy for the constructive direct oracle.
The result agreement and exact-basis dimension witness come from the same
strengthened trace. -/
theorem term
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : S.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Consistent Delta Gamma Psi GammaV sigma rho ->
      ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (evalVal rho [] [] v) /\
        AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) :=
  fun sigma GammaV hc => Adequacy.term directOracle directApplicationOracle_spec h sigma GammaV hc.raw

/-- Strengthened-term adequacy through the validating value denotation.  The
exact compiled value type selects the check, and adequacy proves that check
cannot return `DimError`. -/
theorem termChecked
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : S.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Consistent Delta Gamma Psi GammaV sigma rho ->
      ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (evalValCheckedAt rho [] [] tauV v) /\
        AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) := by
  intro sigma GammaV hconsistent
  obtain ⟨hresult, hdims⟩ := term h sigma GammaV hconsistent
  exact ⟨GLang.ResultAgree.checkedAt_of_raw directOracle sigma rho
    hdims hresult, hdims⟩

/-- Strengthened change-of-basis adequacy for the constructive direct oracle. -/
theorem cob
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (h : S.Cob Gamma Psi bSrc env bTgt) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent Delta Gamma Psi GammaV sigma rho ->
      CobAgree sigma rho bSrc bTgt env :=
  fun Delta sigma GammaV hc => Adequacy.cob directOracle directApplicationOracle_spec h Delta sigma GammaV hc.raw

/-- Strengthened exact-basis dimension adequacy for the constructive direct
oracle.  The conclusion is indexed by the denotation of the basis retained in
the `S.TyAt` premise. -/
theorem dimsAt
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy}
    (h : S.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Consistent Delta Gamma Psi GammaV sigma rho ->
      AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  fun Delta sigma GammaV hc => Adequacy.dimsAt directOracle directApplicationOracle_spec h Delta sigma GammaV hc.raw

end Adequacy.Direct

namespace Operational

/-- The end-to-end soundness call specialized to `directOracle`.  Compared
with `Operational.SoundnessCall`, it discharges the oracle specification and
requires extensional value-environment membership.  Consistency supplies the semantic-free operational
history; typing and requested-basis validity then construct checked progress. -/
structure DirectSoundnessCall (rho : ValEnvSem)
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (GammaV : ValCtx)
    (sigma : DEnv) (e : GLang.Term) (b : Basis) : Type where
  consistent : Adequacy.Direct.Consistent Delta Gamma Psi GammaV sigma rho
  typed : HasType Delta Gamma e (Basis.tof b)
  basisValid : Basis.BasisValid Gamma b

/-- Accessor for the hereditary shape implied by validity. -/
theorem DirectSoundnessCall.isTyBasis
    (call : DirectSoundnessCall rho Delta Gamma Psi GammaV sigma e b) :
    Basis.IsTyBasis b :=
  call.basisValid.isTyBasis

/-- Descriptive spelling of `DirectSoundnessCall`, used by the canonical
existential checked-progress-and-adequacy theorem. -/
abbrev DirectProgressAdequacyCall := Operational.DirectSoundnessCall

/-- Reinsert the constructively proved direct-oracle specification. -/
def DirectSoundnessCall.toSoundnessCall
    (call : DirectSoundnessCall rho Delta Gamma Psi GammaV sigma e b) :
    SoundnessCall directOracle rho Delta Gamma Psi GammaV sigma e b where
  oracle := directApplicationOracle_spec
  consistent := call.consistent.raw
  typed := call.typed
  basisValid := call.basisValid

/-- Canonical checked-space adequacy with the constructive oracle parameters
discharged. -/
theorem Space.adequacyDirect
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : GLang.Space} {sv : ValSpace}
    (h : Operational.Space Gamma Psi s sv) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.Direct.Consistent Delta Gamma Psi GammaV sigma rho ->
      ValSpace.shpOf (directOracle rho [] []) sv = srcShp sigma [] s :=
  fun Delta sigma GammaV hc => h.adequacy directOracle directApplicationOracle_spec Delta sigma GammaV hc.raw

/-- Canonical checked-term adequacy with the concrete oracle parameters
discharged. -/
theorem Term.adequacyDirect
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : Operational.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.Direct.Consistent Delta Gamma Psi GammaV sigma rho ->
      Adequacy.Direct.ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (Adequacy.Direct.evalVal rho [] [] v) /\
        Adequacy.Direct.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) :=
  fun sigma GammaV hc => h.adequacy directOracle directApplicationOracle_spec sigma GammaV hc.raw

/-- Canonical checked-term adequacy through the validating public value
denotation.  The raw adequacy result and its dimension witness prove that the
additional check succeeds; `DimError` is therefore excluded for compiled
results. -/
theorem Term.adequacyDirectChecked
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : Operational.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.Direct.Consistent Delta Gamma Psi GammaV sigma rho ->
      Adequacy.Direct.ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (Adequacy.Direct.evalValCheckedAt rho [] [] tauV v) /\
        Adequacy.Direct.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) := by
  intro sigma GammaV hconsistent
  obtain ⟨hresult, hdims⟩ := h.adequacyDirect sigma GammaV hconsistent
  exact ⟨GLang.ResultAgree.checkedAt_of_raw directOracle sigma rho
    hdims hresult, hdims⟩

/-- Canonical checked change-of-basis adequacy with the concrete oracle
parameters discharged. -/
theorem Cob.adequacyDirect
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (h : Operational.Cob Gamma Psi bSrc env bTgt) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.Direct.Consistent Delta Gamma Psi GammaV sigma rho ->
      Adequacy.Direct.CobAgree sigma rho bSrc bTgt env :=
  fun Delta sigma GammaV hc => h.adequacy directOracle directApplicationOracle_spec Delta sigma GammaV hc.raw

/-- Canonical checked exact-basis dimension adequacy with the concrete oracle
parameters discharged. -/
theorem TyAt.adequacyDimsDirect
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy}
    (h : Operational.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.Direct.Consistent Delta Gamma Psi GammaV sigma rho ->
      Adequacy.Direct.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  fun Delta sigma GammaV hc => h.adequacyDims directOracle directApplicationOracle_spec Delta sigma GammaV hc.raw

/-- Existential checked progress and adequacy specialized to the constructive direct
oracle.  `DirectSoundnessCall` supplies all operational and consistency facts
but no oracle parameter or oracle-specification proof. -/
theorem Term.progressAndAdequacyDirect
    (call : Operational.DirectProgressAdequacyCall
      rho Delta Gamma Psi GammaV sigma e b) :
    exists v tauV,
      Operational.Term Delta Gamma Psi e b v tauV /\
      ValExpr.inferType v = tauV /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV /\
      Unchecked.OpStep Psi e b v /\
      S.Term Delta Gamma Psi e b v tauV /\
      Adequacy.Direct.ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (Adequacy.Direct.evalVal rho [] [] v) /\
      Adequacy.Direct.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  Operational.Term.progressAndAdequacy call.toSoundnessCall

theorem Term.soundnessDirect
    (call : Operational.DirectSoundnessCall
      rho Delta Gamma Psi GammaV sigma e b) :
    exists v tauV,
      Operational.Term Delta Gamma Psi e b v tauV /\
      ValExpr.inferType v = tauV /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV /\
      Unchecked.OpStep Psi e b v /\
      S.Term Delta Gamma Psi e b v tauV /\
      Adequacy.Direct.ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (Adequacy.Direct.evalVal rho [] [] v) /\
      Adequacy.Direct.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  Operational.Term.progressAndAdequacyDirect call

end Operational
end GLang
