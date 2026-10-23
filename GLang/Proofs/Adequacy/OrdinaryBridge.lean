import GLang.Proofs.Adequacy.Compatibility
import GLang.Proofs.Adequacy.Foundations.Consistent
import GLang.Proofs.Progress.Supporting.ProgressTransport

namespace GLang
namespace OperationalStrengthening

/-- Raw consistency already supplies the operational-context regularity used
by preservation/progress. -/
theorem rawConsistent_evalCtxValidPlus_for_bridge
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    GLang.V2.EvalCtxValidPlus Psi :=
  h.evalCtxValidPlus

theorem rawConsistent_evalCtxValid_for_bridge
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    GLang.V2.EvalCtxValid Psi := by
  intro x b v hlookup
  have hp := rawConsistent_evalCtxValidPlus_for_bridge h x b v hlookup
  exact ⟨(h.stored_fv x b v hlookup).1, hp.1, hp.2.1⟩

theorem rawConsistent_evalCtxLamAnchored_for_bridge
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    GLang.V2.EvalCtxLamAnchored Psi := by
  intro x b0 b1 tau0 tau1 body hlookup
  exact (rawConsistent_evalCtxValidPlus_for_bridge h x (.frame b0 b1)
    (.vlam tau0 tau1 body) hlookup).2.2.2.2
      b0 b1 tau0 tau1 body rfl rfl

private theorem rawConsistent_ctxValid_for_bridge
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    (forall x s, Delta.lookup x = some s -> Nonempty (SValid Gamma s)) /\
    (forall x tau, Gamma.lookup x = some tau ->
      exists k, Nonempty (TValid Gamma tau k)) := by
  induction h with
  | empty =>
      exact ⟨fun _ _ hlookup => by simp at hlookup,
        fun _ _ hlookup => by simp at hlookup⟩
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      refine ⟨fun y s' hlookup => ?_, ih.2⟩
      by_cases hyx : y = x
      · rw [hyx, Finmap.lookup_insert] at hlookup
        obtain rfl := Option.some.inj hlookup
        have hsv := hb.sof_valid
        rw [Basis.sof_of_tof_space htof] at hsv
        exact hsv
      · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
        exact ih.1 y s' hlookup
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      refine ⟨fun y s' hlookup => ?_, fun y tau hlookup => ?_⟩
      · obtain ⟨hvalid⟩ := ih.1 y s' hlookup
        exact ⟨hvalid.weakenInsertNL x (Basis.tof b) hx.2⟩
      · by_cases hyx : y = x
        · rw [hyx, Finmap.lookup_insert] at hlookup
          obtain rfl := Option.some.inj hlookup
          obtain ⟨k, ⟨ht⟩⟩ := hb.tof_tvalid
          exact ⟨k, ⟨ht.weakenInsertNL x (Basis.tof b) hx.2⟩⟩
        · rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
          obtain ⟨k, ⟨ht⟩⟩ := ih.2 y tau hlookup
          exact ⟨k, ⟨ht.weakenInsertNL x (Basis.tof b) hx.2⟩⟩
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      exact ih

theorem rawConsistent_ctxWF_for_bridge
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    GLang.V2.CtxWF' Delta Gamma := by
  have hwf := h.ctxWF_raw
  have hvalid := rawConsistent_ctxValid_for_bridge h
  exact ⟨hwf.disjoint,
    fun x s hx z hz => Finmap.mem_keys.mpr (hwf.lin_fv_in_ε x s hx z hz),
    fun x tau hx z hz => Finmap.mem_keys.mpr (hwf.nl_fv_in_ε x tau hx z hz),
    hvalid.1, hvalid.2⟩

private theorem rawConsistent_source_mem_iff_for_bridge
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    forall x, (x ∈ Delta ∨ x ∈ Gamma) ↔ exists b, (x, b) ∈ Psi := by
  induction h with
  | empty => intro x; simp [Finmap.notMem_empty]
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      intro x'
      rw [Finmap.mem_insert, EvalCtx.exists_mem_extend, ← ih x']
      tauto
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      intro x'
      rw [Finmap.mem_insert, EvalCtx.exists_mem_extend, ← ih x']
      tauto
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      intro x'
      rw [EvalCtx.exists_mem_extend, ← ih x']
      constructor
      · exact Or.inr
      · rintro (rfl | hold)
        · exact hsource.mem_source
        · exact hold

private theorem rawConsistent_basisValid_of_mem_for_bridge
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    forall x b, (x, b) ∈ Psi -> Basis.BasisValid Gamma b := by
  induction h with
  | empty => intro x b hmem; exact absurd hmem Finmap.notMem_empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      intro y b' hmem
      rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
      · exact hb
      · exact ih y b' hmem
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      intro y b' hmem
      rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
      · exact hb.weakenInsertNL hx.2 (hb.not_mem_fv_of_not_mem hx.2)
      · exact (ih y b' hmem).weakenInsertNL hx.2
          ((ih y b' hmem).not_mem_fv_of_not_mem hx.2)
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      intro y b' hmem
      rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
      · exact hb
      · exact ih y b' hmem

theorem rawConsistent_typingImplyEval_for_bridge
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    GLang.V2.TypingImplyEval Delta Gamma Psi := by
  refine ⟨rawConsistent_source_mem_iff_for_bridge h, ?_, ?_,
    rawConsistent_basisValid_of_mem_for_bridge h⟩
  · induction h with
    | empty => intro x s b hlookup; simp at hlookup
    | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
        hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
        hden hagree hdims ih =>
        intro y s' b' hlookup hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · rw [Finmap.lookup_insert] at hlookup
          obtain rfl := Option.some.inj hlookup
          exact htof
        · have hyx : y ≠ x := fun e => hc.freshEvalName hx b' (e ▸ hmem)
          rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
          exact ih y s' b' hlookup hmem
    | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
        hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
        hden hagree hdims hanchor ih =>
        intro y s' b' hlookup hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · exact absurd (Finmap.mem_of_lookup_eq_some hlookup) hx.1
        · exact ih y s' b' hlookup hmem
    | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
        hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
        hden hagree hdims hanchor ih =>
        intro y s' b' hlookup hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · rcases hsource with ⟨s, hxDelta, htof⟩ | hxGamma
          · rw [hxDelta] at hlookup
            obtain rfl := Option.some.inj hlookup
            exact htof
          · exact absurd (Finmap.mem_of_lookup_eq_some hxGamma)
              (hc.ctxWF_raw.disjoint y
                (Finmap.mem_of_lookup_eq_some hlookup))
        · exact ih y s' b' hlookup hmem
  · induction h with
    | empty => intro x tau b hlookup; simp at hlookup
    | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
        hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
        hden hagree hdims ih =>
        intro y tau b' hlookup hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · exact absurd (Finmap.mem_of_lookup_eq_some hlookup) hx.2
        · exact ih y tau b' hlookup hmem
    | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
        hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
        hden hagree hdims hanchor ih =>
        intro y tau b' hlookup hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · rw [Finmap.lookup_insert] at hlookup
          exact Option.some.inj hlookup
        · have hyx : y ≠ x := fun e => hc.freshEvalName hx b' (e ▸ hmem)
          rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
          exact ih y tau b' hlookup hmem
    | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
        hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
        hden hagree hdims hanchor ih =>
        intro y tau b' hlookup hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · rcases hsource with ⟨s, hxDelta, htof⟩ | hxGamma
          · exact absurd (Finmap.mem_of_lookup_eq_some hlookup)
              (hc.ctxWF_raw.disjoint y
                (Finmap.mem_of_lookup_eq_some hxDelta))
          · rw [hxGamma] at hlookup
            exact Option.some.inj hlookup
        · exact ih y tau b' hlookup hmem

/-- Adequacy hypotheses and source-level conditions at an ordinary evaluation call. -/
structure RawAdequacyCall (orc : FFSOracleSem)
    (rho : ValEnvSem) (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (e : Term) (b : Basis)
    (v : ValExpr) : Prop where
  oracle : RawApplicationOracleSpec orc
  consistent : RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho
  typed : Nonempty (HasType Delta Gamma e (Basis.tof b))
  basisValid : Basis.BasisValid Gamma b
  step : ValExpr.OpStep Psi e b v

theorem RawAdequacyCall.isTyBasis
    (call : RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v) :
    Basis.IsTyBasis b :=
  call.basisValid.isTyBasis

/-- Adequacy conditions independent of an evaluation trace. -/
structure RawProgressCall (orc : FFSOracleSem)
    (rho : ValEnvSem) (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (e : Term) (b : Basis) : Prop where
  oracle : RawApplicationOracleSpec orc
  consistent : RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho
  typed : Nonempty (HasType Delta Gamma e (Basis.tof b))
  basisValid : Basis.BasisValid Gamma b

/-- Accessor for the type-basis shape implied by validity. -/
theorem RawProgressCall.isTyBasis
    (call : RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b) :
    Basis.IsTyBasis b :=
  call.basisValid.isTyBasis

abbrev RawReadyAdequacyCall (orc : FFSOracleSem)
    (rho : ValEnvSem) (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (e : Term) (b : Basis)
    (v : ValExpr) : Prop :=
  RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v

/-- Trace-independent conditions corresponding to `RawReadyAdequacyCall`. -/
abbrev RawReadyProgressCall (orc : FFSOracleSem)
    (rho : ValEnvSem) (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (e : Term) (b : Basis) : Prop :=
  RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b

/-! ## Preferred exact-result bridge -/

/-- **Preferred reverse bridge.** Retain literally the result selected by the
supplied ordinary derivation; only the strengthened value-type index is
existential. -/
def ExactRawAdequacyLift : Prop :=
  forall {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis}
    {v : ValExpr},
    RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v ->
      exists tauV, S.Term Delta Gamma Psi e b v tauV

/-- Preferred ordinary-facing consumer: an exact reverse bridge supplies the
strengthened derivation and adequacy statement for the caller's literal raw
result `v`, with no re-evaluation witness or denotational transport. -/
theorem rawResult_of_exactLift
    (bridge : ExactRawAdequacyLift)
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis}
    {v : ValExpr}
    (call : RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v) :
    exists tauV,
      S.Term Delta Gamma Psi e b v tauV /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨tauV, hS⟩ := bridge call
  exact ⟨tauV, hS,
    RawPublicCandidate.term orc call.oracle hS sigma GammaV call.consistent⟩

def RawAdequacyReevaluation : Prop :=
  forall {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis}
    {v : ValExpr},
    RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v ->
      exists vS tauV, S.Term Delta Gamma Psi e b vS tauV

/-- Step-free strengthened progress, not a reverse bridge.  Since there is no
supplied raw result in `RawProgressCall`, an existential `vS` is intrinsic to
this separate statement. -/
def RawStrengthenedProgress : Prop :=
  forall {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis},
    RawProgressCall orc rho Delta Gamma Psi GammaV sigma e b ->
      exists vS tauV, S.Term Delta Gamma Psi e b vS tauV

def RawReadyReevaluation : Prop :=
  forall {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis}
    {v : ValExpr},
    RawReadyAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v ->
      exists vS tauV, S.Term Delta Gamma Psi e b vS tauV

/-- Step-free raw strengthened progress with transport-ready stored bases;
this is not a reverse bridge for a supplied raw result. -/
def RawReadyStrengthenedProgress : Prop :=
  forall {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis},
    RawReadyProgressCall orc rho Delta Gamma Psi GammaV sigma e b ->
      exists vS tauV, S.Term Delta Gamma Psi e b vS tauV

def RawCommonWitnessReevaluation : Prop :=
  forall {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis}
    {v : ValExpr},
    RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v ->
      exists vS tauV,
        ValExpr.OpStep Psi e b vS /\
        S.Term Delta Gamma Psi e b vS tauV

def AdequacyPreservingReevaluation : Prop :=
  forall {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis}
    {v : ValExpr},
    RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v ->
      exists vS tauV,
        S.Term Delta Gamma Psi e b vS tauV /\
        denotValB_semS orc rho [] [] v =
          denotValB_semS orc rho [] [] vS

theorem ExactRawAdequacyLift.toReevaluation
    (bridge : ExactRawAdequacyLift) : RawAdequacyReevaluation := by
  intro orc rho Delta Gamma Psi GammaV sigma e b v call
  obtain ⟨tauV, hS⟩ := bridge call
  exact ⟨v, tauV, hS⟩

theorem RawStrengthenedProgress.toReevaluation
    (progress : RawStrengthenedProgress) : RawAdequacyReevaluation := by
  intro orc rho Delta Gamma Psi GammaV sigma e b v call
  exact progress {
    oracle := call.oracle
    consistent := call.consistent
    typed := call.typed
    basisValid := call.basisValid }

theorem RawReadyStrengthenedProgress.toReevaluation
    (progress : RawReadyStrengthenedProgress) : RawReadyReevaluation := by
  intro orc rho Delta Gamma Psi GammaV sigma e b v call
  exact progress {
    oracle := call.oracle
    consistent := call.consistent
    typed := call.typed
    basisValid := call.basisValid }

theorem RawAdequacyReevaluation.toCommonWitness
    (bridge : RawAdequacyReevaluation) : RawCommonWitnessReevaluation := by
  intro orc rho Delta Gamma Psi GammaV sigma e b v call
  obtain ⟨vS, tauV, hS⟩ := bridge call
  exact ⟨vS, tauV, hS.toOpStep, hS⟩

theorem ExactRawAdequacyLift.toAdequacyPreserving
    (bridge : ExactRawAdequacyLift) : AdequacyPreservingReevaluation := by
  intro orc rho Delta Gamma Psi GammaV sigma e b v call
  obtain ⟨tauV, hS⟩ := bridge call
  exact ⟨v, tauV, hS, rfl⟩

theorem rawResult_of_reevaluation
    (bridge : RawAdequacyReevaluation)
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis}
    {v : ValExpr}
    (call : RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v) :
    exists vS tauV,
      S.Term Delta Gamma Psi e b vS tauV /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] vS) := by
  obtain ⟨vS, tauV, hS⟩ := bridge call
  exact ⟨vS, tauV, hS,
    RawPublicCandidate.term orc call.oracle hS sigma GammaV call.consistent⟩

theorem rawResult_of_adequacyPreservingReevaluation
    (bridge : AdequacyPreservingReevaluation)
    {orc : FFSOracleSem} {rho : ValEnvSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis}
    {v : ValExpr}
    (call : RawAdequacyCall orc rho Delta Gamma Psi GammaV sigma e b v) :
    exists tauV,
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma e)
        (denotValB_semS orc rho [] [] v) := by
  obtain ⟨vS, tauV, hS, hden⟩ := bridge call
  refine ⟨tauV, ?_⟩
  rw [hden]
  exact RawPublicCandidate.term orc call.oracle hS sigma GammaV call.consistent

end OperationalStrengthening
end GLang
