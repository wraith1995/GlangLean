import GLang.Proofs.Adequacy.Raw.Context.RawTypedConsistent
import GLang.Proofs.Adequacy.Raw.RawInferredDomainDims
import GLang.Proofs.Adequacy.Raw.Context.RawConsistentType
import GLang.Proofs.Adequacy.Raw.RawNonBetaValueKernel
import GLang.Proofs.Adequacy.Foundations.StrengthenedMono
import GLang.Proofs.Adequacy.Raw.RawSourceBridge
import GLang.Proofs.Source.Soundness
import GLang.Proofs.Value.Soundness.ValueSoundnessSem

/-!
# Core ordinary-trace adequacy arms

This module packages the root-stack raw term trace used by the direct
non-beta adequacy induction.  The trace is polymorphic over evaluator and
source-context extensions, which is enough to recurse beneath nonlinear
binders without retaining syntax provenance, future-world records, recursive
constructor carriers, or beta certificates.

All evaluator-facing value facts come from the constructive current
theorem `RawNonBetaValueKernel.holds`.
-/

set_option maxHeartbeats 1200000
namespace GLang
open Basis (BasisValid)

/-- Lower-layer spelling of context inclusion. -/
def RawCtxIncl (Delta : LCtx) (Gamma : NLCtx)
    (Delta' : LCtx) (Gamma' : NLCtx) : Prop :=
  (forall x s, Delta.lookup x = some s ->
    Delta'.lookup x = some s \/ Gamma'.lookup x = some (.space s)) /\
  NLCtxIncl Gamma Gamma'

/-- Exact-basis type motive, strengthened only by evaluator-context
monotonicity. -/
def RawMTyAtSubctx (orc : FFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (b : Basis) (tauv : ValTy) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    RawMTyAt orc (RawTypedConsistent orc) Gamma Psi' b tauv

/-- Current term motive.  It quantifies directly over every
larger evaluator context and source context, so an opened `nllam` body can be
invoked at the freshly extended current world without storing a separate
Kripke object. -/
def RawMTermTraceSubctx (orc : FFSOracleSem) (Delta : LCtx)
    (Gamma : NLCtx) (Psi : EvalCtx) (e : Term) (b : Basis)
    (v : ValExpr) (tauv : ValTy) : Prop :=
  forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    Graded.CtxDisj Delta Gamma ->
    forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
      (sigma : DEnv) (GammaV : ValCtx),
      RawCtxIncl Delta Gamma Delta' Gamma' ->
      RawTypedConsistent orc Delta' Gamma' Psi' GammaV sigma rho ->
      RawTermTraceAt orc sigma rho v (Basis.tof b) tauv
        (denotBasis sigma b) (denotTerm sigma e)

/-! ## Structural same-shape facts -/

/-- Context-free valid value types at the same kind have the same outer
space/function skeleton. -/
theorem valTValidC_sameShape_of_sameKind (k : ValKind) :
    forall {tauv tauv' : ValTy}, ValTValidC tauv k -> ValTValidC tauv' k ->
      ValSoundOfDenot.ValTy.SameShape tauv tauv' := by
  induction k with
  | base =>
      intro tauv tauv' h h'
      cases h
      cases h'
      trivial
  | arrow k0 k1 ih0 ih1 =>
      intro tauv tauv' h h'
      cases h with
      | piTy L h0 h1 =>
        cases h' with
        | piTy L' h0' h1' =>
          refine ⟨ih0 h0 h0', ?_⟩
          obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ L')
          rw [Finset.mem_union, not_or] at hx
          have hopen := ih1 (h1 x hx.1) (h1' x hx.2)
          exact
            ((ValSoundOfDenot.ValTy.SameShape_openRec
              0 (.var x _) _).symm.trans hopen).trans
              (ValSoundOfDenot.ValTy.SameShape_openRec 0 (.var x _) _)

/-- Two operational realizations of the same source type have the same
value-type skeleton, even when they were built in different contexts. -/
theorem evalT_sameShape
    {Psi Psi' : EvalCtx} {tau : Ty}
    {tauv tauv' : ValTy}
    (h : ValTy.EvalT Psi tau tauv) (h' : ValTy.EvalT Psi' tau tauv') :
    ValSoundOfDenot.ValTy.SameShape tauv tauv' := by
  have hk : tauv.structuralKind = tauv'.structuralKind := by
    rw [h.structuralKind_eq_sourceKind, h'.structuralKind_eq_sourceKind]
  exact valTValidC_sameShape_of_sameKind _
    (evalT_valid h).some (hk ▸ (evalT_valid h').some)

theorem sty_sameShape
    {Gamma Gamma' : NLCtx} {Psi Psi' : EvalCtx} {tau : Ty}
    {tauv tauv' : ValTy}
    (h : S.Ty Gamma Psi tau tauv) (h' : S.Ty Gamma' Psi' tau tauv') :
    ValSoundOfDenot.ValTy.SameShape tauv tauv' :=
  evalT_sameShape h.toEvalT h'.toEvalT

/-- Raw consistency recovers the shape of a function value's runtime domain.

The conditional mutual motive makes every non-term constructor and every
non-function-valued term case vacuous.  A variable case is the only place
where `inferTypeCtx` is opaque; there the exact compiled type stored in the
raw telescope connects the inferred annotation to the strengthened result.
-/
theorem S.Term.inferType_domain_sameShape_raw
    {DeltaS : LCtx} {GammaS : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauv0 tauv1 : ValTy}
    (h : S.Term DeltaS GammaS Psi e b v (.piTy tauv0 tauv1))
    {orc : FFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hc : RawConsistent orc DeltaC GammaC Psi GammaV sigma rho) :
    ValSoundOfDenot.ValTy.SameShape
      (ValExpr.inferTypeCtx [] v).domain tauv0 := by
  refine S.Term.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ Psi _ _ v tauv _ =>
      forall {dom cod : ValTy}, tauv = .piTy dom cod ->
      forall {orc : FFSOracleSem} {DeltaC : LCtx} {GammaC : NLCtx}
        {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem},
        RawConsistent orc DeltaC GammaC Psi GammaV sigma rho ->
        ValSoundOfDenot.ValTy.SameShape
          (ValExpr.inferTypeCtx [] v).domain dom)
    ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
    ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
    ?tySpace ?tyPi
    ?tyAtSpace ?tyAtFrame
    ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
    ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
    ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
    ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
    ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
    ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
    ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
    ?termAppL ?termAppI ?termNllam ?termAppNVal
    ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
    ?termZero ?termRlit h rfl hc
  case termVarLin =>
    intro Gamma Psi x b v s tauv hlookup _htof _hbv htauv _ihtauv
      dom cod htauvPi orc DeltaC GammaC GammaV sigma rho hc
    obtain ⟨vStored, tauStored, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
        sigma0, rho0, hstored, _hIncl, hPsi, _hsigma, _hctx⟩ :=
      hc.lookup (Finmap.mem_of_lookup_eq_some hlookup)
    have hv : vStored = v := Option.some.inj (hPsi.symm.trans hlookup)
    subst vStored
    have hinfer : ValExpr.inferTypeCtx [] v = tauStored := by
      rw [inferTypeCtx_of_lc [] hstored.hlc, hstored.hinfer]
    have hshape : ValSoundOfDenot.ValTy.SameShape tauStored tauv :=
      evalT_sameShape hstored.hTy htauv.toEvalT
    rw [hinfer]
    simpa only [htauvPi, ValTy.domain_piTy] using hshape.domain
  case termVarNlin =>
    intro Gamma Psi x b v tauv hlookup _hGamma _hbv htauv _ihtauv
      dom cod htauvPi orc DeltaC GammaC GammaV sigma rho hc
    obtain ⟨vStored, tauStored, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
        sigma0, rho0, hstored, _hIncl, hPsi, _hsigma, _hctx⟩ :=
      hc.lookup (Finmap.mem_of_lookup_eq_some hlookup)
    have hv : vStored = v := Option.some.inj (hPsi.symm.trans hlookup)
    subst vStored
    have hinfer : ValExpr.inferTypeCtx [] v = tauStored := by
      rw [inferTypeCtx_of_lc [] hstored.hlc, hstored.hinfer]
    have hshape : ValSoundOfDenot.ValTy.SameShape tauStored tauv :=
      evalT_sameShape hstored.hTy htauv.toEvalT
    rw [hinfer]
    simpa only [htauvPi, ValTy.domain_piTy] using hshape.domain
  all_goals
    simp_all [ValExpr.applyAt, ValExpr.inferTypeCtx]

/-- The codomain recorded by a strengthened function result and the separately
compiled instantiated output have the same structural skeleton.  This fact
forgets dimensions; the exact result-type induction hypothesis supplies those
separately at the application basis. -/
theorem appN_codomain_sameShape
    {GammaFun GammaOut : NLCtx} {PsiFun PsiOut : EvalCtx}
    {b0 b1 : Basis}
    {n0 n1 : Term} {env0 : ValExpr} {tauv0 tauv1 tauOut : ValTy}
    (h0 : S.Term ∅ GammaFun PsiFun n0 (.frame b0 b1) env0
      (.piTy tauv0 tauv1))
    (hOut : S.TyAt GammaOut PsiOut (Basis.instantiate n1 b1) tauOut) :
    ValSoundOfDenot.ValTy.SameShape tauv1 tauOut := by
  obtain ⟨hvalidFun⟩ := evalT_valid h0.toEvalT
  cases hvalidFun with
  | piTy L _hdom hcod =>
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset L
      have hvalidCod := hcod y hy
      have hvalidOut := Classical.choice (evalT_valid hOut.toEvalT)
      have hfunKind := h0.toEvalT.structuralKind_eq_sourceKind
      simp only [Basis.tof, ValTy.structuralKind, Ty.sourceKind] at hfunKind
      injection hfunKind with _ hcodKind
      have houtKind : tauOut.structuralKind =
          (Basis.tof b1).sourceKind := by
        simpa only [Basis.instantiate, Basis.tof_openRec,
          Ty.sourceKind_openRec] using
          hOut.toEvalT.structuralKind_eq_sourceKind
      have hkind : tauv1.structuralKind = tauOut.structuralKind :=
        hcodKind.trans houtKind.symm
      have hvalidOutAt : ValTValidC tauOut tauv1.structuralKind := by
        rw [hkind]
        exact hvalidOut
      have hopen : ValSoundOfDenot.ValTy.SameShape
          (ValTy.openVar y tauv0 tauv1) tauOut :=
        valTValidC_sameShape_of_sameKind _ hvalidCod hvalidOutAt
      exact (ValSoundOfDenot.ValTy.SameShape_openRec
        0 (.var y tauv0) tauv1).symm.trans hopen

/-- Source typing under an empty linear context weakens directly along the
current nonlinear inclusion relation. -/
theorem hasType_mono_nl_raw
    {Gamma Gamma' : NLCtx} {e : Term} {tau : Ty}
    (h : Nonempty (HasType ∅ Gamma e tau))
    (hle : NLCtxIncl Gamma Gamma') :
    Nonempty (HasType ∅ Gamma' e tau) := by
  obtain ⟨h⟩ := h
  refine ⟨Graded.hasTypeBridgeBwd (Graded.CtxDisj.empty Gamma')
    (Graded.gradeWeaken
      (Graded.hasTypeBridge (Graded.CtxDisj.empty Gamma) h) ?_)⟩
  intro x
  simp only [Graded.tr, Finmap.lookup_empty]
  cases hx : Gamma.lookup x with
  | none =>
      cases hx' : Gamma'.lookup x with
      | none => trivial
      | some tau' =>
          exact (by decide : Graded.GGrade.omega ≠ Graded.GGrade.one)
  | some tau' =>
      have hx' : Gamma'.lookup x = some tau' := hle x tau' hx
      rw [hx']
      exact ⟨rfl, Graded.GGrade.Wk.refl _⟩

/-- Source nonlinear application is `DVal.applyEl` at the argument recovered
from its sound domain.  This is the small denotational equality needed when a
frame constructor manufactures a lambda body by applying an existing
function to its fresh binder. -/
theorem denotTerm_appN_applyEl_raw
    {sigma : DEnv} {n0 n1 : Term} {T0 : HType} {g : T0.El -> DVal}
    (hpi : denotTerm sigma n0 = .pi T0.El g)
    (hshape : (denotTerm sigma n1).matchesShape T0) :
    denotTerm sigma (.appN n0 n1) =
      (denotTerm sigma n0).applyEl (T0.extract (denotTerm sigma n1)) := by
  have hsource : denotTerm sigma (.appN n0 n1) =
      (denotTerm sigma n0).applyAsPi (denotTerm sigma n1) := rfl
  rw [hsource, hpi]
  simp only [DVal.applyAsPi, DVal.asPi]
  rw [show (denotTerm sigma n1).shape = T0 from hshape, dif_pos rfl]
  simp only [DVal.applyEl_pi]

/-- Extraction is a left inverse to the canonical raw embedding. -/
theorem htype_extract_embed_raw :
    forall (T : HType) (x : T.El), T.extract (T.embed x) = x
  | .hil _, _ => by simp [HType.extract, HType.embed]
  | .sec _ f, x => by
      simp only [HType.embed, HType.extract, dite_true]
      funext y
      exact htype_extract_embed_raw (f y) (x y)

theorem htype_embed_injective_raw (T : HType) :
    Function.Injective T.embed := by
  intro x y h
  have heq := congrArg T.extract h
  simpa only [htype_extract_embed_raw] using heq

theorem htype_embed_cast_raw {T U : HType} (h : T = U) (x : T.El) :
    U.embed (h ▸ x) = T.embed x := by
  cases h
  rfl

theorem dval_applyEl_hcast_raw {T U : HType} (h : T = U)
    (d : DVal) (x : T.El) :
    d.applyEl (h ▸ x) = d.applyEl x := by
  cases h
  rfl

def RawMDofTraceSubctx (orc : FFSOracleSem) (Gamma : NLCtx)
    (Psi : EvalCtx) (v : ValExpr) (tauV : ValTy) : Prop :=
  forall {sv : ValSpace}, tauV = .space sv ->
    forall {Psi' : EvalCtx}, Psi.Subctx Psi' ->
    forall (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
      (sigma : DEnv) (GammaV : ValCtx),
      NLCtxIncl Gamma Gamma' ->
      RawTypedConsistent orc Delta' Gamma' Psi' GammaV sigma rho ->
      ValSpace.shpOf (orc rho [] []) (ValExpr.inferSpaceCtx [] v) =
        ValSpace.shpOf (orc rho [] []) sv

end GLang
