import GLang.Proofs.Preservation.OperationalTypedContextSoundness
import GLang.Proofs.Value.Runtime.RuntimeValueCompatibility
import GLang.Proofs.Preservation.ApplicationCodomain
import GLang.Elaboration.PaperRules
import GLang.Proofs.Source.SourceContextInductive
import GLang.Proofs.Progress.Supporting.CategoryProgress
import GLang.Proofs.Value.Soundness.ValueSoundVals
import GLang.Proofs.Preservation.OrdinarySpacePreservation
import GLang.Proofs.Preservation.CobPreservationProgress
import GLang.Proofs.Adequacy.Total.DirectPublic
import GLang.Proofs.Adequacy.Partial.Source.PartialSourcePublic
import GLang.Proofs.Value.Partial.PartialValueCorrespondence
import GLang.Proofs.Basis.BasisOrthonormalAt
import GLang.Proofs.Preservation.CobEndpointPreservation
import GLang.Proofs.Adequacy.Raw.RawDirectMutualMaster
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardNatProgress

namespace GLang
namespace Metatheory

theorem surfaceElaborationUnique {Δ ε e t} (hw : InductiveCtxWF Δ ε)
    (h : Surface.HasType Δ.erase ε.erase e t) :
    ∃! p, SurfaceElaboration.TermLift Δ ε e t p :=
  SurfacePaper.elaborate_unique hw h

/-- Reconstruct an internal context from surface context formation and obtain
a unique annotated term/type pair in that context. -/
theorem surfaceTypingUnique {d g e t} (hw : Surface.InductiveCtxWF d g)
    (h : Surface.HasType d g e t) :
    ∃ (D : LCtx) (E : NLCtx),
      D.erase = d ∧ E.erase = g ∧ InductiveCtxWF D E ∧
      ∃! p, SurfaceElaboration.TermLift D E e t p :=
  SurfacePaper.typing_unique hw h

theorem sourceSoundness
    {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (htyped : HasType Δ ε e τ)
    {σ : DEnv} (hctx : InductiveCtxWF Δ ε) (henv : EnvWF σ Δ ε) :
    StrongSourceSoundProp σ Δ ε e τ :=
  hctx.sourceTermSoundness htyped henv

theorem sourceSoundnessWeak
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (htyped : HasType Delta Gamma e tau)
    {sigma : DEnv}
    (hctx : CtxWF Delta Gamma)
    (henv : EnvWF sigma Delta Gamma) :
    SoundClaim sigma Delta e tau :=
  GLang.soundness htyped hctx henv

theorem sourceTermSoundness
    {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (htyped : HasType Δ ε e τ)
    {σ : DEnv}
    (hctx : InductiveCtxWF Δ ε)
    (henv : EnvWF σ Δ ε) :
    StrongSourceSoundProp σ Δ ε e τ :=
  sourceSoundness htyped hctx henv

/-- Source-space regularity: validity gives local closure, context scoping, and
denotational invariance under environments agreeing on that context. -/
theorem sourceSpaceRegularity
    {Gamma : NLCtx} {s : Space}
    (hvalid : SValid Gamma s) :
    Space.lc s /\
      Space.fv s ⊆ Gamma.keys /\
      forall {sigma1 sigma2 : DEnv},
        sigma1.AgreeOn sigma2 Gamma.keys ->
          denotSpace sigma1 s = denotSpace sigma2 s := by
  exact ⟨hvalid.lc, hvalid.fv_closure,
    fun hagree => denotSpace_agree s (hagree.mono hvalid.fv_closure)⟩

/-- Source-space soundness spelling of `sourceSpaceRegularity`.  A semantic
space is intrinsically a valid denotation, so closure, scope, and environment
invariance are the substantive source-space claims. -/
theorem sourceSpaceSoundness
    {Gamma : NLCtx} {s : Space}
    (hvalid : SValid Gamma s) :
    Space.lc s /\
      Space.fv s ⊆ Gamma.keys /\
      forall {sigma1 sigma2 : DEnv},
        sigma1.AgreeOn sigma2 Gamma.keys ->
          denotSpace sigma1 s = denotSpace sigma2 s :=
  sourceSpaceRegularity hvalid

/-- Source-type regularity: validity gives local closure, context scoping, and
denotational invariance under environments agreeing on that context. -/
theorem sourceTypeRegularity
    {Gamma : NLCtx} {tau : Ty} {k : Kind}
    (hvalid : TValid Gamma tau k) :
    Ty.lc tau /\
      Ty.fv tau ⊆ Gamma.keys /\
      forall {sigma1 sigma2 : DEnv},
        sigma1.AgreeOn sigma2 Gamma.keys ->
          denotTy sigma1 tau = denotTy sigma2 tau := by
  exact ⟨hvalid.lc, hvalid.fv_closure,
    fun hagree => denotTy_agree tau (hagree.mono hvalid.fv_closure)⟩

/-- Source-type soundness spelling of `sourceTypeRegularity`.  Semantic types
are intrinsically valid codomains, so closure, scope, and environment
invariance are the substantive source-type claims. -/
theorem sourceTypeSoundness
    {Gamma : NLCtx} {tau : Ty} {k : Kind}
    (hvalid : TValid Gamma tau k) :
    Ty.lc tau /\
      Ty.fv tau ⊆ Gamma.keys /\
      forall {sigma1 sigma2 : DEnv},
        sigma1.AgreeOn sigma2 Gamma.keys ->
          denotTy sigma1 tau = denotTy sigma2 tau :=
  sourceTypeRegularity hvalid

/-- Every valid source basis denotes a recursively sound semantic basis. -/
theorem sourceBasisSoundness
    {sigma : DEnv} {Gamma : NLCtx} {b : Basis}
    (hvalid : Basis.BasisValid Gamma b)
    (hctx : InductiveCtxWF ∅ Gamma)
    (henv : EnvWF sigma ∅ Gamma) :
    Adequacy.Direct.BasisAt sigma [] (Basis.tof b) (denotBasis sigma b) :=
  Adequacy.Direct.basisAt hvalid hctx.toSourceContextWF.scoping henv

/-- **Standard-basis soundness, including dependent frames.**

For every valid source type, the denotation of its syntax-directed standard
basis is aligned with that source type and recursively complete (`BasisAt`),
and it is intrinsically orthonormal throughout its entire semantic shape.  At
a vector leaf the Gram matrix is the identity; at a frame the domain basis and
every semantic codomain fiber satisfy the same property recursively.

The adjacent theorems `Basis.tof_std`, `Basis.std_valid`, and
`Basis.isStd_std` expose the corresponding syntax-side facts.  They are not
duplicated in this semantic conclusion. -/
theorem standardBasisSoundness
    {sigma : DEnv} {Gamma : NLCtx} {tau : Ty} {k : Kind}
    (hvalid : TValid Gamma tau k)
    (hctx : InductiveCtxWF ∅ Gamma)
    (henv : EnvWF sigma ∅ Gamma) :
    Adequacy.Direct.BasisAt sigma [] tau
        (denotBasis sigma (Basis.std tau)) /\
      (denotBasis sigma (Basis.std tau)).RecursiveOrthonormal := by
  constructor
  · simpa only [Basis.tof_std] using
      sourceBasisSoundness (sigma := sigma) (Gamma := Gamma)
        (b := Basis.std tau) (Basis.std_valid tau hvalid) hctx henv
  · exact stdBasis_orthonormal sigma Gamma tau hvalid

/-! ## Value soundness

Dimension errors propagate through shape calculations. Type regularity uses
value typing and context validity. Term soundness uses value typing and
recursive membership of the semantic environment. -/

/-- Partial degrees of freedom are the product of a successful shape;
shape failures retain their error. -/
theorem valueShapeSoundness (orc : PartialFFSOracle) (s : ValSpace) :
    ValSpace.dofPartial orc s = (do
      let shape ← ValSpace.shpOfPartial orc s
      pure (shape.foldr (· * ·) 1)) := by
  rw [ValSpace.dofPartial]

/-- Value-type soundness with its minimal environmental premise.  A typed
value expression has a valid result type at some value kind whenever the
types stored in its value context are valid. -/
theorem valueTypeSoundness
    {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (htyped : ValHasType epsilon e tau)
    (hctx : ValCtxValid epsilon) :
    exists k, Nonempty (ValTValid epsilon tau k) := by
  obtain ⟨k, hvalid⟩ := htyped.regular hctx
  exact ⟨k, ⟨hvalid⟩⟩

/-- Oracle-polymorphic canonical value-denotation soundness.  The named
environment and local type/value stacks are arbitrary and no oracle law is
required.  A `DimError` remains allowed; every successful checked result has
exact canonical storage at the static value type. -/
theorem valueSoundnessOfOracle
    (orc : FFSOracleSem)
    (rho : ValEnvSem) (Gamma : List ValTy) (Delta : List ValValSem)
    {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (htyped : ValHasType epsilon e tau) :
    ValCanonicalResultSoundOfDenotSemS orc rho Gamma Delta tau
      (denotValB_semSChecked orc rho Gamma Delta e) :=
  valHasType_denotValB_semSChecked_canonical
    orc rho Gamma Delta htyped

/-- Value-term soundness with no environment-validity or oracle-law premise. -/
theorem valueTermSoundnessLegacy
    (orc : FFSOracleSem)
    (rho : ValEnvSem) (Gamma : List ValTy) (Delta : List ValValSem)
    {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (htyped : ValHasType epsilon e tau) :
    ValCanonicalResultSoundOfDenotSemS orc rho Gamma Delta tau
      (denotValB_semSChecked orc rho Gamma Delta e) :=
  valueSoundnessOfOracle orc rho Gamma Delta htyped

theorem valueSoundnessLegacy
    (rho : ValEnvSem) (Gamma : List ValTy) (Delta : List ValValSem)
    {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (htyped : ValHasType epsilon e tau) :
    ValCanonicalResultSoundOfDenotSemS directOracle rho Gamma Delta tau
      (denotValB_semSChecked directOracle rho Gamma Delta e) :=
  valueSoundnessOfOracle directOracle rho Gamma Delta htyped

theorem valueSoundnessWeak
    (rho : ValEnvSem) (Gamma : List ValTy) (Delta : List ValValSem)
    {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (htyped : ValHasType epsilon e tau) :
    ValResultSoundOfDenotSemS directOracle rho Gamma Delta tau
      (denotValB_semSChecked directOracle rho Gamma Delta e) := by
  intro out hout
  exact ValCanonicalSoundOfDenotSemS.implies_sound directOracle tau rho
    Gamma Delta out (valueSoundnessLegacy rho Gamma Delta htyped out hout)

/-- Original value typing and recursive environment membership imply
soundness for the live partial evaluator, including arbitrary higher-order
functions and explicit errors. -/
theorem valueSoundness
    {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (rho : ValEnvSem)
    (henv : RuntimeValue.PartialEnvWF PartialDirectOracle.oracle epsilon rho)
    (htyped : RuntimeValue.ValHasType epsilon e tau) :
    PartialValueDomains.PartialCoherent tau
      (denotValTyPartial PartialDirectOracle.oracle rho [] [] tau)
      (denotValTyPartial PartialDirectOracle.oracle rho [] [] tau) ∧
    PaperValueDomains.PartialRel
      (PartialValueDomains.WorldRuntimeRelated PartialDirectOracle.oracle tau
        ⟨rho,[],[]⟩ ⟨rho,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle rho [] [] e)
      (denotValB_partial PartialDirectOracle.oracle rho [] [] e) :=
  RuntimeValue.partialValueDomainSoundness rho henv htyped

/-- Live partial value-term soundness; original typing is used directly. -/
theorem valueTermSoundness
    {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (rho : ValEnvSem)
    (henv : PartialValueDomains.PartialEnvWF PartialDirectOracle.oracle epsilon rho)
    (htyped : ValHasType epsilon e tau) :
    PartialValueDomains.PartialCoherent tau
      (denotValTyPartial PartialDirectOracle.oracle rho [] [] tau)
      (denotValTyPartial PartialDirectOracle.oracle rho [] [] tau) ∧
    PaperValueDomains.PartialRel
      (PartialValueDomains.WorldRuntimeRelated PartialDirectOracle.oracle tau
        ⟨rho,[],[]⟩ ⟨rho,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle rho [] [] e)
      (denotValB_partial PartialDirectOracle.oracle rho [] [] e) :=
  PartialValueDomains.partialValueDomainSoundness rho henv htyped

open PartialValueDomains PaperValueDomains PaperValueDomains.ExtensionalQuotient in
/-- The raw evaluator and checked interpretation yield the same recursive
partial value, at every original value type. -/
theorem valueDenotationCorrespondence {epsilon : ValCtx} {e : ValExpr} {tau : ValTy}
    (rho : ValEnvSem) (henv : PartialEnvWF PartialDirectOracle.oracle epsilon rho)
    (htyped : ValHasType epsilon e tau) :
    partialRecursiveResultEquiv tau _ (partialValueDomainSoundness rho henv htyped).1
      (Quotient.mk _ ⟨(denotValB_partial PartialDirectOracle.oracle rho [] [] e).bind tau.carrierFromVal,
        partial_extract_results (partialValueDomainSoundness rho henv htyped).2⟩) =
      partialValueDenotation rho henv htyped :=
  partialValueDenotation_raw_eq rho henv htyped

/-- Supporting exact-index preservation for a canonical checked term evaluation.  The
conclusion's `tauV` is the actual index carried by this supplied trace; no
second run of progress is used to select it. -/
theorem checkedPreservation
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {rhoScope : V2.ValScope} {e : Term} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hvalid : V2.EvalCtxValidPlus Psi)
    (hkeys : V2.KeyScope Psi rhoScope)
    (hstep : Operational.Term Delta Gamma Psi e b v tauV) :
    Operational.TyAt Gamma Psi b tauV /\
      ValTy.EvalT Psi (Basis.tof b) tauV /\
      (ValExpr.inferType v).structuralKind = tauV.structuralKind /\
      ValTyOk (ValExpr.inferType v) /\
      (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ rhoScope) := by
  have hrho : V2.RhoValid Psi rhoScope := by
    intro x b' v' _hx hlookup
    have hxKeys : x ∈ Psi.keyNames :=
      V2.mem_keyNames_of_lookup hlookup
    obtain ⟨htype, htypeFv, hvalueFv⟩ :=
      hvalid.rhoValid_keyNames x b' v' hxKeys hlookup
    exact ⟨htype, htypeFv.trans hkeys, hvalueFv.trans hkeys⟩
  obtain ⟨htyAt, heval, hreshape, hok, hfvs⟩ :=
    Operational.Term.preservationAtCore hvalid hrho hkeys hstep
  obtain ⟨k, ⟨hinfer⟩, ⟨htauV⟩⟩ := hreshape
  have hkind :
      (ValExpr.inferType v).structuralKind = tauV.structuralKind := by
    calc
      (ValExpr.inferType v).structuralKind = k :=
        (ValTValidC.kind_eq_structural hinfer).symm
      _ = tauV.structuralKind := ValTValidC.kind_eq_structural htauV
  exact ⟨htyAt, heval, hkind, hok, hfvs⟩

theorem checkedPreservationAt
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {rhoScope : V2.ValScope} {e : Term} {b : Basis}
    {v : ValExpr} {tauV : ValTy}
    (hvalid : V2.EvalCtxValidPlus Psi)
    (hkeys : V2.KeyScope Psi rhoScope)
    (hstep : Operational.Term Delta Gamma Psi e b v tauV) :
    OperationalStrengthening.CheckedPreservationAtConclusion
      Gamma Psi rhoScope b v tauV := by
  have hrho : V2.RhoValid Psi rhoScope := by
    intro x b' v' _hx hlookup
    have hxKeys : x ∈ Psi.keyNames :=
      V2.mem_keyNames_of_lookup hlookup
    obtain ⟨htype, htypeFv, hvalueFv⟩ :=
      hvalid.rhoValid_keyNames x b' v' hxKeys hlookup
    exact ⟨htype, htypeFv.trans hkeys, hvalueFv.trans hkeys⟩
  exact Operational.Term.preservationAtCore hvalid hrho hkeys hstep

/-- Public preservation for the literal result of a supplied unchecked step.
Its existential realization and every result fact come directly from
preservation of `hstep` itself; it neither assumes a checked judgment nor runs
progress to manufacture an index from another execution. -/
theorem preservationRegularity
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {b : Basis} {v : ValExpr}
    (hhistory : V2.CtxTele Delta Gamma Psi)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b)
    (hstep : Operational.Unchecked.OpStep Psi e b v) :
    exists tauV,
      ValTy.EvalT Psi (Basis.tof b) tauV /\
      (ValExpr.inferType v).structuralKind = tauV.structuralKind /\
      ValTyOk (ValExpr.inferType v) /\
      (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ Psi.keyNames) := by
  have hplus : V2.EvalCtxValidPlus Psi := hhistory.evalCtxValidPlus
  have hrho : V2.RhoValid Psi Psi.keyNames := hplus.rhoValid_keyNames
  have hkeys : V2.KeyScope Psi Psi.keyNames := V2.keyScope_keyNames Psi
  obtain ⟨hsof⟩ := hbvalid.sof_valid
  obtain ⟨⟨tauV, heval, hreshape⟩, hok, hfvs⟩ :=
    V2.preservation_master.2.2.2 hstep Delta Gamma Psi.keyNames
      hplus hrho hkeys htyped hsof
  obtain ⟨k, ⟨hinfer⟩, ⟨htauV⟩⟩ := hreshape
  have hkind :
      (ValExpr.inferType v).structuralKind = tauV.structuralKind := by
    calc
      (ValExpr.inferType v).structuralKind = k :=
        (ValTValidC.kind_eq_structural hinfer).symm
      _ = tauV.structuralKind := ValTValidC.kind_eq_structural htauV
  exact ⟨tauV, heval, hkind, hok, hfvs⟩

theorem preservation
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {b : Basis} {v : ValExpr}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b)
    (hstep : Operational.Unchecked.OpStep Psi e b v) :
    exists tauV,
      ValTy.EvalT Psi (Basis.tof b) tauV /\
      (ValExpr.inferType v).structuralKind = tauV.structuralKind /\
      ValTyOk (ValExpr.inferType v) /\
      (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ Psi.keyNames) ∧
      Nonempty (RuntimeValue.ValHasType GammaV v (ValExpr.inferType v)) := by
  obtain ⟨tauV,heval,hkind,hok,hfvs⟩ := preservationRegularity hhistory.erase htyped hbvalid hstep
  exact ⟨tauV,heval,hkind,hok,hfvs,hhistory.preservation hstep⟩

theorem ordinaryResultRegularity
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {b : Basis} {v : ValExpr}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b)
    (hstep : Operational.Unchecked.OpStep Psi e b v) :
    exists tauV,
      ValTy.EvalT Psi (Basis.tof b) tauV /\
      (ValExpr.inferType v).structuralKind = tauV.structuralKind /\
      ValTyOk (ValExpr.inferType v) /\
      (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ Psi.keyNames) :=
  preservationRegularity hhistory.erase htyped hbvalid hstep

/-- Explicit term-category spelling of public unchecked `preservation`. -/
theorem termPreservation
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {b : Basis} {v : ValExpr}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b)
    (hstep : Operational.Unchecked.OpStep Psi e b v) :
    exists tauV,
      ValTy.EvalT Psi (Basis.tof b) tauV /\
      (ValExpr.inferType v).structuralKind = tauV.structuralKind /\
      ValTyOk (ValExpr.inferType v) /\
      (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ Psi.keyNames) ∧
      Nonempty (RuntimeValue.ValHasType GammaV v (ValExpr.inferType v)) :=
  preservation hhistory htyped hbvalid hstep

/-- Semantic representation preservation for a checked trace whose retained
result index is a base space.  This is the substantive intermediate theorem
between kind-only regularity and exact value typing: the inferred result space
and the checked result space have the same complete flat-array shape under the
constructive oracle. -/
theorem checkedBaseShapePreservation
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {e : Term} {b : Basis}
    {v : ValExpr} {sv : ValSpace}
    (hstep : Operational.Term Delta Gamma Psi e b v (.space sv))
    (hconsistent :
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho) :
    ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] [])
        (ValExpr.inferSpaceCtx [] v) =
      ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] []) sv := by
  exact (PartialAdequacy.term_mutual hstep.toStrengthened).dof
    rfl (EvalCtx.Subctx.refl Psi) rho Delta Gamma sigma GammaV
    (NLCtxIncl.refl Gamma) hconsistent.typedHistory

private theorem rhoValidOfValidPlus
    {Psi : EvalCtx} {rhoScope : V2.ValScope}
    (hvalid : V2.EvalCtxValidPlus Psi)
    (hkeys : V2.KeyScope Psi rhoScope) :
    V2.RhoValid Psi rhoScope := by
  intro x b v _hx hlookup
  have hxKeys : x ∈ Psi.keyNames := V2.mem_keyNames_of_lookup hlookup
  obtain ⟨htype, htypeFv, hvalueFv⟩ :=
    hvalid.rhoValid_keyNames x b v hxKeys hlookup
  exact ⟨htype, htypeFv.trans hkeys, hvalueFv.trans hkeys⟩

/-- Public space preservation for the literal result of a supplied ordinary
space evaluation.  As for `termPreservation`, the semantic-free creation
history reconstructs the evaluator invariants; source-space validity and the
ordinary evaluation itself are the only category-specific premises. -/
theorem spacePreservation
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {s : Space} {sv : ValSpace}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (hvalid : SValid Gamma s)
    (hstep : Operational.Unchecked.EvalS Psi s sv) :
    Nonempty (ValSValidC sv) /\
      ValSpace.fv sv ⊆ Psi.keyNames ∧ Nonempty (RuntimeValue.ValSValid GammaV sv) := by
  obtain ⟨hk,hfv⟩ := Operational.Unchecked.EvalS.preservation hhistory.erase hvalid hstep
  exact ⟨hk,hfv,RuntimeValue.preservation_mutual.1 hstep GammaV hhistory.evalContext⟩

/-- Supporting preservation for canonical checked space evaluation, under
only the threadable evaluator invariant and the chosen output-name scope. -/
theorem checkedSpacePreservation
    {Psi : EvalCtx} {Gamma : NLCtx} {rhoScope : V2.ValScope}
    {s : Space} {sv : ValSpace}
    (hvalid : V2.EvalCtxValidPlus Psi)
    (hkeys : V2.KeyScope Psi rhoScope)
    (hstep : Operational.Space Gamma Psi s sv) :
    Nonempty (ValSValidC sv) /\ ValSpace.fv sv ⊆ rhoScope := by
  obtain ⟨hsource⟩ := (Operational.Space.toStrengthened hstep).svalid
  obtain ⟨hvalue, hfvs⟩ := V2.preservation_master.1
    (Operational.Space.toUnchecked hstep) (∅ : LCtx) Gamma rhoScope
    hvalid (rhoValidOfValidPlus hvalid hkeys) hkeys hsource
  exact ⟨hvalue, hfvs.trans hkeys⟩

/-- Preservation for canonical checked type evaluation, under only the
threadable evaluator invariant and the chosen output-name scope. -/
theorem typePreservation
    {Psi : EvalCtx} {Gamma : NLCtx} {rhoScope : V2.ValScope}
    {tau : Ty} {tauV : ValTy}
    (hvalid : V2.EvalCtxValidPlus Psi)
    (hkeys : V2.KeyScope Psi rhoScope)
    (hstep : Operational.Ty Gamma Psi tau tauV) :
    ValTyOk tauV /\ ValTy.fv tauV ⊆ rhoScope := by
  obtain ⟨k, ⟨hsource⟩⟩ := (Operational.Ty.toStrengthened hstep).tvalid
  obtain ⟨hvalue, hfvs⟩ := V2.preservation_master.2.1
    (Operational.Ty.toUnchecked hstep) (∅ : LCtx) Gamma rhoScope k
    hvalid (rhoValidOfValidPlus hvalid hkeys) hkeys hsource
  exact ⟨hvalue, hfvs.trans hkeys⟩

/-- Public change-of-basis preservation for the literal witness of a supplied
ordinary evaluation.  As for term preservation, a creation history and source
validity classify the result of that same run; no checked trace or second
evaluation is assumed.  The two realized factors may be rectangular in the
FFS conversion rules. -/
theorem cobPreservation
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (hbvalid : Basis.BasisValid Gamma bSrc)
    (hstep : Operational.Unchecked.EvalBB Psi bSrc env bTgt) :
    CobShapeT Psi env Psi.keyNames ∧
      Nonempty (RuntimeValue.ValHasType GammaV env (ValExpr.inferType env)) :=
  ⟨Operational.Cob.ordinaryPreservation hhistory.erase hbvalid hstep,
    RuntimeValue.preservation_mutual.2.2.1 hstep GammaV hhistory.evalContext⟩

/-- Supporting preservation for canonical checked change-of-basis evaluation.
The result records the matrix-shaped witness, value-type validity, and name
scope; the two realized factors may be rectangular in the FFS conversion
rules. -/
theorem checkedCobPreservation
    {Psi : EvalCtx} {Gamma : NLCtx} {rhoScope : V2.ValScope}
    {bSrc bTgt : Basis} {env : ValExpr}
    (hvalid : V2.EvalCtxValidPlus Psi)
    (hkeys : V2.KeyScope Psi rhoScope)
    (hstep : Operational.Cob Gamma Psi bSrc env bTgt) :
    CobShapeT Psi env rhoScope := by
  have hchecked := Operational.Cob.toStrengthened hstep
  obtain ⟨hsource⟩ := hchecked.basisValid_src.sof_valid
  obtain ⟨hshape, hvalue, hfvs⟩ := V2.preservation_master.2.2.1
    (Operational.Cob.toUnchecked hstep) (∅ : LCtx) Gamma rhoScope
    hvalid (rhoValidOfValidPlus hvalid hkeys) hkeys hsource
  exact ⟨hshape, hvalue, hfvs.trans hkeys⟩

/-- Checked term progress from the semantic-free operational creation history,
source typing, and validity of the requested basis.  The chosen value is
retagged at the exact checked realization, so both public syntactic inferers
recover that realization exactly. -/
theorem progress
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b) :
    exists v tauV,
      Operational.Term Delta Gamma Psi e b v tauV /\
      ValExpr.inferType v = tauV /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV :=
  Operational.Term.progress
    { history := hhistory.erase, typed := htyped, basisValid := hbvalid }

/-- Explicit term-category spelling of `progress`. -/
theorem termProgress
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b) :
    exists v tauV,
      Operational.Term Delta Gamma Psi e b v tauV /\
      ValExpr.inferType v = tauV /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV :=
  progress hhistory htyped hbvalid

theorem ordinaryProgress
    (call : Operational.ProgressCall Delta Gamma Psi e b) :
    exists v, Operational.Unchecked.OpStep Psi e b v :=
  Operational.Term.ordinaryProgress call

/-- Ordinary progress for a valid source space in a standard-complete
operational environment. -/
theorem spaceProgress
    {Gamma : NLCtx} {Psi : EvalCtx} {s : Space}
    (hvalid : SValid Gamma s)
    (hcarrier : V2.PCarrier Psi)
    (hcovered : V2.VarsCovered ∅ Gamma Psi) :
    exists sv, Operational.Unchecked.EvalS Psi s sv :=
  V2.progress_master_std.1 hvalid Psi hcarrier hcovered

/-- Ordinary progress for a valid source type in a standard-complete
operational environment.  The second conjunct retains the dependent-function
anchor needed by higher-order progress. -/
theorem typeProgress
    {Gamma : NLCtx} {Psi : EvalCtx} {tau : Ty} {k : Kind}
    (hvalid : TValid Gamma tau k)
    (hcarrier : V2.PCarrier Psi)
    (hcovered : V2.VarsCovered ∅ Gamma Psi) :
    (exists tauV, Operational.Unchecked.EvalT Psi tau tauV) /\
      (forall tau0 tau1, tau = .piTy tau0 tau1 ->
        V2.StdPiAnchored Psi tau0 tau1) :=
  V2.progress_master_std.2.1 hvalid Psi hcarrier hcovered

/-- Ordinary change-of-basis progress from a valid hereditary space basis to
the literal standard basis of its type. -/
theorem basisProgress
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (hcarrier : V2.PCarrier Psi)
    (hcovered : V2.VarsCovered ∅ Gamma Psi)
    (hvalid : Basis.BasisValid Gamma b)
    (hisSpaceBasis : Basis.tof b = .space (Basis.sof b)) :
    exists env,
      Operational.Unchecked.EvalBB Psi b env (Basis.std (Basis.tof b)) :=
  V2.progress_cob_master hcarrier hcovered hvalid
    (hvalid.isTyBasis.toIsSpaceBasis_of_tof_eq hisSpaceBasis)

/-- Checked space progress from the same joint creation history used by term
progress. -/
theorem checkedSpaceProgress
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {s : Space}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (hvalid : SValid Gamma s) :
    exists sv, Operational.Space Gamma Psi s sv :=
  Operational.Space.progress hhistory.erase hvalid

/-- Checked type progress from the joint creation history.  The canonical
standard basis supplies the dependent-frame representation choices. -/
theorem checkedTypeProgress
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {tau : Ty} {k : Kind}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (hvalid : TValid Gamma tau k) :
    exists tauV, Operational.Ty Gamma Psi tau tauV :=
  Operational.Ty.progress hhistory.erase hvalid

/-- Checked type progress at a literal requested basis.  `BasisValid` already
contains validity of `Basis.tof b`, so no duplicate `TValid` premise is
needed. -/
theorem checkedTypeProgressAtBasis
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (hbvalid : Basis.BasisValid Gamma b) :
    exists tauV, Operational.TyAt Gamma Psi b tauV :=
  Operational.TyAt.progress hhistory.erase hbvalid

/-- Checked change-of-basis progress from the joint creation history. -/
theorem checkedBasisProgress
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (hbvalid : Basis.BasisValid Gamma b)
    (hisSpaceBasis : Basis.tof b = .space (Basis.sof b)) :
    exists env,
      Operational.Cob Gamma Psi b env (Basis.std (Basis.tof b)) :=
  Operational.Cob.progressToStandard hhistory.erase hbvalid hisSpaceBasis

/-- Checked change-of-basis progress between arbitrary compatible endpoint
bases. -/
theorem checkedCobProgress
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (hsrcValid : Basis.BasisValid Gamma bSrc)
    (htgtValid : Basis.BasisValid Gamma bTgt)
    (hsrcSpace : Basis.tof bSrc = .space (Basis.sof bSrc))
    (htypes : Basis.tof bSrc = Basis.tof bTgt) :
    exists env, Operational.Cob Gamma Psi bSrc env bTgt :=
  Operational.Cob.progressBetween hhistory.erase hsrcValid htgtValid hsrcSpace
    htypes

/-- Term adequacy for canonical checked operational evaluation and the
constructive direct oracle.  The value denotation remains the raw,
error-capable evaluator; `ResultAgree` itself proves that it returns `.ok`. -/
theorem termAdequacy
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hstep : Operational.Term Delta Gamma Psi e b v tauV) :
    forall (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho ->
      Adequacy.PartialDirect.ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (Adequacy.PartialDirect.evalVal rho [] [] v) /\
        Adequacy.PartialDirect.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) :=
  Adequacy.PartialDirect.term hstep

/-- Canonical checked-space adequacy for the constructive direct oracle.  The
compiled value-space shape is exactly the denoted source-space shape. -/
theorem spaceAdequacy
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {sv : ValSpace}
    (hstep : Operational.Space Gamma Psi s sv) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho ->
      ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] []) sv = .ok (srcShp sigma [] s) :=
  Adequacy.PartialDirect.space hstep

/-- Basis adequacy is the recursively strong source-basis soundness fact under
the category name used by the adequacy facade. -/
theorem basisAdequacy
    {sigma : DEnv} {Gamma : NLCtx} {b : Basis}
    (hvalid : Basis.BasisValid Gamma b)
    (hctx : InductiveCtxWF ∅ Gamma)
    (henv : EnvWF sigma ∅ Gamma) :
    Adequacy.Direct.BasisAt sigma [] (Basis.tof b) (denotBasis sigma b) :=
  sourceBasisSoundness hvalid hctx henv

/-- Checked progress followed immediately by adequacy for the constructive
direct oracle.  Consistency supplies the semantic-free creation history;
typing and requested-basis validity suffice to construct the checked trace.
All exact anchors, finite/depth certificates, and root transport are internal. -/
theorem checkedProgressAdequacy
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv}
    {e : Term} {b : Basis}
    (hconsistent :
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b) :
    exists v tauV,
      Operational.Term Delta Gamma Psi e b v tauV /\
      ValExpr.inferType v = tauV /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV /\
      Adequacy.PartialDirect.ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (Adequacy.PartialDirect.evalVal rho [] [] v) /\
        Adequacy.PartialDirect.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) := by
  let call : Operational.ProgressCall Delta Gamma Psi e b :=
    { history := hconsistent.history.ctxTele
      typed := htyped
      basisValid := hbvalid }
  obtain ⟨v, tauV, hchecked, hinfer, hinferSpace⟩ :=
    Operational.Term.progress call
  obtain ⟨hresult, hdims⟩ :=
    Adequacy.PartialDirect.term hchecked sigma GammaV hconsistent
  exact ⟨v, tauV, hchecked, hinfer, hinferSpace, hresult, hdims⟩

/-- Concrete unary-certificate form of `checkedProgressAdequacy`.  The root
basis remains explicitly valid and carries only its own syntax-local finite
evidence; consistency supplies the evaluator invariants used to turn that
evidence into the abstract root boundary.  No selected-to-standard pair is a
premise. -/
theorem checkedProgressAdequacy_ofRootLocalFinite
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv}
    {e : Term} {b : Basis}
    (hconsistent :
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b)
    (hroot : Operational.RootBasisLocalFinite Psi hbvalid) :
    exists v tauV,
      Operational.Term Delta Gamma Psi e b v tauV /\
      ValExpr.inferType v = tauV /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV /\
      Adequacy.PartialDirect.ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (Adequacy.PartialDirect.evalVal rho [] [] v) /\
        Adequacy.PartialDirect.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) :=
  checkedProgressAdequacy hconsistent htyped hbvalid

theorem checkedProgressAdequacy_ofPairCertificate_compat
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv}
    {e : Term} {b : Basis}
    (hconsistent :
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b)
    (requestedPair :
      RawCertifiedPairCertificate.CheckedPairBasisFinite Psi Gamma
        (Basis.std (Basis.tof b)) b) :
    exists v tauV,
      Operational.Term Delta Gamma Psi e b v tauV /\
      ValExpr.inferType v = tauV /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV /\
      Adequacy.PartialDirect.ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (Adequacy.PartialDirect.evalVal rho [] [] v) /\
        Adequacy.PartialDirect.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) :=
  checkedProgressAdequacy hconsistent htyped hbvalid

/-- Checked progress followed immediately by adequacy for the constructive
direct oracle, with the unary judgment-local reconstruction certificate
supplied explicitly. -/
theorem checkedProgressAdequacy_explicitCertificate
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv}
    {e : Term} {b : Basis}
    (hconsistent :
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b)
    (hlocal :
      Operational.CheckedProgressAdmissible Psi htyped hbvalid) :
    exists v tauV,
      Operational.Term Delta Gamma Psi e b v tauV /\
      ValExpr.inferType v = tauV /\
      ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV /\
      Adequacy.PartialDirect.ResultAgree sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) (denotTerm sigma e)
          (Adequacy.PartialDirect.evalVal rho [] [] v) /\
        Adequacy.PartialDirect.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
          (denotBasis sigma b) := by

  exact checkedProgressAdequacy hconsistent htyped hbvalid

/-- Change-of-basis adequacy for canonical checked evaluation and the
constructive direct oracle. -/
theorem cobAdequacy
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {bSrc bTgt : Basis} {env : ValExpr}
    (hstep : Operational.Cob Gamma Psi bSrc env bTgt) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho ->
      Adequacy.PartialDirect.CobAgree sigma rho bSrc bTgt env :=
  Adequacy.PartialDirect.cob hstep

/-- Dimension adequacy at the exact basis retained by canonical checked type
evaluation, using the constructive direct oracle. -/
theorem dimensionAdequacy
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy}
    (hstep : Operational.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho ->
      Adequacy.PartialDirect.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  Adequacy.PartialDirect.typeAt hstep

/-- Type adequacy at the exact source basis retained by checked type
evaluation.  This descriptive spelling makes the basis index explicit. -/
theorem typeAdequacyAtBasis
    {rho : ValEnvSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {tauV : ValTy}
    (hstep : Operational.TyAt Gamma Psi b tauV) :
    forall (Delta : LCtx) (sigma : DEnv) (GammaV : ValCtx),
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho ->
      Adequacy.PartialDirect.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) :=
  dimensionAdequacy hstep

/-! ## Category progress followed by adequacy

These are the non-term companions of `checkedProgressAdequacy`.  In each
case consistency is used first only for its semantic-free creation history;
the same checked result is then passed to the corresponding adequacy theorem.
-/

/-- Checked space progress and shape adequacy for one shared result. -/
theorem spaceProgressAdequacy
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv} {s : Space}
    (hconsistent :
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho)
    (hvalid : SValid Gamma s) :
    exists sv,
      Operational.Space Gamma Psi s sv /\
      ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] []) sv = .ok (srcShp sigma [] s) := by
  obtain ⟨sv, hstep⟩ := checkedSpaceProgress
    (Adequacy.PartialDirect.contextHistory hconsistent) hvalid
  exact ⟨sv, hstep, spaceAdequacy hstep Delta sigma GammaV hconsistent⟩

/-- Exact-basis checked type progress and dimension adequacy for one shared
realization. -/
theorem typeProgressAdequacyAtBasis
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv} {b : Basis}
    (hconsistent :
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho)
    (hbvalid : Basis.BasisValid Gamma b) :
    exists tauV,
      Operational.TyAt Gamma Psi b tauV /\
      Adequacy.PartialDirect.AgreeDims sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) := by
  obtain ⟨tauV, hstep⟩ := checkedTypeProgressAtBasis
    (Adequacy.PartialDirect.contextHistory hconsistent) hbvalid
  exact ⟨tauV, hstep,
    dimensionAdequacy hstep Delta sigma GammaV hconsistent⟩

/-- Checked conversion to the standard basis and COB adequacy for the same
conversion value. -/
theorem basisProgressAdequacy
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv} {b : Basis}
    (hconsistent :
      Adequacy.PartialDirect.Consistent Delta Gamma Psi GammaV sigma rho)
    (hbvalid : Basis.BasisValid Gamma b)
    (hisSpaceBasis : Basis.tof b = .space (Basis.sof b)) :
    exists env,
      Operational.Cob Gamma Psi b env (Basis.std (Basis.tof b)) /\
      Adequacy.PartialDirect.CobAgree sigma rho b (Basis.std (Basis.tof b)) env := by
  obtain ⟨env, hstep⟩ := checkedBasisProgress
    (Adequacy.PartialDirect.contextHistory hconsistent)
    hbvalid hisSpaceBasis
  exact ⟨env, hstep, cobAdequacy hstep Delta sigma GammaV hconsistent⟩

end Metatheory
end GLang
