import GLang.Proofs.Progress.MutualCertificates
import GLang.Proofs.Adequacy.Foundations.CofiniteFreshen

namespace GLang
namespace RawCertifiedPairCertificate

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike

/-- A syntactic guard preventing a positive-depth non-frame layer from
silently accepting the dependent-frame case. -/
def BasisNonFrame : Basis -> Prop
  | .frame _ _ => False
  | _ => True

/-- A depth-indexed concrete-pair certificate.  Root validity is supplied by
the executor; only the child/body validity facts actually used below a frame
binder remain in the certificate.  At depth zero the validity witnesses stay
packaged because `CheckedLocalSideBasisZero` is proof-indexed. -/
def CheckedPairBasisDepth (Psi : EvalCtx) :
    (crossDepth : Nat) -> (Gamma : NLCtx) ->
      (source target : Basis) -> Prop
  | 0, Gamma, source, target =>
      Basis.tof target = Basis.tof source /\
      (exists hs : Basis.BasisValid Gamma source,
        CheckedLocalSideBasisZero hs) /\
      (exists ht : Basis.BasisValid Gamma target,
        CheckedLocalSideBasisZero ht)
  | n + 1, Gamma, .frame b10 b11, .frame b20 b21 =>
      Basis.tof b20 = Basis.tof b10 /\
      Basis.tof b21 = Basis.tof b11 /\
      exists sourceAvoid targetAvoid : Finset Name,
      exists sourceDomainValid : Basis.BasisValid Gamma b10,
      exists targetDomainValid : Basis.BasisValid Gamma b20,
      exists sourceBodyValid : forall y, y ∉ sourceAvoid ->
        Basis.BasisValid (Finmap.insert y (Basis.tof b10) Gamma)
          (Basis.openVar y b11),
      exists targetBodyValid : forall y, y ∉ targetAvoid ->
        Basis.BasisValid (Finmap.insert y (Basis.tof b20) Gamma)
          (Basis.openVar y b21),
      -- Exact construction of each endpoint follows that endpoint's own
      -- literal domain before opening its own codomain.
      CheckedPairBasisDepth Psi (n + 1) Gamma b10 b10 /\
      CheckedPairBasisDepth Psi (n + 1) Gamma b20 b20 /\
      (forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
        forall (y : Name), y ∉ Psi'.names -> y ∉ sourceAvoid ->
          forall tauV10, C.TyAt Gamma Psi' b10 tauV10 ->
          let PsiX := Psi'.extend y b10 (.var y tauV10)
          let GammaX := Finmap.insert y (Basis.tof b10) Gamma
          CheckedPairBasisDepth PsiX (n + 1) GammaX
            (Basis.openVar y b11) (Basis.openVar y b11)) /\
      (forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
        forall (y : Name), y ∉ Psi'.names -> y ∉ targetAvoid ->
          forall tauV20, C.TyAt Gamma Psi' b20 tauV20 ->
          let PsiX := Psi'.extend y b20 (.var y tauV20)
          let GammaX := Finmap.insert y (Basis.tof b20) Gamma
          CheckedPairBasisDepth PsiX (n + 1) GammaX
            (Basis.openVar y b21) (Basis.openVar y b21)) /\
      forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
        forall (y : Name), y ∉ Psi'.names ->
          y ∉ sourceAvoid -> y ∉ targetAvoid ->
          forall tauV20, C.TyAt Gamma Psi' b20 tauV20 ->
          let PsiX := Psi'.extend y b20 (.var y tauV20)
          let GammaX := Finmap.insert y (Basis.tof b20) Gamma
          CheckedPairBasisDepth PsiX (n + 1) GammaX b20 b10 /\
          CheckedPairBasisDepth PsiX (n + 1) GammaX
            (Basis.openVar y b11) (Basis.openVar y b21)
  | _n + 1, _Gamma, .frame _ _, _target => False
  | _n + 1, _Gamma, _source, .frame _ _ => False
  | n + 1, Gamma, source, target =>
      let selected : EvalCtx -> CheckedSelectedBasisSide :=
        fun Psi' {Gamma'} {b} _hb =>
          CheckedPairBasisDepth Psi' n Gamma' b (Basis.std (Basis.tof b))
      BasisNonFrame source /\ BasisNonFrame target /\
      Basis.tof target = Basis.tof source /\
      CheckedLocalSideBasisSyntaxLayer Psi selected Gamma source /\
      CheckedLocalSideBasisSyntaxLayer Psi selected Gamma target
termination_by crossDepth Gamma source target =>
  (crossDepth, max (Basis.size source) (Basis.size target))
decreasing_by
  all_goals simp [Basis.size, Basis.size_openVar] <;> omega

def CheckedPairSelectedAt (Psi : EvalCtx) (n : Nat) :
    CheckedSelectedBasisSide :=
  fun {Gamma} {b} _hb =>
    CheckedPairBasisDepth Psi n Gamma b (Basis.std (Basis.tof b))

/-- Pointwise finiteness for one ordered pair.  The quantifier is inside the
pair request, so different concrete pair requests may choose different
depths. -/
def CheckedPairBasisFinite (Psi : EvalCtx) (Gamma : NLCtx)
    (source target : Basis) : Prop :=
  exists n, CheckedPairBasisDepth Psi n Gamma source target

/-- The final variable-leaf policy.  Each lookup selects one literal basis
and asks for one finite transport from that basis to its own standard basis.
There is no common depth across distinct evaluator keys. -/
def CheckedPairSelectedFinite (Psi : EvalCtx) : CheckedSelectedBasisSide :=
  fun {Gamma} {b} _hb =>
    CheckedPairBasisFinite Psi Gamma b (Basis.std (Basis.tof b))

/-- Proof-indexed facade for consumers that already carry the two root
validity derivations. -/
def CheckedPairBasisDepthAt (Psi : EvalCtx) (n : Nat)
    {Gamma : NLCtx} {source target : Basis}
    (_sourceValid : Basis.BasisValid Gamma source)
    (_targetValid : Basis.BasisValid Gamma target) : Prop :=
  CheckedPairBasisDepth Psi n Gamma source target

/-- Source typing trees equipped with the selected-pair basis policy. -/
abbrev CheckedPairLocalSideBases (Psi : EvalCtx) (n : Nat)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (ht : HasType Delta Gamma e tau) : Type :=
  CheckedLocalSideBasesWith (CheckedPairSelectedAt Psi n) Psi ht

abbrev CheckedPairLocalSideS (Psi : EvalCtx) (n : Nat)
    {Gamma : NLCtx} {s : Space} (hs : SValid Gamma s) : Type :=
  CheckedLocalSideSWith (CheckedPairSelectedAt Psi n) Psi hs

abbrev CheckedPairLocalSideT (Psi : EvalCtx) (n : Nat)
    {Gamma : NLCtx} {tau : Ty} {k : Kind}
    (ht : TValid Gamma tau k) : Type :=
  CheckedLocalSideTWith (CheckedPairSelectedAt Psi n) Psi ht

abbrev CheckedPairLocalSideSub (Psi : EvalCtx) (n : Nat)
    {Gamma : NLCtx} {s0 s1 : Space}
    (hs : SubType Gamma s0 s1) : Type :=
  CheckedLocalSideSubWith (CheckedPairSelectedAt Psi n) Psi hs

/-- Source evidence used at the public call boundary. -/
abbrev CheckedPairFiniteLocalSideBases (Psi : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (ht : HasType Delta Gamma e tau) : Type :=
  CheckedLocalSideBasesWith (CheckedPairSelectedFinite Psi) Psi ht

/-- Public checked-progress payload.  The source tree records concrete
selected-to-standard pairs, with an independent finite depth at each lookup.
The final requested basis is reached by one separately finite
standard-to-requested pair. -/
structure CheckedPairLocalCallFinite
    (Psi : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (ht : HasType Delta Gamma e tau)
    (requested : Basis) : Prop where
  termSide : Nonempty (CheckedPairFiniteLocalSideBases Psi ht)
  requestedPair : CheckedPairBasisFinite Psi Gamma (Basis.std tau) requested

/-- A promotion-normalized candidate typing proof for checked progress.  The
forward graded bridge absorbs every source `promote` constructor into grade
weakening, and the backward bridge reconstructs a source derivation of the
same judgment without reintroducing a promotion node.  Because the result is
proof-relevant, callers still build the local certificate for this exact
derivation (or choose any other convenient derivation of the same judgment). -/
noncomputable def normalizeCheckedTyping
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (hdisj : Graded.CtxDisj Delta Gamma)
    (ht : HasType Delta Gamma e tau) : HasType Delta Gamma e tau :=
  Graded.hasTypeBridgeBwd hdisj (Graded.hasTypeBridge hdisj ht)

/-- The canonical checked-typing normalizer really removes every promotion,
including promotions in FFS witnesses nested through formation premises. -/
theorem normalizeCheckedTyping_promotionFree
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (hdisj : Graded.CtxDisj Delta Gamma)
    (ht : HasType Delta Gamma e tau) :
    Graded.PromotionFree (normalizeCheckedTyping hdisj ht) :=
  Graded.hasTypeBridgeBwd_promotionFree hdisj
    (Graded.hasTypeBridge hdisj ht)

/-- Every source typing judgment in a disjoint context admits an equivalent
promotion-free proof object. -/
theorem exists_promotionFreeTyping
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (hdisj : Graded.CtxDisj Delta Gamma)
    (ht : HasType Delta Gamma e tau) :
    ∃ ht' : HasType Delta Gamma e tau, Graded.PromotionFree ht' :=
  ⟨normalizeCheckedTyping hdisj ht,
    normalizeCheckedTyping_promotionFree hdisj ht⟩

/-- The checked-typing normal form with every source binder additionally
reserving an ambient finite set.  The judgment indices are unchanged; only
the proof object's cofinite avoid sets are enlarged. -/
noncomputable def normalizeCheckedTypingAvoiding
    (A : Finset Name)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (hdisj : Graded.CtxDisj Delta Gamma)
    (ht : HasType Delta Gamma e tau) : HasType Delta Gamma e tau :=
  Adequacy.CofiniteFreshen.hasType A (normalizeCheckedTyping hdisj ht)

/-- Freshening the canonical checked-typing normal form does not reintroduce
promotion, including in source terms nested through formation premises. -/
theorem normalizeCheckedTypingAvoiding_promotionFree
    (A : Finset Name)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (hdisj : Graded.CtxDisj Delta Gamma)
    (ht : HasType Delta Gamma e tau) :
    Graded.PromotionFree (normalizeCheckedTypingAvoiding A hdisj ht) :=
  Adequacy.CofiniteFreshen.hasType_promotionFree A
    (normalizeCheckedTyping hdisj ht)
    (normalizeCheckedTyping_promotionFree hdisj ht)

/-- Dependent package used by checked-progress certificate construction: one
equivalent typing proof whose cofinite binders reserve `A`, together with its
hereditary promotion-freedom proof. -/
noncomputable def normalizedTypingAvoidingFree
    (A : Finset Name)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (hdisj : Graded.CtxDisj Delta Gamma)
    (ht : HasType Delta Gamma e tau) :
    {ht' : HasType Delta Gamma e tau // Graded.PromotionFree ht'} :=
  ⟨normalizeCheckedTypingAvoiding A hdisj ht,
    normalizeCheckedTypingAvoiding_promotionFree A hdisj ht⟩

/-- The canonical certificate-facing typing package.  Besides eliminating
`promote`, it records hereditarily that every cofinite binder reserves the
ambient names and the source-context keys visible at that binder. -/
noncomputable def normalizedTypingAvoidingFreeHygienic
    (A : Finset Name)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (hdisj : Graded.CtxDisj Delta Gamma)
    (ht : HasType Delta Gamma e tau) :
    Adequacy.CofiniteFreshen.FreeHygienicTyping
      A Delta Gamma e tau :=
  Adequacy.CofiniteFreshen.hasTypeFreeHygienic A
    (normalizeCheckedTyping hdisj ht)
    (normalizeCheckedTyping_promotionFree hdisj ht)

/-- Pair-local checked-progress evidence for some derivation of the caller's
source typing judgment.  Existing proof-indexed certificates embed directly;
when promotion makes that literal proof unsuitable, the witness may instead
be any certificate-friendly derivation of the same judgment. -/
def CheckedPairJudgmentLocalCallFinite
    (Psi : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (_ht : HasType Delta Gamma e tau)
    (requested : Basis) : Prop :=
  exists ht' : HasType Delta Gamma e tau,
    CheckedPairLocalCallFinite Psi ht' requested

/-- An exact proof-indexed certificate remains a valid judgment-level
certificate, choosing its own typing derivation as the witness. -/
theorem CheckedPairJudgmentLocalCallFinite.ofExact
    {Psi : EvalCtx}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {ht : HasType Delta Gamma e tau} {requested : Basis}
    (cert : CheckedPairLocalCallFinite Psi ht requested) :
    CheckedPairJudgmentLocalCallFinite Psi ht requested :=
  ⟨ht, cert⟩

/-- Package a certificate built for the canonical promotion-normalized
derivation as judgment-level checked-progress evidence. -/
theorem CheckedPairJudgmentLocalCallFinite.ofNormalized
    {Psi : EvalCtx}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {ht : HasType Delta Gamma e tau} {requested : Basis}
    (hdisj : Graded.CtxDisj Delta Gamma)
    (cert : CheckedPairLocalCallFinite Psi
      (normalizeCheckedTyping hdisj ht) requested) :
    CheckedPairJudgmentLocalCallFinite Psi ht requested :=
  ⟨normalizeCheckedTyping hdisj ht, cert⟩

/-- Package a certificate built for the canonical promotion-free derivation
whose binders also reserve every name already owned by the root evaluator. -/
theorem CheckedPairJudgmentLocalCallFinite.ofNormalizedAvoiding
    {Psi : EvalCtx}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {ht : HasType Delta Gamma e tau} {requested : Basis}
    (hdisj : Graded.CtxDisj Delta Gamma)
    (cert : CheckedPairLocalCallFinite Psi
      (normalizeCheckedTypingAvoiding Psi.names hdisj ht) requested) :
    CheckedPairJudgmentLocalCallFinite Psi ht requested :=
  ⟨normalizeCheckedTypingAvoiding Psi.names hdisj ht, cert⟩

/-- Direct extraction at a nonlinear variable: an actual selected basis is
related only to its own standard basis, in the lookup's current world and
typing context. -/
theorem selected_pair_of_var_nlin
    {Psi Psi' : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {x : Name} {tau : Ty} {hGamma : Gamma.lookup x = some tau}
    (side : CheckedPairLocalSideBases Psi n (HasType.var_nlin hGamma))
    (hfuture : CheckedStdFuture Psi Psi')
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi') :
    exists b v, EvalCtx.lookup Psi' (x, b) = some v /\
      Basis.tof b = tau /\
      exists hb : Basis.BasisValid Gamma b,
        CheckedPairBasisDepth Psi n Gamma b (Basis.std (Basis.tof b)) :=
  (side.deepHere Psi' hfuture).1 hcov

/-- Linear variables expose the same concrete selected-to-standard request. -/
theorem selected_pair_of_var_lin
    {Psi Psi' : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {x : Name} {s : Space}
    (side : CheckedPairLocalSideBases Psi n
      (HasType.var_lin : HasType (Finmap.singleton x s) Gamma
        (.var x) (.space s)))
    (hfuture : CheckedStdFuture Psi Psi')
    (hcov : V2.VarsCovered (Finmap.singleton x s) Gamma Psi') :
    exists b v, EvalCtx.lookup Psi' (x, b) = some v /\
      Basis.tof b = .space s /\
      exists hb : Basis.BasisValid Gamma b,
        CheckedPairBasisDepth Psi n Gamma b (Basis.std (Basis.tof b)) :=
  (side.deepHere Psi' hfuture).1 hcov

end RawCertifiedPairCertificate
end GLang
