import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairDepthMonotonicity
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedConsistentPairStore
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardExecutableSyntax

namespace GLang
namespace RawCertifiedPairFreeStandardCertificate

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate
open RawCertifiedPairDepthMonotonicity
open RawCertifiedConsistentPairStore
open RawCertifiedPairFreeStandardExecutableSyntax

/-- A concrete pair certificate whose source-variable recursion stops when
the selected key is already the literal standard basis of its source type. -/
def CheckedFreeStdPairBasisDepth (Psi : EvalCtx) :
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
      CheckedFreeStdPairBasisDepth Psi (n + 1) Gamma b10 b10 /\
      CheckedFreeStdPairBasisDepth Psi (n + 1) Gamma b20 b20 /\
      (forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
        forall (y : Name), y ∉ Psi'.names -> y ∉ sourceAvoid ->
          forall tauV10, C.TyAt Gamma Psi' b10 tauV10 ->
          let PsiX := Psi'.extend y b10 (.var y tauV10)
          let GammaX := Finmap.insert y (Basis.tof b10) Gamma
          CheckedFreeStdPairBasisDepth PsiX (n + 1) GammaX
            (Basis.openVar y b11) (Basis.openVar y b11)) /\
      (forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
        forall (y : Name), y ∉ Psi'.names -> y ∉ targetAvoid ->
          forall tauV20, C.TyAt Gamma Psi' b20 tauV20 ->
          let PsiX := Psi'.extend y b20 (.var y tauV20)
          let GammaX := Finmap.insert y (Basis.tof b20) Gamma
          CheckedFreeStdPairBasisDepth PsiX (n + 1) GammaX
            (Basis.openVar y b21) (Basis.openVar y b21)) /\
      forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
        forall (y : Name), y ∉ Psi'.names ->
          y ∉ sourceAvoid -> y ∉ targetAvoid ->
          forall tauV20, C.TyAt Gamma Psi' b20 tauV20 ->
          let PsiX := Psi'.extend y b20 (.var y tauV20)
          let GammaX := Finmap.insert y (Basis.tof b20) Gamma
          CheckedFreeStdPairBasisDepth PsiX (n + 1) GammaX b20 b10 /\
          CheckedFreeStdPairBasisDepth PsiX (n + 1) GammaX
            (Basis.openVar y b11) (Basis.openVar y b21)
  | _n + 1, _Gamma, .frame _ _, _target => False
  | _n + 1, _Gamma, _source, .frame _ _ => False
  | n + 1, Gamma, source, target =>
      let selected : EvalCtx -> CheckedSelectedBasisSide :=
        fun Psi' {Gamma'} {b} _hb =>
          b = Basis.std (Basis.tof b) ∨
          CheckedFreeStdPairBasisDepth Psi' n Gamma' b
            (Basis.std (Basis.tof b))
      BasisNonFrame source /\ BasisNonFrame target /\
      Basis.tof target = Basis.tof source /\
      CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma source /\
      CheckedFreeStdExecutableBasisSyntaxLayer Psi selected Gamma target
termination_by crossDepth Gamma source target =>
  (crossDepth, max (Basis.size source) (Basis.size target))
decreasing_by
  all_goals simp [Basis.size, Basis.size_openVar] <;> omega

/-- Variable-leaf policy of the free-standard certificate. -/
def CheckedFreeStdSelectedAt (Psi : EvalCtx) (depth : Nat) :
    CheckedSelectedBasisSide :=
  fun {Gamma} {b} _hb =>
    b = Basis.std (Basis.tof b) ∨
    CheckedFreeStdPairBasisDepth Psi depth Gamma b
      (Basis.std (Basis.tof b))

/-- Four orientations required by dependent-frame construction. -/
structure CheckedFreeStdPairDepthQuad
    (Psi : EvalCtx) (depth : Nat) (Gamma : NLCtx) (b : Basis) : Prop where
  self : CheckedFreeStdPairBasisDepth Psi depth Gamma b b
  toStd : CheckedFreeStdPairBasisDepth Psi depth Gamma b
    (Basis.std (Basis.tof b))
  fromStd : CheckedFreeStdPairBasisDepth Psi depth Gamma
    (Basis.std (Basis.tof b)) b
  stdSelf : CheckedFreeStdPairBasisDepth Psi depth Gamma
    (Basis.std (Basis.tof b)) (Basis.std (Basis.tof b))

/-- Pointwise finite relaxed pair evidence. -/
def CheckedFreeStdPairBasisFinite (Psi : EvalCtx) (Gamma : NLCtx)
    (source target : Basis) : Prop :=
  exists depth, CheckedFreeStdPairBasisDepth Psi depth Gamma source target

/-- A promotion-normalized proof of the same source judgment together with
one common-depth free-standard source tree. -/
def CheckedFreeStdJudgmentTermSideFinite
    (Psi : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (_ht : HasType Delta Gamma e tau) : Prop :=
  exists ht' : HasType Delta Gamma e tau,
    Graded.PromotionFree ht' /\
    exists depth,
      Nonempty (CheckedLocalSideBasesWith
        (CheckedFreeStdSelectedAt Psi depth) Psi ht')

/-! ## Numeric-depth monotonicity -/

/-- Raise one relaxed concrete pair by one cross depth. -/
theorem freeStdPairDepth_succ :
    forall (depth : Nat) (Psi : EvalCtx) (Gamma : NLCtx)
      (source target : Basis),
      CheckedFreeStdPairBasisDepth Psi depth Gamma source target ->
      CheckedFreeStdPairBasisDepth Psi (depth + 1) Gamma source target := by
  intro depth
  induction depth with
  | zero =>
      intro Psi Gamma source target pair
      simp only [CheckedFreeStdPairBasisDepth] at pair
      obtain ⟨htof, ⟨hs, sourceZero⟩, ⟨ht, targetZero⟩⟩ := pair
      have result :
          BasisNonFrame source /\ BasisNonFrame target /\
          Basis.tof target = Basis.tof source /\
          CheckedFreeStdExecutableBasisSyntaxLayer Psi
            (fun Psi' {Gamma'} {b} (_hb : Basis.BasisValid Gamma' b) =>
              b = Basis.std (Basis.tof b) ∨
              CheckedFreeStdPairBasisDepth Psi' 0 Gamma' b
                (Basis.std (Basis.tof b))) Gamma source /\
          CheckedFreeStdExecutableBasisSyntaxLayer Psi
            (fun Psi' {Gamma'} {b} (_hb : Basis.BasisValid Gamma' b) =>
              b = Basis.std (Basis.tof b) ∨
              CheckedFreeStdPairBasisDepth Psi' 0 Gamma' b
                (Basis.std (Basis.tof b))) Gamma target :=
        ⟨CheckedLocalSideBasisZero.nonFrame sourceZero,
          CheckedLocalSideBasisZero.nonFrame targetZero, htof,
          CheckedLocalSideBasisZero.toExecutableSyntaxLayer sourceZero,
          CheckedLocalSideBasisZero.toExecutableSyntaxLayer targetZero⟩
      cases source <;> cases target <;>
        first
        | exact (by simpa only [CheckedFreeStdPairBasisDepth] using result)
        | exact (by simpa [BasisNonFrame] using result.1)
        | exact (by simpa [BasisNonFrame] using result.2.1)
  | succ n ihDepth =>
      intro Psi Gamma source target pair
      suffices hraise : forall size, forall (Psi : EvalCtx)
          (Gamma : NLCtx) (source target : Basis),
          max (Basis.size source) (Basis.size target) <= size ->
          CheckedFreeStdPairBasisDepth Psi (n + 1) Gamma source target ->
          CheckedFreeStdPairBasisDepth Psi (n + 2) Gamma source target by
        exact hraise (max (Basis.size source) (Basis.size target))
          Psi Gamma source target (le_refl _) pair
      intro size
      induction size using Nat.strong_induction_on with
      | _ size ihSize =>
        intro Psi Gamma source target hsize pair
        cases source <;> cases target <;>
          simp only [CheckedFreeStdPairBasisDepth] at pair ⊢
        case frame.frame b10 b11 b20 b21 =>
          obtain ⟨htof0, htof1, sourceAvoid, targetAvoid,
            sourceDomainValid, targetDomainValid,
            sourceBodyValid, targetBodyValid,
            sourceDomain, targetDomain, sourceBody, targetBody,
            cross⟩ := pair
          have small10 : max (Basis.size b10) (Basis.size b10) < size := by
            simp only [Basis.size] at hsize ⊢
            omega
          have small20 : max (Basis.size b20) (Basis.size b20) < size := by
            simp only [Basis.size] at hsize ⊢
            omega
          refine ⟨htof0, htof1, sourceAvoid, targetAvoid,
            sourceDomainValid, targetDomainValid,
            sourceBodyValid, targetBodyValid,
            ihSize _ small10 Psi Gamma b10 b10 (le_refl _) sourceDomain,
            ihSize _ small20 Psi Gamma b20 b20 (le_refl _) targetDomain,
            ?_, ?_, ?_⟩
          · intro Psi' hfuture y hyNames hy tauV hty
            have smallBody :
                max (Basis.size (Basis.openVar y b11))
                  (Basis.size (Basis.openVar y b11)) < size := by
              simp only [Basis.size, Basis.size_openVar] at hsize ⊢
              omega
            exact ihSize _ smallBody
              (Psi'.extend y b10 (.var y tauV))
              (Finmap.insert y (Basis.tof b10) Gamma)
              (Basis.openVar y b11) (Basis.openVar y b11)
              (le_refl _)
              (sourceBody Psi' hfuture y hyNames hy tauV hty)
          · intro Psi' hfuture y hyNames hy tauV hty
            have smallBody :
                max (Basis.size (Basis.openVar y b21))
                  (Basis.size (Basis.openVar y b21)) < size := by
              simp only [Basis.size, Basis.size_openVar] at hsize ⊢
              omega
            exact ihSize _ smallBody
              (Psi'.extend y b20 (.var y tauV))
              (Finmap.insert y (Basis.tof b20) Gamma)
              (Basis.openVar y b21) (Basis.openVar y b21)
              (le_refl _)
              (targetBody Psi' hfuture y hyNames hy tauV hty)
          · intro Psi' hfuture y hyNames hySource hyTarget tauV hty
            obtain ⟨domainCross, bodyCross⟩ :=
              cross Psi' hfuture y hyNames hySource hyTarget tauV hty
            have smallDomain :
                max (Basis.size b20) (Basis.size b10) < size := by
              simp only [Basis.size] at hsize ⊢
              omega
            have smallBody :
                max (Basis.size (Basis.openVar y b11))
                  (Basis.size (Basis.openVar y b21)) < size := by
              simp only [Basis.size, Basis.size_openVar] at hsize ⊢
              omega
            exact ⟨ihSize _ smallDomain
                (Psi'.extend y b20 (.var y tauV))
                (Finmap.insert y (Basis.tof b20) Gamma)
                b20 b10 (le_refl _) domainCross,
              ihSize _ smallBody
                (Psi'.extend y b20 (.var y tauV))
                (Finmap.insert y (Basis.tof b20) Gamma)
                (Basis.openVar y b11) (Basis.openVar y b21)
                (le_refl _) bodyCross⟩
        all_goals
          obtain ⟨sourceNonFrame, targetNonFrame, htof,
            sourceSide, targetSide⟩ := pair
          exact ⟨sourceNonFrame, targetNonFrame, htof,
            executableSyntaxLayer_mono
              (fun Psi' {Gamma'} {b} _hb selected =>
                selected.elim Or.inl (fun pair =>
                  Or.inr (ihDepth Psi' Gamma' b
                    (Basis.std (Basis.tof b)) pair)))
              sourceSide,
            executableSyntaxLayer_mono
              (fun Psi' {Gamma'} {b} _hb selected =>
                selected.elim Or.inl (fun pair =>
                  Or.inr (ihDepth Psi' Gamma' b
                    (Basis.std (Basis.tof b)) pair)))
              targetSide⟩

/-- Raise a relaxed concrete pair to any greater numeric depth. -/
theorem freeStdPairDepth_mono
    {source target : Basis} {Gamma : NLCtx} {Psi : EvalCtx}
    {n m : Nat} (hnm : n <= m)
    (pair : CheckedFreeStdPairBasisDepth Psi n Gamma source target) :
    CheckedFreeStdPairBasisDepth Psi m Gamma source target := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hnm
  clear hnm
  induction k with
  | zero => simpa
  | succ k ih =>
      rw [Nat.add_succ]
      exact freeStdPairDepth_succ _ _ _ _ _ ih

/-- Raise all four orientations together. -/
theorem CheckedFreeStdPairDepthQuad.monoDepth
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis} {n m : Nat}
    (hnm : n <= m) (q : CheckedFreeStdPairDepthQuad Psi n Gamma b) :
    CheckedFreeStdPairDepthQuad Psi m Gamma b where
  self := freeStdPairDepth_mono hnm q.self
  toStd := freeStdPairDepth_mono hnm q.toStd
  fromStd := freeStdPairDepth_mono hnm q.fromStd
  stdSelf := freeStdPairDepth_mono hnm q.stdSelf

end RawCertifiedPairFreeStandardCertificate
end GLang
