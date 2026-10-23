import GLang.Proofs.Adequacy.Partial.Source.PartialSourceNormalization

namespace GLang.PartialAdequacy

private theorem raw_fn_recast {A B : Type} (h : A = B)
    (f : A → Except DimError ValValSem) :
    ValValSem.fn A f = ValValSem.fn B (fun b => f (h.symm ▸ b)) := by
  cases h
  rfl

private theorem decode_cast {d d' : ValTy}
    (h : ValSoundOfDenot.ValTy.SameShape d d') (v : ValValSem)
    (a' : d'.carrierEl) (hto : d'.carrierFromVal v = .ok a') :
    d.carrierFromVal v = .ok
      ((ValSoundOfDenot.ValTy.SameShape.carrierEl_eq h).symm ▸ a') := by
  have hc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq h
  have hd := carrierFromVal_SameShape d d' h v
  exact eq_of_heq (hd.trans ((heq_of_eq hto).trans
    (except_ok_heq hc (cast_heq hc.symm a')).symm))

/-- Exact-basis agreement is invariant under any two successful realizations
of the same source dimensions and structural value kind. The oracles, runtime
environments, local stacks, and space annotations may differ. -/
theorem Agree.representation_transport (sigma : DEnv) :
    forall {orcs orct : PartialFFSOracleSem} {rhos rhot : ValEnvSem} {Ds : List DVal} {Gs Gt : List ValTy}
      {Dvs Dvt : List ValValSem} {tau : Ty} {tauvs tauvt : ValTy}
      {B : BasisDenot} {source : DVal} {value : ValValSem},
      ValSoundOfDenot.ValTy.SameShape tauvs tauvt ->
      DimsAt orcs sigma rhos Ds Gs Dvs tau tauvs B ->
      DimsAt orct sigma rhot Ds Gt Dvt tau tauvt B ->
      Agree orcs sigma rhos Ds Gs Dvs tau tauvs B source value ->
      Agree orct sigma rhot Ds Gt Dvt tau tauvt B source value := by
  intro orcs orct rhos rhot Ds Gs Gt Dvs Dvt tau tauvs tauvt B source value hshape hds hdt ha
  generalize hn : Ty.size tau + ValTy.kindSize tauvs +
      ValTy.kindSize tauvt = n
  induction n using Nat.strong_induction_on generalizing
      orcs orct rhos rhot Ds Gs Gt Dvs Dvt tau tauvs tauvt B source value with
  | h n ih =>
      cases tau with
      | space s =>
          cases tauvs with
          | space svs =>
              cases tauvt with
              | space svt =>
                  cases value with
                  | fn T f => simpa only [Agree] using ha
                  | array a =>
                      simp only [DimsAt] at hds hdt
                      simp only [Agree] at ha ⊢
                      have hdim : svs.dofPartial (orcs rhos Gs Dvs) =
                          svt.dofPartial (orct rhot Gt Dvt) := by
                        simp only [ValSpace.dofPartial, hds, hdt]
                      rw [hdim] at ha
                      exact ha
              | piTy _ _ => exact hshape.elim
          | piTy _ _ =>
              cases tauvt with
              | space _ => exact hshape.elim
              | piTy _ _ => simpa only [Agree] using ha
      | piTy tau0 tau1 =>
          cases tauvs with
          | space _ => simpa only [Agree] using ha
          | piTy tauvs0 tauvs1 =>
              cases tauvt with
              | space _ => exact hshape.elim
              | piTy tauvt0 tauvt1 =>
                  simp only [DimsAt] at hds hdt
                  simp only [Agree] at ha ⊢
                  obtain ⟨_,_,f, hy, hf⟩ := ha
                  obtain ⟨hshape0, hshape1⟩ := hshape
                  let hEl : tauvs0.carrierEl = tauvt0.carrierEl :=
                    ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape0
                  obtain ⟨D,hD⟩ := hdt.1.type_ok
                  let ft : tauvt0.carrierEl -> Except DimError ValValSem :=
                    fun arg => f (hEl.symm ▸ arg)
                  refine ⟨D,hD,ft, ?_, ?_⟩
                  · exact hy.trans (raw_fn_recast hEl f)
                  · intro x' argVal argt htot hargt
                    let args : tauvs0.carrierEl := hEl.symm ▸ argt
                    have htos : tauvs0.carrierFromVal argVal = .ok args := by
                      exact decode_cast hshape0 argVal argt htot
                    have hdomLt : Ty.size tau0 + ValTy.kindSize tauvt0 +
                        ValTy.kindSize tauvs0 < n := by
                      simp only [Ty.size, ValTy.kindSize_piTy] at hn
                      omega
                    have hargs : Agree orcs sigma rhos Ds Gs Dvs
                        tau0 tauvs0 B.domainBasis
                        ((denotTyAux sigma Ds tau0).embed x') argVal := by
                      apply ih (Ty.size tau0 + ValTy.kindSize tauvt0 +
                        ValTy.kindSize tauvs0) hdomLt
                      · exact hshape0.symm
                      · exact hdt.1
                      · exact hds.1
                      · exact hargt
                      · rfl
                    obtain ⟨out, hout, houtAgree⟩ :=
                      hf x' argVal args htos hargs
                    have hdscod := hds.2 x' argVal args htos hargs
                    have hdtcod := hdt.2 x' argVal argt htot hargt
                    have hcodLt : Ty.size tau1 + ValTy.kindSize tauvs1 +
                        ValTy.kindSize tauvt1 < n := by
                      simp only [Ty.size, ValTy.kindSize_piTy] at hn
                      omega
                    have houtAgreeT : Agree orct sigma rhot
                        ((denotTyAux sigma Ds tau0).embed x' :: Ds)
                        (tauvt0 :: Gt) (argVal :: Dvt) tau1 tauvt1
                        (B.applyEl x') (source.applyEl x') out := by
                      apply ih (Ty.size tau1 + ValTy.kindSize tauvs1 +
                        ValTy.kindSize tauvt1) hcodLt
                      · exact hshape1
                      · exact hdscod
                      · exact hdtcod
                      · exact houtAgree
                      · rfl
                    refine ⟨out, ?_, houtAgreeT⟩
                    simpa only [ft, args] using hout

end GLang.PartialAdequacy
