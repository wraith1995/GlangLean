import GLang.Proofs.Adequacy.Partial.Source.PartialSourceChecking
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceInferredAgreement

namespace GLang.PartialAdequacy

/-- Partial reshape preserves exact source representations across different
local value worlds, including contravariant higher-order argument conversion. -/
theorem reshape_result (orc : PartialFFSOracleSem) (sigma : DEnv) (rho : ValEnvSem) :
    forall (tau : Ty) (target sourceTy : ValTy)
      (Ds : List DVal) (Gt : List ValTy) (Dt : List ValValSem)
      (Gs : List ValTy) (Dvs : List ValValSem)
      (B : BasisDenot) (sourceOut : DVal) (value : ValValSem),
      DimsAt orc sigma rho Ds Gt Dt tau target B ->
      DimsAt orc sigma rho Ds Gs Dvs tau sourceTy B ->
      Agree orc sigma rho Ds Gs Dvs tau sourceTy B sourceOut value ->
      ResultAgree orc sigma rho Ds Gt Dt tau target B sourceOut
        (PartialValueEval.reshapeBetween orc rho Gt Dt Gs Dvs value target sourceTy) := by
  intro tau target sourceTy Ds Gt Dt Gs Dvs B sourceOut value hdt hds ha
  generalize hn : ValTy.kindSize target + ValTy.kindSize sourceTy = n
  induction n using Nat.strong_induction_on generalizing
      tau target sourceTy Ds Gt Dt Gs Dvs B sourceOut value with
  | h n ih =>
    cases tau <;> cases target <;> cases sourceTy <;>
      simp only [DimsAt] at hdt hds
    · rename_i s st ss
      cases value with
      | fn A f => simp only [Agree] at ha
      | array a =>
        simp only [Agree] at ha
        obtain ⟨dim,hdim,hB,hlen,hrepr⟩ := ha
        have hsame : ss.dofPartial (orc rho Gs Dvs) = st.dofPartial (orc rho Gt Dt) := by
          simp only [ValSpace.dofPartial,hds,hdt]
        have ht := hsame.symm.trans hdim
        refine ⟨.array a,?_,?_⟩
        · simp [PartialValueEval.reshapeBetween,PartialValueEval.reshapeArray,hdim,ht,hlen]
        · simp only [Agree]
          exact ⟨dim,ht,hB,hlen,hrepr⟩
    · rename_i d c dt ct ds cs
      simp only [Agree] at ha
      obtain ⟨SD,hSD,f,rfl,hf⟩ := ha
      obtain ⟨TD,hTD⟩ := hdt.1.type_ok
      rw [PartialValueEval.reshapeBetween,hTD,hSD]
      refine ⟨_,rfl,?_⟩
      simp only [Agree]
      refine ⟨TD,hTD,_,rfl,?_⟩
      intro src raw arg hdecode harg
      obtain ⟨checked,hcheck,hargT⟩ := Agree.checked hdt.1 hTD harg hdecode
      let rawT := dt.carrierToVal checked
      have hargLt : ValTy.kindSize ds + ValTy.kindSize dt < n := by
        simp only [ValTy.kindSize_piTy] at hn
        omega
      obtain ⟨rawS,hreshapeArg,hargS⟩ :=
        ih _ hargLt d ds dt Ds Gs Dvs Gt Dt B.domainBasis
          ((denotTyAux sigma Ds d).embed src) rawT hds.1 hdt.1 hargT rfl
      obtain ⟨argS,htoS,_⟩ := hargS.decode
      obtain ⟨result,happ,hresultS⟩ := hf src rawS argS htoS hargS
      have htoT := PartialValueDomains.carrier_roundtrip dt checked
      have hcodT := hdt.2 src rawT checked htoT hargT
      have hcodS := hds.2 src rawS argS htoS hargS
      have hcodLt : ValTy.kindSize ct + ValTy.kindSize cs < n := by
        simp only [ValTy.kindSize_piTy] at hn
        omega
      obtain ⟨out,hreshapeOut,houtT⟩ :=
        ih _ hcodLt c ct cs ((denotTyAux sigma Ds d).embed src :: Ds)
          (dt :: Gt) (rawT :: Dt) (ds :: Gs) (rawS :: Dvs)
          (B.applyEl src) (sourceOut.applyEl src) result hcodT hcodS hresultS rfl
      have hcodRaw := hdt.2 src raw arg hdecode harg
      refine ⟨out,?_,Agree.stack_transport hcodT hcodRaw houtT⟩
      dsimp only [rawT] at hreshapeArg hreshapeOut
      simp only [hcheck,hreshapeArg,htoS,ValValSem.applyTyped_fn,happ,hreshapeOut]

theorem reshape_evaluation {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {tau : Ty} {target sourceTy : ValTy} {Ds : List DVal}
    {G : List ValTy} {D : List ValValSem} {B : BasisDenot} {sourceOut : DVal}
    {e : ValExpr}
    (ht : DimsAt orc sigma rho Ds G D tau target B)
    (hs : DimsAt orc sigma rho Ds G D tau sourceTy B)
    (he : ResultAgree orc sigma rho Ds G D tau sourceTy B sourceOut
      (denotValB_partial orc rho G D e))
    (hinfer : ValExpr.inferTypeCtx G e = sourceTy) :
    ResultAgree orc sigma rho Ds G D tau target B sourceOut
      (denotValB_partial orc rho G D (.reshap e target sourceTy)) := by
  obtain ⟨v,hv,ha⟩ := he
  simp only [denotValB_partial,hv,hinfer,PartialValueEval.reshapeInferred_self]
  exact reshape_result orc sigma rho tau target sourceTy Ds G D G D B sourceOut v ht hs ha

/-- A compiled operand may carry a different realization from its inferred
type. Array checks use the declared source dimensions; function conversion
uses the inferred dependent type and its proved source agreement. -/
theorem reshape_compiled
    {Δ Γ Ψ e b v tv} (h : S.Term Δ Γ Ψ e b v tv)
    {orc : PartialFFSOracleSem} {Δc Γc Γv σ ρ} {target : ValTy}
    (hc : History orc Δc Γc Ψ Γv σ ρ) (hirr : PartialDirectFv.OracleFresh orc)
    (ht : DimsAt orc σ ρ [] [] [] (Basis.tof b) target (denotBasis σ b))
    (hv : TermTraceAt orc σ ρ v (Basis.tof b) tv (denotBasis σ b) (denotTerm σ e)) :
    TermTraceAt orc σ ρ (.reshap v target tv) (Basis.tof b) target
      (denotBasis σ b) (denotTerm σ e) := by
  refine ⟨?_, ht⟩
  cases tv with
  | space s =>
    obtain ⟨r,hr,ha⟩ := hv.result
    rw [denotValB_partial,hr]
    exact reshape_result orc σ ρ _ target (.space s) [] [] [] [] [] _ _ r ht hv.dims ha
  | piTy d c =>
    have hactual := TermTraceAt.inferred h hc hirr hv (by intro sv heq; cases heq)
    have hshape := inferType_sameShape h hc
    cases hi : ValExpr.inferTypeCtx [] v with
    | space s => simp only [hi, ValSoundOfDenot.ValTy.SameShape] at hshape
    | piTy di ci =>
      rw [hi] at hactual
      obtain ⟨r,hr,ha⟩ := hactual.result
      rw [denotValB_partial,hr]
      simp only [PartialValueEval.reshapeInferred,hi]
      exact reshape_result orc σ ρ _ target (.piTy di ci) [] [] [] [] [] _ _ r ht hactual.dims ha

end GLang.PartialAdequacy
