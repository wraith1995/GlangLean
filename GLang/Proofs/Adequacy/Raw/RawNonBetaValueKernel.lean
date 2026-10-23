import GLang.Proofs.Adequacy.Raw.RawAgreement
import GLang.Proofs.Adequacy.Raw.RawSourceInstantiation
import GLang.Proofs.Adequacy.Raw.RawBasisInstantiation
import GLang.Proofs.Value.Soundness.ValueSoundnessSem

namespace GLang

structure RawTermTraceAt (orc : FFSOracleSem) (sigma : DEnv)
    (rho : ValEnvSem) (e : ValExpr) (tau : Ty) (tauv : ValTy)
    (B : BasisDenot) (source : DVal) : Prop where
  result : RawResultAgree orc sigma rho [] [] [] tau tauv B source
    (denotValB_semS orc rho [] [] e)
  dims : RawAgreeDimsAt orc sigma rho [] [] [] tau tauv B

private theorem FlatArray.resize_eq_self_of_length_raw
    {a : FlatArray} {n : Nat} (h : a.length = n) : a.resize n = a := by
  apply FlatArray.ext h.symm
  intro i
  simp [FlatArray.resize, FlatArray.ofFn, FlatArray.get, h]

/-! ## Runtime carrier lemmas -/

/-- Oracle environments affect dimensions, but not the Lean carrier of a
value type. -/
theorem denotValTyS_El_eq_carrierEl_raw (orc : FFSOracleSem) :
    forall (rho : ValEnvSem) (G : List ValTy) (D : List ValValSem)
      (tauv : ValTy),
      (denotValTyS orc rho G D tauv).El = tauv.carrierEl
  | _rho, _G, _D, .space _ => rfl
  | rho, G, D, .piTy tauv0 tauv1 => by
      show ((v : (denotValTyS orc rho G D tauv0).El) ->
              Except DimError (denotValTyS orc rho (tauv0 :: G)
                (ValValSem.fromEl (denotValTyS orc rho G D tauv0) v :: D)
                tauv1).El) =
        (tauv0.carrierEl -> Except DimError tauv1.carrierEl)
      have hdom : (denotValTyS orc rho G D tauv0).El = tauv0.carrierEl :=
        denotValTyS_El_eq_carrierEl_raw orc rho G D tauv0
      have hcod : forall v, Except DimError
          (denotValTyS orc rho (tauv0 :: G)
            (ValValSem.fromEl (denotValTyS orc rho G D tauv0) v :: D)
            tauv1).El = Except DimError tauv1.carrierEl :=
        fun v => congrArg (Except DimError)
          (denotValTyS_El_eq_carrierEl_raw orc rho (tauv0 :: G)
            (ValValSem.fromEl (denotValTyS orc rho G D tauv0) v :: D)
            tauv1)
      rw [show ((v : (denotValTyS orc rho G D tauv0).El) ->
              Except DimError (denotValTyS orc rho (tauv0 :: G)
                (ValValSem.fromEl (denotValTyS orc rho G D tauv0) v :: D)
                tauv1).El) =
            ((_v : (denotValTyS orc rho G D tauv0).El) ->
              Except DimError tauv1.carrierEl) from
          congrArg (fun F => (v : (denotValTyS orc rho G D tauv0).El) -> F v)
            (funext hcod)]
      rw [hdom]

/-- Decoding is invariant, up to heterogeneous equality, under same-shape
replacement of the value type and its semantic environments. -/
theorem toEl_denotValTyS_sameShape_raw (orc : FFSOracleSem) :
    forall (d d' : ValTy), ValSoundOfDenot.ValTy.SameShape d d' ->
      forall (rho rho' : ValEnvSem) (G G' : List ValTy)
        (D D' : List ValValSem) (v : ValValSem),
      HEq (ValValSem.toEl (denotValTyS orc rho G D d) v)
          (ValValSem.toEl (denotValTyS orc rho' G' D' d') v)
  | .space _, .space _, _, _, _, _, _, _, _, v => by
      apply heq_of_eq
      cases v <;> rfl
  | .piTy d0 d1, .piTy d0' d1', hshape, rho, rho', G, G', D, D', v => by
      have hshapeAll : ValSoundOfDenot.ValTy.SameShape
          (.piTy d0 d1) (.piTy d0' d1') := hshape
      obtain ⟨hshape0, hshape1⟩ := hshape
      have hEl : (denotValTyS orc rho G D d0).El =
          (denotValTyS orc rho' G' D' d0').El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw,
          ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape0]
      have hPiEl : (denotValTyS orc rho G D (.piTy d0 d1)).El =
          (denotValTyS orc rho' G' D' (.piTy d0' d1')).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw,
          ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshapeAll]
      cases v with
      | array _ =>
          simp only [denotValTyS, ValValSem.toEl]
          exact except_error_heq hPiEl DimError.mismatch
      | fn T' f =>
          simp only [denotValTyS, ValValSem.toEl]
          by_cases hT : (denotValTyS orc rho G D d0).El = T'
          · have hT' : (denotValTyS orc rho' G' D' d0').El = T' := hEl ▸ hT
            rw [dif_pos hT, dif_pos hT']
            apply except_ok_heq hPiEl
            refine Function.hfunext hEl ?_
            intro a a' haa
            have hcast : f (hT ▸ a) = f (hT' ▸ a') := by
              congr 1
              apply eq_of_heq
              exact HEq.trans (cast_heq hT a)
                (HEq.trans haa (HEq.symm (cast_heq hT' a')))
            rw [hcast]
            have hCodEl : (denotValTyS orc rho (d0 :: G)
                (ValValSem.fromEl (denotValTyS orc rho G D d0) a :: D) d1).El =
                (denotValTyS orc rho' (d0' :: G')
                  (ValValSem.fromEl (denotValTyS orc rho' G' D' d0') a' :: D')
                  d1').El := by
              rw [denotValTyS_El_eq_carrierEl_raw,
                denotValTyS_El_eq_carrierEl_raw,
                ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape1]
            cases hf : f (hT' ▸ a') with
            | error err => exact except_error_heq hCodEl err
            | ok out =>
                exact toEl_denotValTyS_sameShape_raw orc d1 d1' hshape1
                  rho rho' (d0 :: G) (d0' :: G')
                  (ValValSem.fromEl (denotValTyS orc rho G D d0) a :: D)
                  (ValValSem.fromEl (denotValTyS orc rho' G' D' d0') a' :: D')
                  out
          · have hT' : ¬ ((denotValTyS orc rho' G' D' d0').El = T') :=
              fun h => hT (hEl ▸ h)
            rw [dif_neg hT, dif_neg hT']
            exact except_error_heq hPiEl DimError.mismatch
  | .space _, .piTy _ _, hshape, _, _, _, _, _, _, _ => hshape.elim
  | .piTy _ _, .space _, hshape, _, _, _, _, _, _, _ => hshape.elim
  termination_by d _ _ _ _ _ _ _ _ _ => ValTy.kindSize d
  decreasing_by all_goals simp only [ValTy.kindSize_piTy]; omega

/-- Base-domain decoding checks the dimensions justified by raw agreement. -/
theorem RawAgree.domainChecked_eq_toEl
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {G : List ValTy} {D : List ValValSem}
    {tau : Ty} {tauv d : ValTy} {B : BasisDenot}
    {x : DVal} {v : ValValSem}
    (ha : RawAgree orc sigma rho Ds G D tau tauv B x v)
    (hs : ValSoundOfDenot.ValTy.SameShape d tauv)
    (hd : forall s s', d = .space s -> tauv = .space s' ->
      ValSpace.dof (orc rho G D) s = ValSpace.dof (orc rho G D) s') :
    ValValSem.toElDomainChecked (denotValTyS orc rho G D d) v =
      ValValSem.toEl (denotValTyS orc rho G D d) v := by
  cases d with
  | piTy d0 d1 => rfl
  | space s =>
    cases tauv with
    | piTy _ _ => exact hs.elim
    | space s' =>
      cases tau with
      | piTy _ _ => simpa only [RawAgree] using ha
      | space t =>
        cases v with
        | fn _ _ => simpa only [RawAgree] using ha
        | array a =>
          simp only [RawAgree] at ha
          have hlen : a.length = ValSpace.dof (orc rho G D) s' := ha.2.1
          exact ValValSem.toElDomainChecked_eq_toEl_space s _ a
            (hlen.trans (hd s s' rfl rfl).symm)

/-- Evaluation of ordinary value application uses structural agreement and
successful immediate-domain checking. -/
theorem denotValB_semS_appV_fn_of_sameShape_raw
    (orc : FFSOracleSem) (rho : ValEnvSem)
    (G : List ValTy) (D : List ValValSem)
    (e0 e1 : ValExpr) (tauOut tauv0 : ValTy)
    (fam : (denotValTyS orc rho G D tauv0).El ->
      Except DimError ValValSem)
    (v1 : ValValSem) (arg : (denotValTyS orc rho G D tauv0).El)
    (hshape : ValSoundOfDenot.ValTy.SameShape
      (ValExpr.inferTypeCtx G e0).domain tauv0)
    (hv0 : denotValB_semS orc rho G D e0 =
      .ok (.fn (denotValTyS orc rho G D tauv0).El fam))
    (hv1 : denotValB_semS orc rho G D e1 = .ok v1)
    (hchecked : ValValSem.toElDomainChecked
      (denotValTyS orc rho G D (ValExpr.inferTypeCtx G e0).domain) v1 =
      ValValSem.toEl (denotValTyS orc rho G D (ValExpr.inferTypeCtx G e0).domain) v1)
    (hto : ValValSem.toEl (denotValTyS orc rho G D tauv0) v1 =
      .ok arg) :
    denotValB_semS orc rho G D (.appV e0 e1) = fam arg := by
  let inferredDomain := (ValExpr.inferTypeCtx G e0).domain
  have hEl : (denotValTyS orc rho G D inferredDomain).El =
      (denotValTyS orc rho G D tauv0).El := by
    rw [denotValTyS_El_eq_carrierEl_raw,
      denotValTyS_El_eq_carrierEl_raw,
      ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape]
  have htoHEq : HEq
      (ValValSem.toEl (denotValTyS orc rho G D inferredDomain) v1)
      (ValValSem.toEl (denotValTyS orc rho G D tauv0) v1) :=
    toEl_denotValTyS_sameShape_raw orc inferredDomain tauv0 hshape
      rho rho G G D D v1
  have htoOk : HEq
      (ValValSem.toEl (denotValTyS orc rho G D inferredDomain) v1)
      (Except.ok arg : Except DimError
        (denotValTyS orc rho G D tauv0).El) :=
    HEq.trans htoHEq (heq_of_eq hto)
  let argD : (denotValTyS orc rho G D inferredDomain).El := hEl.symm ▸ arg
  have hargHEq : HEq argD arg := cast_heq hEl.symm arg
  have hokHEq : HEq
      (Except.ok argD : Except DimError
        (denotValTyS orc rho G D inferredDomain).El)
      (Except.ok arg : Except DimError
        (denotValTyS orc rho G D tauv0).El) :=
    except_ok_heq hEl hargHEq
  have htoD :
      ValValSem.toEl (denotValTyS orc rho G D inferredDomain) v1 =
        .ok argD :=
    eq_of_heq (HEq.trans htoOk (HEq.symm hokHEq))
  rw [denotValB_semS.eq_28]
  simp only [hv0, hv1]
  rw [dif_pos hEl.symm, hchecked, htoD]
  apply congrArg fam
  exact eq_of_heq (HEq.trans (cast_heq _ argD) hargHEq)

/-- End-to-end evaluator-facing ordinary value application. -/
theorem RawAgree.appV_result
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau0 tau1 : Ty} {tauv0 tauv1 : ValTy} {B : BasisDenot}
    {funSource : DVal} {funValue argValue : ValValSem}
    (x' : (denotTyAux sigma Ds tau0).El)
    (e0 e1 : ValExpr) (tauOut : ValTy)
    (hfun : RawAgree orc sigma rho Ds Gv Dv
      (.piTy tau0 tau1) (.piTy tauv0 tauv1) B funSource funValue)
    (harg : RawAgree orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis
      ((denotTyAux sigma Ds tau0).embed x') argValue)
    (hshape : ValSoundOfDenot.ValTy.SameShape
      (ValExpr.inferTypeCtx Gv e0).domain tauv0)
    (hdomainDim : forall s s', (ValExpr.inferTypeCtx Gv e0).domain = .space s ->
      tauv0 = .space s' ->
      ValSpace.dof (orc rho Gv Dv) s = ValSpace.dof (orc rho Gv Dv) s')
    (hv0 : denotValB_semS orc rho Gv Dv e0 = .ok funValue)
    (hv1 : denotValB_semS orc rho Gv Dv e1 = .ok argValue) :
    exists (arg : (denotValTyS orc rho Gv Dv tauv0).El)
      (out : ValValSem),
      ValValSem.toEl (denotValTyS orc rho Gv Dv tauv0) argValue =
        .ok arg /\
      denotValB_semS orc rho Gv Dv (.appV e0 e1) = .ok out /\
      RawAgree orc sigma rho
        ((denotTyAux sigma Ds tau0).embed x' :: Ds)
        (tauv0 :: Gv) (argValue :: Dv) tau1 tauv1
        (B.applyEl x') (funSource.applyEl x') out := by
  obtain ⟨arg, hto⟩ := harg.toEl
  simp only [RawAgree] at hfun
  obtain ⟨f, rfl, hf⟩ := hfun
  obtain ⟨out, hout, houtAgree⟩ := hf x' argValue arg hto harg
  refine ⟨arg, out, hto, ?_, houtAgree⟩
  exact (denotValB_semS_appV_fn_of_sameShape_raw
    orc rho Gv Dv e0 e1 tauOut tauv0 f argValue arg
    hshape hv0 hv1 (harg.domainChecked_eq_toEl hshape hdomainDim) hto).trans hout

/-- Re-index an untyped function along equality of its argument carrier. -/
private theorem raw_fn_recast {A B : Type} (h : A = B)
    (f : A -> Except DimError ValValSem) :
    ValValSem.fn A f =
      ValValSem.fn B (fun b => f (h.symm ▸ b)) := by
  cases h
  rfl

private theorem raw_decode_cast_of_sameShape (orc : FFSOracleSem)
    {d d' : ValTy} (hshape : ValSoundOfDenot.ValTy.SameShape d d')
    (rho : ValEnvSem) (G G' : List ValTy) (D D' : List ValValSem)
    (v : ValValSem) (a' : (denotValTyS orc rho G' D' d').El)
    (hto' : ValValSem.toEl (denotValTyS orc rho G' D' d') v = .ok a') :
    let hEl : (denotValTyS orc rho G D d).El =
        (denotValTyS orc rho G' D' d').El := by
          rw [denotValTyS_El_eq_carrierEl_raw,
            denotValTyS_El_eq_carrierEl_raw,
            ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape]
    ValValSem.toEl (denotValTyS orc rho G D d) v = .ok (hEl.symm ▸ a') := by
  dsimp only
  let hEl : (denotValTyS orc rho G D d).El =
      (denotValTyS orc rho G' D' d').El := by
    rw [denotValTyS_El_eq_carrierEl_raw,
      denotValTyS_El_eq_carrierEl_raw,
      ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape]
  let a : (denotValTyS orc rho G D d).El := hEl.symm ▸ a'
  have ha : HEq a a' := cast_heq hEl.symm a'
  have htoHEq : HEq
      (ValValSem.toEl (denotValTyS orc rho G D d) v)
      (ValValSem.toEl (denotValTyS orc rho G' D' d') v) :=
    toEl_denotValTyS_sameShape_raw orc d d' hshape rho rho G G' D D' v
  have hOk : HEq
      (Except.ok a : Except DimError (denotValTyS orc rho G D d).El)
      (Except.ok a' : Except DimError (denotValTyS orc rho G' D' d').El) :=
    except_ok_heq hEl ha
  have hres : ValValSem.toEl (denotValTyS orc rho G D d) v = .ok a :=
    eq_of_heq (HEq.trans (HEq.trans htoHEq (heq_of_eq hto')) (HEq.symm hOk))
  simpa only [a, hEl] using hres

/-! ## Same-raw realization transport -/

theorem RawAgree.realize_transport (orc : FFSOracleSem)
    (sigma : DEnv) (rho : ValEnvSem) :
    forall {Ds : List DVal} {Gs Gt : List ValTy}
      {Dvs Dvt : List ValValSem} {tau : Ty} {tauvs tauvt : ValTy}
      {B : BasisDenot} {source : DVal} {value : ValValSem},
      ValSoundOfDenot.ValTy.SameShape tauvs tauvt ->
      RawAgreeDimsAt orc sigma rho Ds Gs Dvs tau tauvs B ->
      RawAgreeDimsAt orc sigma rho Ds Gt Dvt tau tauvt B ->
      RawAgree orc sigma rho Ds Gs Dvs tau tauvs B source value ->
      RawAgree orc sigma rho Ds Gt Dvt tau tauvt B source value := by
  intro Ds Gs Gt Dvs Dvt tau tauvs tauvt B source value hshape hds hdt ha
  generalize hn : Ty.size tau + ValTy.kindSize tauvs +
      ValTy.kindSize tauvt = n
  induction n using Nat.strong_induction_on generalizing
      Ds Gs Gt Dvs Dvt tau tauvs tauvt B source value with
  | h n ih =>
      cases tau with
      | space s =>
          cases tauvs with
          | space svs =>
              cases tauvt with
              | space svt =>
                  cases value with
                  | fn T f => simpa only [RawAgree] using ha
                  | array a =>
                      simp only [RawAgreeDimsAt] at hds hdt
                      simp only [RawAgree, LegacyAgree] at ha ⊢
                      have hdim : ValSpace.dof (orc rho Gs Dvs) svs =
                          ValSpace.dof (orc rho Gt Dvt) svt := by
                        simp only [ValSpace.dof, hds, hdt]
                      rw [hdim] at ha
                      exact ha
              | piTy _ _ => exact hshape.elim
          | piTy _ _ =>
              cases tauvt with
              | space _ => exact hshape.elim
              | piTy _ _ => simpa only [RawAgree] using ha
      | piTy tau0 tau1 =>
          cases tauvs with
          | space _ => simpa only [RawAgree] using ha
          | piTy tauvs0 tauvs1 =>
              cases tauvt with
              | space _ => exact hshape.elim
              | piTy tauvt0 tauvt1 =>
                  simp only [RawAgreeDimsAt] at hds hdt
                  simp only [RawAgree] at ha ⊢
                  obtain ⟨f, hy, hf⟩ := ha
                  obtain ⟨hshape0, hshape1⟩ := hshape
                  let Tvs0 := denotValTyS orc rho Gs Dvs tauvs0
                  let Tvt0 := denotValTyS orc rho Gt Dvt tauvt0
                  let hEl : Tvs0.El = Tvt0.El := by
                    dsimp only [Tvs0, Tvt0]
                    rw [denotValTyS_El_eq_carrierEl_raw,
                      denotValTyS_El_eq_carrierEl_raw,
                      ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape0]
                  let ft : Tvt0.El -> Except DimError ValValSem :=
                    fun arg => f (hEl.symm ▸ arg)
                  refine ⟨ft, ?_, ?_⟩
                  · exact hy.trans (raw_fn_recast hEl f)
                  · intro x' argVal argt htot hargt
                    let args : Tvs0.El := hEl.symm ▸ argt
                    have htos : ValValSem.toEl Tvs0 argVal = .ok args := by
                      simpa only [Tvs0, Tvt0, hEl, args] using
                        (raw_decode_cast_of_sameShape orc hshape0 rho
                          Gs Gt Dvs Dvt argVal argt htot)
                    have hdomLt : Ty.size tau0 + ValTy.kindSize tauvt0 +
                        ValTy.kindSize tauvs0 < n := by
                      simp only [Ty.size, ValTy.kindSize_piTy] at hn
                      omega
                    have hargs : RawAgree orc sigma rho Ds Gs Dvs
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
                    have houtAgreeT : RawAgree orc sigma rho
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

theorem RawAgree.toEl_fromEl (orc : FFSOracleSem)
    (sigma : DEnv) (rho : ValEnvSem) :
    forall {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
      {tau : Ty} {tauv : ValTy} {B : BasisDenot} {source : DVal}
      {value : ValValSem},
      RawAgreeDimsAt orc sigma rho Ds Gv Dv tau tauv B ->
      RawAgree orc sigma rho Ds Gv Dv tau tauv B source value ->
      exists a : (denotValTyS orc rho Gv Dv tauv).El,
        ValValSem.toEl (denotValTyS orc rho Gv Dv tauv) value = .ok a /\
        RawAgree orc sigma rho Ds Gv Dv tau tauv B source
          (ValValSem.fromEl (denotValTyS orc rho Gv Dv tauv) a) := by
  intro Ds Gv Dv tau tauv B source value hd ha
  generalize hn : Ty.size tau + ValTy.kindSize tauv = n
  induction n using Nat.strong_induction_on generalizing
      Ds Gv Dv tau tauv B source value with
  | h n ih =>
      cases tau with
      | space s =>
          cases tauv with
          | space sv =>
              cases value with
              | fn T f => simpa only [RawAgree] using ha
              | array a =>
                  simp only [RawAgree] at ha
                  have hlen : a.length = ValSpace.dof (orc rho Gv Dv) sv :=
                    ha.2.1
                  refine ⟨a, rfl, ?_⟩
                  simp only [denotValTyS, ValValSem.fromEl]
                  rw [FlatArray.resize_eq_self_of_length_raw hlen]
                  simpa only [RawAgree] using ha
          | piTy _ _ => simpa only [RawAgree] using ha
      | piTy tau0 tau1 =>
          cases tauv with
          | space _ => simpa only [RawAgree] using ha
          | piTy tauv0 tauv1 =>
              simp only [RawAgreeDimsAt] at hd
              simp only [RawAgree] at ha
              obtain ⟨f, rfl, hf⟩ := ha
              let Tv0 := denotValTyS orc rho Gv Dv tauv0
              let fam : Tv0.El -> ValTypeSem := fun arg =>
                denotValTyS orc rho (tauv0 :: Gv)
                  (ValValSem.fromEl Tv0 arg :: Dv) tauv1
              let a : (arg : Tv0.El) -> Except DimError (fam arg).El :=
                fun arg => match f arg with
                  | .error err => .error err
                  | .ok out => ValValSem.toEl (fam arg) out
              refine ⟨a, ?_, ?_⟩
              · simp [denotValTyS, ValValSem.toEl, Tv0, fam, a]
                funext arg
                cases f arg <;> rfl
              · simp only [denotValTyS, ValValSem.fromEl, RawAgree]
                refine ⟨fun arg => (a arg).map
                  (ValValSem.fromEl (fam arg)), rfl, ?_⟩
                intro x' argVal arg hto harg
                obtain ⟨out, hout, houtAgree⟩ :=
                  hf x' argVal arg hto harg
                have hdRaw := hd.2 x' argVal arg hto harg
                have hdomLt : Ty.size tau0 + ValTy.kindSize tauv0 < n := by
                  simp only [Ty.size, ValTy.kindSize_piTy] at hn
                  omega
                obtain ⟨argCanonEl, htoCanonEl, hargCanon⟩ :=
                  ih (Ty.size tau0 + ValTy.kindSize tauv0) hdomLt
                    hd.1 harg rfl
                have hargEq : argCanonEl = arg :=
                  Except.ok.inj (htoCanonEl.symm.trans hto)
                subst argCanonEl
                let argCanon := ValValSem.fromEl Tv0 arg
                have hargCanon' : RawAgree orc sigma rho Ds Gv Dv
                    tau0 tauv0 B.domainBasis
                    ((denotTyAux sigma Ds tau0).embed x') argCanon := by
                  simpa only [Tv0, argCanon] using hargCanon
                obtain ⟨argAgain, htoAgain⟩ := hargCanon'.toEl
                have hdCanon := hd.2 x' argCanon argAgain htoAgain hargCanon'
                have houtCanonCtx : RawAgree orc sigma rho
                    ((denotTyAux sigma Ds tau0).embed x' :: Ds)
                    (tauv0 :: Gv) (argCanon :: Dv) tau1 tauv1
                    (B.applyEl x') (source.applyEl x') out :=
                  RawAgree.realize_transport orc sigma rho
                    (ValSoundOfDenot.ValTy.SameShape.refl tauv1)
                    hdRaw hdCanon houtAgree
                have hcodLt : Ty.size tau1 + ValTy.kindSize tauv1 < n := by
                  simp only [Ty.size, ValTy.kindSize_piTy] at hn
                  omega
                obtain ⟨outEl, htoOut, houtCanonized⟩ :=
                  ih (Ty.size tau1 + ValTy.kindSize tauv1) hcodLt
                    hdCanon houtCanonCtx rfl
                have houtRaw : RawAgree orc sigma rho
                    ((denotTyAux sigma Ds tau0).embed x' :: Ds)
                    (tauv0 :: Gv) (argVal :: Dv) tau1 tauv1
                    (B.applyEl x') (source.applyEl x')
                    (ValValSem.fromEl (fam arg) outEl) := by
                  apply RawAgree.realize_transport orc sigma rho
                    (ValSoundOfDenot.ValTy.SameShape.refl tauv1)
                    hdCanon hdRaw
                  simpa only [fam, Tv0, argCanon] using houtCanonized
                refine ⟨ValValSem.fromEl (fam arg) outEl, ?_, houtRaw⟩
                have htoOut' : ValValSem.toEl (fam arg) out = .ok outEl := by
                  simpa only [fam, Tv0, argCanon] using htoOut
                simp only [a, hout, htoOut', Except.map]

/-- Checked reification of a decoded raw-agreeing value cannot raise a
dimension error. -/
theorem RawAgree.fromElChecked_of_toEl
    (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem) :
    forall {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
      {tau : Ty} {tauv : ValTy} {B : BasisDenot} {source : DVal}
      {value : ValValSem} {a : (denotValTyS orc rho Gv Dv tauv).El},
      RawAgreeDimsAt orc sigma rho Ds Gv Dv tau tauv B ->
      RawAgree orc sigma rho Ds Gv Dv tau tauv B source value ->
      ValValSem.toEl (denotValTyS orc rho Gv Dv tauv) value = .ok a ->
      exists canon,
        ValValSem.fromElChecked (denotValTyS orc rho Gv Dv tauv) a =
            .ok canon /\
          RawAgree orc sigma rho Ds Gv Dv tau tauv B source canon := by
  intro Ds Gv Dv tau tauv B source value a hd ha hto
  generalize hn : Ty.size tau + ValTy.kindSize tauv = n
  induction n using Nat.strong_induction_on generalizing
      Ds Gv Dv tau tauv B source value a with
  | h n ih =>
      cases tau with
      | space s =>
          cases tauv with
          | piTy _ _ => simpa only [RawAgree] using ha
          | space sv =>
              cases value with
              | fn T f => simpa only [RawAgree] using ha
              | array rawArray =>
                  simp only [RawAgree] at ha
                  have haEq : rawArray = a := Except.ok.inj hto
                  subst a
                  refine ⟨.array rawArray, ?_, ?_⟩
                  · simpa only [denotValTyS] using
                      ValValSem.fromElChecked_space_of_length sv
                        (ValSpace.dof (orc rho Gv Dv) sv) rawArray ha.2.1
                  · simpa only [RawAgree] using ha
      | piTy tau0 tau1 =>
          cases tauv with
          | space _ => simpa only [RawAgree] using ha
          | piTy tauv0 tauv1 =>
              simp only [RawAgreeDimsAt] at hd
              simp only [RawAgree] at ha
              obtain ⟨f, rfl, hf⟩ := ha
              let Tv0 := denotValTyS orc rho Gv Dv tauv0
              let fam : Tv0.El -> ValTypeSem := fun arg =>
                denotValTyS orc rho (tauv0 :: Gv)
                  (ValValSem.fromEl Tv0 arg :: Dv) tauv1
              let decoded : (arg : Tv0.El) -> Except DimError (fam arg).El :=
                fun arg => match f arg with
                  | .error err => .error err
                  | .ok out => ValValSem.toEl (fam arg) out
              have hto' :
                  (Except.ok decoded : Except DimError
                    ((arg : Tv0.El) -> Except DimError (fam arg).El)) =
                    (Except.ok a : Except DimError
                      ((arg : Tv0.El) -> Except DimError (fam arg).El)) := by
                simpa only [denotValTyS, ValValSem.toEl, dif_pos rfl,
                  Tv0, fam, decoded] using hto
              have haEq : decoded = a := Except.ok.inj hto'
              subst a
              let checked : Tv0.El -> Except DimError ValValSem := fun arg =>
                (decoded arg).bind (ValValSem.fromElChecked (fam arg))
              refine ⟨.fn Tv0.El checked, ?_, ?_⟩
              · change ValValSem.fromElChecked (.piTy Tv0.El fam) decoded =
                  .ok (.fn Tv0.El checked)
                rfl
              · simp only [RawAgree]
                refine ⟨checked, rfl, ?_⟩
                intro x' argVal arg htoArg harg
                obtain ⟨out, hout, houtAgree⟩ :=
                  hf x' argVal arg htoArg harg
                obtain ⟨argCanonEl, htoCanonEl, hargCanon⟩ :=
                  RawAgree.toEl_fromEl orc sigma rho hd.1 harg
                have hargEq : argCanonEl = arg :=
                  Except.ok.inj (htoCanonEl.symm.trans htoArg)
                subst argCanonEl
                let argCanon := ValValSem.fromEl Tv0 arg
                have hargCanon' : RawAgree orc sigma rho Ds Gv Dv
                    tau0 tauv0 B.domainBasis
                    ((denotTyAux sigma Ds tau0).embed x') argCanon := by
                  simpa only [Tv0, argCanon] using hargCanon
                have hdRaw := hd.2 x' argVal arg htoArg harg
                obtain ⟨argAgain, htoAgain⟩ := hargCanon'.toEl
                have hdCanon := hd.2 x' argCanon argAgain htoAgain hargCanon'
                have houtCanonCtx : RawAgree orc sigma rho
                    ((denotTyAux sigma Ds tau0).embed x' :: Ds)
                    (tauv0 :: Gv) (argCanon :: Dv) tau1 tauv1
                    (B.applyEl x') (source.applyEl x') out :=
                  RawAgree.realize_transport orc sigma rho
                    (ValSoundOfDenot.ValTy.SameShape.refl tauv1)
                    hdRaw hdCanon houtAgree
                obtain ⟨outEl, htoOut⟩ := houtCanonCtx.toEl
                have hcodLt : Ty.size tau1 + ValTy.kindSize tauv1 < n := by
                  simp only [Ty.size, ValTy.kindSize_piTy] at hn
                  omega
                obtain ⟨canonOut, hcheckOut, hcanonAgree⟩ :=
                  ih (Ty.size tau1 + ValTy.kindSize tauv1) hcodLt
                    hdCanon houtCanonCtx htoOut rfl
                have htoOut' : ValValSem.toEl (fam arg) out = .ok outEl := by
                  simpa only [fam, Tv0, argCanon] using htoOut
                have hcheckOut' :
                    ValValSem.fromElChecked (fam arg) outEl = .ok canonOut := by
                  simpa only [fam, Tv0, argCanon] using hcheckOut
                refine ⟨canonOut, ?_, ?_⟩
                · simp only [checked, decoded, hout, htoOut', Except.bind,
                    hcheckOut']
                · exact RawAgree.realize_transport orc sigma rho
                    (ValSoundOfDenot.ValTy.SameShape.refl tauv1)
                    hdCanon hdRaw hcanonAgree

/-- Raw function introduction from a body proof evaluated at the canonical
representation of each decoded argument. -/
theorem RawAgree.pi_intro_from_canonical
    (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau0 tau1 : Ty} {tauv0 tauv1 : ValTy} {B : BasisDenot}
    {funSource : DVal}
    (hd : RawAgreeDimsAt orc sigma rho Ds Gv Dv
      (.piTy tau0 tau1) (.piTy tauv0 tauv1) B)
    (f : (denotValTyS orc rho Gv Dv tauv0).El ->
      Except DimError ValValSem)
    (hbody : forall (x' : (denotTyAux sigma Ds tau0).El)
        (arg : (denotValTyS orc rho Gv Dv tauv0).El),
      RawAgree orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis
        ((denotTyAux sigma Ds tau0).embed x')
        (ValValSem.fromEl (denotValTyS orc rho Gv Dv tauv0) arg) ->
      exists out, f arg = .ok out /\
        RawAgree orc sigma rho
          ((denotTyAux sigma Ds tau0).embed x' :: Ds)
          (tauv0 :: Gv)
          (ValValSem.fromEl (denotValTyS orc rho Gv Dv tauv0) arg :: Dv)
          tau1 tauv1 (B.applyEl x') (funSource.applyEl x') out) :
    RawAgree orc sigma rho Ds Gv Dv (.piTy tau0 tau1)
      (.piTy tauv0 tauv1) B funSource
      (.fn (denotValTyS orc rho Gv Dv tauv0).El f) := by
  simp only [RawAgree]
  refine ⟨f, rfl, ?_⟩
  intro x' argVal arg hto harg
  simp only [RawAgreeDimsAt] at hd
  obtain ⟨argCanonEl, htoCanonEl, hargCanon⟩ :=
    RawAgree.toEl_fromEl orc sigma rho hd.1 harg
  have hargEq : argCanonEl = arg :=
    Except.ok.inj (htoCanonEl.symm.trans hto)
  subst argCanonEl
  let argCanon :=
    ValValSem.fromEl (denotValTyS orc rho Gv Dv tauv0) arg
  have hargCanon' : RawAgree orc sigma rho Ds Gv Dv tau0 tauv0
      B.domainBasis ((denotTyAux sigma Ds tau0).embed x') argCanon := by
    simpa only [argCanon] using hargCanon
  obtain ⟨out, hout, houtCanon⟩ := hbody x' arg hargCanon'
  have hdRaw := hd.2 x' argVal arg hto harg
  obtain ⟨argAgain, htoAgain⟩ := hargCanon'.toEl
  have hdCanon := hd.2 x' argCanon argAgain htoAgain hargCanon'
  refine ⟨out, hout, ?_⟩
  exact RawAgree.realize_transport orc sigma rho
    (ValSoundOfDenot.ValTy.SameShape.refl tauv1)
    hdCanon hdRaw houtCanon

/-- The semantic value produced by a value lambda satisfies raw function
agreement whenever its body does at every canonical argument. -/
theorem denotValB_semS_vlam_rawResult
    (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau0 tau1 : Ty} {tauv0 tauv1 : ValTy} {B : BasisDenot}
    {funSource : DVal} (body : ValExpr)
    (hd : RawAgreeDimsAt orc sigma rho Ds Gv Dv
      (.piTy tau0 tau1) (.piTy tauv0 tauv1) B)
    (hbody : forall (x' : (denotTyAux sigma Ds tau0).El)
        (arg : (denotValTyS orc rho Gv Dv tauv0).El),
      RawAgree orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis
        ((denotTyAux sigma Ds tau0).embed x')
        (ValValSem.fromEl (denotValTyS orc rho Gv Dv tauv0) arg) ->
      RawResultAgree orc sigma rho
        ((denotTyAux sigma Ds tau0).embed x' :: Ds)
        (tauv0 :: Gv)
        (ValValSem.fromEl (denotValTyS orc rho Gv Dv tauv0) arg :: Dv)
        tau1 tauv1 (B.applyEl x') (funSource.applyEl x')
        (denotValB_semS orc rho (tauv0 :: Gv)
          (ValValSem.fromEl (denotValTyS orc rho Gv Dv tauv0) arg :: Dv)
          body)) :
    RawResultAgree orc sigma rho Ds Gv Dv
      (.piTy tau0 tau1) (.piTy tauv0 tauv1) B funSource
      (denotValB_semS orc rho Gv Dv (.vlam tauv0 tauv1 body)) := by
  let Tv0 := denotValTyS orc rho Gv Dv tauv0
  let f : Tv0.El -> Except DimError ValValSem := fun arg =>
    denotValB_semS orc rho (tauv0 :: Gv)
      (ValValSem.fromEl Tv0 arg :: Dv) body
  refine ⟨.fn Tv0.El f, ?_, ?_⟩
  · rw [denotValB_semS]
  · apply RawAgree.pi_intro_from_canonical orc sigma rho hd f
    intro x' arg harg
    obtain ⟨out, hout, houtAgree⟩ := hbody x' arg harg
    exact ⟨out, by simpa only [f, Tv0] using hout, houtAgree⟩

/-! ## Checked reshape -/

/-- Paired-context higher-order reshape preserves raw agreement. -/
theorem reshapDenotSemBetweenS_rawResult
    (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem) :
    forall (tau : Ty) (target sourceTy : ValTy)
      (Ds : List DVal)
      (Gt : List ValTy) (Dt : List ValValSem)
      (Gs : List ValTy) (DsVal : List ValValSem)
      (B : BasisDenot) (sourceOut : DVal) (value : ValValSem),
      RawAgreeDimsAt orc sigma rho Ds Gt Dt tau target B ->
      RawAgreeDimsAt orc sigma rho Ds Gs DsVal tau sourceTy B ->
      RawAgree orc sigma rho Ds Gs DsVal tau sourceTy B sourceOut value ->
      RawResultAgree orc sigma rho Ds Gt Dt tau target B sourceOut
        (reshapDenotSemBetweenS orc rho Gt Dt Gs DsVal value
          target sourceTy) := by
  intro tau target sourceTy Ds Gt Dt Gs DsVal B sourceOut value
    hdt hds ha
  generalize hn : ValTy.kindSize target + ValTy.kindSize sourceTy = n
  induction n using Nat.strong_induction_on generalizing
      tau target sourceTy Ds Gt Dt Gs DsVal B sourceOut value with
  | h n ih =>
      cases tau <;> cases target <;> cases sourceTy <;>
        simp only [RawAgreeDimsAt] at hdt hds
      · rename_i s st ss
        cases value with
        | fn T f => simp only [RawAgree] at ha
        | array a =>
            simp only [RawAgree, LegacyAgree] at ha
            have hdim : ValSpace.dof (orc rho Gs DsVal) ss =
                ValSpace.dof (orc rho Gt Dt) st := by
              unfold ValSpace.dof
              rw [hds, hdt]
            rw [hdim] at ha
            have hlen : a.length = ValSpace.dof (orc rho Gt Dt) st :=
              ha.2.1
            have hlenSource : a.length = ValSpace.dof (orc rho Gs DsVal) ss :=
              hlen.trans hdim.symm
            refine ⟨.array a, ?_, ?_⟩
            · simp only [reshapDenotSemBetweenS, reshapArrayBetweenS,
                hlenSource, hdim, if_pos]
            · simpa only [RawAgree, LegacyAgree] using ha
      · rename_i tau0 tau1 target0 target1 source0 source1
        simp only [RawAgree] at ha
        obtain ⟨f, rfl, hf⟩ := ha
        rw [reshapDenotSemBetweenS]
        refine ⟨_, rfl, ?_⟩
        simp only [RawAgree]
        refine ⟨_, rfl, ?_⟩
        intro x' argVal arg htoArg harg
        obtain ⟨argT, hcheckT, hargT⟩ :=
          RawAgree.fromElChecked_of_toEl orc sigma rho hdt.1 harg htoArg
        have hargLt :
            ValTy.kindSize source0 + ValTy.kindSize target0 < n := by
          simp only [ValTy.kindSize_piTy] at hn
          omega
        obtain ⟨argS, hreshapeArg, hargS⟩ :=
          ih (ValTy.kindSize source0 + ValTy.kindSize target0) hargLt
            tau0 source0 target0 Ds Gs DsVal Gt Dt B.domainBasis
            ((denotTyAux sigma Ds tau0).embed x') argT
            hds.1 hdt.1 hargT rfl
        obtain ⟨argSEl, htoS⟩ := hargS.toEl
        obtain ⟨result, happ, hresultS⟩ :=
          hf x' argS argSEl htoS hargS
        obtain ⟨argTEl, htoT⟩ := hargT.toEl
        have hcodT := hdt.2 x' argT argTEl htoT hargT
        have hcodS := hds.2 x' argS argSEl htoS hargS
        have hcodLt :
            ValTy.kindSize target1 + ValTy.kindSize source1 < n := by
          simp only [ValTy.kindSize_piTy] at hn
          omega
        obtain ⟨out, hreshapeOut, houtT⟩ :=
          ih (ValTy.kindSize target1 + ValTy.kindSize source1) hcodLt
            tau1 target1 source1
            ((denotTyAux sigma Ds tau0).embed x' :: Ds)
            (target0 :: Gt) (argT :: Dt)
            (source0 :: Gs) (argS :: DsVal)
            (B.applyEl x') (sourceOut.applyEl x') result
            hcodT hcodS hresultS rfl
        have hcodRaw := hdt.2 x' argVal arg htoArg harg
        have houtRaw : RawAgree orc sigma rho
            ((denotTyAux sigma Ds tau0).embed x' :: Ds)
            (target0 :: Gt) (argVal :: Dt)
            tau1 target1 (B.applyEl x') (sourceOut.applyEl x') out :=
          RawAgree.realize_transport orc sigma rho
            (ValSoundOfDenot.ValTy.SameShape.refl target1)
            hcodT hcodRaw houtT
        refine ⟨out, ?_, houtRaw⟩
        simp only [hcheckT, hreshapeArg, htoS,
          ValValSem.applyTyped_fn, happ, hreshapeOut]

/-- One-context specialization of checked reshape adequacy. -/
theorem reshapDenotSemS_rawResult
    (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    {tau : Ty} {target sourceTy : ValTy} {Ds : List DVal}
    {G : List ValTy} {D : List ValValSem}
    {B : BasisDenot} {sourceOut : DVal} {value : ValValSem}
    (hdt : RawAgreeDimsAt orc sigma rho Ds G D tau target B)
    (hds : RawAgreeDimsAt orc sigma rho Ds G D tau sourceTy B)
    (ha : RawAgree orc sigma rho Ds G D tau sourceTy B sourceOut value) :
    RawResultAgree orc sigma rho Ds G D tau target B sourceOut
      (reshapDenotSemS orc rho G D value target sourceTy) := by
  rw [reshapDenotSemS_eq_between]
  exact reshapDenotSemBetweenS_rawResult orc sigma rho tau target sourceTy
    Ds G D G D B sourceOut value hdt hds ha

/-! ## Ordinary nonlinear application -/

/-- The two ordinary operand traces and exact output dimensions suffice for
the complete `appN_val` result. -/
theorem rawAppNVal_result
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {n0 n1 : Term} {env0 env1 : ValExpr}
    {tauv0 tauv1 tauOut : ValTy}
    (hn1Lc : Term.lc n1)
    (hmatch : (denotTerm sigma n1).matchesShape
      (denotTy sigma (Basis.tof b0)))
    (hpi : exists g : (denotTy sigma (Basis.tof b0)).El -> DVal,
      denotTerm sigma n0 =
        .pi (denotTy sigma (Basis.tof b0)).El g)
    (hdomain : ValSoundOfDenot.ValTy.SameShape
      (ValExpr.inferTypeCtx [] env0).domain tauv0)
    (hdomainDim : forall s s', (ValExpr.inferTypeCtx [] env0).domain = .space s ->
      tauv0 = .space s' ->
      ValSpace.dof (orc rho [] []) s = ValSpace.dof (orc rho [] []) s')
    (hcodomain : ValSoundOfDenot.ValTy.SameShape tauv1 tauOut)
    (function : RawTermTraceAt orc sigma rho env0
      (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
      (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0))
    (argument : RawTermTraceAt orc sigma rho env1
      (Basis.tof b0) tauv0 (denotBasis sigma b0) (denotTerm sigma n1))
    (hdOut : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof (Basis.instantiate n1 b1)) tauOut
      (denotBasis sigma (Basis.instantiate n1 b1))) :
    RawTermTraceAt orc sigma rho (.appV env0 env1)
      (Basis.tof (Basis.instantiate n1 b1)) tauOut
      (denotBasis sigma (Basis.instantiate n1 b1))
      (denotTerm sigma (.appN n0 n1)) := by
  let T0 := denotTy sigma (Basis.tof b0)
  let x' : T0.El := T0.extract (denotTerm sigma n1)
  have hxT : T0.embed x' = denotTerm sigma n1 :=
    HType.embed_extract_of_matchesShape hmatch
  obtain ⟨funValue, hfunEval, hfunAgree⟩ := function.result
  obtain ⟨argValue, hargEval, hargAgree⟩ := argument.result
  have hargForApp : RawAgree orc sigma rho [] [] []
      (Basis.tof b0) tauv0
      (denotBasis sigma (.frame b0 b1)).domainBasis
      (T0.embed x') argValue := by
    simpa only [denotBasis_frame_domainBasis, hxT] using hargAgree
  obtain ⟨arg, out, hto, happ, houtPush⟩ :=
    RawAgree.appV_result x' env0 env1 tauOut
      hfunAgree hargForApp hdomain hdomainDim hfunEval hargEval
  have hdFun := function.dims
  simp only [Basis.tof, RawAgreeDimsAt] at hdFun
  have hdCodPush := hdFun.2 x' argValue arg hto hargForApp
  have houtOpen : RawAgree orc sigma rho [] [tauv0] [argValue]
      (Ty.openRec 0 n1 (Basis.tof b1)) tauv1
      ((denotBasis sigma (.frame b0 b1)).applyEl x')
      ((denotTerm sigma n0).applyEl x') out := by
    apply (RawAgree.instantiate_src hn1Lc (Basis.tof b1)
      [tauv0] [argValue] tauv1
      ((denotBasis sigma (.frame b0 b1)).applyEl x')
      ((denotTerm sigma n0).applyEl x') out).mp
    simpa only [T0, hxT] using houtPush
  have hdOpen : RawAgreeDimsAt orc sigma rho [] [tauv0] [argValue]
      (Ty.openRec 0 n1 (Basis.tof b1)) tauv1
      ((denotBasis sigma (.frame b0 b1)).applyEl x') := by
    apply (RawAgreeDimsAt.instantiate_src hn1Lc (Basis.tof b1)
      [tauv0] [argValue] tauv1
      ((denotBasis sigma (.frame b0 b1)).applyEl x')).mp
    simpa only [T0, hxT] using hdCodPush
  obtain ⟨g, hg⟩ := hpi
  have hbasis := denotBasis_frame_applyEl_instantiate
    (sigma := sigma) (n1 := n1) (b0 := b0) (b1 := b1)
    hn1Lc hmatch
  have hsource := denotTerm_appN_applyEl
    (sigma := sigma) (n0 := n0) (n1 := n1) (T0 := T0) (g := g)
    (by simpa only [T0] using hg) hmatch
  rw [hbasis, ← hsource] at houtOpen
  rw [hbasis] at hdOpen
  have hdOutOpen : RawAgreeDimsAt orc sigma rho [] [] []
      (Ty.openRec 0 n1 (Basis.tof b1)) tauOut
      (denotBasis sigma (Basis.instantiate n1 b1)) := by
    simpa only [Basis.instantiate, Basis.tof_openRec] using hdOut
  have houtFinal : RawAgree orc sigma rho [] [] []
      (Basis.tof (Basis.instantiate n1 b1)) tauOut
      (denotBasis sigma (Basis.instantiate n1 b1))
      (denotTerm sigma (.appN n0 n1)) out := by
    have htransport := RawAgree.realize_transport orc sigma rho
      hcodomain hdOpen hdOutOpen houtOpen
    simpa only [Basis.instantiate, Basis.tof_openRec] using htransport
  exact ⟨⟨out, happ, houtFinal⟩, hdOut⟩

/-! ## Packaged current boundary -/

/-- The value-only facts consumed by the non-beta raw term induction. -/
structure RawNonBetaValueKernel (orc : FFSOracleSem) : Prop where
  realize :
    forall {sigma : DEnv} {rho : ValEnvSem}
      {Gs Gt : List ValTy} {Dvs Dvt : List ValValSem}
      {tau : Ty} {tauvs tauvt : ValTy} {B : BasisDenot}
      {source : DVal} {value : ValValSem},
      ValSoundOfDenot.ValTy.SameShape tauvs tauvt ->
      RawAgreeDimsAt orc sigma rho [] Gs Dvs tau tauvs B ->
      RawAgreeDimsAt orc sigma rho [] Gt Dvt tau tauvt B ->
      RawAgree orc sigma rho [] Gs Dvs tau tauvs B source value ->
      RawAgree orc sigma rho [] Gt Dvt tau tauvt B source value
  reshape :
    forall {sigma : DEnv} {rho : ValEnvSem} {e : ValExpr}
      {tau : Ty} {target sourceTy : ValTy} {B : BasisDenot}
      {source : DVal},
      RawAgreeDimsAt orc sigma rho [] [] [] tau target B ->
      RawAgreeDimsAt orc sigma rho [] [] [] tau sourceTy B ->
      RawResultAgree orc sigma rho [] [] [] tau sourceTy B source
        (denotValB_semS orc rho [] [] e) ->
      RawResultAgree orc sigma rho [] [] [] tau target B source
        (denotValB_semS orc rho [] [] (.reshap e target sourceTy))
  vlam :
    forall {sigma : DEnv} {rho : ValEnvSem}
      {tau0 tau1 : Ty} {tauv0 tauv1 : ValTy} {B : BasisDenot}
      {funSource : DVal} (body : ValExpr),
      RawAgreeDimsAt orc sigma rho [] [] []
        (.piTy tau0 tau1) (.piTy tauv0 tauv1) B ->
      (forall (x' : (denotTy sigma tau0).El)
        (arg : (denotValTyS orc rho [] [] tauv0).El),
        RawAgree orc sigma rho [] [] [] tau0 tauv0 B.domainBasis
          ((denotTy sigma tau0).embed x')
          (ValValSem.fromEl (denotValTyS orc rho [] [] tauv0) arg) ->
        RawResultAgree orc sigma rho
          [((denotTy sigma tau0).embed x')] [tauv0]
          [ValValSem.fromEl (denotValTyS orc rho [] [] tauv0) arg]
          tau1 tauv1 (B.applyEl x') (funSource.applyEl x')
          (denotValB_semS orc rho [tauv0]
            [ValValSem.fromEl (denotValTyS orc rho [] [] tauv0) arg]
            body)) ->
      RawResultAgree orc sigma rho [] [] []
        (.piTy tau0 tau1) (.piTy tauv0 tauv1) B funSource
        (denotValB_semS orc rho [] [] (.vlam tauv0 tauv1 body))
  appN :
    forall {sigma : DEnv} {rho : ValEnvSem}
      {b0 b1 : Basis} {n0 n1 : Term} {env0 env1 : ValExpr}
      {tauv0 tauv1 tauOut : ValTy},
      Term.lc n1 ->
      (denotTerm sigma n1).matchesShape
        (denotTy sigma (Basis.tof b0)) ->
      (exists g : (denotTy sigma (Basis.tof b0)).El -> DVal,
        denotTerm sigma n0 =
          .pi (denotTy sigma (Basis.tof b0)).El g) ->
      ValSoundOfDenot.ValTy.SameShape
        (ValExpr.inferTypeCtx [] env0).domain tauv0 ->
      (forall s s', (ValExpr.inferTypeCtx [] env0).domain = .space s ->
        tauv0 = .space s' ->
        ValSpace.dof (orc rho [] []) s = ValSpace.dof (orc rho [] []) s') ->
      ValSoundOfDenot.ValTy.SameShape tauv1 tauOut ->
      RawTermTraceAt orc sigma rho env0
        (Basis.tof (.frame b0 b1)) (.piTy tauv0 tauv1)
        (denotBasis sigma (.frame b0 b1)) (denotTerm sigma n0) ->
      RawTermTraceAt orc sigma rho env1 (Basis.tof b0) tauv0
        (denotBasis sigma b0) (denotTerm sigma n1) ->
      RawAgreeDimsAt orc sigma rho [] [] []
        (Basis.tof (Basis.instantiate n1 b1)) tauOut
        (denotBasis sigma (Basis.instantiate n1 b1)) ->
      RawTermTraceAt orc sigma rho (.appV env0 env1)
        (Basis.tof (Basis.instantiate n1 b1)) tauOut
        (denotBasis sigma (Basis.instantiate n1 b1))
        (denotTerm sigma (.appN n0 n1))

/-- The non-beta value kernel is fully constructive. -/
theorem RawNonBetaValueKernel.holds (orc : FFSOracleSem) :
    RawNonBetaValueKernel orc where
  realize hshape hds hdt ha :=
    RawAgree.realize_transport orc _ _ hshape hds hdt ha
  reshape hdt hds hresult := by
    obtain ⟨value, heval, hagree⟩ := hresult
    have hr := reshapDenotSemS_rawResult orc _ _ hdt hds hagree
    simpa only [denotValB_semS.eq_17, heval] using hr
  vlam body hd hbody :=
    denotValB_semS_vlam_rawResult orc _ _ body hd hbody
  appN hn1Lc hmatch hpi hdomain hdomainDim hcodomain function argument hdOut :=
    rawAppNVal_result hn1Lc hmatch hpi hdomain hdomainDim hcodomain
      function argument hdOut

end GLang
