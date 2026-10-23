import GLang.Proofs.Adequacy.Foundations.OpenBridgeCore
import GLang.Proofs.Adequacy.Agreement

/-!
# Source-stack bridges for raw agreement

These lemmas relate a fresh named source binding to the corresponding source
de Bruijn entry, and show that locally closed source types ignore an otherwise
unused source stack.  They are independent of consistency and of the adequacy
master, so the exact-basis type theorem can live below both.
-/

namespace GLang.PartialAdequacy

/-- Raw agreement is invariant under the standard source-side open-and-bind
presentation change.  Value-side stacks and the raw runtime value are fixed. -/
theorem Agree.openRec_bind_src (orc : PartialFFSOracleSem) {z : Name}
    (sigma : DEnv) (rho : ValEnvSem) :
    forall (tau : Ty) (tauv : ValTy) (Ds : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (k : Nat)
      (B : BasisDenot) (x : DVal) (y : ValValSem),
      z ∉ Ty.fv tau ->
      (Agree orc (sigma.bind z (Ds.getD k DVal.default)) rho Ds Gv Dv
          (Ty.openRec k (.var z) tau) tauv B x y <->
        Agree orc sigma rho Ds Gv Dv tau tauv B x y)
  | .space s, .space sv, Ds, Gv, Dv, k, B, x, y, hz => by
      simp only [Ty.fv] at hz
      cases y with
      | array a =>
          simp only [Ty.openRec, Agree]
          rw [denotSpaceAux_openRec_bind sigma Ds k s hz]
      | fn T f => simp only [Ty.openRec, Agree]
  | .space _, .piTy _ _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.openRec, Agree]
  | .piTy _ _, .space _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.openRec, Agree]
  | .piTy tau0 tau1, .piTy tauv0 tauv1, Ds, Gv, Dv, k, B, x, y, hz => by
      simp only [Ty.fv, Finset.mem_union, not_or] at hz
      have hT0 :
          denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
              (Ty.openRec k (.var z) tau0) = denotTyAux sigma Ds tau0 :=
        denotTyAux_openRec_bind sigma Ds k tau0 hz.1
      simp only [Ty.openRec, Agree]
      revert hT0
      generalize denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
          (Ty.openRec k (.var z) tau0) = T0
      generalize denotTyAux sigma Ds tau0 = T1
      intro hT0
      subst T1
      constructor
      · rintro ⟨D, hD, f, hy, hf⟩
        refine ⟨D, hD, f, hy, ?_⟩
        intro x' argVal arg hto harg
        have hargOpen := (Agree.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis _ _ hz.1).mpr harg
        obtain ⟨out, hout, houtAgree⟩ := hf x' argVal arg hto hargOpen
        refine ⟨out, hout, ?_⟩
        have hcod := Agree.openRec_bind_src orc sigma rho tau1 tauv1
          (T0.embed x' :: Ds) (tauv0 :: Gv) (argVal :: Dv) (k + 1)
          (B.applyEl x') (x.applyEl x') out hz.2
        simpa only [List.getD_cons_succ] using hcod.mp houtAgree
      · rintro ⟨D, hD, f, hy, hf⟩
        refine ⟨D, hD, f, hy, ?_⟩
        intro x' argVal arg hto harg
        have hargClosed := (Agree.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis _ _ hz.1).mp harg
        obtain ⟨out, hout, houtAgree⟩ := hf x' argVal arg hto hargClosed
        refine ⟨out, hout, ?_⟩
        have hcod := Agree.openRec_bind_src orc sigma rho tau1 tauv1
          (T0.embed x' :: Ds) (tauv0 :: Gv) (argVal :: Dv) (k + 1)
          (B.applyEl x') (x.applyEl x') out hz.2
        simpa only [List.getD_cons_succ] using hcod.mpr houtAgree
  termination_by tau _ _ _ _ _ _ _ _ => Ty.size tau
  decreasing_by all_goals simp only [Ty.size]; omega

/-- Exact raw dimensions obey the same source open-and-bind bridge. -/
theorem DimsAt.openRec_bind_src (orc : PartialFFSOracleSem) {z : Name}
    (sigma : DEnv) (rho : ValEnvSem) :
    forall (tau : Ty) (tauv : ValTy) (Ds : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (k : Nat)
      (B : BasisDenot),
      z ∉ Ty.fv tau ->
      (DimsAt orc (sigma.bind z (Ds.getD k DVal.default)) rho
          Ds Gv Dv (Ty.openRec k (.var z) tau) tauv B <->
        DimsAt orc sigma rho Ds Gv Dv tau tauv B)
  | .space s, .space sv, Ds, Gv, Dv, k, B, hz => by
      simp only [Ty.fv] at hz
      simp only [Ty.openRec, DimsAt]
      rw [srcShp_openRec_bind sigma Ds k s hz]
  | .space _, .piTy _ _, _, _, _, _, _, _ => by
      simp only [Ty.openRec, DimsAt]
  | .piTy _ _, .space _, _, _, _, _, _, _ => by
      simp only [Ty.openRec, DimsAt]
  | .piTy tau0 tau1, .piTy tauv0 tauv1, Ds, Gv, Dv, k, B, hz => by
      simp only [Ty.fv, Finset.mem_union, not_or] at hz
      have hT0 :
          denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
              (Ty.openRec k (.var z) tau0) = denotTyAux sigma Ds tau0 :=
        denotTyAux_openRec_bind sigma Ds k tau0 hz.1
      simp only [Ty.openRec, DimsAt]
      revert hT0
      generalize denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
          (Ty.openRec k (.var z) tau0) = T0
      generalize denotTyAux sigma Ds tau0 = T1
      intro hT0
      subst T1
      constructor
      · rintro ⟨hdom, hcod⟩
        refine ⟨(DimsAt.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis hz.1).mp hdom, ?_⟩
        intro x' argVal arg hto harg
        have hargOpen := (Agree.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis _ _ hz.1).mpr harg
        have hcodOpen := hcod x' argVal arg hto hargOpen
        have hbridge := DimsAt.openRec_bind_src orc sigma rho tau1 tauv1
          (T0.embed x' :: Ds) (tauv0 :: Gv) (argVal :: Dv) (k + 1)
          (B.applyEl x') hz.2
        simpa only [List.getD_cons_succ] using hbridge.mp hcodOpen
      · rintro ⟨hdom, hcod⟩
        refine ⟨(DimsAt.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis hz.1).mpr hdom, ?_⟩
        intro x' argVal arg hto harg
        have hargClosed := (Agree.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis _ _ hz.1).mp harg
        have hcodClosed := hcod x' argVal arg hto hargClosed
        have hbridge := DimsAt.openRec_bind_src orc sigma rho tau1 tauv1
          (T0.embed x' :: Ds) (tauv0 :: Gv) (argVal :: Dv) (k + 1)
          (B.applyEl x') hz.2
        simpa only [List.getD_cons_succ] using hbridge.mpr hcodClosed
  termination_by tau _ _ _ _ _ _ => Ty.size tau
  decreasing_by all_goals simp only [Ty.size]; omega

/-- Locally closed raw agreement ignores the source de Bruijn stack. -/
theorem Agree.lc_irrel_src (orc : PartialFFSOracleSem) :
    forall {tau : Ty}, Ty.lc tau -> forall (tauv : ValTy)
      (sigma : DEnv) (rho : ValEnvSem) (Ds0 Ds1 : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (B : BasisDenot)
      (x : DVal) (y : ValValSem),
      Agree orc sigma rho Ds0 Gv Dv tau tauv B x y <->
        Agree orc sigma rho Ds1 Gv Dv tau tauv B x y
  | _, .space hs => fun tauv sigma rho Ds0 Ds1 Gv Dv B x y => by
      cases tauv with
      | piTy _ _ => simp only [Agree]
      | space sv =>
          cases y with
          | fn T f => simp only [Agree]
          | array a =>
              simp only [Agree]
              rw [denotSpaceAux_lc_irrel hs sigma Ds0 Ds1]
  | .piTy tau0 tau1, .piTy L htau0 hbody =>
      fun tauv sigma rho Ds0 Ds1 Gv Dv B x y => by
      cases tauv with
      | space sv => simp only [Agree]
      | piTy tauv0 tauv1 =>
          have hT0 : denotTyAux sigma Ds0 tau0 = denotTyAux sigma Ds1 tau0 :=
            denotTyAux_lc_irrel htau0 sigma Ds0 Ds1
          simp only [Agree]
          revert hT0
          generalize denotTyAux sigma Ds0 tau0 = T0
          generalize denotTyAux sigma Ds1 tau0 = T1
          intro hT0
          subst T1
          constructor
          · rintro ⟨D, hD, f, hy, hf⟩
            refine ⟨D, hD, f, hy, ?_⟩
            intro x' argVal arg hto harg
            have harg0 := (Agree.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis _ _).mpr harg
            obtain ⟨out, hout, houtAgree0⟩ := hf x' argVal arg hto harg0
            refine ⟨out, hout, ?_⟩
            obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv tau1)
            simp only [Finset.mem_union, not_or] at hw
            have hb0 := Agree.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds0) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') (x.applyEl x') out hw.2
            have hb1 := Agree.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds1) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') (x.applyEl x') out hw.2
            simp only [List.getD_cons_zero] at hb0 hb1
            exact hb1.mp ((Agree.lc_irrel_src orc (hbody w hw.1) tauv1
              (sigma.bind w (T0.embed x')) rho
              (T0.embed x' :: Ds0) (T0.embed x' :: Ds1)
              (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')
              (x.applyEl x') out).mp (hb0.mpr houtAgree0))
          · rintro ⟨D, hD, f, hy, hf⟩
            refine ⟨D, hD, f, hy, ?_⟩
            intro x' argVal arg hto harg
            have harg1 := (Agree.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis _ _).mp harg
            obtain ⟨out, hout, houtAgree1⟩ := hf x' argVal arg hto harg1
            refine ⟨out, hout, ?_⟩
            obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv tau1)
            simp only [Finset.mem_union, not_or] at hw
            have hb0 := Agree.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds0) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') (x.applyEl x') out hw.2
            have hb1 := Agree.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds1) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') (x.applyEl x') out hw.2
            simp only [List.getD_cons_zero] at hb0 hb1
            exact hb0.mp ((Agree.lc_irrel_src orc (hbody w hw.1) tauv1
              (sigma.bind w (T0.embed x')) rho
              (T0.embed x' :: Ds0) (T0.embed x' :: Ds1)
              (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')
              (x.applyEl x') out).mpr (hb1.mpr houtAgree1))

/-- Locally closed exact raw dimensions ignore the source de Bruijn stack. -/
theorem DimsAt.lc_irrel_src (orc : PartialFFSOracleSem) :
    forall {tau : Ty}, Ty.lc tau -> forall (tauv : ValTy)
      (sigma : DEnv) (rho : ValEnvSem) (Ds0 Ds1 : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (B : BasisDenot),
      DimsAt orc sigma rho Ds0 Gv Dv tau tauv B <->
        DimsAt orc sigma rho Ds1 Gv Dv tau tauv B
  | _, .space hs => fun tauv sigma rho Ds0 Ds1 Gv Dv B => by
      cases tauv with
      | piTy _ _ => simp only [DimsAt]
      | space sv =>
          simp only [DimsAt]
          rw [srcShp_lc_irrel hs sigma Ds0 Ds1]
  | .piTy tau0 tau1, .piTy L htau0 hbody =>
      fun tauv sigma rho Ds0 Ds1 Gv Dv B => by
      cases tauv with
      | space sv => simp only [DimsAt]
      | piTy tauv0 tauv1 =>
          have hT0 : denotTyAux sigma Ds0 tau0 = denotTyAux sigma Ds1 tau0 :=
            denotTyAux_lc_irrel htau0 sigma Ds0 Ds1
          simp only [DimsAt]
          revert hT0
          generalize denotTyAux sigma Ds0 tau0 = T0
          generalize denotTyAux sigma Ds1 tau0 = T1
          intro hT0
          subst T1
          constructor
          · rintro ⟨hdom, hcod⟩
            refine ⟨(DimsAt.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis).mp hdom, ?_⟩
            intro x' argVal arg hto harg
            have harg0 := (Agree.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis _ _).mpr harg
            have hcod0 := hcod x' argVal arg hto harg0
            obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv tau1)
            simp only [Finset.mem_union, not_or] at hw
            have hb0 := DimsAt.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds0) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') hw.2
            have hb1 := DimsAt.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds1) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') hw.2
            simp only [List.getD_cons_zero] at hb0 hb1
            exact hb1.mp ((DimsAt.lc_irrel_src orc
              (hbody w hw.1) tauv1 (sigma.bind w (T0.embed x')) rho
              (T0.embed x' :: Ds0) (T0.embed x' :: Ds1)
              (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')).mp (hb0.mpr hcod0))
          · rintro ⟨hdom, hcod⟩
            refine ⟨(DimsAt.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis).mpr hdom, ?_⟩
            intro x' argVal arg hto harg
            have harg1 := (Agree.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis _ _).mp harg
            have hcod1 := hcod x' argVal arg hto harg1
            obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv tau1)
            simp only [Finset.mem_union, not_or] at hw
            have hb0 := DimsAt.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds0) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') hw.2
            have hb1 := DimsAt.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds1) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') hw.2
            simp only [List.getD_cons_zero] at hb0 hb1
            exact hb0.mp ((DimsAt.lc_irrel_src orc
              (hbody w hw.1) tauv1 (sigma.bind w (T0.embed x')) rho
              (T0.embed x' :: Ds0) (T0.embed x' :: Ds1)
              (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')).mpr (hb1.mpr hcod1))

end GLang.PartialAdequacy
