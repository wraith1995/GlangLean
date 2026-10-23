import GLang.Proofs.Adequacy.Foundations.OpenBridgeCore
import GLang.Proofs.Adequacy.Raw.RawAgreement

/-!
# Source-stack bridges for raw agreement

These lemmas relate a fresh named source binding to the corresponding source
de Bruijn entry, and show that locally closed source types ignore an otherwise
unused source stack.  They are independent of consistency and of the adequacy
master, so the exact-basis type theorem can live below both.
-/

namespace GLang

/-- Raw agreement is invariant under the standard source-side open-and-bind
presentation change.  Value-side stacks and the raw runtime value are fixed. -/
theorem RawAgree.openRec_bind_src (orc : FFSOracleSem) {z : Name}
    (sigma : DEnv) (rho : ValEnvSem) :
    forall (tau : Ty) (tauv : ValTy) (Ds : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (k : Nat)
      (B : BasisDenot) (x : DVal) (y : ValValSem),
      z ∉ Ty.fv tau ->
      (RawAgree orc (sigma.bind z (Ds.getD k DVal.default)) rho Ds Gv Dv
          (Ty.openRec k (.var z) tau) tauv B x y <->
        RawAgree orc sigma rho Ds Gv Dv tau tauv B x y)
  | .space s, .space sv, Ds, Gv, Dv, k, B, x, y, hz => by
      simp only [Ty.fv] at hz
      cases y with
      | array a =>
          simpa only [Ty.openRec, RawAgree] using
            (LegacyAgree.openRec_bind_src orc sigma rho (.space s) (.space sv)
              Ds Gv Dv k B x (.array a) hz)
      | fn T f => simp only [Ty.openRec, RawAgree]
  | .space _, .piTy _ _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.openRec, RawAgree]
  | .piTy _ _, .space _, _, _, _, _, _, _, _, _ => by
      simp only [Ty.openRec, RawAgree]
  | .piTy tau0 tau1, .piTy tauv0 tauv1, Ds, Gv, Dv, k, B, x, y, hz => by
      simp only [Ty.fv, Finset.mem_union, not_or] at hz
      have hT0 :
          denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
              (Ty.openRec k (.var z) tau0) = denotTyAux sigma Ds tau0 :=
        denotTyAux_openRec_bind sigma Ds k tau0 hz.1
      simp only [Ty.openRec, RawAgree]
      revert hT0
      generalize denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
          (Ty.openRec k (.var z) tau0) = T0
      generalize denotTyAux sigma Ds tau0 = T1
      intro hT0
      subst T1
      constructor
      · rintro ⟨f, hy, hf⟩
        refine ⟨f, hy, ?_⟩
        intro x' argVal arg hto harg
        have hargOpen := (RawAgree.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis _ _ hz.1).mpr harg
        obtain ⟨out, hout, houtAgree⟩ := hf x' argVal arg hto hargOpen
        refine ⟨out, hout, ?_⟩
        have hcod := RawAgree.openRec_bind_src orc sigma rho tau1 tauv1
          (T0.embed x' :: Ds) (tauv0 :: Gv) (argVal :: Dv) (k + 1)
          (B.applyEl x') (x.applyEl x') out hz.2
        simpa only [List.getD_cons_succ] using hcod.mp houtAgree
      · rintro ⟨f, hy, hf⟩
        refine ⟨f, hy, ?_⟩
        intro x' argVal arg hto harg
        have hargClosed := (RawAgree.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis _ _ hz.1).mp harg
        obtain ⟨out, hout, houtAgree⟩ := hf x' argVal arg hto hargClosed
        refine ⟨out, hout, ?_⟩
        have hcod := RawAgree.openRec_bind_src orc sigma rho tau1 tauv1
          (T0.embed x' :: Ds) (tauv0 :: Gv) (argVal :: Dv) (k + 1)
          (B.applyEl x') (x.applyEl x') out hz.2
        simpa only [List.getD_cons_succ] using hcod.mpr houtAgree
  termination_by tau _ _ _ _ _ _ _ _ => Ty.size tau
  decreasing_by all_goals simp only [Ty.size]; omega

/-- Exact raw dimensions obey the same source open-and-bind bridge. -/
theorem RawAgreeDimsAt.openRec_bind_src (orc : FFSOracleSem) {z : Name}
    (sigma : DEnv) (rho : ValEnvSem) :
    forall (tau : Ty) (tauv : ValTy) (Ds : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (k : Nat)
      (B : BasisDenot),
      z ∉ Ty.fv tau ->
      (RawAgreeDimsAt orc (sigma.bind z (Ds.getD k DVal.default)) rho
          Ds Gv Dv (Ty.openRec k (.var z) tau) tauv B <->
        RawAgreeDimsAt orc sigma rho Ds Gv Dv tau tauv B)
  | .space s, .space sv, Ds, Gv, Dv, k, B, hz => by
      simp only [Ty.fv] at hz
      simp only [Ty.openRec, RawAgreeDimsAt]
      rw [srcShp_openRec_bind sigma Ds k s hz]
  | .space _, .piTy _ _, _, _, _, _, _, _ => by
      simp only [Ty.openRec, RawAgreeDimsAt]
  | .piTy _ _, .space _, _, _, _, _, _, _ => by
      simp only [Ty.openRec, RawAgreeDimsAt]
  | .piTy tau0 tau1, .piTy tauv0 tauv1, Ds, Gv, Dv, k, B, hz => by
      simp only [Ty.fv, Finset.mem_union, not_or] at hz
      have hT0 :
          denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
              (Ty.openRec k (.var z) tau0) = denotTyAux sigma Ds tau0 :=
        denotTyAux_openRec_bind sigma Ds k tau0 hz.1
      simp only [Ty.openRec, RawAgreeDimsAt]
      revert hT0
      generalize denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
          (Ty.openRec k (.var z) tau0) = T0
      generalize denotTyAux sigma Ds tau0 = T1
      intro hT0
      subst T1
      constructor
      · rintro ⟨hdom, hcod⟩
        refine ⟨(RawAgreeDimsAt.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis hz.1).mp hdom, ?_⟩
        intro x' argVal arg hto harg
        have hargOpen := (RawAgree.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis _ _ hz.1).mpr harg
        have hcodOpen := hcod x' argVal arg hto hargOpen
        have hbridge := RawAgreeDimsAt.openRec_bind_src orc sigma rho tau1 tauv1
          (T0.embed x' :: Ds) (tauv0 :: Gv) (argVal :: Dv) (k + 1)
          (B.applyEl x') hz.2
        simpa only [List.getD_cons_succ] using hbridge.mp hcodOpen
      · rintro ⟨hdom, hcod⟩
        refine ⟨(RawAgreeDimsAt.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis hz.1).mpr hdom, ?_⟩
        intro x' argVal arg hto harg
        have hargClosed := (RawAgree.openRec_bind_src orc sigma rho tau0 tauv0
          Ds Gv Dv k B.domainBasis _ _ hz.1).mp harg
        have hcodClosed := hcod x' argVal arg hto hargClosed
        have hbridge := RawAgreeDimsAt.openRec_bind_src orc sigma rho tau1 tauv1
          (T0.embed x' :: Ds) (tauv0 :: Gv) (argVal :: Dv) (k + 1)
          (B.applyEl x') hz.2
        simpa only [List.getD_cons_succ] using hbridge.mpr hcodClosed
  termination_by tau _ _ _ _ _ _ => Ty.size tau
  decreasing_by all_goals simp only [Ty.size]; omega

/-- Locally closed raw agreement ignores the source de Bruijn stack. -/
theorem RawAgree.lc_irrel_src (orc : FFSOracleSem) :
    forall {tau : Ty}, Ty.lc tau -> forall (tauv : ValTy)
      (sigma : DEnv) (rho : ValEnvSem) (Ds0 Ds1 : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (B : BasisDenot)
      (x : DVal) (y : ValValSem),
      RawAgree orc sigma rho Ds0 Gv Dv tau tauv B x y <->
        RawAgree orc sigma rho Ds1 Gv Dv tau tauv B x y
  | _, .space hs => fun tauv sigma rho Ds0 Ds1 Gv Dv B x y => by
      cases tauv with
      | piTy _ _ => simp only [RawAgree]
      | space sv =>
          cases y with
          | fn T f => simp only [RawAgree]
          | array a =>
              simpa only [RawAgree] using
                (LegacyAgree.lc_irrel_src orc (.space hs) (.space sv) sigma rho
                  Ds0 Ds1 Gv Dv B x (.array a))
  | .piTy tau0 tau1, .piTy L htau0 hbody =>
      fun tauv sigma rho Ds0 Ds1 Gv Dv B x y => by
      cases tauv with
      | space sv => simp only [RawAgree]
      | piTy tauv0 tauv1 =>
          have hT0 : denotTyAux sigma Ds0 tau0 = denotTyAux sigma Ds1 tau0 :=
            denotTyAux_lc_irrel htau0 sigma Ds0 Ds1
          simp only [RawAgree]
          revert hT0
          generalize denotTyAux sigma Ds0 tau0 = T0
          generalize denotTyAux sigma Ds1 tau0 = T1
          intro hT0
          subst T1
          constructor
          · rintro ⟨f, hy, hf⟩
            refine ⟨f, hy, ?_⟩
            intro x' argVal arg hto harg
            have harg0 := (RawAgree.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis _ _).mpr harg
            obtain ⟨out, hout, houtAgree0⟩ := hf x' argVal arg hto harg0
            refine ⟨out, hout, ?_⟩
            obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv tau1)
            simp only [Finset.mem_union, not_or] at hw
            have hb0 := RawAgree.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds0) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') (x.applyEl x') out hw.2
            have hb1 := RawAgree.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds1) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') (x.applyEl x') out hw.2
            simp only [List.getD_cons_zero] at hb0 hb1
            exact hb1.mp ((RawAgree.lc_irrel_src orc (hbody w hw.1) tauv1
              (sigma.bind w (T0.embed x')) rho
              (T0.embed x' :: Ds0) (T0.embed x' :: Ds1)
              (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')
              (x.applyEl x') out).mp (hb0.mpr houtAgree0))
          · rintro ⟨f, hy, hf⟩
            refine ⟨f, hy, ?_⟩
            intro x' argVal arg hto harg
            have harg1 := (RawAgree.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis _ _).mp harg
            obtain ⟨out, hout, houtAgree1⟩ := hf x' argVal arg hto harg1
            refine ⟨out, hout, ?_⟩
            obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv tau1)
            simp only [Finset.mem_union, not_or] at hw
            have hb0 := RawAgree.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds0) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') (x.applyEl x') out hw.2
            have hb1 := RawAgree.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds1) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') (x.applyEl x') out hw.2
            simp only [List.getD_cons_zero] at hb0 hb1
            exact hb0.mp ((RawAgree.lc_irrel_src orc (hbody w hw.1) tauv1
              (sigma.bind w (T0.embed x')) rho
              (T0.embed x' :: Ds0) (T0.embed x' :: Ds1)
              (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')
              (x.applyEl x') out).mpr (hb1.mpr houtAgree1))

/-- Locally closed exact raw dimensions ignore the source de Bruijn stack. -/
theorem RawAgreeDimsAt.lc_irrel_src (orc : FFSOracleSem) :
    forall {tau : Ty}, Ty.lc tau -> forall (tauv : ValTy)
      (sigma : DEnv) (rho : ValEnvSem) (Ds0 Ds1 : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (B : BasisDenot),
      RawAgreeDimsAt orc sigma rho Ds0 Gv Dv tau tauv B <->
        RawAgreeDimsAt orc sigma rho Ds1 Gv Dv tau tauv B
  | _, .space hs => fun tauv sigma rho Ds0 Ds1 Gv Dv B => by
      cases tauv with
      | piTy _ _ => simp only [RawAgreeDimsAt]
      | space sv =>
          simp only [RawAgreeDimsAt]
          rw [srcShp_lc_irrel hs sigma Ds0 Ds1]
  | .piTy tau0 tau1, .piTy L htau0 hbody =>
      fun tauv sigma rho Ds0 Ds1 Gv Dv B => by
      cases tauv with
      | space sv => simp only [RawAgreeDimsAt]
      | piTy tauv0 tauv1 =>
          have hT0 : denotTyAux sigma Ds0 tau0 = denotTyAux sigma Ds1 tau0 :=
            denotTyAux_lc_irrel htau0 sigma Ds0 Ds1
          simp only [RawAgreeDimsAt]
          revert hT0
          generalize denotTyAux sigma Ds0 tau0 = T0
          generalize denotTyAux sigma Ds1 tau0 = T1
          intro hT0
          subst T1
          constructor
          · rintro ⟨hdom, hcod⟩
            refine ⟨(RawAgreeDimsAt.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis).mp hdom, ?_⟩
            intro x' argVal arg hto harg
            have harg0 := (RawAgree.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis _ _).mpr harg
            have hcod0 := hcod x' argVal arg hto harg0
            obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv tau1)
            simp only [Finset.mem_union, not_or] at hw
            have hb0 := RawAgreeDimsAt.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds0) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') hw.2
            have hb1 := RawAgreeDimsAt.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds1) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') hw.2
            simp only [List.getD_cons_zero] at hb0 hb1
            exact hb1.mp ((RawAgreeDimsAt.lc_irrel_src orc
              (hbody w hw.1) tauv1 (sigma.bind w (T0.embed x')) rho
              (T0.embed x' :: Ds0) (T0.embed x' :: Ds1)
              (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')).mp (hb0.mpr hcod0))
          · rintro ⟨hdom, hcod⟩
            refine ⟨(RawAgreeDimsAt.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis).mpr hdom, ?_⟩
            intro x' argVal arg hto harg
            have harg1 := (RawAgree.lc_irrel_src orc htau0 tauv0 sigma rho
              Ds0 Ds1 Gv Dv B.domainBasis _ _).mp harg
            have hcod1 := hcod x' argVal arg hto harg1
            obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv tau1)
            simp only [Finset.mem_union, not_or] at hw
            have hb0 := RawAgreeDimsAt.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds0) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') hw.2
            have hb1 := RawAgreeDimsAt.openRec_bind_src orc (z := w) sigma rho
              tau1 tauv1 (T0.embed x' :: Ds1) (tauv0 :: Gv)
              (argVal :: Dv) 0 (B.applyEl x') hw.2
            simp only [List.getD_cons_zero] at hb0 hb1
            exact hb0.mp ((RawAgreeDimsAt.lc_irrel_src orc
              (hbody w hw.1) tauv1 (sigma.bind w (T0.embed x')) rho
              (T0.embed x' :: Ds0) (T0.embed x' :: Ds1)
              (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')).mpr (hb1.mpr hcod1))

end GLang
