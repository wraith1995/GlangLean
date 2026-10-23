import GLang.Proofs.Adequacy.Raw.Context.RawWorld
import GLang.Proofs.Adequacy.Raw.RawAgreementTransport
import GLang.Proofs.Adequacy.Foundations.STyScopedCore
import GLang.Proofs.Adequacy.Foundations.Erasure
import GLang.Graded.SourceWeaken
import GLang.Proofs.Basis.BasisSoundnessLive
import GLang.Proofs.Progress.Supporting.ProgressTransportSpec

namespace GLang

open Basis (BasisValid)

private theorem raw_evalCtx_mem_extend
    {Psi : EvalCtx} {x x' : VName} {b b' : Basis} {v : ValExpr} :
    (x', b') ∈ Psi.extend x b v ↔
      (x' = x ∧ b' = b) ∨ (x', b') ∈ Psi := by
  simp only [EvalCtx.extend, Finmap.mem_insert, Prod.mk.injEq]

private theorem raw_evalCtx_mem_keyNames
    {Psi : EvalCtx} {x : VName} :
    x ∈ Psi.keyNames ↔ ∃ b, (x, b) ∈ Psi := by
  rw [EvalCtx.keyNames, Finset.mem_image]
  constructor
  · rintro ⟨⟨x', b⟩, hp, rfl⟩
    exact ⟨b, Finmap.mem_keys.mp hp⟩
  · rintro ⟨b, hb⟩
    exact ⟨(x, b), Finmap.mem_keys.mpr hb, rfl⟩

private theorem raw_evalCtx_keyNames_subset_extend
    (Psi : EvalCtx) (y : VName) (b : Basis) (v : ValExpr) :
    Psi.keyNames ⊆ (Psi.extend y b v).keyNames := by
  rw [EvalCtx.keyNames_extend_core]
  exact Finset.subset_insert _ _

private theorem raw_evalCtx_not_mem_keyNames_of_forall
    {Psi : EvalCtx} {y : VName}
    (hy : ∀ b', (y, b') ∉ Psi) : y ∉ Psi.keyNames := by
  rw [raw_evalCtx_mem_keyNames]
  rintro ⟨b, hb⟩
  exact hy b hb

private theorem raw_valEnv_update_comm
    (rho : ValEnvSem) {x y : VName} (h : x ≠ y)
    (a b : ValValSem) :
    (rho.update x a).update y b = (rho.update y b).update x a := by
  funext z
  simp only [ValEnvSem.update]
  by_cases hzy : z = y
  · subst z
    simp [Ne.symm h]
  · simp [hzy]

private theorem raw_valEnv_update_update_same
    (rho : ValEnvSem) (y : VName) (a b : ValValSem) :
    (rho.update y a).update y b = rho.update y b := by
  funext z
  simp only [ValEnvSem.update]
  by_cases hzy : z = y <;> simp [hzy]

private theorem raw_valExpr_fv_var_subset_keyNames_extend
    {Psi : EvalCtx} {y : VName} {b0 : Basis} {tauV : ValTy}
    (hfv : ValTy.fv tauV ⊆ Psi.keyNames) :
    ValExpr.fv (.var y tauV) ⊆
      (Psi.extend y b0 (.var y tauV)).keyNames := by
  rw [EvalCtx.keyNames_extend_core]
  simp only [ValExpr.fv]
  exact Finset.insert_subset_insert _ hfv

private theorem raw_basis_fv_subset_of_openVar_body
    {b : Basis} {L A : Finset Name}
    (h : ∀ y, y ∉ L → ∀ z,
      z ∈ Basis.fv (Basis.openVar y b) → z = y ∨ z ∈ A) :
    Basis.fv b ⊆ A := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Basis.fv b)
  simp only [Finset.mem_union, not_or] at hy
  intro z hz
  rcases h y hy.1 z (Basis.fv_subset_openRec hz) with rfl | hzA
  · exact absurd hz hy.2
  · exact hzA

private theorem raw_basisValid_fv_subset_keys
    {Gamma : NLCtx} {b : Basis} (h : BasisValid Gamma b) :
    Basis.fv b ⊆ Gamma.keys := by
  induction h with
  | empty | one => simp [Basis.fv]
  | dual _ _ ih => simpa only [Basis.fv] using ih
  | dsum _ _ _ _ ih0 ih1 | tprod _ _ _ _ ih0 ih1 =>
      simpa only [Basis.fv] using Finset.union_subset ih0 ih1
  | proj_ker hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_ker hb0 hb1 hs0 hs1 htype)).some
  | proj_coker hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_coker hb0 hb1 hs0 hs1 htype)).some
  | proj_img hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_img hb0 hb1 hs0 hs1 htype)).some
  | proj_coimg hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid
          (Basis.BasisValid.proj_coimg hb0 hb1 hs0 hs1 htype)).some
  | image _ _ _ ih => simpa only [Basis.fv] using ih
  | terms hb hs hsv hterms _ ih =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih) ?_
      · exact SValid.fv_closure hsv.some
      · intro z hz
        obtain ⟨e, he, hze⟩ := Term.mem_fvList.mp hz
        have hzctx := HasType.fv_closure (hterms e he).some hze
        simpa only [Finmap.keys_empty, Finset.empty_union] using hzctx
  | frame L hb0 hbody ih0 ihbody =>
      simp only [Basis.fv]
      refine Finset.union_subset ih0 ?_
      apply raw_basis_fv_subset_of_openVar_body (L := L)
      intro y hy z hz
      have hzctx := ihbody y hy hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hzctx
      exact hzctx

private theorem raw_basisValid_not_mem_fv_of_not_mem
    {Gamma : NLCtx} {b : Basis} {x : Name}
    (h : BasisValid Gamma b) (hx : x ∉ Gamma) : x ∉ Basis.fv b :=
  fun hm => hx (Finmap.mem_keys.mp (raw_basisValid_fv_subset_keys h hm))

private theorem raw_asTypeCtx_submap_insert
    (Gamma : NLCtx) (y : Name) (tau : Ty) (hyGamma : y ∉ Gamma) :
    Graded.SubMap (Graded.asTypeCtx Gamma)
      (Graded.asTypeCtx (Finmap.insert y tau Gamma)) := by
  intro x source hx
  by_cases hxy : x = y
  · subst x
    simp only [Graded.asTypeCtx,
      Finmap.lookup_eq_none.mpr hyGamma] at hx
    contradiction
  · simpa only [Graded.asTypeCtx,
      Finmap.lookup_insert_of_ne _ hxy] using hx

private noncomputable def raw_svalid_weakenInsert
    {Gamma : NLCtx} {s : Space}
    (y : Name) (tau : Ty) (hyGamma : y ∉ Gamma) (h : SValid Gamma s) :
    SValid (Finmap.insert y tau Gamma) s :=
  Graded.svalidBwd (Graded.gsvalid_wk (Graded.svalidBridge h)
    (raw_asTypeCtx_submap_insert Gamma y tau hyGamma))
    (by exact fun _ _ h => h)

private noncomputable def raw_tvalid_weakenInsert
    {Gamma : NLCtx} {t : Ty} {k : Kind}
    (y : Name) (tau : Ty) (hyGamma : y ∉ Gamma) (h : TValid Gamma t k) :
    TValid (Finmap.insert y tau Gamma) t k :=
  Graded.tvalidBwd (Graded.gtvalid_wk (Graded.tvalidBridge h)
    (raw_asTypeCtx_submap_insert Gamma y tau hyGamma))
    (by exact fun _ _ h => h)

private theorem raw_basisValid_weakenInsert
    {Gamma : NLCtx} {b : Basis} {y : Name} {tau : Ty}
    (hyGamma : y ∉ Gamma) (hyb : y ∉ Basis.fv b)
    (hb : BasisValid Gamma b) :
    BasisValid (Finmap.insert y tau Gamma) b := by
  induction hb generalizing y tau with
  | empty => exact .empty
  | one => exact .one
  | dual hb htof ih =>
      exact .dual (ih hyGamma (by simpa [Basis.fv] using hyb)) htof
  | dsum hb0 hb1 htof0 htof1 ih0 ih1 =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hyb
      exact .dsum (ih0 hyGamma hyb.1) (ih1 hyGamma hyb.2) htof0 htof1
  | tprod hb0 hb1 htof0 htof1 ih0 ih1 =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hyb
      exact .tprod (ih0 hyGamma hyb.1) (ih1 hyGamma hyb.2) htof0 htof1
  | proj_ker hb0 hb1 hsof0 hsof1 hterm ih0 ih1 =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hyb
      refine .proj_ker (ih0 hyGamma hyb.1.2) (ih1 hyGamma hyb.2)
        hsof0 hsof1 ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyGamma
        hterm.some⟩
  | proj_coker hb0 hb1 hsof0 hsof1 hterm ih0 ih1 =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hyb
      refine .proj_coker (ih0 hyGamma hyb.1.2) (ih1 hyGamma hyb.2)
        hsof0 hsof1 ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyGamma
        hterm.some⟩
  | proj_img hb0 hb1 hsof0 hsof1 hterm ih0 ih1 =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hyb
      refine .proj_img (ih0 hyGamma hyb.1.2) (ih1 hyGamma hyb.2)
        hsof0 hsof1 ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyGamma
        hterm.some⟩
  | proj_coimg hb0 hb1 hsof0 hsof1 hterm ih0 ih1 =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hyb
      refine .proj_coimg (ih0 hyGamma hyb.1.2) (ih1 hyGamma hyb.2)
        hsof0 hsof1 ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyGamma
        hterm.some⟩
  | image hb hsof hterm ih =>
      simp only [Basis.fv] at hyb
      refine .image (ih hyGamma hyb) hsof ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyGamma
        hterm.some⟩
  | terms hb htof hsv hes hne ih =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hyb
      refine .terms (ih hyGamma hyb.1.2) htof
        ⟨raw_svalid_weakenInsert y tau hyGamma hsv.some⟩ ?_ hne
      intro e he
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyGamma
        (hes e he).some⟩
  | @frame Gamma b0 b1 L hb0 hbody ih0 ihbody =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hyb
      refine .frame (L ∪ {y}) (ih0 hyGamma hyb.1) ?_
      intro z hz
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
      have hzy : z ≠ y := hz.2
      have hyz : y ≠ z := Ne.symm hzy
      have hyGammaz : y ∉ Finmap.insert z (Basis.tof b0) Gamma := by
        simp [Finmap.mem_insert, hyGamma, hyz]
      have hyopen : y ∉ Basis.fv (Basis.openVar z b1) := by
        intro hm
        have hs := Basis.fv_openRec_subset 0 (.var z) b1 hm
        simp only [Finset.mem_union, Term.fv,
          Finset.mem_singleton] at hs
        exact hs.elim hyb.2 hyz
      have hw := ihbody z hz.1 (tau := tau) hyGammaz hyopen
      have hcomm :
          Finmap.insert z (Basis.tof b0) (Finmap.insert y tau Gamma) =
            Finmap.insert y tau (Finmap.insert z (Basis.tof b0) Gamma) := by
        apply Finmap.ext_lookup
        intro w
        by_cases hwz : w = z
        · subst w
          simp [Finmap.lookup_insert, hzy]
        · by_cases hwy : w = y
          · subst w
            simp [Finmap.lookup_insert, hyz]
          · simp [Finmap.lookup_insert_of_ne, hwz, hwy]
      rw [hcomm]
      exact hw

private theorem raw_basisValid_mono_aux {b : Basis} (S : Finset Name) :
    ∀ (Gamma0 Gamma : NLCtx), BasisValid Gamma0 b →
      NLCtxIncl Gamma0 Gamma →
      (∀ x, x ∈ Gamma → x ∉ Gamma0 → x ∈ S) → BasisValid Gamma b := by
  induction S using Finset.induction_on with
  | empty =>
      intro Gamma0 Gamma hb hle hS
      have hGamma : Gamma = Gamma0 := by
        apply Finmap.ext_lookup
        intro x
        by_cases hx : x ∈ Gamma0
        · obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp hx
          rw [htau, hle x tau htau]
        · have hx' : x ∉ Gamma := fun h =>
            absurd (hS x h hx) (Finset.notMem_empty x)
          rw [Finmap.lookup_eq_none.mpr hx',
            Finmap.lookup_eq_none.mpr hx]
      rw [hGamma]
      exact hb
  | insert y S hyS ih =>
      intro Gamma0 Gamma hb hle hS
      by_cases hy : y ∈ Gamma ∧ y ∉ Gamma0
      · obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp hy.1
        have hErase : BasisValid (Gamma.erase y) b := by
          refine ih Gamma0 (Gamma.erase y) hb ?_ ?_
          · intro x tau' hx
            have hxy : x ≠ y := fun h =>
              hy.2 (h ▸ Finmap.mem_of_lookup_eq_some hx)
            rw [Finmap.lookup_erase_ne hxy]
            exact hle x tau' hx
          · intro x hx hx0
            obtain ⟨hxy, hxGamma⟩ := Finmap.mem_erase.mp hx
            rcases Finset.mem_insert.mp (hS x hxGamma hx0) with h | h
            · exact absurd h hxy
            · exact h
        have hyErase : y ∉ Gamma.erase y := fun h =>
          (Finmap.mem_erase.mp h).1 rfl
        have hInsert := raw_basisValid_weakenInsert (tau := tau) hyErase
          (raw_basisValid_not_mem_fv_of_not_mem hb hy.2) hErase
        have hEq : Finmap.insert y tau (Gamma.erase y) = Gamma := by
          apply Finmap.ext_lookup
          intro z
          by_cases hz : z = y
          · subst z
            rw [Finmap.lookup_insert, htau]
          · rw [Finmap.lookup_insert_of_ne _ hz,
              Finmap.lookup_erase_ne hz]
        rw [hEq] at hInsert
        exact hInsert
      · refine ih Gamma0 Gamma hb hle ?_
        intro x hx hx0
        rcases Finset.mem_insert.mp (hS x hx hx0) with h | h
        · exact absurd ⟨h ▸ hx, h ▸ hx0⟩ hy
        · exact h

private theorem raw_basisValid_mono_of_nlCtxIncl
    {b : Basis} {Gamma0 Gamma : NLCtx}
    (hb : BasisValid Gamma0 b) (hle : NLCtxIncl Gamma0 Gamma) :
    BasisValid Gamma b := by
  apply raw_basisValid_mono_aux (Gamma.keys \ Gamma0.keys)
    Gamma0 Gamma hb hle
  intro x hx hx0
  exact Finset.mem_sdiff.mpr
    ⟨Finmap.mem_keys.mpr hx,
      fun hx' => hx0 (Finmap.mem_keys.mp hx')⟩

/-- `BasisValid` weakening along the nonlinear-context inclusion used by the
raw adequacy motives. -/
theorem raw_basisValid_mono
    {b : Basis} {Gamma0 Gamma : NLCtx}
    (hb : BasisValid Gamma0 b) (hle : NLCtxIncl Gamma0 Gamma) :
    BasisValid Gamma b :=
  raw_basisValid_mono_of_nlCtxIncl hb hle

/-! ## Telescope and creation-prefix record -/

/-- The space inferer is relevant only when a stored value type is base-kind.
At `.space sv` it must recover exactly `sv`; at dependent-function type there
is no base space to compare, so the condition is deliberately vacuous. -/
def ValExpr.InferSpaceMatchesBase (v : ValExpr) : ValTy -> Prop
  | .space sv => ValExpr.inferSpaceCtx [] v = sv
  | .piTy _ _ => True

/-- A full inference-space equality implies the base-only condition.  This is
the compatibility lemma for producers that already establish the stronger fact. -/
theorem ValExpr.InferSpaceMatchesBase.ofSpaceOfEq
    {v : ValExpr} {tauV : ValTy}
    (h : ValExpr.inferSpaceCtx [] v = ValTy.spaceOf tauV) :
    ValExpr.InferSpaceMatchesBase v tauV := by
  cases tauV <;> simp_all [ValExpr.InferSpaceMatchesBase, ValTy.spaceOf]

/-- Eliminate the base-only condition after the value type is known to be a
space. -/
theorem ValExpr.InferSpaceMatchesBase.spaceEq
    {v : ValExpr} {sv : ValSpace}
    (h : ValExpr.InferSpaceMatchesBase v (.space sv)) :
    ValExpr.inferSpaceCtx [] v = sv :=
  h

/-- Consistency of the source, evaluator, compiled-type, and denotational
environments using exact raw agreement. -/
inductive RawConsistent (orc : FFSOracleSem) :
    LCtx -> NLCtx -> EvalCtx -> ValCtx -> DEnv -> ValEnvSem -> Prop
  | empty {rho : ValEnvSem} : RawConsistent orc ∅ ∅ ∅ ∅ ⟨∅⟩ rho
  | extend_lin {Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV}
      (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
      (hx : x ∉ Delta /\ x ∉ Gamma)
      (htof : Basis.tof b = .space s)
      (hb : BasisValid Gamma b)
      (hTy : ValTy.EvalT Psi (Basis.tof b) tauV)
      (hinfer : ValExpr.inferType v = tauV)
      (hinferSpaceBase : ValExpr.InferSpaceMatchesBase v tauV)
      (hfvv : ValExpr.fv v ⊆ (Psi.extend x b v).keyNames)
      (hlc : ValExpr.lc v)
      (hnr : x ∉ ValExpr.fv v \/ exists tau, v = .var x tau)
      (hxs : xs.matchesShape (denotTy sigma (Basis.tof b)))
      (hden : denotValB_semS orc rho [] [] v = .ok yV)
      (hagree : RawAgree orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b) xs yV)
      (hdims : RawAgreeDimsAt orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b)) :
      RawConsistent orc (Finmap.insert x s Delta) Gamma
        (Psi.extend x b v) (Finmap.insert x tauV GammaV)
        (sigma.bind x xs) (rho.update x yV)
  | extend_nl {Delta Gamma Psi GammaV sigma rho x b v tauV xs yV}
      (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
      (hx : x ∉ Delta /\ x ∉ Gamma)
      (hb : BasisValid Gamma b)
      (hTy : ValTy.EvalT Psi (Basis.tof b) tauV)
      (hinfer : ValExpr.inferType v = tauV)
      (hinferSpaceBase : ValExpr.InferSpaceMatchesBase v tauV)
      (hfvv : ValExpr.fv v ⊆ (Psi.extend x b v).keyNames)
      (hlc : ValExpr.lc v)
      (hnr : x ∉ ValExpr.fv v \/ exists tau, v = .var x tau)
      (hxs : xs.matchesShape (denotTy sigma (Basis.tof b)))
      (hden : denotValB_semS orc rho [] [] v = .ok yV)
      (hagree : RawAgree orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b) xs yV)
      (hdims : RawAgreeDimsAt orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b))
      (hcreation : V2.EvalEntryCreation Psi x b v) :
      RawConsistent orc Delta (Finmap.insert x (Basis.tof b) Gamma)
        (Psi.extend x b v) (Finmap.insert x tauV GammaV)
        (sigma.bind x xs) (rho.update x yV)
  /-- Add another evaluator representation of an existing source binding. -/
  | extend_rep {Delta Gamma Psi GammaV sigma rho x b v tauV xs yV}
      (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
      (hkey : (x, b) ∉ Psi)
      (hsource : V2.SourceEntryLinked Delta Gamma x b)
      (hsigma : sigma.vars.lookup x = some xs)
      (hb : BasisValid Gamma b)
      (hTy : ValTy.EvalT Psi (Basis.tof b) tauV)
      (hinfer : ValExpr.inferType v = tauV)
      (hinferSpaceBase : ValExpr.InferSpaceMatchesBase v tauV)
      (hfvv : ValExpr.fv v ⊆ (Psi.extend x b v).keyNames)
      (hlc : ValExpr.lc v)
      (hxs : xs.matchesShape (denotTy sigma (Basis.tof b)))
      (hden : denotValB_semS orc rho [] [] v = .ok yV)
      (hagree : RawAgree orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b) xs yV)
      (hdims : RawAgreeDimsAt orc sigma rho [] [] []
        (Basis.tof b) tauV (denotBasis sigma b))
      (hcreation : V2.EvalEntryCreation Psi x b v) :
      RawConsistent orc Delta Gamma (Psi.extend x b v) GammaV sigma rho

/-- Canonical environment consistency. -/
abbrev UntypedConsistent := RawConsistent

/-- Every evaluator name was introduced at the same step as a source name. -/
theorem RawConsistent.evalName_mem_source {orc : FFSOracleSem} :
    forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
      {sigma : DEnv} {rho : ValEnvSem} {z : VName},
      RawConsistent orc Delta Gamma Psi GammaV sigma rho ->
      (exists b, (z, b) ∈ Psi) -> z ∈ Delta \/ z ∈ Gamma := by
  intro Delta Gamma Psi GammaV sigma rho z h
  induction h with
  | empty =>
      rintro ⟨b, hmem⟩
      exact absurd hmem Finmap.notMem_empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden _hagree
      hdims ih =>
      rintro ⟨b', hmem⟩
      rcases raw_evalCtx_mem_extend.mp hmem with hnew | hold
      · have hzx : z = x := hnew.1
        subst z
        exact Or.inl (Finmap.mem_insert.mpr (Or.inl rfl))
      · rcases ih ⟨b', hold⟩ with hDelta | hGamma
        · exact Or.inl (Finmap.mem_insert.mpr (Or.inr hDelta))
        · exact Or.inr hGamma
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden hagree hdims
      hanchor ih =>
      rintro ⟨b', hmem⟩
      rcases raw_evalCtx_mem_extend.mp hmem with hnew | hold
      · have hzx : z = x := hnew.1
        subst z
        exact Or.inr (Finmap.mem_insert.mpr (Or.inl rfl))
      · rcases ih ⟨b', hold⟩ with hDelta | hGamma
        · exact Or.inl hDelta
        · exact Or.inr (Finmap.mem_insert.mpr (Or.inr hGamma))
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      rintro ⟨b', hmem⟩
      rcases raw_evalCtx_mem_extend.mp hmem with hnew | hold
      · have hzx : z = x := hnew.1
        subst z
        rcases hsource with ⟨s, hs, _⟩ | hGamma
        · exact Or.inl (Finmap.mem_of_lookup_eq_some hs)
        · exact Or.inr (Finmap.mem_of_lookup_eq_some hGamma)
      · exact ih ⟨b', hold⟩

/-- Source-name freshness therefore implies evaluator-key freshness. -/
theorem RawConsistent.freshEvalName {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem} {x : VName}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (hx : x ∉ Delta /\ x ∉ Gamma) : forall b, (x, b) ∉ Psi := by
  intro b hmem
  rcases h.evalName_mem_source ⟨b, hmem⟩ with hDelta | hGamma
  · exact hx.1 hDelta
  · exact hx.2 hGamma

/-- Lockstep creation places every nonlinear source name in the evaluator
context. -/
theorem RawConsistent.nlKeys_subset_keyNames {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    Gamma.keys ⊆ Psi.keyNames := by
  induction h with
  | empty => simp
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden _hagree
      hdims ih =>
      exact ih.trans (raw_evalCtx_keyNames_subset_extend Psi x b v)
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden hagree hdims
      hanchor ih =>
      intro z hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hz
      rw [EvalCtx.keyNames_extend_core, Finset.mem_insert]
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · exact Or.inr (ih (Finmap.mem_keys.mpr hz))
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      exact ih.trans (raw_evalCtx_keyNames_subset_extend Psi x b v)

/-- All stored evaluator values mention only names already present in the
current telescope.  This is derived once from the per-entry value-scoping
premise and reused to derive realized-type scoping. -/
theorem RawConsistent.evalCtxScoped {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    EvalCtxScoped Psi := by
  induction h with
  | empty => exact EvalCtxScoped.empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden _hagree
      hdims ih =>
      exact ih.extend (by simpa only [EvalCtx.keyNames_extend_core] using hfvv)
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden hagree hdims
      hanchor ih =>
      exact ih.extend (by simpa only [EvalCtx.keyNames_extend_core] using hfvv)
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      exact ih.extend (by simpa only [EvalCtx.keyNames_extend_core] using hfvv)

/-- Basis free-variable closure is a theorem of consistency, not additional
entry data. -/
theorem RawConsistent.basisFvPrefix {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem} {b : Basis}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (hb : BasisValid Gamma b) : Basis.fv b ⊆ Psi.keyNames :=
  (raw_basisValid_fv_subset_keys hb).trans h.nlKeys_subset_keyNames

private theorem raw_frameAnchor_after_insert
    {Psi : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
    (hkey : (x, b) ∉ Psi)
    (hanchor : V2.EvalFrameAnchored Psi b v) :
    forall c0 c1 tauV0 tauV1 body,
      b = .frame c0 c1 -> v = .vlam tauV0 tauV1 body ->
      exists L : Finset VName, forall z, z ∉ L ->
        ValTy.EvalT
          ((Psi.extend x b v).extend z c0 (.var z tauV0))
          (Ty.openVar z (Basis.tof c1))
          (ValTy.openVar z tauV0 tauV1) := by
  intro c0 c1 tauV0 tauV1 body hb hv
  obtain ⟨L, hL⟩ := hanchor c0 c1 tauV0 tauV1 body hb hv
  refine ⟨insert x L, fun z hz => ?_⟩
  rw [Finset.mem_insert, not_or] at hz
  have hne : (x, b) ≠ (z, c0) :=
    fun h => hz.1 (congrArg Prod.fst h).symm
  have hfresh : (x, b) ∉ Psi.extend z c0 (.var z tauV0) := by
    rw [EvalCtx.extend]
    exact fun h => (Finmap.mem_insert.mp h).elim hne hkey
  exact evalctx_extend_comm hne ▸ evalT_wk (hL z hz.2) hfresh

/-- Raw consistency contains precisely the entry-local facts needed for the
operational evaluator context.  Type free-variable closure is derived during
this induction from each entry's `EvalT`; it is not stored as a certificate. -/
theorem RawConsistent.evalCtxValidPlus {orc : FFSOracleSem} :
    forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
      {sigma : DEnv} {rho : ValEnvSem},
      RawConsistent orc Delta Gamma Psi GammaV sigma rho ->
      V2.EvalCtxValidPlus Psi := by
  intro Delta Gamma Psi GammaV sigma rho h
  induction h with
  | empty =>
      intro x b v hlookup
      simp [EvalCtx.lookup] at hlookup
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden
      hagree hdims ih =>
      apply V2.evalCtxValidPlus_extend_value ih
        (hc.freshEvalName hx b) hfvv
      · rw [hinfer]
        exact hTy
      · rw [hinfer]
        exact V2.evalT_fv hTy ih
      · exact hlc
      · intro c0 c1 tauV0 tauV1 body hbFrame _hv
        subst b
        exact nomatch htof
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden
      hagree hdims hanchor ih =>
      apply V2.evalCtxValidPlus_extend_value ih
        (hc.freshEvalName hx b) hfvv
      · rw [hinfer]
        exact hTy
      · rw [hinfer]
        exact V2.evalT_fv hTy ih
      · exact hlc
      · exact raw_frameAnchor_after_insert (hc.freshEvalName hx b)
          hanchor.frameAnchored
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      apply V2.evalCtxValidPlus_extend_value ih hkey hfvv
      · rw [hinfer]
        exact hTy
      · rw [hinfer]
        exact V2.evalT_fv hTy ih
      · exact hlc
      · exact raw_frameAnchor_after_insert hkey hanchor.frameAnchored

/-- A realized value type is scoped by its `EvalT` derivation and the
operational validity derived from the creation prefix. -/
theorem RawConsistent.typeFvPrefix {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem} {tau : Ty} {tauV : ValTy}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (hTy : ValTy.EvalT Psi tau tauV) : ValTy.fv tauV ⊆ Psi.keyNames :=
  V2.evalT_fv hTy h.evalCtxValidPlus

/-- Facts retained unchanged from the creation prefix of one stored entry. -/
structure RawConsistent.Stored (orc : FFSOracleSem)
    (x : VName) (b : Basis) (v : ValExpr) (tauV : ValTy)
    (xs : DVal) (yV : ValValSem)
    (Delta0 : LCtx) (Gamma0 : NLCtx) (Psi0 : EvalCtx) (GammaV0 : ValCtx)
    (sigma0 : DEnv) (rho0 : ValEnvSem) : Prop where
  prefixConsistent : RawConsistent orc Delta0 Gamma0 Psi0 GammaV0 sigma0 rho0
  hb : BasisValid Gamma0 b
  hTy : ValTy.EvalT Psi0 (Basis.tof b) tauV
  hinfer : ValExpr.inferType v = tauV
  hinferSpaceBase : ValExpr.InferSpaceMatchesBase v tauV
  hfvv : ValExpr.fv v ⊆ (Psi0.extend x b v).keyNames
  hlc : ValExpr.lc v
  hxs : xs.matchesShape (denotTy sigma0 (Basis.tof b))
  hden : denotValB_semS orc rho0 [] [] v = .ok yV
  hagree : RawAgree orc sigma0 rho0 [] [] []
    (Basis.tof b) tauV (denotBasis sigma0 b) xs yV
  hdims : RawAgreeDimsAt orc sigma0 rho0 [] [] []
    (Basis.tof b) tauV (denotBasis sigma0 b)

theorem RawConsistent.Stored.hfvb
    (h : RawConsistent.Stored orc x b v tauV xs yV
      Delta0 Gamma0 Psi0 GammaV0 sigma0 rho0) :
    Basis.fv b ⊆ Psi0.keyNames :=
  h.prefixConsistent.basisFvPrefix h.hb

theorem RawConsistent.Stored.hfvTy
    (h : RawConsistent.Stored orc x b v tauV xs yV
      Delta0 Gamma0 Psi0 GammaV0 sigma0 rho0) :
    ValTy.fv tauV ⊆ Psi0.keyNames :=
  h.prefixConsistent.typeFvPrefix h.hTy

/-- Every basis stored by a raw-consistency history is hereditarily shaped
like its source type.  The proof follows creation history only; in
particular, it is insensitive to whether a stored value is an ordinary
prefix-closed value or the explicitly permitted self placeholder. -/
theorem RawConsistent.storedWF {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    V2.StoredWF Psi := by
  induction h with
  | empty =>
      intro x b hmem
      exact absurd hmem Finmap.notMem_empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      intro x' b' hmem
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with heq | hmem'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact hb.isTyBasis
      · exact ih x' b' hmem'
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      intro x' b' hmem
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with heq | hmem'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact hb.isTyBasis
      · exact ih x' b' hmem'
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      intro x' b' hmem
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with heq | hmem'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact hb.isTyBasis
      · exact ih x' b' hmem'

/-! ## Exact creation-prefix lookup -/

/-- Lookup returns the entry's creation-prefix record unchanged, together
with its current source-value and source-typing projections.

The realized `tauV` and payload `yV` are deliberately entry-local.  A second
representation of the same source name may use a different realized shape and
different coordinates, so neither is identified with the name-indexed
`GammaV[x]` or `rho x`. -/
theorem RawConsistent.lookup {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    {x : VName} {b : Basis} (hmem : (x, b) ∈ Psi) :
    exists (v : ValExpr) (tauV : ValTy) (xs : DVal) (yV : ValValSem)
      (Delta0 : LCtx) (Gamma0 : NLCtx) (Psi0 : EvalCtx)
      (GammaV0 : ValCtx) (sigma0 : DEnv) (rho0 : ValEnvSem),
      RawConsistent.Stored orc x b v tauV xs yV
        Delta0 Gamma0 Psi0 GammaV0 sigma0 rho0 /\
      NLCtxIncl Gamma0 Gamma /\
      EvalCtx.lookup Psi (x, b) = some v /\
      sigma.vars.lookup x = some xs /\
      V2.SourceEntryLinked Delta Gamma x b := by
  induction h with
  | empty => exact absurd hmem Finmap.notMem_empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x' b' v' tauV' xs' s yV'
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      rcases raw_evalCtx_mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · refine ⟨v', tauV', xs', yV', Delta, Gamma, Psi, GammaV, sigma, rho,
          ⟨hc, hb, hTy, hinfer, hinferSpace, hfvv,
            hlc, hxs, hden, hagree, hdims⟩,
          NLCtxIncl.refl Gamma, ?_, ?_, ?_⟩
        · simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert]
        · simp [DEnv.bind, Finmap.lookup_insert]
        · exact Or.inl ⟨s, by simp [Finmap.lookup_insert], htof⟩
      · obtain ⟨v, tauV, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
          sigma0, rho0, hst, hGammaIncl, hPsi, hsigma, hctx⟩ := ih hmem'
        have hxx : x ≠ x' := fun e =>
          hc.freshEvalName hx b (e ▸ hmem')
        refine ⟨v, tauV, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
          sigma0, rho0, hst, hGammaIncl, ?_, ?_, ?_⟩
        · have hne : (x, b) ≠ (x', b') := fun e => hxx (Prod.mk.inj e).1
          simpa [EvalCtx.extend, EvalCtx.lookup,
            Finmap.lookup_insert_of_ne _ hne] using hPsi
        · simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hxx] using hsigma
        · rcases hctx with ⟨s', hs', htof'⟩ | hGamma
          · exact Or.inl ⟨s', by
              simpa [Finmap.lookup_insert_of_ne _ hxx] using hs', htof'⟩
          · exact Or.inr hGamma
  | @extend_nl Delta Gamma Psi GammaV sigma rho x' b' v' tauV' xs' yV'
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      rcases raw_evalCtx_mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · refine ⟨v', tauV', xs', yV', Delta, Gamma, Psi, GammaV, sigma, rho,
          ⟨hc, hb, hTy, hinfer, hinferSpace, hfvv,
            hlc, hxs, hden, hagree, hdims⟩,
          (NLCtxIncl.refl Gamma).insert_right hx.2 (Basis.tof b),
          ?_, ?_, ?_⟩
        · simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert]
        · simp [DEnv.bind, Finmap.lookup_insert]
        · exact Or.inr (by simp [Finmap.lookup_insert])
      · obtain ⟨v, tauV, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
          sigma0, rho0, hst, hGammaIncl, hPsi, hsigma, hctx⟩ := ih hmem'
        have hxx : x ≠ x' := fun e =>
          hc.freshEvalName hx b (e ▸ hmem')
        refine ⟨v, tauV, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
          sigma0, rho0, hst,
          hGammaIncl.insert_right hx.2 (Basis.tof b'),
          ?_, ?_, ?_⟩
        · have hne : (x, b) ≠ (x', b') := fun e => hxx (Prod.mk.inj e).1
          simpa [EvalCtx.extend, EvalCtx.lookup,
            Finmap.lookup_insert_of_ne _ hne] using hPsi
        · simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hxx] using hsigma
        · rcases hctx with ⟨s', hs', htof'⟩ | hGamma
          · exact Or.inl ⟨s', hs', htof'⟩
          · exact Or.inr (by
              simpa [Finmap.lookup_insert_of_ne _ hxx] using hGamma)
  | @extend_rep Delta Gamma Psi GammaV sigma rho x' b' v' tauV' xs' yV'
      hc hkey hsource hsigma' hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      rcases raw_evalCtx_mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · exact ⟨v', tauV', xs', yV', Delta, Gamma, Psi, GammaV, sigma, rho,
          ⟨hc, hb, hTy, hinfer, hinferSpace, hfvv,
            hlc, hxs, hden, hagree, hdims⟩,
          NLCtxIncl.refl Gamma,
          by simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert],
          hsigma', hsource⟩
      · obtain ⟨v, tauV, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
          sigma0, rho0, hst, hGammaIncl, hPsi, hsigma, hctx⟩ := ih hmem'
        refine ⟨v, tauV, xs, yV, Delta0, Gamma0, Psi0, GammaV0,
          sigma0, rho0, hst, hGammaIncl, ?_, hsigma, hctx⟩
        have hne : (x, b) ≠ (x', b') := fun e => hkey (e ▸ hmem')
        simpa [EvalCtx.extend, EvalCtx.lookup,
          Finmap.lookup_insert_of_ne _ hne] using hPsi

/-- A basis selected from a raw-consistent evaluator remains valid after any
later nonlinear-context extension which preserves the root bindings.

`RawConsistent.lookup` recovers the basis-validity proof at the entry's
creation prefix.  The telescope relates that prefix to its current nonlinear
context, and the caller-supplied inclusion relates the current context to the
local (for example, binder-extended) context. -/
theorem RawConsistent.lookup_basisValid_mono {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma Gamma' : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    {x : VName} {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (hGamma : NLCtxIncl Gamma Gamma') :
    BasisValid Gamma' b := by
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  obtain ⟨_v, _tauV, _xs, _yV, _Delta0, _Gamma0, _Psi0, _GammaV0,
      _sigma0, _rho0, hstored, hcreation, _⟩ := h.lookup hmem
  exact raw_basisValid_mono hstored.hb (hcreation.trans hGamma)

/-- Stored basis and value syntax remain scoped after later fresh telescope
extensions. -/
theorem RawConsistent.stored_fv {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    forall x b v, EvalCtx.lookup Psi (x, b) = some v ->
      Basis.fv b ⊆ Psi.keyNames /\ ValExpr.fv v ⊆ Psi.keyNames := by
  induction h with
  | empty => intro x b v hlookup; simp [EvalCtx.lookup] at hlookup
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      intro x' b' v' hlookup
      have hfvb := hc.basisFvPrefix hb
      have hsub := raw_evalCtx_keyNames_subset_extend Psi x b v
      by_cases hkey : (x', b') = (x, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
        rw [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert] at hlookup
        obtain rfl := Option.some.inj hlookup
        exact ⟨hfvb.trans hsub, hfvv⟩
      · rw [EvalCtx.lookup, EvalCtx.extend,
          Finmap.lookup_insert_of_ne _ hkey] at hlookup
        obtain ⟨hfvb', hfvv'⟩ := ih x' b' v' hlookup
        exact ⟨hfvb'.trans hsub, hfvv'.trans hsub⟩
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      intro x' b' v' hlookup
      have hfvb := hc.basisFvPrefix hb
      have hsub := raw_evalCtx_keyNames_subset_extend Psi x b v
      by_cases hkey' : (x', b') = (x, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey'
        rw [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert] at hlookup
        obtain rfl := Option.some.inj hlookup
        exact ⟨hfvb.trans hsub, hfvv⟩
      · rw [EvalCtx.lookup, EvalCtx.extend,
          Finmap.lookup_insert_of_ne _ hkey'] at hlookup
        obtain ⟨hfvb', hfvv'⟩ := ih x' b' v' hlookup
        exact ⟨hfvb'.trans hsub, hfvv'.trans hsub⟩
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      intro x' b' v' hlookup
      have hfvb := hc.basisFvPrefix hb
      have hsub := raw_evalCtx_keyNames_subset_extend Psi x b v
      by_cases hkey : (x', b') = (x, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
        rw [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert] at hlookup
        obtain rfl := Option.some.inj hlookup
        exact ⟨hfvb.trans hsub, hfvv⟩
      · rw [EvalCtx.lookup, EvalCtx.extend,
          Finmap.lookup_insert_of_ne _ hkey] at hlookup
        obtain ⟨hfvb', hfvv'⟩ := ih x' b' v' hlookup
        exact ⟨hfvb'.trans hsub, hfvv'.trans hsub⟩

/-! ## Transport of stored entries to the current world -/

/-- One fresh telescope extension transports raw agreement and exact-basis
dimensions at every kind, retaining the same raw runtime argument at Pi. -/
theorem raw_bind_update_of_fresh {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc)
    {sigma : DEnv} {rho : ValEnvSem} {b : Basis} {tauV : ValTy}
    {xs : DVal} {w0 : ValValSem} {y : VName}
    (hyb : y ∉ Basis.fv b) (hyTy : y ∉ ValTy.fv tauV)
    (ys : DVal) (w : ValValSem)
    (hagree : RawAgree orc sigma rho [] [] [] (Basis.tof b) tauV
      (denotBasis sigma b) xs w0)
    (hdims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof b) tauV (denotBasis sigma b)) :
    RawAgree orc (sigma.bind y ys) (rho.update y w) [] [] []
        (Basis.tof b) tauV (denotBasis (sigma.bind y ys) b) xs w0 /\
      RawAgreeDimsAt orc (sigma.bind y ys) (rho.update y w) [] [] []
        (Basis.tof b) tauV (denotBasis (sigma.bind y ys) b) := by
  have hySource : y ∉ Ty.fv (Basis.tof b) :=
    fun hm => hyb (Basis.fv_tof_subset b hm)
  have hsigmaBasis : (sigma.bind y ys).AgreeOn sigma (Basis.fv b) :=
    DEnv.AgreeOn.bind_left_of_not_mem hyb
  have hsigmaTy : (sigma.bind y ys).AgreeOn sigma (Ty.fv (Basis.tof b)) :=
    DEnv.AgreeOn.bind_left_of_not_mem hySource
  rw [denotBasis_agree b hsigmaBasis]
  refine ⟨?_, ?_⟩
  · rw [RawAgree.agreeOn (rho.update y w) (Basis.tof b) tauV [] [] []
      (denotBasis sigma b) xs w0 hsigmaTy]
    exact (RawAgree.update_of_not_mem_fv hirr sigma rho y w
      (Basis.tof b) tauV [] [] [] (denotBasis sigma b) xs w0
      (by simp [ValTyCtxFresh]) hyTy).mpr hagree
  · rw [RawAgreeDimsAt.agreeOn (rho.update y w) (Basis.tof b) tauV [] [] []
      (denotBasis sigma b) hsigmaTy]
    exact (RawAgreeDimsAt.update_of_not_mem_fv hirr sigma rho y w
      (Basis.tof b) tauV [] [] [] (denotBasis sigma b)
      (by simp [ValTyCtxFresh]) hyTy).mpr hdims

/-- A newly introduced source entry still denotes its entry-local payload after
the constructor installs that payload at the same source name. -/
private theorem raw_denot_after_self_update {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc) {rho : ValEnvSem} {x : VName}
    {v : ValExpr} {yV : ValValSem}
    (hnr : x ∉ ValExpr.fv v \/ exists tau, v = .var x tau)
    (hden : denotValB_semS orc rho [] [] v = .ok yV) :
    denotValB_semS orc (rho.update x yV) [] [] v = .ok yV := by
  rcases hnr with hnot | ⟨tau, rfl⟩
  · rw [denotValB_semS_update_of_not_mem_fv hirr rho x yV v
      [] [] hnot (by simp)]
    exact hden
  · simp only [denotValB_semS.eq_2, ValEnvSem.update_same]

/-- Every stored entry's exact, entry-local denotation, agreement, and
dimensions are available at the current telescope.  In particular the result
does not identify a representation's `tauV` or `yV` with the canonical
name-level entries in `GammaV` or `rho`. -/
theorem RawConsistent.stored_raw_current {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    {x : VName} {b : Basis} (hmem : (x, b) ∈ Psi) :
    exists (v : ValExpr) (tauV : ValTy) (xs : DVal) (yV : ValValSem)
      (Gamma0 : NLCtx) (Psi0 : EvalCtx),
      EvalCtx.lookup Psi (x, b) = some v /\
      sigma.vars.lookup x = some xs /\
      ValTy.EvalT Psi0 (Basis.tof b) tauV /\
      ValExpr.InferSpaceMatchesBase v tauV /\
      Basis.fv b ⊆ Psi.keyNames /\
      ValTy.fv tauV ⊆ Psi.keyNames /\
      denotValB_semS orc rho [] [] v = .ok yV /\
      RawAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) xs yV /\
      RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) := by
  induction h with
  | empty => exact absurd hmem Finmap.notMem_empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x' b' v' tauV' xs' s yV'
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      have hfvb := hc.basisFvPrefix hb
      have hfvTy := hc.typeFvPrefix hTy
      have hxKey : x' ∉ Psi.keyNames :=
        raw_evalCtx_not_mem_keyNames_of_forall (hc.freshEvalName hx)
      have hsub := raw_evalCtx_keyNames_subset_extend Psi x' b' v'
      rcases raw_evalCtx_mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · obtain ⟨hagree', hdims'⟩ := raw_bind_update_of_fresh hirr
          (fun hm => hxKey (hfvb hm)) (fun hm => hxKey (hfvTy hm))
          xs' yV' hagree hdims
        exact ⟨v', tauV', xs', yV', Gamma, Psi,
          by simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert],
          by simp [DEnv.bind, Finmap.lookup_insert], hTy, hinferSpace,
          hfvb.trans hsub, hfvTy.trans hsub,
          raw_denot_after_self_update hirr hnr hden,
          hagree', hdims'⟩
      · obtain ⟨v, tauV, xs, yV, Gamma0, Psi0, hPsi, hsigma,
          hsty, hinfer0, hfvb0, hfvTy0, hden0, hagree0, hdims0⟩ := ih hmem'
        have hxx : x ≠ x' := fun e =>
          hc.freshEvalName hx b (e ▸ hmem')
        obtain ⟨hagree', hdims'⟩ := raw_bind_update_of_fresh hirr
          (fun hm => hxKey (hfvb0 hm)) (fun hm => hxKey (hfvTy0 hm))
          xs' yV' hagree0 hdims0
        have hne : (x, b) ≠ (x', b') := fun e => hxx (Prod.mk.inj e).1
        have hfvv0 : ValExpr.fv v ⊆ Psi.keyNames :=
          (hc.stored_fv x b v hPsi).2
        refine ⟨v, tauV, xs, yV, Gamma0, Psi0,
          by simpa [EvalCtx.extend, EvalCtx.lookup,
            Finmap.lookup_insert_of_ne _ hne] using hPsi,
          by simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hxx] using hsigma,
          hsty, hinfer0, hfvb0.trans hsub, hfvTy0.trans hsub, ?_,
          hagree', hdims'⟩
        rw [denotValB_semS_update_of_not_mem_fv hirr rho x' yV' v [] []
          (fun hm => hxKey (hfvv0 hm))
          (by simp)]
        exact hden0
  | @extend_nl Delta Gamma Psi GammaV sigma rho x' b' v' tauV' xs' yV'
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      have hfvb := hc.basisFvPrefix hb
      have hfvTy := hc.typeFvPrefix hTy
      have hxKey : x' ∉ Psi.keyNames :=
        raw_evalCtx_not_mem_keyNames_of_forall (hc.freshEvalName hx)
      have hsub := raw_evalCtx_keyNames_subset_extend Psi x' b' v'
      rcases raw_evalCtx_mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · obtain ⟨hagree', hdims'⟩ := raw_bind_update_of_fresh hirr
          (fun hm => hxKey (hfvb hm)) (fun hm => hxKey (hfvTy hm))
          xs' yV' hagree hdims
        exact ⟨v', tauV', xs', yV', Gamma, Psi,
          by simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert],
          by simp [DEnv.bind, Finmap.lookup_insert], hTy, hinferSpace,
          hfvb.trans hsub, hfvTy.trans hsub,
          raw_denot_after_self_update hirr hnr hden,
          hagree', hdims'⟩
      · obtain ⟨v, tauV, xs, yV, Gamma0, Psi0, hPsi, hsigma,
          hsty, hinfer0, hfvb0, hfvTy0, hden0, hagree0, hdims0⟩ := ih hmem'
        have hxx : x ≠ x' := fun e =>
          hc.freshEvalName hx b (e ▸ hmem')
        obtain ⟨hagree', hdims'⟩ := raw_bind_update_of_fresh hirr
          (fun hm => hxKey (hfvb0 hm)) (fun hm => hxKey (hfvTy0 hm))
          xs' yV' hagree0 hdims0
        have hne : (x, b) ≠ (x', b') := fun e => hxx (Prod.mk.inj e).1
        have hfvv0 : ValExpr.fv v ⊆ Psi.keyNames :=
          (hc.stored_fv x b v hPsi).2
        refine ⟨v, tauV, xs, yV, Gamma0, Psi0,
          by simpa [EvalCtx.extend, EvalCtx.lookup,
            Finmap.lookup_insert_of_ne _ hne] using hPsi,
          by simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hxx] using hsigma,
          hsty, hinfer0, hfvb0.trans hsub, hfvTy0.trans hsub, ?_,
          hagree', hdims'⟩
        rw [denotValB_semS_update_of_not_mem_fv hirr rho x' yV' v [] []
          (fun hm => hxKey (hfvv0 hm))
          (by simp)]
        exact hden0
  | @extend_rep Delta Gamma Psi GammaV sigma rho x' b' v' tauV' xs' yV'
      hc hkey hsource hsigma' hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      have hfvb := hc.basisFvPrefix hb
      have hfvTy := hc.typeFvPrefix hTy
      have hsub := raw_evalCtx_keyNames_subset_extend Psi x' b' v'
      rcases raw_evalCtx_mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · exact ⟨v', tauV', xs', yV', Gamma, Psi,
          by simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert],
          hsigma', hTy, hinferSpace, hfvb.trans hsub, hfvTy.trans hsub,
          hden, hagree, hdims⟩
      · obtain ⟨v, tauV, xs, yV, Gamma0, Psi0, hPsi, hsigma,
          hsty, hinfer0, hfvb0, hfvTy0, hden0, hagree0, hdims0⟩ := ih hmem'
        have hne : (x, b) ≠ (x', b') := fun e => hkey (e ▸ hmem')
        exact ⟨v, tauV, xs, yV, Gamma0, Psi0,
          by simpa [EvalCtx.extend, EvalCtx.lookup,
            Finmap.lookup_insert_of_ne _ hne] using hPsi,
          hsigma, hsty, hinfer0, hfvb0.trans hsub, hfvTy0.trans hsub,
          hden0, hagree0, hdims0⟩

/-! ## Current evaluator result -/

/-- Every stored evaluator expression has an entry-local result in the current
value environment. -/
theorem RawConsistent.denot_stored_exists {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    {x : VName} {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v) :
    exists yV, denotValB_semS orc rho [] [] v = .ok yV := by
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  obtain ⟨v', _tauV, _xs, yV, _Gamma0, _Psi0, hlookup', _hsigma,
      _hTy, _hinfer, _hfvb, _hfvTy, hden, _hagree, _hdims⟩ :=
    h.stored_raw_current hirr hmem
  have hv : v' = v := Option.some.inj (hlookup'.symm.trans hlookup)
  subst hv
  exact ⟨yV, hden⟩

/-- Exact current-world conclusion used by variable arms. -/
theorem RawConsistent.lookup_current_result {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    {x : VName} {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v) :
    exists (tauV : ValTy) (xs : DVal) (Gamma0 : NLCtx) (Psi0 : EvalCtx),
      sigma.vars.lookup x = some xs /\
      ValTy.EvalT Psi0 (Basis.tof b) tauV /\
      ValExpr.InferSpaceMatchesBase v tauV /\
      RawResultAgree orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) (denotTerm sigma (.var x))
        (denotValB_semS orc rho [] [] v) /\
      RawAgreeDimsAt orc sigma rho [] [] [] (Basis.tof b) tauV
        (denotBasis sigma b) := by
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  obtain ⟨v', tauV, xs, yV, Gamma0, Psi0, hlookup', hsigma,
      hsty, hinfer, hfvb, hfvTy, hden, hagree, hdims⟩ :=
    h.stored_raw_current hirr hmem
  have hv : v' = v := Option.some.inj (hlookup'.symm.trans hlookup)
  subst hv
  refine ⟨tauV, xs, Gamma0, Psi0, hsigma, hsty, hinfer, ?_, hdims⟩
  refine ⟨yV, hden, ?_⟩
  simpa [denotTerm, denotTermAux, hsigma] using hagree

/-! ## Structural projections -/

/-- Every nonlinear source binding has an evaluator-context key. -/
theorem RawConsistent.nl_mem_to_eval {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    forall x, x ∈ Gamma -> exists b, (x, b) ∈ Psi := by
  induction h with
  | empty => intro x hx; exact absurd hx Finmap.notMem_empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      intro z hz
      obtain ⟨bz, hbz⟩ := ih z hz
      exact ⟨bz, raw_evalCtx_mem_extend.mpr (Or.inr hbz)⟩
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      intro z hz
      rcases Finmap.mem_insert.mp hz with rfl | hz
      · exact ⟨b, raw_evalCtx_mem_extend.mpr (Or.inl ⟨rfl, rfl⟩)⟩
      · obtain ⟨bz, hbz⟩ := ih z hz
        exact ⟨bz, raw_evalCtx_mem_extend.mpr (Or.inr hbz)⟩
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      intro z hz
      obtain ⟨bz, hbz⟩ := ih z hz
      exact ⟨bz, raw_evalCtx_mem_extend.mpr (Or.inr hbz)⟩

/-- All stored evaluator values are locally closed. -/
theorem RawConsistent.evalCtxLc {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    EvalCtxLc Psi := by
  induction h with
  | empty => intro k v hlookup; simp [EvalCtx.lookup] at hlookup
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      exact ih.extend hlc
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      exact ih.extend hlc
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      exact ih.extend hlc

/-- The nonlinear source context of a raw telescope is well formed. -/
theorem RawConsistent.ctxWF_nl {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    CtxWF ∅ Gamma := by
  induction h with
  | empty =>
      exact ⟨fun x hx => absurd hx Finmap.notMem_empty,
        fun x s hx => absurd hx (by simp),
        fun x tau hx => absurd hx (by simp)⟩
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      exact ih
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      exact ih.insert_nl Finmap.notMem_empty hx.2
        ((Basis.fv_tof_subset b).trans (raw_basisValid_fv_subset_keys hb))
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      exact ih

/-- The nonlinear source environment agrees with the source context. -/
theorem RawConsistent.envWF_nl {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    EnvWF sigma ∅ Gamma := by
  induction h with
  | empty =>
      exact ⟨fun x s hx => absurd hx (by simp),
        fun x tau hx => absurd hx (by simp)⟩
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      refine ⟨fun z s hz => absurd hz (by simp), fun z tau hz => ?_⟩
      obtain ⟨value, hlookup, hshape⟩ := ih.nl_match z tau hz
      have hzx : z ≠ x := fun e => hx.2
        (e ▸ Finmap.mem_of_lookup_eq_some hz)
      have hxfv : x ∉ Ty.fv tau := fun hm => hx.2
        (hc.ctxWF_nl.nl_fv_in_ε z tau hz x hm)
      refine ⟨value, ?_, ?_⟩
      · simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hzx] using hlookup
      · rw [denotTy_agree tau (DEnv.AgreeOn.bind_left_of_not_mem hxfv)]
        exact hshape
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      have hfv : Ty.fv (Basis.tof b) ⊆ Gamma.keys :=
        (Basis.fv_tof_subset b).trans (raw_basisValid_fv_subset_keys hb)
      have hxGamma : x ∉ Gamma.keys := fun hm =>
        hx.2 (Finmap.mem_keys.mp hm)
      have hxfvb : x ∉ Ty.fv (Basis.tof b) := fun hm => hxGamma (hfv hm)
      refine ⟨fun z s hz => absurd hz (by simp), fun z tau hz => ?_⟩
      by_cases hzx : z = x
      · rw [hzx] at hz ⊢
        rw [Finmap.lookup_insert] at hz
        have htau : tau = Basis.tof b := (Option.some.inj hz).symm
        rw [htau]
        refine ⟨xs, by simp [DEnv.bind, Finmap.lookup_insert], ?_⟩
        rw [denotTy_agree _ (DEnv.AgreeOn.bind_left_of_not_mem hxfvb)]
        exact hxs
      · rw [Finmap.lookup_insert_of_ne _ hzx] at hz
        obtain ⟨value, hlookup, hshape⟩ := ih.nl_match z tau hz
        have hxfv : x ∉ Ty.fv tau := fun hm => hx.2
          (hc.ctxWF_nl.nl_fv_in_ε z tau hz x hm)
        refine ⟨value, ?_, ?_⟩
        · simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hzx] using hlookup
        · rw [denotTy_agree tau (DEnv.AgreeOn.bind_left_of_not_mem hxfv)]
          exact hshape
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      exact ih

/-! ## Fresh value-environment extension -/

/-- Updating the value environment at a name outside the evaluator telescope
preserves raw consistency. -/
theorem RawConsistent.update_of_not_mem_keyNames
    {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    forall (y : VName), y ∉ Psi.keyNames -> forall (w : ValValSem),
      RawConsistent orc Delta Gamma Psi GammaV sigma (rho.update y w) := by
  induction h with
  | empty => intro y hy w; exact RawConsistent.empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims ih =>
      intro y hy w
      have hfvTy := hc.typeFvPrefix hTy
      rw [EvalCtx.keyNames_extend_core, Finset.mem_insert, not_or] at hy
      have hyv : y ∉ ValExpr.fv v := fun hm => by
        have hmem := hfvv hm
        rw [EvalCtx.keyNames_extend_core, Finset.mem_insert] at hmem
        exact absurd hmem (not_or.mpr hy)
      have hyTy : y ∉ ValTy.fv tauV := fun hm => hy.2 (hfvTy hm)
      have hdenEq := denotValB_semS_update_of_not_mem_fv hirr rho y w v
        [] [] hyv (by simp)
      have hagree' : RawAgree orc sigma (rho.update y w) [] [] []
          (Basis.tof b) tauV (denotBasis sigma b) xs yV :=
        (RawAgree.update_of_not_mem_fv hirr sigma rho y w
          _ _ _ _ _ _ _ _ (by simp [ValTyCtxFresh]) hyTy).mpr hagree
      have hnew := RawConsistent.extend_lin (ih y hy.2 w) hx htof hb
        hTy hinfer hinferSpace hfvv hlc hnr hxs
        (by rw [hdenEq]; exact hden) hagree'
        ((RawAgreeDimsAt.update_of_not_mem_fv hirr sigma rho y w
          (Basis.tof b) tauV [] [] [] (denotBasis sigma b)
          (by simp [ValTyCtxFresh]) hyTy).mpr hdims)
      rw [raw_valEnv_update_comm _ hy.1] at hnew
      exact hnew
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hagree hdims hanchor ih =>
      intro y hy w
      have hfvTy := hc.typeFvPrefix hTy
      rw [EvalCtx.keyNames_extend_core, Finset.mem_insert, not_or] at hy
      have hyv : y ∉ ValExpr.fv v := fun hm => by
        have hmem := hfvv hm
        rw [EvalCtx.keyNames_extend_core, Finset.mem_insert] at hmem
        exact absurd hmem (not_or.mpr hy)
      have hyTy : y ∉ ValTy.fv tauV := fun hm => hy.2 (hfvTy hm)
      have hdenEq := denotValB_semS_update_of_not_mem_fv hirr rho y w v
        [] [] hyv (by simp)
      have hagree' : RawAgree orc sigma (rho.update y w) [] [] []
          (Basis.tof b) tauV (denotBasis sigma b) xs yV :=
        (RawAgree.update_of_not_mem_fv hirr sigma rho y w
          _ _ _ _ _ _ _ _ (by simp [ValTyCtxFresh]) hyTy).mpr hagree
      have hnew := RawConsistent.extend_nl (ih y hy.2 w) hx hb hTy
        hinfer hinferSpace hfvv hlc hnr hxs
        (by rw [hdenEq]; exact hden) hagree'
        ((RawAgreeDimsAt.update_of_not_mem_fv hirr sigma rho y w
          (Basis.tof b) tauV [] [] [] (denotBasis sigma b)
          (by simp [ValTyCtxFresh]) hyTy).mpr hdims)
        hanchor
      rw [raw_valEnv_update_comm _ hy.1] at hnew
      exact hnew
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hagree hdims hanchor ih =>
      intro y hy w
      have hfvTy := hc.typeFvPrefix hTy
      rw [EvalCtx.keyNames_extend_core, Finset.mem_insert, not_or] at hy
      have hyv : y ∉ ValExpr.fv v := fun hm => by
        have hmem := hfvv hm
        rw [EvalCtx.keyNames_extend_core, Finset.mem_insert] at hmem
        exact absurd hmem (not_or.mpr hy)
      have hyTy : y ∉ ValTy.fv tauV := fun hm => hy.2 (hfvTy hm)
      have hdenEq := denotValB_semS_update_of_not_mem_fv hirr rho y w v
        [] [] hyv (by simp)
      have hagree' : RawAgree orc sigma (rho.update y w) [] [] []
          (Basis.tof b) tauV (denotBasis sigma b) xs yV :=
        (RawAgree.update_of_not_mem_fv hirr sigma rho y w
          _ _ _ _ _ _ _ _ (by simp [ValTyCtxFresh]) hyTy).mpr hagree
      exact RawConsistent.extend_rep (ih y hy.2 w) hkey hsource hsigma hb
        hTy hinfer hinferSpace hfvv hlc hxs
        (by rw [hdenEq]; exact hden) hagree'
        ((RawAgreeDimsAt.update_of_not_mem_fv hirr sigma rho y w
          (Basis.tof b) tauV [] [] [] (denotBasis sigma b)
          (by simp [ValTyCtxFresh]) hyTy).mpr hdims)
        hanchor

/-! ## Exact-raw nonlinear binder extension -/

/-- `RawConsistent` implements the same-raw binder interface consumed by the
exact-basis `S.TyAt.frame` proof. -/
theorem rawConsistent_worldExtendNLAt
    {orc : FFSOracleSem} (hirr : OracleFvIrrel orc) :
    RawWorldExtendNLAt orc (RawConsistent orc) := by
  intro Delta Gamma0 Gamma Psi GammaV sigma rho hc hle y hy b0 tauV
    hb0 _hisTy hTyAt x' w hagree hdims
  let d : DVal := (denotTy sigma (Basis.tof b0)).embed x'
  have hb0' : BasisValid Gamma b0 :=
    raw_basisValid_mono_of_nlCtxIncl hb0 hle
  have hfvTy : ValTy.fv tauV ⊆ Psi.keyNames :=
    hTyAt.fv_subset_keyNames hc.evalCtxScoped
  have hlcTy : ValTy.lc tauV := evalT_lc hTyAt.toEvalT hc.evalCtxLc
  have hyKey : y ∉ Psi.keyNames :=
    raw_evalCtx_not_mem_keyNames_of_forall hy.2.2
  have hyTy : y ∉ ValTy.fv tauV := fun hm => hyKey (hfvTy hm)
  have hcUpdated := hc.update_of_not_mem_keyNames hirr y hyKey w
  have hagreeUpdated : RawAgree orc sigma (rho.update y w) [] [] []
      (Basis.tof b0) tauV (denotBasis sigma b0) d w :=
    (RawAgree.update_of_not_mem_fv hirr sigma rho y w
      _ _ _ _ _ _ _ _ (by simp [ValTyCtxFresh]) hyTy).mpr
        (by simpa only [d] using hagree)
  have hdimsUpdated : RawAgreeDimsAt orc sigma (rho.update y w) [] [] []
      (Basis.tof b0) tauV (denotBasis sigma b0) :=
    (RawAgreeDimsAt.update_of_not_mem_fv hirr sigma rho y w
      (Basis.tof b0) tauV [] [] [] (denotBasis sigma b0)
      (by simp [ValTyCtxFresh]) hyTy).mpr hdims
  have hden : denotValB_semS orc (rho.update y w) [] []
      (.var y tauV) = .ok w := by
    rw [denotValB_semS.eq_2, ValEnvSem.update_same]
  have hnew := RawConsistent.extend_nl hcUpdated ⟨hy.1, hy.2.1⟩ hb0'
    hTyAt.toEvalT (by simp)
    (by cases tauV <;> simp [ValExpr.InferSpaceMatchesBase,
      ValExpr.inferSpaceCtx])
    (raw_valExpr_fv_var_subset_keyNames_extend hfvTy) (.var hlcTy)
    (Or.inr ⟨tauV, rfl⟩) (HType.embed_matchesShape _ _) hden hagreeUpdated
    hdimsUpdated {
      valid := {
        typeRealized := by simpa using hTyAt.toEvalT
        valueScoped := raw_valExpr_fv_var_subset_keyNames_extend hfvTy
        locallyClosed := .var hlcTy }
      frameAnchored := by
        intro b0' b1' tauV0 tauV1 body _ hv
        exact nomatch hv }
  rw [raw_valEnv_update_update_same] at hnew
  simpa only [d] using hnew

end GLang
