import GLang.Proofs.Adequacy.Raw.RawDofAdequacyCore
import GLang.Proofs.Adequacy.Raw.RawSpaceAdequacyCore
import GLang.Proofs.Adequacy.Foundations.AgreeBasics
import GLang.Proofs.Source.BasisSoundness

namespace GLang

open scoped BigOperators TensorProduct
open Basis (BasisValid)

/-! ## Full source well-formedness from the raw telescope -/

private theorem raw_composite_basis_fv_subset_of_openVar_body
    {b : Basis} {L A : Finset Name}
    (h : forall y, y ∉ L -> forall z,
      z ∈ Basis.fv (Basis.openVar y b) -> z = y ∨ z ∈ A) :
    Basis.fv b ⊆ A := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Basis.fv b)
  simp only [Finset.mem_union, not_or] at hy
  intro z hz
  rcases h y hy.1 z (Basis.fv_subset_openRec hz) with rfl | hzA
  · exact absurd hz hy.2
  · exact hzA

private theorem raw_composite_basisValid_fv_subset_keys
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
      apply raw_composite_basis_fv_subset_of_openVar_body (L := L)
      intro y hy z hz
      have hzctx := ihbody y hy hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hzctx
      exact hzctx

private theorem RawConsistent.ctxWF_composite
    {orc : FFSOracleSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    CtxWF Delta Gamma := by
  induction h with
  | empty =>
      exact ⟨fun x hx => absurd hx Finmap.notMem_empty,
        fun x s hx => absurd hx (by simp),
        fun x tau hx => absurd hx (by simp)⟩
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hresult hdims ih =>
      have hsof : Basis.sof b = s := Basis.sof_of_tof_space htof
      exact ih.extend_lin hx.2 (hsof ▸ hb.sof_valid.some)
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hresult hdims _hanchor ih =>
      have hfv : Ty.fv (Basis.tof b) ⊆ Gamma.keys :=
        (Basis.fv_tof_subset b).trans
          (raw_composite_basisValid_fv_subset_keys hb)
      exact ih.insert_nl hx.1 hx.2 hfv
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hresult hdims hanchor ih =>
      exact ih

private theorem RawConsistent.envWF_composite
    {orc : FFSOracleSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    EnvWF sigma Delta Gamma := by
  induction h with
  | empty =>
      exact ⟨fun x s hx => absurd hx (by simp),
        fun x tau hx => absurd hx (by simp)⟩
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hc hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hresult hdims ih =>
      have hctx := hc.ctxWF_composite
      have hsof : Basis.sof b = s := Basis.sof_of_tof_space htof
      have hvalid : SValid Gamma s := hsof ▸ hb.sof_valid.some
      have hshape : xs.matchesShape (.hil (denotSpace sigma s)) := by
        simpa only [htof, denotTy, denotTyAux] using hxs
      obtain ⟨y, rfl⟩ := DVal.matchesShape_hil_eq hshape
      exact ih.extend_lin hctx hx.2 hvalid y
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hresult hdims _hanchor ih =>
      have hctx := hc.ctxWF_composite
      have hfv : Ty.fv (Basis.tof b) ⊆ Gamma.keys :=
        (Basis.fv_tof_subset b).trans
          (raw_composite_basisValid_fv_subset_keys hb)
      have hxKeys : x ∉ Gamma.keys := fun hm =>
        hx.2 (Finmap.mem_keys.mp hm)
      have hxfv : x ∉ Ty.fv (Basis.tof b) := fun hm => hxKeys (hfv hm)
      let y := (denotTy sigma (Basis.tof b)).extract xs
      have hembed : (denotTy sigma (Basis.tof b)).embed y = xs :=
        HType.embed_extract_of_matchesShape hxs
      rw [← hembed]
      exact ih.bind_nl hctx hx.1 hx.2 hxfv y
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc hxs
      hden hresult hdims hanchor ih =>
      exact ih

/-! ## Promotion-aware source typing and shapes -/

private theorem raw_composite_hasType_demote
    {lin Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (hdisj : Finmap.Disjoint lin Delta)
    (hctx : Graded.CtxDisj (lin ∪ Delta) Gamma)
    (h : Nonempty (HasType (lin ∪ Delta) Gamma e tau)) :
    Nonempty (HasType Delta (lin.toNL ∪ Gamma) e tau) := by
  obtain ⟨h⟩ := h
  have hctx' : Graded.CtxDisj Delta (lin.toNL ∪ Gamma) := by
    intro x hx hmem
    rcases Finmap.mem_union.mp hmem with hl | hg
    · exact hdisj x ((LCtx.mem_toNL_iff lin x).mp hl) hx
    · exact hctx x (Finmap.mem_union.mpr (Or.inr hx)) hg
  exact ⟨Graded.hasTypeBridgeBwd hctx'
    (Graded.gradeWeaken (Graded.hasTypeBridge hctx h)
      (Graded.GWk.of_wk (Graded.tr_promote_wk lin Delta Gamma hdisj)))⟩

private theorem raw_composite_hasType_mono_nl_aux
    {Delta : LCtx} {e : Term} {tau : Ty} (S : Finset Name) :
    forall (Gamma Gamma' : NLCtx), Nonempty (HasType Delta Gamma e tau) ->
      NLCtxIncl Gamma Gamma' -> Graded.CtxDisj Delta Gamma' ->
      (forall x, x ∈ Gamma' -> x ∉ Gamma -> x ∈ S) ->
      Nonempty (HasType Delta Gamma' e tau) := by
  induction S using Finset.induction_on with
  | empty =>
      intro Gamma Gamma' h hle _hctx hS
      have hGamma : Gamma' = Gamma := by
        apply Finmap.ext_lookup
        intro x
        by_cases hx : x ∈ Gamma
        · obtain ⟨tau', htau'⟩ := Finmap.mem_iff.mp hx
          rw [htau', hle x tau' htau']
        · have hx' : x ∉ Gamma' := fun h =>
            absurd (hS x h hx) (Finset.notMem_empty x)
          rw [Finmap.lookup_eq_none.mpr hx,
            Finmap.lookup_eq_none.mpr hx']
      rw [hGamma]
      exact h
  | insert y S' hyS ih =>
      intro Gamma Gamma' h hle hctx hS
      by_cases hy : y ∈ Gamma' ∧ y ∉ Gamma
      · obtain ⟨tau', htau'⟩ := Finmap.mem_iff.mp hy.1
        have hctx' : Graded.CtxDisj Delta (Gamma'.erase y) :=
          fun x hx hm => hctx x hx (Finmap.mem_erase.mp hm).2
        have h1 : Nonempty (HasType Delta (Gamma'.erase y) e tau) := by
          refine ih Gamma (Gamma'.erase y) h ?_ hctx' ?_
          · intro x tau'' hx
            have hxy : x ≠ y := fun hxy =>
              hy.2 (hxy ▸ Finmap.mem_of_lookup_eq_some hx)
            rw [Finmap.lookup_erase_ne hxy]
            exact hle x tau'' hx
          · intro x hx hxGamma
            obtain ⟨hxy, hx'⟩ := Finmap.mem_erase.mp hx
            rcases Finset.mem_insert.mp (hS x hx' hxGamma) with hxy' | hxS
            · exact absurd hxy' hxy
            · exact hxS
        have hyE : y ∉ Gamma'.erase y := fun hm =>
          (Finmap.mem_erase.mp hm).1 rfl
        have hyDelta : y ∉ Delta := fun hm => hctx y hm hy.1
        have h2 := Graded.hasType_weaken_insert
          (τ' := tau') hctx' hyDelta hyE h1.some
        have hGamma : Finmap.insert y tau' (Gamma'.erase y) = Gamma' := by
          apply Finmap.ext_lookup
          intro z
          by_cases hz : z = y
          · subst z
            rw [Finmap.lookup_insert, htau']
          · rw [Finmap.lookup_insert_of_ne _ hz,
              Finmap.lookup_erase_ne hz]
        rw [hGamma] at h2
        exact ⟨h2⟩
      · refine ih Gamma Gamma' h hle hctx ?_
        intro x hx hxGamma
        rcases Finset.mem_insert.mp (hS x hx hxGamma) with hxy | hxS
        · exact absurd ⟨hxy ▸ hx, hxy ▸ hxGamma⟩ hy
        · exact hxS

private theorem raw_composite_hasType_mono_nl
    {Delta : LCtx} {Gamma Gamma' : NLCtx} {e : Term} {tau : Ty}
    (h : Nonempty (HasType Delta Gamma e tau))
    (hle : NLCtxIncl Gamma Gamma')
    (hctx : Graded.CtxDisj Delta Gamma') :
    Nonempty (HasType Delta Gamma' e tau) :=
  raw_composite_hasType_mono_nl_aux (Gamma'.keys \ Gamma.keys)
    Gamma Gamma' h hle hctx
    (fun x hx hxGamma => Finset.mem_sdiff.mpr
      ⟨Finmap.mem_keys.mpr hx,
        fun hm => hxGamma (Finmap.mem_keys.mp hm)⟩)

private theorem raw_composite_hasType_ctxIncl_aux
    {Delta' : LCtx} {Gamma' : NLCtx} {e : Term} {tau : Ty}
    (hwf : CtxWF Delta' Gamma') (S : Finset Name) :
    forall (Delta : LCtx) (Gamma : NLCtx),
      Nonempty (HasType Delta Gamma e tau) -> Graded.CtxDisj Delta Gamma ->
      RawCtxIncl Delta Gamma Delta' Gamma' ->
      (forall x, x ∈ Delta -> x ∈ Gamma' -> x ∈ S) ->
      exists Delta1 : LCtx,
        (forall x s, Delta1.lookup x = some s ->
          Delta'.lookup x = some s) ∧
        Nonempty (HasType Delta1 Gamma' e tau) := by
  induction S using Finset.induction_on with
  | empty =>
      intro Delta Gamma h hctx hle hS
      have hctx' : Graded.CtxDisj Delta Gamma' := fun x hx hm =>
        Finset.notMem_empty x (hS x hx hm)
      refine ⟨Delta, ?_,
        raw_composite_hasType_mono_nl h hle.2 hctx'⟩
      intro x s hx
      rcases hle.1 x s hx with hlin | hnl
      · exact hlin
      · exact absurd (Finmap.mem_of_lookup_eq_some hnl)
          (hctx' x (Finmap.mem_of_lookup_eq_some hx))
  | insert y S' hyS ih =>
      intro Delta Gamma h hctx hle hS
      by_cases hy : y ∈ Delta ∧ y ∈ Gamma'
      · obtain ⟨s, hs⟩ := Finmap.mem_iff.mp hy.1
        have hyDelta' : y ∉ Delta' := fun hm =>
          hwf.disjoint y hm hy.2
        have hGamma'y : Gamma'.lookup y = some (.space s) := by
          rcases hle.1 y s hs with hlin | hnl
          · exact absurd (Finmap.mem_of_lookup_eq_some hlin) hyDelta'
          · exact hnl
        have hsplit : Delta =
            Finmap.singleton y s ∪ Delta.erase y := by
          apply Finmap.ext_lookup
          intro z
          by_cases hz : z = y
          · subst z
            rw [Finmap.lookup_union_left
              ((Finmap.mem_singleton _ _ _).mpr rfl),
              Finmap.lookup_singleton_eq, hs]
          · rw [Finmap.lookup_union_right
              (fun hm => hz ((Finmap.mem_singleton _ _ _).mp hm)),
              Finmap.lookup_erase_ne hz]
        have hdisj : Finmap.Disjoint
            (Finmap.singleton y s) (Delta.erase y) :=
          fun z hz hm => (Finmap.mem_erase.mp hm).1
            ((Finmap.mem_singleton _ _ _).mp hz)
        have hctx0 : Graded.CtxDisj
            (Finmap.singleton y s ∪ Delta.erase y) Gamma := by
          rw [← hsplit]
          exact hctx
        have h0 : Nonempty (HasType
            (Finmap.singleton y s ∪ Delta.erase y) Gamma e tau) := by
          rw [← hsplit]
          exact h
        have h' := raw_composite_hasType_demote hdisj hctx0 h0
        refine ih (Delta.erase y) _ h' ?_ ⟨?_, ?_⟩ ?_
        · intro z hz hm
          obtain ⟨hzy, hzDelta⟩ := Finmap.mem_erase.mp hz
          rcases Finmap.mem_union.mp hm with hl | hg
          · exact hzy ((Finmap.mem_singleton _ _ _).mp
              ((LCtx.mem_toNL_iff _ z).mp hl))
          · exact hctx z hzDelta hg
        · intro z s' hz
          have hzy : z ≠ y :=
            (Finmap.mem_erase.mp
              (Finmap.mem_of_lookup_eq_some hz)).1
          exact hle.1 z s' (by
            rw [← Finmap.lookup_erase_ne hzy]
            exact hz)
        · intro z tau' hz
          by_cases hzl : z ∈ LCtx.toNL (Finmap.singleton y s)
          · rw [Finmap.lookup_union_left hzl] at hz
            have hzy : z = y :=
              (Finmap.mem_singleton _ _ _).mp
                ((LCtx.mem_toNL_iff _ z).mp hzl)
            subst hzy
            have hl := LCtx.toNL_lookup
              (Finmap.singleton z s) z s
              Finmap.lookup_singleton_eq
            obtain rfl := Option.some.inj (hl.symm.trans hz)
            exact hGamma'y
          · rw [Finmap.lookup_union_right hzl] at hz
            exact hle.2 z tau' hz
        · intro z hz hm
          obtain ⟨hzy, hzDelta⟩ := Finmap.mem_erase.mp hz
          rcases Finset.mem_insert.mp (hS z hzDelta hm) with hzy' | hzS
          · exact absurd hzy' hzy
          · exact hzS
      · refine ih Delta Gamma h hctx hle ?_
        intro z hz hm
        rcases Finset.mem_insert.mp (hS z hz hm) with hzy | hzS
        · exact absurd ⟨hzy ▸ hz, hzy ▸ hm⟩ hy
        · exact hzS

private theorem raw_composite_hasType_ctxIncl
    {Delta Delta' : LCtx} {Gamma Gamma' : NLCtx}
    {e : Term} {tau : Ty}
    (hwf : CtxWF Delta' Gamma')
    (h : Nonempty (HasType Delta Gamma e tau))
    (hctx : Graded.CtxDisj Delta Gamma)
    (hle : RawCtxIncl Delta Gamma Delta' Gamma') :
    exists Delta1 : LCtx,
      (forall x s, Delta1.lookup x = some s ->
        Delta'.lookup x = some s) ∧
      Nonempty (HasType Delta1 Gamma' e tau) :=
  raw_composite_hasType_ctxIncl_aux hwf Delta.keys Delta Gamma h hctx hle
    (fun x hx _ => Finmap.mem_keys.mpr hx)

private theorem S.Term.raw_shape_at_composite
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    {s : GLang.Space}
    (he : S.Term Delta Gamma Psi e b v tauV)
    (htof : Basis.tof b = .space s)
    (hctx : Graded.CtxDisj Delta Gamma)
    {orc : FFSOracleSem} {Delta' : LCtx} {Gamma' : NLCtx}
    {Psi' : EvalCtx} {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hle : RawCtxIncl Delta Gamma Delta' Gamma')
    (hc : RawTypedConsistent orc Delta' Gamma' Psi' GammaV sigma rho) :
    exists x, denotTerm sigma e = .hil ⟨denotSpace sigma s, x⟩ := by
  obtain ⟨Delta1, hDelta, ⟨ht⟩⟩ :=
    raw_composite_hasType_ctxIncl hc.raw.ctxWF_composite he.hasType hctx hle
  have hs := (soundness ht
    (hc.raw.ctxWF_composite.of_sub_Δ hDelta)
    (hc.raw.envWF_composite.of_sub_Δ hDelta)).1
  rw [htof] at hs
  exact DVal.matchesShape_hil_eq hs

/-! ## Context-inclusion bookkeeping -/

private theorem RawCtxIncl.composite_union_left
    {Delta0 Delta1 Delta' : LCtx} {Gamma Gamma' : NLCtx}
    (h : RawCtxIncl (Delta0 ∪ Delta1) Gamma Delta' Gamma') :
    RawCtxIncl Delta0 Gamma Delta' Gamma' := by
  refine ⟨?_, h.2⟩
  intro x s hx
  apply h.1 x s
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)]
  exact hx

private theorem RawCtxIncl.composite_union_right
    {Delta0 Delta1 Delta' : LCtx} {Gamma Gamma' : NLCtx}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (h : RawCtxIncl (Delta0 ∪ Delta1) Gamma Delta' Gamma') :
    RawCtxIncl Delta1 Gamma Delta' Gamma' := by
  refine ⟨?_, h.2⟩
  intro x s hx
  apply h.1 x s
  rw [Finmap.lookup_union_right
    (fun hm => hdisj x hm (Finmap.mem_of_lookup_eq_some hx))]
  exact hx

/-! ## Small coefficient identities -/

private theorem raw_composite_fin_sum_of_eq_one
    {M : Type} [AddCommMonoid M] {n : Nat}
    (h : n = 1) (f : Fin n -> M) :
    (∑ i, f i) = f ⟨0, by omega⟩ := by
  subst h
  simp

private theorem raw_composite_agree_one_real
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {x : ℝ} {a : FlatArray}
    (h : LegacyAgree orc sigma rho [] [] [] (.space .real) (.space .real)
      (denotBasis sigma .one) (.hil ⟨HSpace.real, x⟩) (.array a)) :
    x = a.get 0 := by
  have hc := LegacyAgree.coords h
  simp only [denotSpaceAux] at hc
  rw [DVal.atSpace_hil_self,
    raw_composite_fin_sum_of_eq_one (ValSpace.dof_real _)] at hc
  simp only [denotBasis, BasisDenot.atSpace_vecs_self] at hc
  simp at hc
  rw [hc]
  simpa only [smul_eq_mul] using (mul_one (a.get 0 : ℝ))

private theorem raw_composite_rawAgree_space_array
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {s : GLang.Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : RawAgree orc sigma rho Ds Gv Dv
      (.space s) (.space sv) B x y) : exists a, y = .array a := by
  cases y with
  | array a => exact ⟨a, rfl⟩
  | fn T f => simpa only [RawAgree] using h

private theorem raw_composite_fin_sum_cast_of_eq
    {M : Type} [AddCommMonoid M] {n m : Nat}
    (h : n = m) (f : Fin n -> M) :
    (∑ i, f i) = ∑ i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  rfl

private theorem raw_composite_sum_prod_left
    {iota A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset iota) (g : iota -> A) :
    (∑ i ∈ s, (g i, (0 : B))) = (∑ i ∈ s, g i, 0) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem raw_composite_sum_prod_right
    {iota A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset iota) (g : iota -> B) :
    (∑ i ∈ s, ((0 : A), g i)) = (0, ∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem raw_composite_dsum_getD_left
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) (i : Nat) (hi : i < vs0.length) :
    (HSpace.dsumOfLists V0 V1 vs0 vs1).getD i 0 =
      (vs0.getD i 0, 0) := by
  unfold HSpace.dsumOfLists
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  change (vs0.map (fun x => (x, 0))).getD i ((0, 0)) = _
  rw [show ((0, 0) : V0.carrier × V1.carrier) =
      (fun x => (x, 0)) 0 by rfl, List.getD_map]

private theorem raw_composite_dsum_getD_right
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) (i : Nat) (hi : i < vs1.length) :
    (HSpace.dsumOfLists V0 V1 vs0 vs1).getD (vs0.length + i) 0 =
      (0, vs1.getD i 0) := by
  unfold HSpace.dsumOfLists
  have hmaplen :
      (vs0.map (LinearMap.inl ℝ V0.carrier V1.carrier)).length =
        vs0.length := List.length_map _
  rw [← hmaplen]
  rw [List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]
  change (vs1.map (fun x => (0, x))).getD i ((0, 0)) = _
  rw [show ((0, 0) : V0.carrier × V1.carrier) =
      (fun x => (0, x)) 0 by rfl, List.getD_map]

private theorem raw_composite_dsum_coeff_sum
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) {N0 N1 : Nat}
    (hl0 : vs0.length = N0) (hl1 : vs1.length = N1)
    (c : Fin (N0 + N1) -> ℝ) :
    (∑ i, c i • (HSpace.dsumOfLists V0 V1 vs0 vs1).getD i 0) =
      (∑ i : Fin N0, c (Fin.castAdd N1 i) • vs0.getD i 0,
       ∑ i : Fin N1, c (Fin.natAdd N0 i) • vs1.getD i 0) := by
  subst hl0
  subst hl1
  rw [Fin.sum_univ_add]
  have h0 : (∑ i : Fin vs0.length,
      c (Fin.castAdd vs1.length i) •
        (HSpace.dsumOfLists V0 V1 vs0 vs1).getD
          (Fin.castAdd vs1.length i) 0) =
      (∑ i : Fin vs0.length,
        c (Fin.castAdd vs1.length i) • vs0.getD i 0, 0) := by
    rw [← raw_composite_sum_prod_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_castAdd,
      raw_composite_dsum_getD_left _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  have h1 : (∑ i : Fin vs1.length,
      c (Fin.natAdd vs0.length i) •
        (HSpace.dsumOfLists V0 V1 vs0 vs1).getD
          (Fin.natAdd vs0.length i) 0) =
      (0, ∑ i : Fin vs1.length,
        c (Fin.natAdd vs0.length i) • vs1.getD i 0) := by
    rw [← raw_composite_sum_prod_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.val_natAdd,
      raw_composite_dsum_getD_right _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  rw [h0, h1]
  ext <;> simp

private theorem raw_composite_sum_range_mul_div_mod
    {M : Type} [AddCommMonoid M]
    (m n : Nat) (g : Nat -> Nat -> M) :
    (∑ k ∈ Finset.range (m * n), g (k / n) (k % n)) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, g i j := by
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro i
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro j
  have hnpos : 0 < n := Nat.zero_lt_of_lt j.isLt
  change g ((j.val + n * i.val) / n) ((j.val + n * i.val) % n) =
    g i.val j.val
  rw [Nat.add_mul_div_left _ _ hnpos, Nat.div_eq_of_lt j.isLt,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  simp

private theorem raw_composite_tprod_coeff_sum_range
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) (c0 c1 : Nat -> ℝ) :
    (∑ k ∈ Finset.range (vs0.length * vs1.length),
      (c0 (k / vs1.length) * c1 (k % vs1.length)) •
        (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0) =
      (∑ i ∈ Finset.range vs0.length, c0 i • vs0.getD i 0) ⊗ₜ[ℝ]
        (∑ j ∈ Finset.range vs1.length, c1 j • vs1.getD j 0) := by
  by_cases hn : vs1.length = 0
  · rw [hn, Nat.mul_zero]
    simp
  have hnpos : 0 < vs1.length := Nat.pos_of_ne_zero hn
  calc
    (∑ k ∈ Finset.range (vs0.length * vs1.length),
      (c0 (k / vs1.length) * c1 (k % vs1.length)) •
        (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0) =
        ∑ k ∈ Finset.range (vs0.length * vs1.length),
          (c0 (k / vs1.length) * c1 (k % vs1.length)) •
            (vs0.getD (k / vs1.length) 0 ⊗ₜ[ℝ]
              vs1.getD (k % vs1.length) 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hklist : k <
          (HSpace.tprodOfLists V0 V1 vs0 vs1).length := by
        rw [HSpace.tprodOfLists_length]
        exact hk'
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hklist,
        HSpace.tprodOfLists_getElem vs0 vs1 k hk' hnpos]
      have hi : k / vs1.length < vs0.length :=
        (Nat.div_lt_iff_lt_mul hnpos).2 hk'
      have hj : k % vs1.length < vs1.length :=
        Nat.mod_lt _ hnpos
      rw [List.getD_eq_getElem vs0 0 hi,
        List.getD_eq_getElem vs1 0 hj]
      simp only [Option.getD_some]
    _ = ∑ i ∈ Finset.range vs0.length,
          ∑ j ∈ Finset.range vs1.length,
          (c0 i * c1 j) • (vs0.getD i 0 ⊗ₜ[ℝ] vs1.getD j 0) := by
      exact raw_composite_sum_range_mul_div_mod vs0.length vs1.length
        (fun i j => (c0 i * c1 j) •
          (vs0.getD i 0 ⊗ₜ[ℝ] vs1.getD j 0))
    _ = (∑ i ∈ Finset.range vs0.length,
          c0 i • vs0.getD i 0) ⊗ₜ[ℝ]
        (∑ j ∈ Finset.range vs1.length,
          c1 j • vs1.getD j 0) := by
      rw [TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [TensorProduct.smul_tmul_smul]

private theorem raw_composite_tprod_coeff_sum
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) {N0 N1 : Nat}
    (hl0 : vs0.length = N0) (hl1 : vs1.length = N1)
    (c : Fin (N0 * N1) -> ℝ) (c0 c1 : Nat -> ℝ)
    (hc : forall k : Fin (N0 * N1),
      c k = c0 (k / N1) * c1 (k % N1)) :
    (∑ k, c k • (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0) =
      (∑ i : Fin N0, c0 i • vs0.getD i 0) ⊗ₜ[ℝ]
        (∑ j : Fin N1, c1 j • vs1.getD j 0) := by
  subst hl0
  subst hl1
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range
      (fun k => (c0 (k / vs1.length) * c1 (k % vs1.length)) •
        (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0),
    Fin.sum_univ_eq_sum_range (fun i => c0 i • vs0.getD i 0),
    Fin.sum_univ_eq_sum_range (fun j => c1 j • vs1.getD j 0)]
  exact raw_composite_tprod_coeff_sum_range V0 V1 vs0 vs1 c0 c1

/-- Row-major tensor coefficients expand into a double sum. -/
private theorem raw_composite_tprod_double_sum
    (V0 V1 : HSpace) (vs0 : List V0.carrier)
    (vs1 : List V1.carrier) {N0 N1 : Nat}
    (hl0 : vs0.length = N0) (hl1 : vs1.length = N1)
    (c : Fin (N0 * N1) -> ℝ) (c' : Nat -> Nat -> ℝ)
    (hc : forall k : Fin (N0 * N1),
      c k = c' (k / N1) (k % N1)) :
    (∑ k, c k • (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0) =
      ∑ i ∈ Finset.range N0, ∑ j ∈ Finset.range N1,
        c' i j • (vs0.getD i 0 ⊗ₜ[ℝ] vs1.getD j 0) := by
  subst hl0
  subst hl1
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => c' (k / vs1.length) (k % vs1.length) •
      (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0)]
  by_cases hn : vs1.length = 0
  · rw [hn]
    simp
  have hnpos : 0 < vs1.length := Nat.pos_of_ne_zero hn
  calc
    (∑ k ∈ Finset.range (vs0.length * vs1.length),
      c' (k / vs1.length) (k % vs1.length) •
        (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0) =
        ∑ k ∈ Finset.range (vs0.length * vs1.length),
          c' (k / vs1.length) (k % vs1.length) •
            (vs0.getD (k / vs1.length) 0 ⊗ₜ[ℝ]
              vs1.getD (k % vs1.length) 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hklist : k <
          (HSpace.tprodOfLists V0 V1 vs0 vs1).length := by
        rw [HSpace.tprodOfLists_length]
        exact hk'
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hklist,
        HSpace.tprodOfLists_getElem vs0 vs1 k hk' hnpos]
      have hi : k / vs1.length < vs0.length :=
        (Nat.div_lt_iff_lt_mul hnpos).2 hk'
      have hj : k % vs1.length < vs1.length := Nat.mod_lt _ hnpos
      rw [List.getD_eq_getElem vs0 0 hi,
        List.getD_eq_getElem vs1 0 hj]
      simp only [Option.getD_some]
    _ = _ := by
      exact raw_composite_sum_range_mul_div_mod vs0.length vs1.length
        (fun i j => c' i j •
          (vs0.getD i 0 ⊗ₜ[ℝ] vs1.getD j 0))

/-- Kronecker-delta evaluation of the list dual basis, in `getD` form. -/
private theorem raw_composite_dualOfList_delta
    {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) {i j : Nat}
    (hi : i < vs.length) (hj : j < vs.length) :
    (V.dualOfList vs).getD i 0 (vs.getD j 0) =
      if i = j then 1 else 0 := by
  have hdualLen : (V.dualOfList vs).length = vs.length :=
    HSpace.dualOfList_length V vs
  have hiDual : i < (V.dualOfList vs).length := hdualLen.symm ▸ hi
  rw [List.getD_eq_getElem (V.dualOfList vs) 0 hiDual,
    List.getD_eq_getElem vs 0 hj]
  change ((V.dualOfList vs).get ⟨i, hiDual⟩) (vs.get ⟨j, hj⟩) = _
  have hdual : (V.dualOfList vs).get ⟨i, hiDual⟩ =
      V.dualVec vs ⟨i, hi⟩ := by
    refine (List.get_of_eq
      (HSpace.dualOfList_eq_finRange_map V vs) ⟨i, hiDual⟩).trans ?_
    simp
  rw [hdual]
  simpa only [Fin.mk.injEq] using h.dual_delta ⟨i, hi⟩ ⟨j, hj⟩

/-! ## Composite ordinary-trace arms -/

/-- Scalar multiplication consumes the inferred-space companion of exactly
the vector child.  The scalar child is used only through its ordinary trace. -/
theorem arm_scale
    {orc : FFSOracleSem}
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b : Basis} {v0 v1 : ValExpr} {sv : ValSpace}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (htof : Basis.tof b = .space (Basis.sof b))
    (_ht : Nonempty
      (HasType (Delta0 ∪ Delta1) Gamma (.smul e0 e1) (Basis.tof b)))
    (_hbv : BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b (.space sv))
    (he0 : S.Term Delta0 Gamma Psi e0 .one v0 (.space .real))
    (he1 : S.Term Delta1 Gamma Psi e1 b v1 (.space sv))
    (ihTy : RawMTyAtSubctx orc Gamma Psi b (.space sv))
    (ih0 : RawMTermTraceSubctx orc Delta0 Gamma Psi
      e0 .one v0 (.space .real))
    (ih1 : RawTermDofFactsSubctx orc Delta1 Gamma Psi
      e1 b v1 (.space sv)) :
    RawMTermTraceSubctx orc (Delta0 ∪ Delta1) Gamma Psi
      (.smul e0 e1) b (.scale v0 v1) (.space sv) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hle0 := hle.composite_union_left
  have hle1 := hle.composite_union_right hdisj
  have hctx0 := Graded.CtxDisj.of_union_left hctx
  have hctx1 := Graded.CtxDisj.of_union_right hctx
  have trace0 := ih0 hsub hctx0 rho Delta' Gamma' sigma GammaV hle0 hc
  have trace1 := ih1.trace hsub hctx1 rho Delta' Gamma' sigma GammaV hle1 hc
  have hdof1 : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] v1) = ValSpace.dof (orc rho [] []) sv :=
    dof_eq_of_shpOf_eq
      (ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have targetDims :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨y0, hy0, hA0⟩ := trace0.result
  obtain ⟨y1, hy1, hA1⟩ := trace1.result
  obtain ⟨x0, hx0⟩ := he0.raw_shape_at_composite rfl hctx0 hle0 hc
  obtain ⟨x1, hx1⟩ := he1.raw_shape_at_composite htof hctx1 hle1 hc
  have hx0Aux : denotTermAux sigma [] e0 =
      .hil ⟨denotSpaceAux sigma [] .real, x0⟩ := hx0
  have hx1Aux : denotTermAux sigma [] e1 =
      .hil ⟨denotSpaceAux sigma [] (Basis.sof b), x1⟩ := hx1
  rw [htof] at hA1
  obtain ⟨a0, rfl⟩ := raw_composite_rawAgree_space_array hA0
  obtain ⟨a1, rfl⟩ := raw_composite_rawAgree_space_array hA1
  simp only [Basis.tof, Basis.sof, RawAgree] at hA0
  simp only [RawAgree] at hA1
  rw [hx0] at hA0
  have hv0 : x0 = a0.get 0 := raw_composite_agree_one_real hA0
  have hlen1 := LegacyAgree.length hA1
  have hcoords1 := LegacyAgree.coords hA1
  rw [hx1, DVal.atSpace_hil_self] at hcoords1
  have result : RawResultAgree orc sigma rho [] [] []
      (Basis.tof b) (.space sv) (denotBasis sigma b)
      (denotTerm sigma (.smul e0 e1))
      (denotValB_semS orc rho [] [] (.scale v0 v1)) := by
    rw [denotValB_semS.eq_5, hy0, hy1]
    have hshape : ValueShape.scale (orc rho [] [])
        (ValExpr.inferSpaceCtx [] v1) a0 a1 := by
      refine ⟨?_, hlen1.2.trans hdof1.symm⟩
      simpa only [ValSpace.dof_real] using (LegacyAgree.length hA0).2
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hshape]
    refine ⟨_, rfl, ?_⟩
    rw [htof]
    simp only [ValExpr.inferSpaceCtx, ValValSem.arrayOf]
    simp only [RawAgree]
    rw [LegacyAgree.space_iff]
    refine ⟨hlen1.1, ?_, ?_⟩
    · rw [FlatArray.length_ofFn, hdof1]
    · simp only [denotTerm, denotTermAux]
      rw [hx0Aux, hx1Aux]
      have hr : DVal.asReal (.hil ⟨denotSpaceAux sigma [] .real, x0⟩) =
          x0 := by
        simp only [DVal.asReal, DVal.asHil, denotSpaceAux]
        rw [dif_pos trivial]
      change DVal.atSpace _
        (DVal.hil ⟨denotSpaceAux sigma [] (Basis.sof b),
          DVal.asReal (.hil ⟨denotSpaceAux sigma [] .real, x0⟩) • x1⟩) = _
      rw [DVal.atSpace_hil_self, hr, hv0, hcoords1,
        Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul,
        FlatArray.get_ofFn_lt _ _ _ (by rw [hdof1]; exact i.isLt)]
  exact ⟨result, targetDims⟩

/-- Direct-sum evaluation reads both child inferred spaces, so both children
enter through `RawTermDofFactsSubctx`. -/
theorem arm_dsumE
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b0 b1 : Basis} {v0 v1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (htof0 : Basis.tof b0 = .space (Basis.sof b0))
    (htof1 : Basis.tof b1 = .space (Basis.sof b1))
    (_ht : Nonempty
      (HasType Delta Gamma (.dsumE e0 e1)
        (Basis.tof (.dsum b0 b1))))
    (_hbv : BasisValid Gamma (.dsum b0 b1))
    (hTy : S.TyAt Gamma Psi (.dsum b0 b1)
      (.space (.dsum sv0 sv1)))
    (he0 : S.Term Delta Gamma Psi e0 b0 v0 (.space sv0))
    (he1 : S.Term Delta Gamma Psi e1 b1 v1 (.space sv1))
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.dsum b0 b1)
      (.space (.dsum sv0 sv1)))
    (ih0 : RawTermDofFactsSubctx orc Delta Gamma Psi
      e0 b0 v0 (.space sv0))
    (ih1 : RawTermDofFactsSubctx orc Delta Gamma Psi
      e1 b1 v1 (.space sv1)) :
    RawMTermTraceSubctx orc Delta Gamma Psi (.dsumE e0 e1)
      (.dsum b0 b1) (.dsumE v0 v1) (.space (.dsum sv0 sv1)) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have trace0 := ih0.trace hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have trace1 := ih1.trace hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hdof0 : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] v0) = ValSpace.dof (orc rho [] []) sv0 :=
    dof_eq_of_shpOf_eq
      (ih0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hdof1 : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] v1) = ValSpace.dof (orc rho [] []) sv1 :=
    dof_eq_of_shpOf_eq
      (ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  obtain ⟨y0, hy0, hA0⟩ := trace0.result
  obtain ⟨y1, hy1, hA1⟩ := trace1.result
  obtain ⟨x0, hx0⟩ := he0.raw_shape_at_composite htof0 hctx hle hc
  obtain ⟨x1, hx1⟩ := he1.raw_shape_at_composite htof1 hctx hle hc
  have hx0Aux : denotTermAux sigma [] e0 =
      .hil ⟨denotSpaceAux sigma [] (Basis.sof b0), x0⟩ := hx0
  have hx1Aux : denotTermAux sigma [] e1 =
      .hil ⟨denotSpaceAux sigma [] (Basis.sof b1), x1⟩ := hx1
  rw [htof0] at hA0
  rw [htof1] at hA1
  obtain ⟨a0, rfl⟩ := raw_composite_rawAgree_space_array hA0
  obtain ⟨a1, rfl⟩ := raw_composite_rawAgree_space_array hA1
  simp only [RawAgree] at hA0 hA1
  have hlen0 := LegacyAgree.length hA0
  have hlen1 := LegacyAgree.length hA1
  have hcoords0 := LegacyAgree.coords hA0
  have hcoords1 := LegacyAgree.coords hA1
  rw [hx0, DVal.atSpace_hil_self] at hcoords0
  rw [hx1, DVal.atSpace_hil_self] at hcoords1
  have hN : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.dsumE v0 v1)) =
      ValSpace.dof (orc rho [] []) sv0 +
        ValSpace.dof (orc rho [] []) sv1 := by
    simp only [ValExpr.inferSpaceCtx, ValSpace.dof_dsum, hdof0, hdof1]
  have result : RawResultAgree orc sigma rho [] [] []
      (Basis.tof (.dsum b0 b1)) (.space (.dsum sv0 sv1))
      (denotBasis sigma (.dsum b0 b1))
      (denotTerm sigma (.dsumE e0 e1))
      (denotValB_semS orc rho [] [] (.dsumE v0 v1)) := by
    rw [denotValB_semS.eq_10, hy0, hy1]
    have hshape : ValueShape.pair (orc rho [] [])
        (ValExpr.inferSpaceCtx [] v0) (ValExpr.inferSpaceCtx [] v1) a0 a1 :=
      ⟨hlen0.2.trans hdof0.symm, hlen1.2.trans hdof1.symm⟩
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hshape]
    refine ⟨_, rfl, ?_⟩
    simp only [ValValSem.arrayOf]
    simp only [Basis.tof, RawAgree]
    rw [LegacyAgree.space_iff]
    change ((denotBasis sigma (.dsum b0 b1)).atSpace
        (HSpace.dsum (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1)))).length =
          ValSpace.dof (orc rho [] []) (.dsum sv0 sv1) ∧
      (FlatArray.ofFn (ValSpace.dof (orc rho [] [])
        (ValExpr.inferSpaceCtx [] (.dsumE v0 v1))) _).length =
          ValSpace.dof (orc rho [] []) (.dsum sv0 sv1) ∧
      DVal.atSpace
        (HSpace.dsum (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1)))
        (denotTerm sigma (.dsumE e0 e1)) =
          ∑ i : Fin (ValSpace.dof (orc rho [] []) (.dsum sv0 sv1)),
            (FlatArray.ofFn (ValSpace.dof (orc rho [] [])
              (ValExpr.inferSpaceCtx [] (.dsumE v0 v1))) _).get i •
            ((denotBasis sigma (.dsum b0 b1)).atSpace
              (HSpace.dsum (denotSpaceAux sigma [] (Basis.sof b0))
                (denotSpaceAux sigma [] (Basis.sof b1)))).getD i 0
    have hB : (denotBasis sigma (.dsum b0 b1)).atSpace
        (HSpace.dsum (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1))) =
        HSpace.dsumOfLists
          (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1))
          ((denotBasis sigma b0).atSpace
            (denotSpaceAux sigma [] (Basis.sof b0)))
          ((denotBasis sigma b1).atSpace
            (denotSpaceAux sigma [] (Basis.sof b1))) := by
      simp only [denotBasis]
      exact BasisDenot.atSpace_vecs_self _ _
    rw [hB]
    refine ⟨?_, ?_, ?_⟩
    · rw [HSpace.dsumOfLists_length, ValSpace.dof_dsum,
        hlen0.1, hlen1.1]
    · rw [FlatArray.length_ofFn, hN, ValSpace.dof_dsum]
    · simp only [denotTerm, denotTermAux]
      rw [hx0Aux, hx1Aux]
      change DVal.atSpace _
        (DVal.hil ⟨HSpace.dsum
          (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1)), (x0, x1)⟩) = _
      rw [DVal.atSpace_hil_self,
        raw_composite_fin_sum_cast_of_eq
          (ValSpace.dof_dsum _ _ _)]
      simp only [Fin.val_cast]
      rw [raw_composite_dsum_coeff_sum _ _ _ _ hlen0.1 hlen1.1]
      refine Prod.ext ?_ ?_
      · show x0 = _
        rw [hcoords0]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        simp only [Fin.val_castAdd]
        rw [FlatArray.get_ofFn_lt _ _ _ (by rw [hN]; omega)]
        simp only [hdof0]
        rw [if_pos i.isLt]
      · show x1 = _
        rw [hcoords1]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        simp only [Fin.val_natAdd]
        rw [FlatArray.get_ofFn_lt _ _ _ (by rw [hN]; omega)]
        simp only [hdof0]
        rw [if_neg (by omega), Nat.add_sub_cancel_left]
  exact ⟨result, targetDims⟩

/-- Tensor-product evaluation likewise reads both child inferred spaces. -/
theorem arm_tprodE
    {orc : FFSOracleSem}
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b0 b1 : Basis} {v0 v1 : ValExpr}
    {sv0 sv1 : ValSpace}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (htof0 : Basis.tof b0 = .space (Basis.sof b0))
    (htof1 : Basis.tof b1 = .space (Basis.sof b1))
    (_ht : Nonempty
      (HasType (Delta0 ∪ Delta1) Gamma (.tprodE e0 e1)
        (Basis.tof (.tprod b0 b1))))
    (_hbv : BasisValid Gamma (.tprod b0 b1))
    (hTy : S.TyAt Gamma Psi (.tprod b0 b1)
      (.space (.tprod sv0 sv1)))
    (he0 : S.Term Delta0 Gamma Psi e0 b0 v0 (.space sv0))
    (he1 : S.Term Delta1 Gamma Psi e1 b1 v1 (.space sv1))
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod b0 b1)
      (.space (.tprod sv0 sv1)))
    (ih0 : RawTermDofFactsSubctx orc Delta0 Gamma Psi
      e0 b0 v0 (.space sv0))
    (ih1 : RawTermDofFactsSubctx orc Delta1 Gamma Psi
      e1 b1 v1 (.space sv1)) :
    RawMTermTraceSubctx orc (Delta0 ∪ Delta1) Gamma Psi
      (.tprodE e0 e1) (.tprod b0 b1) (.tprodE v0 v1)
      (.space (.tprod sv0 sv1)) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hle0 := hle.composite_union_left
  have hle1 := hle.composite_union_right hdisj
  have hctx0 := Graded.CtxDisj.of_union_left hctx
  have hctx1 := Graded.CtxDisj.of_union_right hctx
  have trace0 := ih0.trace hsub hctx0 rho Delta' Gamma' sigma GammaV hle0 hc
  have trace1 := ih1.trace hsub hctx1 rho Delta' Gamma' sigma GammaV hle1 hc
  have hdof0 : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] v0) = ValSpace.dof (orc rho [] []) sv0 :=
    dof_eq_of_shpOf_eq
      (ih0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hdof1 : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] v1) = ValSpace.dof (orc rho [] []) sv1 :=
    dof_eq_of_shpOf_eq
      (ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  obtain ⟨y0, hy0, hA0⟩ := trace0.result
  obtain ⟨y1, hy1, hA1⟩ := trace1.result
  obtain ⟨x0, hx0⟩ := he0.raw_shape_at_composite htof0 hctx0 hle0 hc
  obtain ⟨x1, hx1⟩ := he1.raw_shape_at_composite htof1 hctx1 hle1 hc
  have hx0Aux : denotTermAux sigma [] e0 =
      .hil ⟨denotSpaceAux sigma [] (Basis.sof b0), x0⟩ := hx0
  have hx1Aux : denotTermAux sigma [] e1 =
      .hil ⟨denotSpaceAux sigma [] (Basis.sof b1), x1⟩ := hx1
  rw [htof0] at hA0
  rw [htof1] at hA1
  obtain ⟨a0, rfl⟩ := raw_composite_rawAgree_space_array hA0
  obtain ⟨a1, rfl⟩ := raw_composite_rawAgree_space_array hA1
  simp only [RawAgree] at hA0 hA1
  have hlen0 := LegacyAgree.length hA0
  have hlen1 := LegacyAgree.length hA1
  have hcoords0 := LegacyAgree.coords hA0
  have hcoords1 := LegacyAgree.coords hA1
  rw [hx0, DVal.atSpace_hil_self] at hcoords0
  rw [hx1, DVal.atSpace_hil_self] at hcoords1
  have hN : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.tprodE v0 v1)) =
      ValSpace.dof (orc rho [] []) sv0 *
        ValSpace.dof (orc rho [] []) sv1 := by
    simp only [ValExpr.inferSpaceCtx, ValSpace.dof_tprod, hdof0, hdof1]
  have result : RawResultAgree orc sigma rho [] [] []
      (Basis.tof (.tprod b0 b1)) (.space (.tprod sv0 sv1))
      (denotBasis sigma (.tprod b0 b1))
      (denotTerm sigma (.tprodE e0 e1))
      (denotValB_semS orc rho [] [] (.tprodE v0 v1)) := by
    rw [denotValB_semS.eq_9, hy0, hy1]
    have hshape : ValueShape.pair (orc rho [] [])
        (ValExpr.inferSpaceCtx [] v0) (ValExpr.inferSpaceCtx [] v1) a0 a1 :=
      ⟨hlen0.2.trans hdof0.symm, hlen1.2.trans hdof1.symm⟩
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hshape]
    refine ⟨_, rfl, ?_⟩
    simp only [ValValSem.arrayOf]
    simp only [Basis.tof, RawAgree]
    rw [LegacyAgree.space_iff]
    change ((denotBasis sigma (.tprod b0 b1)).atSpace
        (HSpace.tprod (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1)))).length =
          ValSpace.dof (orc rho [] []) (.tprod sv0 sv1) ∧
      (FlatArray.ofFn (ValSpace.dof (orc rho [] [])
        (ValExpr.inferSpaceCtx [] (.tprodE v0 v1))) _).length =
          ValSpace.dof (orc rho [] []) (.tprod sv0 sv1) ∧
      DVal.atSpace
        (HSpace.tprod (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1)))
        (denotTerm sigma (.tprodE e0 e1)) =
          ∑ i : Fin (ValSpace.dof (orc rho [] []) (.tprod sv0 sv1)),
            (FlatArray.ofFn (ValSpace.dof (orc rho [] [])
              (ValExpr.inferSpaceCtx [] (.tprodE v0 v1))) _).get i •
            ((denotBasis sigma (.tprod b0 b1)).atSpace
              (HSpace.tprod (denotSpaceAux sigma [] (Basis.sof b0))
                (denotSpaceAux sigma [] (Basis.sof b1)))).getD i 0
    have hB : (denotBasis sigma (.tprod b0 b1)).atSpace
        (HSpace.tprod (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1))) =
        HSpace.tprodOfLists
          (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1))
          ((denotBasis sigma b0).atSpace
            (denotSpaceAux sigma [] (Basis.sof b0)))
          ((denotBasis sigma b1).atSpace
            (denotSpaceAux sigma [] (Basis.sof b1))) := by
      simp only [denotBasis]
      exact BasisDenot.atSpace_vecs_self _ _
    rw [hB]
    refine ⟨?_, ?_, ?_⟩
    · rw [HSpace.tprodOfLists_length, ValSpace.dof_tprod,
        hlen0.1, hlen1.1]
    · rw [FlatArray.length_ofFn, hN, ValSpace.dof_tprod]
    · simp only [denotTerm, denotTermAux]
      rw [hx0Aux, hx1Aux]
      change DVal.atSpace _
        (DVal.hil ⟨HSpace.tprod
          (denotSpaceAux sigma [] (Basis.sof b0))
          (denotSpaceAux sigma [] (Basis.sof b1)), x0 ⊗ₜ[ℝ] x1⟩) = _
      rw [DVal.atSpace_hil_self,
        raw_composite_fin_sum_cast_of_eq
          (ValSpace.dof_tprod _ _ _)]
      simp only [Fin.val_cast]
      rw [raw_composite_tprod_coeff_sum _ _ _ _ hlen0.1 hlen1.1 _
        (fun i => a0.get i) (fun j => a1.get j) ?_]
      · rw [hcoords0, hcoords1]
      · intro k
        dsimp only
        rw [FlatArray.get_ofFn_lt _ _ _ (by rw [hN]; exact k.isLt)]
        simp only [hdof1]
  exact ⟨result, targetDims⟩

/-- Linear tensor application checks both operand dimensions. Its guard uses
inferred-space companions already supplied by the mutual induction. -/
theorem arm_appL_lin
    {orc : FFSOracleSem}
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {n0 n1 : Term} {env0 env1 : ValExpr}
    {sv svOut svMat0 svMat1 svArg : ValSpace}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (htof1 : Basis.tof b1 = .space (Basis.sof b1))
    (_ht : Nonempty
      (HasType (Delta0 ∪ Delta1) Gamma
        (.appL (Basis.sof b0) (Basis.sof b1) n0 n1)
        (Basis.tof b1)))
    (hbv : BasisValid Gamma b1)
    (_hsv : S.Space Gamma Psi (Basis.sof b0) sv)
    (hTy : S.TyAt Gamma Psi b1 (.space svOut))
    (h0 : S.Term Delta0 Gamma Psi n0 (.tprod (.dual b0) b1)
      env0 (.space (.tprod svMat0 svMat1)))
    (h1 : S.Term Delta1 Gamma Psi n1 b0 env1 (.space svArg))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv)
    (ihTy : RawMTyAtSubctx orc Gamma Psi b1 (.space svOut))
    (ih0 : RawTermDofFactsSubctx orc Delta0 Gamma Psi n0
      (.tprod (.dual b0) b1) env0 (.space (.tprod svMat0 svMat1)))
    (ih1 : RawTermDofFactsSubctx orc Delta1 Gamma Psi n1 b0 env1
      (.space svArg)) :
    RawMTermTraceSubctx orc (Delta0 ∪ Delta1) Gamma Psi
      (.appL (Basis.sof b0) (Basis.sof b1) n0 n1) b1
      (ValExpr.reshapBase (.ttv sv env0 env1) svOut) (.space svOut) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hle0 := hle.composite_union_left
  have hle1 := hle.composite_union_right hdisj
  have hctx0 := Graded.CtxDisj.of_union_left hctx
  have hctx1 := Graded.CtxDisj.of_union_right hctx
  have trace0 := ih0.trace hsub hctx0 rho Delta' Gamma' sigma GammaV hle0 hc
  have trace1 := ih1.trace hsub hctx1 rho Delta' Gamma' sigma GammaV hle1 hc
  have hdof1 : ValSpace.dof (orc rho [] []) (ValExpr.inferSpaceCtx [] env1) =
      ValSpace.dof (orc rho [] []) svArg :=
    dof_eq_of_shpOf_eq (ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hsd := ih0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨sa, sb, hsab⟩ := eq_tprod_of_shpOf_eq hsd
  rw [hsab] at hsd
  have hinferFac := tprod_factor_dof_eq_of_shpOf_eq hsd
  obtain ⟨_s0, htof0', _⟩ := S.Ty.space_inv h1.ty
  have htof0 : Basis.tof b0 = .space (Basis.sof b0) :=
    Basis.tof_eq_space_sof_of_tof_space htof0'
  obtain ⟨t, htshape⟩ := h0.raw_shape_at_composite rfl hctx0 hle0 hc
  change denotTerm sigma n0 =
    .hil ⟨denotSpaceAux sigma []
      (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)), t⟩ at htshape
  obtain ⟨x1, hx1⟩ := h1.raw_shape_at_composite htof0 hctx1 hle1 hc
  obtain ⟨y0, hy0, hA0⟩ := trace0.result
  obtain ⟨y1, hy1, hA1⟩ := trace1.result
  change RawAgree orc sigma rho [] [] []
    (.space (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)))
    (.space (.tprod svMat0 svMat1))
    (denotBasis sigma (.tprod (.dual b0) b1))
    (denotTerm sigma n0) y0 at hA0
  rw [htof0] at hA1
  obtain ⟨a0, rfl⟩ := raw_composite_rawAgree_space_array hA0
  obtain ⟨a1, rfl⟩ := raw_composite_rawAgree_space_array hA1
  simp only [RawAgree] at hA0 hA1
  have hlen1 := LegacyAgree.length hA1
  have hc0 := LegacyAgree.coords hA0
  have hc1 := LegacyAgree.coords hA1
  have hB := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono h1.basisValid hle.2)
    hc.ctxWF_nl hc.envWF_nl
  have hB1 := denotBasis_atSpace_isListBasis sigma Gamma' b1
    (raw_basisValid_mono hbv hle.2)
    hc.ctxWF_nl hc.envWF_nl
  have hshapeOut : ValSpace.shpOf (orc rho [] []) svOut =
      srcShp sigma [] (Basis.sof b1) := by
    simpa only [htof1, RawAgreeDimsAt] using targetDims
  have hdimOut := ValSpace.raw_dof_eq_finrank_of_shpOf hshapeOut
  have hvsOut : ((denotBasis sigma b1).atSpace
      (denotSpaceAux sigma [] (Basis.sof b1))).length =
      ValSpace.dof (orc rho [] []) svOut :=
    hB1.finrank_eq.symm.trans hdimOut.symm
  have hsvShape : ValSpace.shpOf (orc rho [] []) sv =
      srcShp sigma [] (Basis.sof b0) :=
    ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hsvDim : ValSpace.dof (orc rho [] []) sv =
      Module.finrank ℝ (denotSpaceAux sigma [] (Basis.sof b0)).carrier :=
    ValSpace.raw_dof_eq_finrank_of_shpOf hsvShape
  have hvs : ((denotBasis sigma b0).atSpace
      (denotSpaceAux sigma [] (Basis.sof b0))).length =
      ValSpace.dof (orc rho [] []) sv :=
    hB.finrank_eq.symm.trans hsvDim.symm
  have hargDof : ValSpace.dof (orc rho [] []) svArg =
      ValSpace.dof (orc rho [] []) sv := hlen1.1.symm.trans hvs
  have hmatShape : ValSpace.shpOf (orc rho [] [])
      (.tprod svMat0 svMat1) =
      srcShp sigma []
        (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)) := by
    simpa only [Basis.tof, RawAgreeDimsAt] using trace0.dims
  simp only [ValSpace.shpOf_tprod, srcShp] at hmatShape
  have hmat0Rank : ValSpace.dof (orc rho [] []) svMat0 =
      Module.finrank ℝ
        (denotSpaceAux sigma [] (.dual (Basis.sof b0))).carrier :=
    (List.cons.inj hmatShape).1
  have hmat1Rank : ValSpace.dof (orc rho [] []) svMat1 =
      Module.finrank ℝ
        (denotSpaceAux sigma [] (Basis.sof b1)).carrier :=
    (List.cons.inj (List.cons.inj hmatShape).2).1
  have hdualRank : Module.finrank ℝ
      (denotSpaceAux sigma [] (.dual (Basis.sof b0))).carrier =
      Module.finrank ℝ
        (denotSpaceAux sigma [] (Basis.sof b0)).carrier :=
    Subspace.dual_finrank_eq
  have hmat0Dof : ValSpace.dof (orc rho [] []) svMat0 =
      ValSpace.dof (orc rho [] []) sv :=
    hmat0Rank.trans (hdualRank.trans hsvDim.symm)
  have hmat1Dof : ValSpace.dof (orc rho [] []) svMat1 =
      ValSpace.dof (orc rho [] []) svOut :=
    hmat1Rank.trans hdimOut.symm
  have hsa : ValSpace.dof (orc rho [] []) sa =
      ValSpace.dof (orc rho [] []) sv := hinferFac.1.trans hmat0Dof
  have hsb : ValSpace.dof (orc rho [] []) sb =
      ValSpace.dof (orc rho [] []) svOut := hinferFac.2.trans hmat1Dof
  have hD : (denotBasis sigma (.dual b0)).atSpace
      (denotSpaceAux sigma [] (.dual (Basis.sof b0))) =
      (denotSpaceAux sigma [] (Basis.sof b0)).dualOfList
        ((denotBasis sigma b0).atSpace
          (denotSpaceAux sigma [] (Basis.sof b0))) := by
    show BasisDenot.atSpace
      (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
      (denotBasis sigma (.dual b0)) = _
    simp only [denotBasis]
    exact BasisDenot.atSpace_vecs_self _ _
  have hT : (denotBasis sigma (.tprod (.dual b0) b1)).atSpace
      (denotSpaceAux sigma []
        (.tprod (.dual (Basis.sof b0)) (Basis.sof b1))) =
      HSpace.tprodOfLists
        (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
        (denotSpaceAux sigma [] (Basis.sof b1))
        ((denotSpaceAux sigma [] (Basis.sof b0)).dualOfList
          ((denotBasis sigma b0).atSpace
            (denotSpaceAux sigma [] (Basis.sof b0))))
        ((denotBasis sigma b1).atSpace
          (denotSpaceAux sigma [] (Basis.sof b1))) := by
    show BasisDenot.atSpace
      (HSpace.tprod
        (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
        (denotSpaceAux sigma [] (Basis.sof b1)))
      (denotBasis sigma (.tprod (.dual b0) b1)) = _
    rw [show denotBasis sigma (.tprod (.dual b0) b1) =
        BasisDenot.vecs
          (HSpace.tprod
            (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
            (denotSpaceAux sigma [] (Basis.sof b1)))
          (HSpace.tprodOfLists _ _
            ((denotBasis sigma (.dual b0)).atSpace
              (denotSpaceAux sigma [] (.dual (Basis.sof b0))))
            ((denotBasis sigma b1).atSpace
              (denotSpaceAux sigma [] (Basis.sof b1))))
        from by simp only [denotBasis]; rfl, hD]
    exact BasisDenot.atSpace_vecs_self _ _
  rw [hT] at hc0
  rw [htshape, DVal.atSpace_hil_self] at hc0
  rw [hx1, DVal.atSpace_hil_self] at hc1
  rw [hargDof] at hc1
  have hj0 : forall j : Fin (ValSpace.dof (orc rho [] []) sv),
      (j : Nat) < ((denotBasis sigma b0).atSpace
        (denotSpaceAux sigma [] (Basis.sof b0))).length :=
    fun j => by rw [hvs]; exact j.isLt
  have hm0 : (denotTerm sigma n0).matchesShape
      (.hil (HSpace.tprod
        (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
        (denotSpaceAux sigma [] (Basis.sof b1)))) := by
    rw [htshape]
    exact DVal.matchesShape_hil_rfl _ _
  have hL : (denotTerm sigma n0).asLinMap
      (denotSpace sigma (Basis.sof b0))
      (denotSpace sigma (Basis.sof b1)) =
      dualTensorHom ℝ (denotSpaceAux sigma [] (Basis.sof b0)).carrier
        (denotSpaceAux sigma [] (Basis.sof b1)).carrier t := by
    rw [DVal.asLinMap_eq_of_matchesShape hm0]
    congr 1
    change DVal.atSpace
      (denotSpaceAux sigma []
        (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)))
      (denotTerm sigma n0) = t
    rw [htshape, DVal.atSpace_hil_self]
  have hR : (denotTerm sigma n1).atSpace
      (denotSpace sigma (Basis.sof b0)) = x1 := by
    change DVal.atSpace (denotSpaceAux sigma [] (Basis.sof b0))
      (denotTerm sigma n1) = x1
    rw [hx1, DVal.atSpace_hil_self]
  have innerResult : RawResultAgree orc sigma rho [] [] []
      (Basis.tof b1) (.space svOut) (denotBasis sigma b1)
      (denotTerm sigma
        (.appL (Basis.sof b0) (Basis.sof b1) n0 n1))
      (denotValB_semS orc rho [] [] (.ttv sv env0 env1)) := by
    rw [denotValB_semS.eq_12, hy0, hy1]
    have hshape : ValueShape.ttv (orc rho [] []) sv
        (ValExpr.inferSpaceCtx [] env0) (ValExpr.inferSpaceCtx [] env1) a0 a1 := by
      simp only [ValueShape.ttv, ValueShape.pair, hsab, ValSpace.dof_tprod]
      refine ⟨⟨?_, hlen1.2.trans hdof1.symm⟩, hsa, hdof1.trans hargDof⟩
      simpa only [ValSpace.dof_tprod, hinferFac.1, hinferFac.2] using
        (LegacyAgree.length hA0).2
    simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hshape]
    refine ⟨_, rfl, ?_⟩
    simp only [ValExpr.inferSpaceCtx, hsab, ValValSem.arrayOf]
    rw [htof1]
    simp only [RawAgree]
    rw [LegacyAgree.space_iff]
    refine ⟨hvsOut, ?_, ?_⟩
    · rw [FlatArray.length_ofFn, hsb]
    · rw [denotTerm_appL, hL, hR]
      change DVal.atSpace (denotSpaceAux sigma [] (Basis.sof b1))
        (DVal.hil ⟨denotSpaceAux sigma [] (Basis.sof b1),
          dualTensorHom ℝ
            (denotSpaceAux sigma [] (Basis.sof b0)).carrier
            (denotSpaceAux sigma [] (Basis.sof b1)).carrier t x1⟩) = _
      rw [DVal.atSpace_hil_self]
      rw [ValSpace.dof_tprod, hmat0Dof, hmat1Dof] at hc0
      have hc0' : t =
          (∑ k : Fin (ValSpace.dof (orc rho [] []) sv *
              ValSpace.dof (orc rho [] []) svOut),
            a0.get k •
              (HSpace.tprodOfLists
                (HSpace.dual
                  (denotSpaceAux sigma [] (Basis.sof b0)))
                (denotSpaceAux sigma [] (Basis.sof b1))
                ((denotSpaceAux sigma [] (Basis.sof b0)).dualOfList
                  ((denotBasis sigma b0).atSpace
                    (denotSpaceAux sigma [] (Basis.sof b0))))
                ((denotBasis sigma b1).atSpace
                  (denotSpaceAux sigma [] (Basis.sof b1)))).getD k
                  (0 : Module.Dual ℝ
                    (denotSpaceAux sigma [] (Basis.sof b0)).carrier ⊗[ℝ]
                    (denotSpaceAux sigma [] (Basis.sof b1)).carrier)) := hc0
      rw [hc0']
      rw [raw_composite_tprod_double_sum _ _ _ _
        ((HSpace.dualOfList_length _ _).trans hvs) hvsOut _
        (fun i j => a0.get
          (i * ValSpace.dof (orc rho [] []) svOut + j)) ?_]
      swap
      · intro k
        show a0.get k = a0.get
          (k / ValSpace.dof (orc rho [] []) svOut *
            ValSpace.dof (orc rho [] []) svOut +
            k % ValSpace.dof (orc rho [] []) svOut)
        rw [Nat.div_add_mod']
      simp only [map_sum, map_smul, LinearMap.sum_apply,
        LinearMap.smul_apply, dualTensorHom_apply]
      rw [Finset.sum_comm, hc1]
      rw [Fin.sum_univ_eq_sum_range (fun j =>
        (FlatArray.ofFn (ValSpace.dof (orc rho [] []) sb) _).get j •
          ((denotBasis sigma b1).atSpace
            (denotSpaceAux sigma [] (Basis.sof b1))).getD j 0)]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := Finset.mem_range.mp hj
      rw [FlatArray.get_ofFn_lt _ _ _ (by rw [hsb]; exact hj'),
        if_neg (by rw [hsb]; exact Nat.not_le.mpr hj'),
        Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hi'' : i < ((denotBasis sigma b0).atSpace
          (denotSpaceAux sigma [] (Basis.sof b0))).length := by
        rw [hvs]
        exact hi'
      simp only [map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_eq_single
        (⟨i, hi'⟩ : Fin (ValSpace.dof (orc rho [] []) sv))]
      · rw [raw_composite_dualOfList_delta hB hi'' (hj0 _),
          if_pos rfl, hsb, Nat.mul_comm]
        simp only [smul_smul, mul_one]
      · intro l _ hli
        rw [raw_composite_dualOfList_delta hB hi'' (hj0 l),
          if_neg (fun h => hli (Fin.ext h.symm))]
        simp
      · intro h
        exact absurd (Finset.mem_univ _) h
  have result := (RawNonBetaValueKernel.holds orc).reshape
    targetDims targetDims innerResult
  exact ⟨by simpa only [ValExpr.reshapBase] using result, targetDims⟩

end GLang
