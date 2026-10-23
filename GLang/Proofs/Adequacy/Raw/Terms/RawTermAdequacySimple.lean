import GLang.Proofs.Adequacy.Raw.RawSpaceAdequacyCore
import GLang.Proofs.Adequacy.Foundations.AgreeBasics
import GLang.Proofs.Source.BasisSoundness

/-!
# Elementary raw term-adequacy arms

This module contains the residual-free ordinary-trace proofs for the seven
elementary `S.Term` constructors.  It stays on the raw current stack: the
only recursive term hypotheses are `RawMTermTraceSubctx`, and every conclusion
also carries the exact-basis dimensions supplied by `RawMTyAtSubctx`.
-/

namespace GLang

open scoped BigOperators TensorProduct
open Basis (BasisValid)

/-! ## Source well-formedness exposed by the raw telescope -/

private theorem raw_simple_basis_fv_subset_of_openVar_body
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

private theorem raw_simple_basisValid_fv_subset_keys
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
      apply raw_simple_basis_fv_subset_of_openVar_body (L := L)
      intro y hy z hz
      have hzctx := ihbody y hy hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hzctx
      exact hzctx

theorem RawConsistent.ctxWF_raw
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
          (raw_simple_basisValid_fv_subset_keys hb)
      exact ih.insert_nl hx.1 hx.2 hfv
  | extend_rep hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc
      hxs hden hresult hdims hanchor ih =>
      exact ih

/-- The source environment stored by `RawConsistent` realizes the full linear
and nonlinear telescope. -/
theorem RawConsistent.envWF_raw
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
      have hctx := hc.ctxWF_raw
      have hsof : Basis.sof b = s := Basis.sof_of_tof_space htof
      have hvalid : SValid Gamma s := hsof ▸ hb.sof_valid.some
      have hshape : xs.matchesShape (.hil (denotSpace sigma s)) := by
        simpa only [htof, denotTy, denotTyAux] using hxs
      obtain ⟨y, rfl⟩ := DVal.matchesShape_hil_eq hshape
      exact ih.extend_lin hctx hx.2 hvalid y
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hc hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs
      hden hresult hdims _hanchor ih =>
      have hctx := hc.ctxWF_raw
      have hfv : Ty.fv (Basis.tof b) ⊆ Gamma.keys :=
        (Basis.fv_tof_subset b).trans
          (raw_simple_basisValid_fv_subset_keys hb)
      have hxKeys : x ∉ Gamma.keys := fun hm => hx.2 (Finmap.mem_keys.mp hm)
      have hxfv : x ∉ Ty.fv (Basis.tof b) := fun hm => hxKeys (hfv hm)
      let y := (denotTy sigma (Basis.tof b)).extract xs
      have hembed : (denotTy sigma (Basis.tof b)).embed y = xs :=
        HType.embed_extract_of_matchesShape hxs
      rw [← hembed]
      exact ih.bind_nl hctx hx.1 hx.2 hxfv y
  | extend_rep hc hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc
      hxs hden hresult hdims hanchor ih =>
      exact ih

/-! ## Typing transport and source shapes -/

private theorem raw_hasType_demote
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

private theorem raw_hasType_mono_nl_aux
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
          rw [Finmap.lookup_eq_none.mpr hx, Finmap.lookup_eq_none.mpr hx']
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
          · rw [Finmap.lookup_insert_of_ne _ hz, Finmap.lookup_erase_ne hz]
        rw [hGamma] at h2
        exact ⟨h2⟩
      · refine ih Gamma Gamma' h hle hctx ?_
        intro x hx hxGamma
        rcases Finset.mem_insert.mp (hS x hx hxGamma) with hxy | hxS
        · exact absurd ⟨hxy ▸ hx, hxy ▸ hxGamma⟩ hy
        · exact hxS

private theorem raw_hasType_mono_nl
    {Delta : LCtx} {Gamma Gamma' : NLCtx} {e : Term} {tau : Ty}
    (h : Nonempty (HasType Delta Gamma e tau))
    (hle : NLCtxIncl Gamma Gamma')
    (hctx : Graded.CtxDisj Delta Gamma') :
    Nonempty (HasType Delta Gamma' e tau) :=
  raw_hasType_mono_nl_aux (Gamma'.keys \ Gamma.keys) Gamma Gamma' h hle hctx
    (fun x hx hxGamma => Finset.mem_sdiff.mpr
      ⟨Finmap.mem_keys.mpr hx, fun hm => hxGamma (Finmap.mem_keys.mp hm)⟩)

private theorem raw_hasType_ctxIncl_aux
    {Delta' : LCtx} {Gamma' : NLCtx} {e : Term} {tau : Ty}
    (hwf : CtxWF Delta' Gamma') (S : Finset Name) :
    forall (Delta : LCtx) (Gamma : NLCtx),
      Nonempty (HasType Delta Gamma e tau) -> Graded.CtxDisj Delta Gamma ->
      RawCtxIncl Delta Gamma Delta' Gamma' ->
      (forall x, x ∈ Delta -> x ∈ Gamma' -> x ∈ S) ->
      exists Delta1 : LCtx,
        (forall x s, Delta1.lookup x = some s -> Delta'.lookup x = some s) ∧
        Nonempty (HasType Delta1 Gamma' e tau) := by
  induction S using Finset.induction_on with
  | empty =>
      intro Delta Gamma h hctx hle hS
      have hctx' : Graded.CtxDisj Delta Gamma' := fun x hx hm =>
        Finset.notMem_empty x (hS x hx hm)
      refine ⟨Delta, ?_, raw_hasType_mono_nl h hle.2 hctx'⟩
      intro x s hx
      rcases hle.1 x s hx with hlin | hnl
      · exact hlin
      · exact absurd (Finmap.mem_of_lookup_eq_some hnl)
          (hctx' x (Finmap.mem_of_lookup_eq_some hx))
  | insert y S' hyS ih =>
      intro Delta Gamma h hctx hle hS
      by_cases hy : y ∈ Delta ∧ y ∈ Gamma'
      · obtain ⟨s, hs⟩ := Finmap.mem_iff.mp hy.1
        have hyDelta' : y ∉ Delta' := fun hm => hwf.disjoint y hm hy.2
        have hGamma'y : Gamma'.lookup y = some (.space s) := by
          rcases hle.1 y s hs with hlin | hnl
          · exact absurd (Finmap.mem_of_lookup_eq_some hlin) hyDelta'
          · exact hnl
        have hsplit : Delta = Finmap.singleton y s ∪ Delta.erase y := by
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
        have hdisj : Finmap.Disjoint (Finmap.singleton y s) (Delta.erase y) :=
          fun z hz hm => (Finmap.mem_erase.mp hm).1
            ((Finmap.mem_singleton _ _ _).mp hz)
        have hctx0 : Graded.CtxDisj
            (Finmap.singleton y s ∪ Delta.erase y) Gamma := by
          rw [← hsplit]
          exact hctx
        have h0 : Nonempty
            (HasType (Finmap.singleton y s ∪ Delta.erase y) Gamma e tau) := by
          rw [← hsplit]
          exact h
        have h' := raw_hasType_demote hdisj hctx0 h0
        refine ih (Delta.erase y) _ h' ?_ ⟨?_, ?_⟩ ?_
        · intro z hz hm
          obtain ⟨hzy, hzDelta⟩ := Finmap.mem_erase.mp hz
          rcases Finmap.mem_union.mp hm with hl | hg
          · exact hzy ((Finmap.mem_singleton _ _ _).mp
              ((LCtx.mem_toNL_iff _ z).mp hl))
          · exact hctx z hzDelta hg
        · intro z s' hz
          have hzy : z ≠ y :=
            (Finmap.mem_erase.mp (Finmap.mem_of_lookup_eq_some hz)).1
          exact hle.1 z s' (by
            rw [← Finmap.lookup_erase_ne hzy]
            exact hz)
        · intro z tau' hz
          by_cases hzl : z ∈ LCtx.toNL (Finmap.singleton y s)
          · rw [Finmap.lookup_union_left hzl] at hz
            have hzy : z = y := (Finmap.mem_singleton _ _ _).mp
              ((LCtx.mem_toNL_iff _ z).mp hzl)
            subst hzy
            have hl := LCtx.toNL_lookup (Finmap.singleton z s) z s
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

private theorem raw_hasType_ctxIncl
    {Delta Delta' : LCtx} {Gamma Gamma' : NLCtx}
    {e : Term} {tau : Ty}
    (hwf : CtxWF Delta' Gamma')
    (h : Nonempty (HasType Delta Gamma e tau))
    (hctx : Graded.CtxDisj Delta Gamma)
    (hle : RawCtxIncl Delta Gamma Delta' Gamma') :
    exists Delta1 : LCtx,
      (forall x s, Delta1.lookup x = some s -> Delta'.lookup x = some s) ∧
      Nonempty (HasType Delta1 Gamma' e tau) :=
  raw_hasType_ctxIncl_aux hwf Delta.keys Delta Gamma h hctx hle
    (fun x hx _ => Finmap.mem_keys.mpr hx)

private theorem S.Term.raw_shape_at
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
    raw_hasType_ctxIncl hc.raw.ctxWF_raw he.hasType hctx hle
  have hs := (soundness ht
    (hc.raw.ctxWF_raw.of_sub_Δ hDelta) (hc.raw.envWF_raw.of_sub_Δ hDelta)).1
  rw [htof] at hs
  exact DVal.matchesShape_hil_eq hs

/-! ## Context-inclusion bookkeeping -/

private theorem RawCtxIncl.union_left
    {Delta0 Delta1 Delta' : LCtx} {Gamma Gamma' : NLCtx}
    (h : RawCtxIncl (Delta0 ∪ Delta1) Gamma Delta' Gamma') :
    RawCtxIncl Delta0 Gamma Delta' Gamma' := by
  refine ⟨?_, h.2⟩
  intro x s hx
  apply h.1 x s
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)]
  exact hx

private theorem RawCtxIncl.union_right
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

private theorem raw_simple_not_frame_of_tof_space
    {b : Basis} {s : GLang.Space} (htof : Basis.tof b = .space s) :
    forall b0 b1, b ≠ .frame b0 b1 := by
  intro b0 b1 h
  subst b
  simp only [Basis.tof, reduceCtorEq] at htof

private theorem RawAgree.space_array_raw
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {s : GLang.Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : RawAgree orc sigma rho Ds Gv Dv
      (.space s) (.space sv) B x y) : exists a, y = .array a := by
  cases y with
  | array a => exact ⟨a, rfl⟩
  | fn T f => simpa only [RawAgree] using h

private theorem S.TyAt.space_data_raw
    {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {sv : ValSpace}
    (h : S.TyAt Gamma Psi b (.space sv)) :
    Basis.tof b = .space (Basis.sof b) ∧ BasisValid Gamma b := by
  obtain ⟨s, htofS, _hspace⟩ := h.toTy.space_inv
  refine ⟨?_, h.basisValid⟩
  exact Basis.tof_eq_space_sof_of_tof_space htofS

private theorem raw_simple_dualOfList_delta
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

private theorem raw_simple_fin_sum_of_eq_one
    {M : Type} [AddCommMonoid M] {n : Nat}
    (h : n = 1) (f : Fin n -> M) :
    (∑ i, f i) = f ⟨0, by omega⟩ := by
  subst h
  simp

private theorem raw_simple_agree_one_intro
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem} {x0 : ℝ}
    {a : FlatArray} (hlen : a.length = 1) (hx : x0 = a.get 0) :
    LegacyAgree orc sigma rho [] [] [] (.space .real) (.space .real)
      (denotBasis sigma .one) (.hil ⟨HSpace.real, x0⟩) (.array a) := by
  rw [LegacyAgree.space_iff]
  simp only [denotSpaceAux, ValSpace.dof_real]
  refine ⟨?_, hlen, ?_⟩
  · simp [denotBasis, BasisDenot.atSpace_vecs_self]
  · rw [DVal.atSpace_hil_self,
      raw_simple_fin_sum_of_eq_one (ValSpace.dof_real _)]
    simp only [denotBasis, BasisDenot.atSpace_vecs_self]
    simp
    rw [hx]
    change a.get 0 = a.get 0 * 1
    ring

/-! ## Elementary trace arms -/

theorem arm_var_lin
    {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {s : Space} {tauV : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (_htof : Basis.tof b = .space s)
    (_hbv : BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b tauV)
    (ihTy : RawMTyAtSubctx orc Gamma Psi b tauV) :
    RawMTermTraceSubctx orc (Finmap.singleton x s) Gamma Psi
      (.var x) b v tauV := by
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have hlookup' : EvalCtx.lookup Psi' (x, b) = some v :=
    hsub (x, b) v hlookup
  obtain ⟨tauStored, xs, Gamma0, Psi0, _hsigma, hStoredTy,
      _hinferSpace, hresult, hdimsStored⟩ :=
    hc.raw.lookup_current_result hirr hlookup'
  have hdimsTarget : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof b) tauV (denotBasis sigma b) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hshape : ValSoundOfDenot.ValTy.SameShape tauStored tauV :=
    evalT_sameShape hStoredTy (hTy.mono hsub).toEvalT
  obtain ⟨out, hout, hagree⟩ := hresult
  exact ⟨⟨out, hout,
    (RawNonBetaValueKernel.holds orc).realize
      hshape hdimsStored hdimsTarget hagree⟩, hdimsTarget⟩

theorem arm_promote
    {orc : FFSOracleSem}
    {Delta lin : LCtx} {Gamma Gamma'' : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (_hdDelta : Finmap.Disjoint lin Delta)
    (hdGamma : Finmap.Disjoint lin.toNL Gamma'')
    (_hfr : PromoteFresh lin Delta Gamma)
    (hleP : NLCtxIncl Gamma Gamma'')
    (_ht : Nonempty (HasType Delta (lin.toNL ∪ Gamma'') e (Basis.tof b)))
    (_hbv : BasisValid (lin.toNL ∪ Gamma'') b)
    (_hTy : S.TyAt (lin.toNL ∪ Gamma'') Psi b tauV)
    (_he : S.Term (lin ∪ Delta) Gamma Psi e b v tauV)
    (ih : RawMTermTraceSubctx orc (lin ∪ Delta) Gamma Psi e b v tauV) :
    RawMTermTraceSubctx orc Delta (lin.toNL ∪ Gamma'') Psi e b v tauV := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hctxP : Graded.CtxDisj (lin ∪ Delta) Gamma := fun x hxD hxG =>
    Graded.CtxDisj.promote_inner hctx hdGamma x hxD (hleP.mem_of hxG)
  apply ih hsub hctxP rho Delta' Gamma' sigma GammaV ?_ hc
  refine ⟨?_, ?_⟩
  · intro x s hx
    by_cases hmem : x ∈ lin
    · rw [Finmap.lookup_union_left hmem] at hx
      have hnl : (lin.toNL ∪ Gamma'').lookup x = some (.space s) := by
        have hl := LCtx.toNL_lookup lin x s hx
        rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hl)]
        exact hl
      exact Or.inr (hle.2 x _ hnl)
    · rw [Finmap.lookup_union_right hmem] at hx
      exact hle.1 x s hx
  · intro x tau hx
    have hx'' : Gamma''.lookup x = some tau := hleP x tau hx
    have hnot : x ∉ lin.toNL := fun hm =>
      hdGamma x hm (Finmap.mem_of_lookup_eq_some hx'')
    apply hle.2 x tau
    rw [Finmap.lookup_union_right hnot]
    exact hx''

theorem arm_add
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e0 e1 : Term} {b : Basis} {v0 v1 : ValExpr}
    {sv sv0 sv1 : ValSpace}
    (htof : Basis.tof b = .space (Basis.sof b))
    (_ht : Nonempty (HasType Delta Gamma (.add e0 e1) (Basis.tof b)))
    (hbv : BasisValid Gamma b)
    (_hTy : S.TyAt Gamma Psi b (.space sv))
    (he0 : S.Term Delta Gamma Psi e0 b v0 (.space sv0))
    (he1 : S.Term Delta Gamma Psi e1 b v1 (.space sv1))
    (ihTy : RawMTyAtSubctx orc Gamma Psi b (.space sv))
    (ih0 : RawMTermTraceSubctx orc Delta Gamma Psi
      e0 b v0 (.space sv0))
    (ih1 : RawMTermTraceSubctx orc Delta Gamma Psi
      e1 b v1 (.space sv1)) :
    RawMTermTraceSubctx orc Delta Gamma Psi (.add e0 e1) b
      (.vadd sv v0 v1) (.space sv) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof b) (.space sv) (denotBasis sigma b) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have trace0 := ih0 hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have trace1 := ih1 hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨y0, hy0, hA0⟩ := trace0.result
  obtain ⟨y1, hy1, hA1⟩ := trace1.result
  rw [htof] at hA0 hA1
  obtain ⟨a0, rfl⟩ := RawAgree.space_array_raw hA0
  obtain ⟨a1, rfl⟩ := RawAgree.space_array_raw hA1
  have hA0' : LegacyAgree orc sigma rho [] [] [] (.space (Basis.sof b))
      (.space sv0) (denotBasis sigma b)
      (denotTerm sigma e0) (.array a0) := by
    simpa only [RawAgree, LegacyAgree] using hA0
  have hA1' : LegacyAgree orc sigma rho [] [] [] (.space (Basis.sof b))
      (.space sv1) (denotBasis sigma b)
      (denotTerm sigma e1) (.array a1) := by
    simpa only [RawAgree, LegacyAgree] using hA1
  obtain ⟨x0, hx0⟩ := S.Term.raw_shape_at he0 htof hctx hle hc
  obtain ⟨x1, hx1⟩ := S.Term.raw_shape_at he1 htof hctx hle hc
  have hlb := denotBasis_isListBasis
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
    (raw_simple_not_frame_of_tof_space htof)
  have hshape : ValSpace.shpOf (orc rho [] []) sv =
      srcShp sigma [] (Basis.sof b) := by
    simpa only [htof, RawAgreeDimsAt] using targetDims
  have hdim := ValSpace.raw_dof_eq_finrank_of_shpOf hshape
  have hB : ((denotBasis sigma b).atSpace
      (denotSpace sigma (Basis.sof b))).length =
      ValSpace.dof (orc rho [] []) sv := by
    rw [hdim, hlb.finrank_eq]
  have hlen0 := LegacyAgree.length hA0'
  have hlen1 := LegacyAgree.length hA1'
  have hdof0 : ValSpace.dof (orc rho [] []) sv0 =
      ValSpace.dof (orc rho [] []) sv := hlen0.1.symm.trans hB
  have hdof1 : ValSpace.dof (orc rho [] []) sv1 =
      ValSpace.dof (orc rho [] []) sv := hlen1.1.symm.trans hB
  have ha0len : a0.length = ValSpace.dof (orc rho [] []) sv :=
    hlen0.2.trans hdof0
  have ha1len : a1.length = ValSpace.dof (orc rho [] []) sv :=
    hlen1.2.trans hdof1
  have hc0 := LegacyAgree.coords hA0'
  have hc1 := LegacyAgree.coords hA1'
  rw [hdof0] at hc0
  rw [hdof1] at hc1
  have hm0 : (denotTerm sigma e0).matchesShape
      (.hil (denotSpace sigma (Basis.sof b))) := by
    rw [hx0]
    exact DVal.matchesShape_hil_rfl _ _
  have hm1 : (denotTerm sigma e1).matchesShape
      (.hil (denotSpace sigma (Basis.sof b))) := by
    rw [hx1]
    exact DVal.matchesShape_hil_rfl _ _
  refine ⟨⟨.array (FlatArray.zipWith (ValSpace.dof (orc rho [] []) sv)
      (fun x y => x + y) a0 a1 ha0len ha1len), ?_, ?_⟩, targetDims⟩
  · rw [denotValB_semS.eq_6, hy0, hy1]
    simp only [ValValSem.bindArrays, ValValSem.bindArray,
      ha0len, ha1len, dite_true]
  · rw [htof]
    have hlegacy : LegacyAgree orc sigma rho [] [] []
        (.space (Basis.sof b)) (.space sv) (denotBasis sigma b)
        (denotTerm sigma (.add e0 e1))
        (.array (FlatArray.zipWith (ValSpace.dof (orc rho [] []) sv)
          (fun x y => x + y) a0 a1 ha0len ha1len)) := by
      rw [LegacyAgree.space_iff]
      refine ⟨hB, rfl, ?_⟩
      change ((denotTerm sigma e0).addAt (denotTerm sigma e1)).atSpace _ = _
      rw [DVal.addAt_atSpace_eq_add hm0 hm1, hc0, hc1,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← add_smul]
      rw [FlatArray.zipWith, FlatArray.get_ofFn_lt _ _ _ i.isLt]
    simpa only [RawAgree, LegacyAgree] using hlegacy

theorem arm_appI_lin
    {orc : FFSOracleSem}
    {Delta0 Delta1 : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 : Basis} {n0 n1 : Term} {env0 env1 : ValExpr}
    {sv svFun svArg : ValSpace}
    (hdisj : Finmap.Disjoint Delta0 Delta1)
    (_ht : Nonempty (HasType (Delta0 ∪ Delta1) Gamma
      (.appI (Basis.sof b0) n0 n1) (Basis.tof .one)))
    (_hsv : S.Space Gamma Psi (Basis.sof b0) sv)
    (_hTy : S.TyAt Gamma Psi .one (.space .real))
    (h0 : S.Term Delta0 Gamma Psi n0 (.dual b0) env0 (.space svFun))
    (h1 : S.Term Delta1 Gamma Psi n1 b0 env1 (.space svArg))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv)
    (ihTy : RawMTyAtSubctx orc Gamma Psi .one (.space .real))
    (ih0 : RawMTermTraceSubctx orc Delta0 Gamma Psi
      n0 (.dual b0) env0 (.space svFun))
    (ih1 : RawTermDofFactsSubctx orc Delta1 Gamma Psi
      n1 b0 env1 (.space svArg)) :
    RawMTermTraceSubctx orc (Delta0 ∪ Delta1) Gamma Psi
      (.appI (Basis.sof b0) n0 n1) .one
      (.ttv sv
        (.reshap env0 (.space (.tprod sv .real)) (.space sv)) env1)
      (.space .real) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hle0 := RawCtxIncl.union_left hle
  have hle1 := RawCtxIncl.union_right hdisj hle
  have hctx0 := Graded.CtxDisj.of_union_left hctx
  have hctx1 := Graded.CtxDisj.of_union_right hctx
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof .one) (.space .real) (denotBasis sigma .one) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have trace0 := ih0 hsub hctx0 rho Delta' Gamma' sigma GammaV hle0 hc
  have trace1 := ih1.trace hsub hctx1 rho Delta' Gamma' sigma GammaV hle1 hc
  have hdof1 : ValSpace.dof (orc rho [] []) (ValExpr.inferSpaceCtx [] env1) =
      ValSpace.dof (orc rho [] []) svArg :=
    dof_eq_of_shpOf_eq (ih1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  obtain ⟨y0, hy0, hA0⟩ := trace0.result
  obtain ⟨y1, hy1, hA1⟩ := trace1.result
  obtain ⟨htof0, hb0v⟩ := S.TyAt.space_data_raw h1.tyAt
  rw [show Basis.tof (.dual b0) =
    .space (.dual (Basis.sof b0)) from rfl] at hA0
  rw [htof0] at hA1
  obtain ⟨a0, rfl⟩ := RawAgree.space_array_raw hA0
  obtain ⟨a1, rfl⟩ := RawAgree.space_array_raw hA1
  have hA0' : LegacyAgree orc sigma rho [] [] []
      (.space (.dual (Basis.sof b0))) (.space svFun)
      (denotBasis sigma (.dual b0)) (denotTerm sigma n0) (.array a0) := by
    simpa only [RawAgree, LegacyAgree] using hA0
  have hA1' : LegacyAgree orc sigma rho [] [] []
      (.space (Basis.sof b0)) (.space svArg)
      (denotBasis sigma b0) (denotTerm sigma n1) (.array a1) := by
    simpa only [RawAgree, LegacyAgree] using hA1
  have hB := denotBasis_isListBasis
    (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
    (raw_simple_not_frame_of_tof_space htof0)
  obtain ⟨phi, hphi⟩ := S.Term.raw_shape_at h0 rfl hctx0 hle0 hc
  obtain ⟨x1, hx1⟩ := S.Term.raw_shape_at h1 htof0 hctx1 hle1 hc
  have hphi' : denotTerm sigma n0 =
      .hil ⟨denotSpaceAux sigma [] (.dual (Basis.sof b0)), phi⟩ := by
    simpa only [denotSpace, Basis.sof] using hphi
  have hlen0 := LegacyAgree.length hA0'
  have hlen1 := LegacyAgree.length hA1'
  have hc0 := LegacyAgree.coords hA0'
  have hc1 := LegacyAgree.coords hA1'
  have hD : (denotBasis sigma (.dual b0)).atSpace
      (denotSpace sigma (.dual (Basis.sof b0))) =
      (denotSpace sigma (Basis.sof b0)).dualOfList
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0))) := by
    show BasisDenot.atSpace (HSpace.dual
      (denotSpace sigma (Basis.sof b0)))
      (denotBasis sigma (.dual b0)) = _
    simp only [denotBasis]
    exact BasisDenot.atSpace_vecs_self _ _
  rw [hD] at hc0
  rw [hphi', DVal.atSpace_hil_self] at hc0
  rw [hx1, DVal.atSpace_hil_self] at hc1
  have hsvShape : ValSpace.shpOf (orc rho [] []) sv =
      srcShp sigma [] (Basis.sof b0) :=
    ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hsvDim : ValSpace.dof (orc rho [] []) sv =
      Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier :=
    ValSpace.raw_dof_eq_finrank_of_shpOf hsvShape
  have hvs : ((denotBasis sigma b0).atSpace
      (denotSpace sigma (Basis.sof b0))).length =
      ValSpace.dof (orc rho [] []) sv :=
    hB.finrank_eq.symm.trans hsvDim.symm
  have hfunDof : ValSpace.dof (orc rho [] []) svFun =
      ValSpace.dof (orc rho [] []) sv :=
    hlen0.1.symm.trans ((congrArg List.length hD).trans
      ((HSpace.dualOfList_length _ _).trans hvs))
  have hargDof : ValSpace.dof (orc rho [] []) svArg =
      ValSpace.dof (orc rho [] []) sv := hlen1.1.symm.trans hvs
  rw [hfunDof] at hc0
  rw [hargDof] at hc1
  have hm0 : (denotTerm sigma n0).matchesShape
      (.hil (HSpace.dual (denotSpace sigma (Basis.sof b0)))) := by
    rw [hphi']
    exact DVal.matchesShape_hil_rfl _ _
  have hL : (denotTerm sigma n0).asLinFunctional
      (denotSpace sigma (Basis.sof b0)) = phi := by
    rw [DVal.asLinFunctional_eq_of_matchesShape hm0]
    change (denotTerm sigma n0).atSpace
      (denotSpace sigma (.dual (Basis.sof b0))) = phi
    rw [hphi', DVal.atSpace_hil_self]
  have hR : (denotTerm sigma n1).atSpace
      (denotSpace sigma (Basis.sof b0)) = x1 := by
    rw [hx1, DVal.atSpace_hil_self]
  have ha0len : a0.length =
      ValSpace.dof (orc rho [] []) (.tprod sv .real) := by
    simpa [ValSpace.dof_tprod, ValSpace.dof_real, hfunDof] using hlen0.2
  have ha0src : a0.length = ValSpace.dof (orc rho [] []) sv := by
    exact hlen0.2.trans hfunDof
  have hsourceTarget : ValSpace.dof (orc rho [] []) sv =
      ValSpace.dof (orc rho [] []) (.tprod sv .real) := by
    simp [ValSpace.dof_tprod, ValSpace.dof_real]
  have hreshape : denotValB_semS orc rho [] []
      (.reshap env0 (.space (.tprod sv .real)) (.space sv)) =
      .ok (.array a0) :=
    denotValB_semS_reshap_spaces_ok orc rho [] [] env0
      (.tprod sv .real) sv a0 hy0 ha0src hsourceTarget
  refine ⟨?_, targetDims⟩
  unfold RawResultAgree
  rw [denotValB_semS.eq_12, hreshape, hy1]
  have hshape : ValueShape.ttv (orc rho [] []) sv
      (ValExpr.inferSpaceCtx [] (.reshap env0 (.space (.tprod sv .real)) (.space sv)))
      (ValExpr.inferSpaceCtx [] env1) a0 a1 := by
    simp only [ValueShape.ttv, ValueShape.pair, ValExpr.inferSpaceCtx, ValTy.spaceOf]
    exact ⟨⟨ha0len, hlen1.2.trans hdof1.symm⟩, True.intro, hdof1.trans hargDof⟩
  simp only [ValValSem.bindArrays, ValValSem.bindArray, if_pos hshape]
  refine ⟨_, rfl, ?_⟩
  simp only [ValExpr.inferSpaceCtx, ValTy.spaceOf,
    ValValSem.arrayOf, ValSpace.dof_real]
  rw [denotTerm_appI, hL, hR]
  simp only [Basis.tof, RawAgree]
  refine raw_simple_agree_one_intro rfl ?_
  rw [FlatArray.get_ofFn_lt _ _ _ Nat.one_pos]
  simp only [ge_iff_le, Nat.not_succ_le_zero, if_false, Nat.one_mul,
    Nat.add_zero, ValSpace.dof_tprod, ValSpace.dof_real, Nat.mul_one]
  rw [hc0, hc1, ← Fin.sum_univ_eq_sum_range]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, smul_eq_mul]
  have hj : forall j : Fin (ValSpace.dof (orc rho [] []) sv),
      (j : Nat) < ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))).length :=
    fun j => by rw [hvs]; exact j.isLt
  apply Finset.sum_congr rfl
  intro i _
  change a1.get ↑i *
      (∑ i' : Fin (ValSpace.dof (orc rho [] []) sv),
        a0.get ↑i' •
          ((denotSpace sigma (Basis.sof b0)).dualOfList
            ((denotBasis sigma b0).atSpace
              (denotSpace sigma (Basis.sof b0)))).getD ↑i'
            (0 : (denotSpace sigma (Basis.sof b0)).carrier →ₗ[ℝ] ℝ) :
            (denotSpace sigma (Basis.sof b0)).carrier →ₗ[ℝ] ℝ)
        (((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0))).getD ↑i 0) =
      a0.get ↑i * a1.get ↑i
  rw [LinearMap.sum_apply, Finset.mul_sum]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [raw_simple_dualOfList_delta hB (hj i) (hj i), if_pos rfl]
    ring
  · intro j _ hji
    rw [raw_simple_dualOfList_delta hB (hj j) (hj i),
      if_neg (fun h => hji (Fin.ext h))]
    ring
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## Standard inner-product trace -/

private theorem raw_simple_fin_sum_cast_of_eq
    {M : Type} [AddCommMonoid M] {n m : Nat}
    (h : n = m) (f : Fin n -> M) :
    (∑ i, f i) = ∑ i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  rfl

private theorem raw_simple_sum_range_mul_div_mod
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

private theorem raw_simple_dualOfList_getD_eq_dualVec
    (V : HSpace) (vs : List V.carrier) {i : Nat}
    (hi : i < vs.length) :
    (V.dualOfList vs).getD i 0 = V.dualVec vs ⟨i, hi⟩ := by
  have hdualLen : (V.dualOfList vs).length = vs.length :=
    HSpace.dualOfList_length V vs
  have hiDual : i < (V.dualOfList vs).length := hdualLen.symm ▸ hi
  rw [List.getD_eq_getElem (V.dualOfList vs) 0 hiDual]
  change (V.dualOfList vs).get ⟨i, hiDual⟩ = _
  refine (List.get_of_eq
    (HSpace.dualOfList_eq_finRange_map V vs) ⟨i, hiDual⟩).trans ?_
  simp

private theorem raw_simple_tprodOfLists_diag_sum
    (W : HSpace) (ws : List W.carrier) {N : Nat}
    (hl : ws.length = N) (c : Fin (N * N) -> ℝ)
    (hc : forall k : Fin (N * N),
      c k = if (k : Nat) / N = (k : Nat) % N then 1 else 0) :
    (∑ k, c k • (HSpace.tprodOfLists W W ws ws).getD k 0) =
      ∑ i : Fin N, ws.getD i 0 ⊗ₜ[ℝ] ws.getD i 0 := by
  subst hl
  simp only [hc]
  rw [Fin.sum_univ_eq_sum_range
      (fun k => (if k / ws.length = k % ws.length then (1 : ℝ) else 0) •
        (HSpace.tprodOfLists W W ws ws).getD k 0),
    Fin.sum_univ_eq_sum_range
      (fun i => ws.getD i 0 ⊗ₜ[ℝ] ws.getD i 0)]
  by_cases hn : ws.length = 0
  · rw [hn]
    simp
  have hnpos : 0 < ws.length := Nat.pos_of_ne_zero hn
  calc
    (∑ k ∈ Finset.range (ws.length * ws.length),
      (if k / ws.length = k % ws.length then (1 : ℝ) else 0) •
        (HSpace.tprodOfLists W W ws ws).getD k 0) =
        ∑ k ∈ Finset.range (ws.length * ws.length),
          (if k / ws.length = k % ws.length then (1 : ℝ) else 0) •
            (ws.getD (k / ws.length) 0 ⊗ₜ[ℝ]
              ws.getD (k % ws.length) 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hklist : k < (HSpace.tprodOfLists W W ws ws).length := by
        rw [HSpace.tprodOfLists_length]
        exact hk'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hklist,
        HSpace.tprodOfLists_getElem ws ws k hk' hnpos]
      have hi : k / ws.length < ws.length :=
        (Nat.div_lt_iff_lt_mul hnpos).2 hk'
      have hj : k % ws.length < ws.length := Nat.mod_lt _ hnpos
      rw [List.getD_eq_getElem ws 0 hi, List.getD_eq_getElem ws 0 hj]
      simp only [Option.getD_some]
    _ = ∑ i ∈ Finset.range ws.length, ∑ j ∈ Finset.range ws.length,
          (if i = j then (1 : ℝ) else 0) •
            (ws.getD i 0 ⊗ₜ[ℝ] ws.getD j 0) := by
      exact raw_simple_sum_range_mul_div_mod ws.length ws.length
        (fun i j => (if i = j then (1 : ℝ) else 0) •
          (ws.getD i 0 ⊗ₜ[ℝ] ws.getD j 0))
    _ = ∑ i ∈ Finset.range ws.length,
        ws.getD i 0 ⊗ₜ[ℝ] ws.getD i 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, hi, if_true]

theorem arm_inner_std
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 : Basis}
    {s : GLang.Space} {sv : ValSpace}
    (hb0 : Basis.isStd b0)
    (hsof : Basis.sof b0 = s)
    (_ht : Nonempty (HasType ∅ Gamma (.inner s)
      (Basis.tof (.tprod (.dual b0) (.dual b0)))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) (.dual b0)))
    (_hTy : S.TyAt Gamma Psi (.tprod (.dual b0) (.dual b0))
      (.space (.tprod sv sv)))
    (_hsv : S.Space Gamma Psi s sv)
    (ihTy : RawMTyAtSubctx orc Gamma Psi
      (.tprod (.dual b0) (.dual b0)) (.space (.tprod sv sv)))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi s sv) :
    RawMTermTraceSubctx orc ∅ Gamma Psi (.inner s)
      (.tprod (.dual b0) (.dual b0)) (.idelta sv)
      (.space (.tprod sv sv)) := by
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof (.tprod (.dual b0) (.dual b0)))
      (.space (.tprod sv sv))
      (denotBasis sigma (.tprod (.dual b0) (.dual b0))) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hb0v : BasisValid Gamma b0 := by
    cases hbv with
    | tprod h _ _ _ =>
        cases h with
        | dual h _ => exact h
  obtain ⟨hlb, horth⟩ := denotBasis_std_orthonormal_core
    (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl hb0
  have hshape : ValSpace.shpOf (orc rho [] []) sv =
      srcShp sigma [] s :=
    ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  subst s
  have hdim := ValSpace.raw_dof_eq_finrank_of_shpOf hshape
  have hvs : ((denotBasis sigma b0).atSpace
      (denotSpace sigma (Basis.sof b0))).length =
      ValSpace.dof (orc rho [] []) sv :=
    hlb.finrank_eq.symm.trans hdim.symm
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
  have hB : (denotBasis sigma
      (.tprod (.dual b0) (.dual b0))).atSpace
      (HSpace.tprod
        (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
        (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))) =
      HSpace.tprodOfLists
        (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
        (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
        ((denotSpaceAux sigma [] (Basis.sof b0)).dualOfList
          ((denotBasis sigma b0).atSpace
            (denotSpaceAux sigma [] (Basis.sof b0))))
        ((denotSpaceAux sigma [] (Basis.sof b0)).dualOfList
          ((denotBasis sigma b0).atSpace
            (denotSpaceAux sigma [] (Basis.sof b0)))) := by
    rw [show denotBasis sigma (.tprod (.dual b0) (.dual b0)) =
        BasisDenot.vecs
          (HSpace.tprod
            (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
            (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0))))
          (HSpace.tprodOfLists _ _
            ((denotBasis sigma (.dual b0)).atSpace
              (denotSpaceAux sigma [] (.dual (Basis.sof b0))))
            ((denotBasis sigma (.dual b0)).atSpace
              (denotSpaceAux sigma [] (.dual (Basis.sof b0)))))
      from by simp only [denotBasis]; rfl, hD]
    exact BasisDenot.atSpace_vecs_self _ _
  refine ⟨?_, targetDims⟩
  unfold RawResultAgree
  rw [denotValB_semS.eq_8]
  refine ⟨_, rfl, ?_⟩
  simp only [Basis.tof, Basis.sof, RawAgree,
    ValExpr.inferSpaceCtx, ValValSem.arrayOf]
  rw [LegacyAgree.space_iff]
  change ((denotBasis sigma (.tprod (.dual b0) (.dual b0))).atSpace
      (HSpace.tprod
        (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
        (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0))))).length =
        ValSpace.dof (orc rho [] []) (.tprod sv sv) ∧
    (FlatArray.ofFn (ValSpace.dof (orc rho [] []) (.tprod sv sv)) _).length =
        ValSpace.dof (orc rho [] []) (.tprod sv sv) ∧
    DVal.atSpace
        (HSpace.tprod
          (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
          (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0))))
        (denotTerm sigma (.inner (Basis.sof b0))) =
      ∑ i : Fin (ValSpace.dof (orc rho [] []) (.tprod sv sv)),
        (FlatArray.ofFn (ValSpace.dof (orc rho [] []) (.tprod sv sv)) _).get
            (i : Nat) •
          ((denotBasis sigma (.tprod (.dual b0) (.dual b0))).atSpace
            (HSpace.tprod
              (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0)))
              (HSpace.dual (denotSpaceAux sigma [] (Basis.sof b0))))).getD
                (i : Nat) 0
  rw [hB]
  refine ⟨?_, FlatArray.length_ofFn _ _, ?_⟩
  · rw [HSpace.tprodOfLists_length, HSpace.dualOfList_length,
      hvs, ValSpace.dof_tprod]
  · simp only [denotTerm, denotTermAux]
    rw [IsListBasis.innerTensor_atSpace_eq_sum_dual_tmul hlb horth,
      raw_simple_fin_sum_cast_of_eq (ValSpace.dof_tprod _ _ _)]
    simp only [Fin.val_cast]
    rw [raw_simple_tprodOfLists_diag_sum _ _
      (HSpace.dualOfList_length _ _ |>.trans hvs) _ ?_]
    · rw [raw_simple_fin_sum_cast_of_eq hvs]
      apply Finset.sum_congr rfl
      intro i _
      rw [raw_simple_dualOfList_getD_eq_dualVec _ _
        (by rw [hvs]; exact i.isLt)]
      rfl
    · intro k
      rw [FlatArray.get_ofFn_lt _ _ _
        (by rw [ValSpace.dof_tprod]; exact k.isLt)]
      have hd : ValSpace.dof (orc rho [] []) sv ≠ 0 := by
        intro hd
        have h2 : ValSpace.dof (orc rho [] []) sv *
            ValSpace.dof (orc rho [] []) sv = 0 := by
          rw [hd]
        exact Nat.not_lt_zero _ (lt_of_lt_of_eq k.isLt h2)
      rw [if_neg hd, if_pos k.isLt]
      simp only [
        (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hd)).mpr k.isLt,
        and_true]

theorem arm_zero
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {sv : ValSpace}
    (htof : Basis.tof b = .space (Basis.sof b))
    (_ht : Nonempty
      (HasType Delta Gamma (.zero (Basis.sof b)) (Basis.tof b)))
    (hbv : BasisValid Gamma b)
    (_hTy : S.TyAt Gamma Psi b (.space sv))
    (_hsv : S.Space Gamma Psi (Basis.sof b) sv)
    (ihTy : RawMTyAtSubctx orc Gamma Psi b (.space sv)) :
    RawMTermTraceSubctx orc Delta Gamma Psi
      (.zero (Basis.sof b)) b (.zero sv) (.space sv) := by
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof b) (.space sv) (denotBasis sigma b) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hlb := denotBasis_isListBasis
    (raw_basisValid_mono hbv hle.2) hc.ctxWF_nl hc.envWF_nl
    (raw_simple_not_frame_of_tof_space htof)
  have hshape : ValSpace.shpOf (orc rho [] []) sv =
      srcShp sigma [] (Basis.sof b) := by
    simpa only [htof, RawAgreeDimsAt] using targetDims
  have hdim := ValSpace.raw_dof_eq_finrank_of_shpOf hshape
  have hlen : ((denotBasis sigma b).atSpace
      (denotSpace sigma (Basis.sof b))).length =
      ValSpace.dof (orc rho [] []) sv := by
    rw [hdim, hlb.finrank_eq]
  have hresult : RawResultAgree orc sigma rho [] [] []
      (Basis.tof b) (.space sv) (denotBasis sigma b)
      (denotTerm sigma (.zero (Basis.sof b)))
      (denotValB_semS orc rho [] [] (.zero sv)) := by
    unfold RawResultAgree
    rw [denotValB_semS.eq_4]
    refine ⟨_, rfl, ?_⟩
    rw [htof]
    simp only [RawAgree, ValExpr.inferSpaceCtx, ValValSem.arrayOf]
    rw [LegacyAgree.space_iff]
    refine ⟨hlen, FlatArray.length_ofFn _ _, ?_⟩
    have hsrc : (denotTerm sigma (.zero (Basis.sof b))).atSpace
        (denotSpace sigma (Basis.sof b)) = 0 := by
      show (DVal.hil ⟨denotSpace sigma (Basis.sof b),
        (0 : (denotSpace sigma (Basis.sof b)).carrier)⟩).atSpace
          (denotSpace sigma (Basis.sof b)) = 0
      exact DVal.atSpace_hil_self _ _
    rw [hsrc]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [FlatArray.get_ofFn_lt _ _ _ i.isLt, zero_smul]
  exact ⟨hresult, targetDims⟩

theorem arm_rlit
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx} (r : ℝ)
    (_ht : Nonempty (HasType ∅ Gamma (.real r) (Basis.tof .one)))
    (_hTy : S.TyAt Gamma Psi .one (.space .real))
    (ihTy : RawMTyAtSubctx orc Gamma Psi .one (.space .real)) :
    RawMTermTraceSubctx orc ∅ Gamma Psi
      (.real r) .one (.rlit r) (.space .real) := by
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : RawAgreeDimsAt orc sigma rho [] [] []
      (Basis.tof .one) (.space .real) (denotBasis sigma .one) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  refine ⟨?_, targetDims⟩
  unfold RawResultAgree
  rw [denotValB_semS.eq_3]
  refine ⟨_, rfl, ?_⟩
  simp only [Basis.tof, RawAgree, ValExpr.inferSpaceCtx,
    ValValSem.arrayOf]
  rw [LegacyAgree.space_iff]
  have hT : denotTerm sigma (.real r) = .hil ⟨HSpace.real, r⟩ := rfl
  have hBd : denotBasis sigma .one =
      .vecs HSpace.real [(1 : ℝ)] := by simp [denotBasis]
  rw [hT, hBd]
  simp only [Basis.sof, denotSpaceAux]
  rw [BasisDenot.atSpace_vecs_self, DVal.atSpace_hil_self]
  refine ⟨by rw [ValSpace.dof_real]; rfl,
    FlatArray.length_ofFn _ _, ?_⟩
  rw [ValSpace.dof_real, Fin.sum_univ_one]
  change r = r * 1
  ring

end GLang
