import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMotives
import GLang.Proofs.Source.BasisSoundness

namespace GLang.PartialAdequacy
open Basis (BasisValid)

theorem raw_simple_basis_fv_subset_of_openVar_body
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

theorem raw_simple_basisValid_fv_subset_keys
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

theorem History.ctxWF_raw
    {orc : PartialFFSOracleSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : History orc Delta Gamma Psi GammaV sigma rho) :
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

/-- The source environment stored by `History` realizes the full linear
and nonlinear telescope. -/
theorem History.envWF_raw
    {orc : PartialFFSOracleSem} {Delta : LCtx} {Gamma : NLCtx}
    {Psi : EvalCtx} {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : History orc Delta Gamma Psi GammaV sigma rho) :
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

theorem raw_hasType_demote
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

theorem raw_hasType_mono_nl_aux
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

theorem raw_hasType_mono_nl
    {Delta : LCtx} {Gamma Gamma' : NLCtx} {e : Term} {tau : Ty}
    (h : Nonempty (HasType Delta Gamma e tau))
    (hle : NLCtxIncl Gamma Gamma')
    (hctx : Graded.CtxDisj Delta Gamma') :
    Nonempty (HasType Delta Gamma' e tau) :=
  raw_hasType_mono_nl_aux (Gamma'.keys \ Gamma.keys) Gamma Gamma' h hle hctx
    (fun x hx hxGamma => Finset.mem_sdiff.mpr
      ⟨Finmap.mem_keys.mpr hx, fun hm => hxGamma (Finmap.mem_keys.mp hm)⟩)

theorem raw_hasType_ctxIncl_aux
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

theorem raw_hasType_ctxIncl
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

theorem term_shape_at
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    {s : GLang.Space}
    (he : S.Term Delta Gamma Psi e b v tauV)
    (htof : Basis.tof b = .space s)
    (hctx : Graded.CtxDisj Delta Gamma)
    {orc : PartialFFSOracleSem} {Delta' : LCtx} {Gamma' : NLCtx}
    {Psi' : EvalCtx} {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (hle : RawCtxIncl Delta Gamma Delta' Gamma')
    (hc : History orc Delta' Gamma' Psi' GammaV sigma rho) :
    exists x, denotTerm sigma e = .hil ⟨denotSpace sigma s, x⟩ := by
  obtain ⟨Delta1, hDelta, ⟨ht⟩⟩ :=
    raw_hasType_ctxIncl hc.ctxWF_raw he.hasType hctx hle
  have hs := (soundness ht
    (hc.ctxWF_raw.of_sub_Δ hDelta) (hc.envWF_raw.of_sub_Δ hDelta)).1
  rw [htof] at hs
  exact DVal.matchesShape_hil_eq hs

/-! ## Context-inclusion bookkeeping -/

theorem RawCtxIncl.union_left
    {Delta0 Delta1 Delta' : LCtx} {Gamma Gamma' : NLCtx}
    (h : RawCtxIncl (Delta0 ∪ Delta1) Gamma Delta' Gamma') :
    RawCtxIncl Delta0 Gamma Delta' Gamma' := by
  refine ⟨?_, h.2⟩
  intro x s hx
  apply h.1 x s
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hx)]
  exact hx

theorem RawCtxIncl.union_right
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

theorem not_frame_of_tof_space
    {b : Basis} {s : GLang.Space} (htof : Basis.tof b = .space s) :
    forall b0 b1, b ≠ .frame b0 b1 := by
  intro b0 b1 h
  subst b
  simp only [Basis.tof, reduceCtorEq] at htof

abbrev TypedHistory.ctxWF_raw
    (h : TypedHistory orc Δ Γ Ψ Γv σ ρ) := h.history.ctxWF_raw
abbrev TypedHistory.envWF_raw
    (h : TypedHistory orc Δ Γ Ψ Γv σ ρ) := h.history.envWF_raw

end GLang.PartialAdequacy
