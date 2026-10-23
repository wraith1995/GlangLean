import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacySimple

namespace GLang

private theorem raw_source_hasType_demote
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
      (Graded.GWk.of_wk
        (Graded.tr_promote_wk lin Delta Gamma hdisj)))⟩

private theorem raw_source_hasType_mono_nl_aux
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
        · have hx' : x ∉ Gamma' := fun hmem =>
            absurd (hS x hmem hx) (Finset.notMem_empty x)
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

private theorem raw_source_hasType_mono_nl
    {Delta : LCtx} {Gamma Gamma' : NLCtx} {e : Term} {tau : Ty}
    (h : Nonempty (HasType Delta Gamma e tau))
    (hle : NLCtxIncl Gamma Gamma')
    (hctx : Graded.CtxDisj Delta Gamma') :
    Nonempty (HasType Delta Gamma' e tau) :=
  raw_source_hasType_mono_nl_aux (Gamma'.keys \ Gamma.keys)
    Gamma Gamma' h hle hctx
    (fun x hx hxGamma => Finset.mem_sdiff.mpr
      ⟨Finmap.mem_keys.mpr hx,
        fun hm => hxGamma (Finmap.mem_keys.mp hm)⟩)

private theorem raw_source_hasType_ctxIncl_aux
    {Delta' : LCtx} {Gamma' : NLCtx} {e : Term} {tau : Ty}
    (hwf : CtxWF Delta' Gamma') (S : Finset Name) :
    forall (Delta : LCtx) (Gamma : NLCtx),
      Nonempty (HasType Delta Gamma e tau) ->
      Graded.CtxDisj Delta Gamma ->
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
        raw_source_hasType_mono_nl h hle.2 hctx'⟩
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
        have h' := raw_source_hasType_demote hdisj hctx0 h0
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

/-- Transport a source typing into exactly the target raw world, after
discarding target-only linear bindings.  The resulting subcontext is enough
to invoke source soundness with `RawConsistent.ctxWF_raw` and
`RawConsistent.envWF_raw`. -/
theorem raw_hasType_ctxIncl
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
  raw_source_hasType_ctxIncl_aux hwf Delta.keys Delta Gamma h hctx hle
    (fun x hx _ => Finmap.mem_keys.mpr hx)

end GLang
