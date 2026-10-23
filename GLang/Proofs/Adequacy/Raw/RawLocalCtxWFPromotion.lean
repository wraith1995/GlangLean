import GLang.Proofs.Source.SourceStrengthen
import GLang.Proofs.Preservation.ValuePreservationV2

namespace GLang
namespace RawLocalCtxWFPromotion

private theorem lookup_toNL (lin : LCtx) (x : Name) :
    lin.toNL.lookup x = (lin.lookup x).map Ty.space := by
  cases hx : lin.lookup x with
  | none =>
      have hnot : x ∉ lin := Finmap.lookup_eq_none.mp hx
      have hnot' : x ∉ lin.toNL :=
        fun hm => hnot ((LCtx.mem_toNL_iff lin x).mp hm)
      rw [Finmap.lookup_eq_none.mpr hnot']
      rfl
  | some s =>
      rw [LCtx.toNL_lookup lin x s hx]
      rfl

private theorem toNL_insert {lin : LCtx} {y : Name} {s : Space} :
    LCtx.toNL (Finmap.insert y s lin) =
      Finmap.insert y (.space s) (LCtx.toNL lin) := by
  apply Finmap.ext_lookup
  intro x
  rw [lookup_toNL]
  by_cases hxy : x = y
  · subst x
    simp only [Finmap.lookup_insert, Option.map_some]
  · rw [Finmap.lookup_insert_of_ne _ hxy, Finmap.lookup_insert_of_ne _ hxy,
      lookup_toNL]

private theorem toNL_insert_union {lin : LCtx} {Gamma : NLCtx}
    {y : Name} {s : Space} :
    LCtx.toNL (Finmap.insert y s lin) ∪ Gamma =
      Finmap.insert y (.space s) (LCtx.toNL lin ∪ Gamma) := by
  rw [toNL_insert, Finmap.insert_union]

/-- A fresh key may be moved from the right operand of a left-biased union
to an insertion outside the union. -/
private theorem union_insert_of_not_mem
    {lin Delta : LCtx} {y : Name} {s : Space} (hy : y ∉ lin) :
    lin ∪ Finmap.insert y s Delta =
      Finmap.insert y s (lin ∪ Delta) := by
  apply Finmap.ext_lookup
  intro x
  by_cases hxy : x = y
  · subst x
    rw [Finmap.lookup_union_right hy]
    simp only [Finmap.lookup_insert]
  · by_cases hxlin : x ∈ lin
    · rw [Finmap.lookup_union_left hxlin,
        Finmap.lookup_insert_of_ne _ hxy,
        Finmap.lookup_union_left hxlin]
    · rw [Finmap.lookup_union_right hxlin,
        Finmap.lookup_insert_of_ne _ hxy,
        Finmap.lookup_insert_of_ne _ hxy,
        Finmap.lookup_union_right hxlin]

private theorem ctxWF_empty_of_insert
    {Gamma : NLCtx} {y : Name} {tauY : Ty}
    (hyGamma : y ∉ Gamma)
    (hfresh : ∀ x tau, Gamma.lookup x = some tau → y ∉ Ty.fv tau)
    (h : V2.CtxWF' (∅ : LCtx) (Finmap.insert y tauY Gamma)) :
    CtxWF (∅ : LCtx) Gamma where
  disjoint := by
    intro x hx _
    exact Finmap.notMem_empty hx
  lin_fv_in_ε := by
    intro x s hx
    exact absurd (Finmap.mem_of_lookup_eq_some hx) Finmap.notMem_empty
  nl_fv_in_ε := by
    intro x tau hx z hz
    have hxy : x ≠ y := by
      intro hxy
      subst x
      exact hyGamma (Finmap.mem_of_lookup_eq_some hx)
    have hx' : (Finmap.insert y tauY Gamma).lookup x = some tau := by
      rw [Finmap.lookup_insert_of_ne _ hxy]
      exact hx
    have hz' := h.nl_fv x tau hx' hz
    rw [Finmap.mem_keys, Finmap.mem_insert] at hz'
    rcases hz' with rfl | hzGamma
    · exact absurd hz (hfresh x tau hx)
    · exact hzGamma

/-- Move one fresh space binding from the nonlinear context back to the
linear context, including the validity fields of `CtxWF'`. -/
theorem ctxWF'_unpromote_one
    {Delta : LCtx} {Gamma : NLCtx} {y : Name} {sY : Space}
    (hyDelta : y ∉ Delta) (hyGamma : y ∉ Gamma)
    (hfreshDelta : ∀ x s,
      Delta.lookup x = some s → y ∉ Space.fv s)
    (hfreshGamma : ∀ x tau,
      Gamma.lookup x = some tau → y ∉ Ty.fv tau)
    (hfreshSelf : y ∉ Space.fv sY)
    (h : V2.CtxWF' Delta (Finmap.insert y (.space sY) Gamma)) :
    V2.CtxWF' (Finmap.insert y sY Delta) Gamma := by
  have hempty : V2.CtxWF' (∅ : LCtx)
      (Finmap.insert y (.space sY) Gamma) := by
    refine ⟨?_, ?_, h.nl_fv, ?_, h.nl_valid⟩
    · intro x hx _
      exact Finmap.notMem_empty hx
    · intro x s hx
      exact absurd (Finmap.mem_of_lookup_eq_some hx) Finmap.notMem_empty
    · intro x s hx
      exact absurd (Finmap.mem_of_lookup_eq_some hx) Finmap.notMem_empty
  have hbase : CtxWF (∅ : LCtx) Gamma :=
    ctxWF_empty_of_insert hyGamma hfreshGamma hempty
  constructor
  · intro x hx hGamma
    rw [Finmap.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hyGamma hGamma
    · exact h.disjoint x hx (Finmap.mem_insert.mpr (Or.inr hGamma))
  · intro x s hx z hz
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hx
      obtain rfl := Option.some.inj hx
      have hz' := h.nl_fv y (.space sY) (by simp)
        (by simpa [Ty.fv] using hz)
      rw [Finmap.mem_keys, Finmap.mem_insert] at hz'
      rcases hz' with rfl | hzGamma
      · exact absurd hz hfreshSelf
      · exact Finmap.mem_keys.mpr hzGamma
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      have hz' := h.lin_fv x s hx hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hz'
      rcases hz' with rfl | hzGamma
      · exact absurd hz (hfreshDelta x s hx)
      · exact Finmap.mem_keys.mpr hzGamma
  · intro x tau hx z hz
    have hxy : x ≠ y := by
      intro hxy
      subst x
      exact hyGamma (Finmap.mem_of_lookup_eq_some hx)
    have hx' : (Finmap.insert y (.space sY) Gamma).lookup x = some tau := by
      rw [Finmap.lookup_insert_of_ne _ hxy]
      exact hx
    have hz' := h.nl_fv x tau hx' hz
    rw [Finmap.mem_keys, Finmap.mem_insert] at hz'
    rcases hz' with rfl | hzGamma
    · exact absurd hz (hfreshGamma x tau hx)
    · exact Finmap.mem_keys.mpr hzGamma
  · intro x s hx
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hx
      obtain rfl := Option.some.inj hx
      obtain ⟨k, ⟨ht⟩⟩ := h.nl_valid y (.space sY) (by simp)
      cases ht with
      | space hs =>
          exact ⟨sValidNLErase hbase hyGamma hfreshSelf hs⟩
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      obtain ⟨hs⟩ := h.lin_valid x s hx
      exact ⟨sValidNLErase hbase hyGamma (hfreshDelta x s hx) hs⟩
  · intro x tau hx
    have hxy : x ≠ y := by
      intro hxy
      subst x
      exact hyGamma (Finmap.mem_of_lookup_eq_some hx)
    have hx' : (Finmap.insert y (.space sY) Gamma).lookup x = some tau := by
      rw [Finmap.lookup_insert_of_ne _ hxy]
      exact hx
    obtain ⟨k, ⟨ht⟩⟩ := h.nl_valid x tau hx'
    exact ⟨k, ⟨tValidNLErase hbase hyGamma
      (hfreshGamma x tau hx) ht⟩⟩

/-- Full rule-local context inversion for `HasType.promote`. -/
theorem V2.CtxWF'.promote_inner
    {lin Delta : LCtx} {Gamma : NLCtx}
    (h : V2.CtxWF' Delta (lin.toNL ∪ Gamma))
    (hdisjDelta : Finmap.Disjoint lin Delta)
    (hdisjGamma : Finmap.Disjoint lin.toNL Gamma)
    (hfresh : PromoteFresh lin Delta Gamma) :
    V2.CtxWF' (lin ∪ Delta) Gamma := by
  let C : LCtx → Prop := fun lin' =>
    ∀ (Delta' : LCtx) (Gamma' : NLCtx),
      Finmap.Disjoint lin' Delta' →
      Finmap.Disjoint lin'.toNL Gamma' →
      PromoteFresh lin' Delta' Gamma' →
      V2.CtxWF' Delta' (lin'.toNL ∪ Gamma') →
      V2.CtxWF' (lin' ∪ Delta') Gamma'
  have hall : ∀ lin' : LCtx, C lin' := by
    apply Graded.lctx_insert_induction
    · intro Delta' Gamma' _ _ _ hwf
      have hto : (∅ : LCtx).toNL = (∅ : NLCtx) := by
        apply Finmap.ext_lookup
        intro x
        rw [lookup_toNL]
        rfl
      rw [hto, Finmap.empty_union] at hwf
      simpa only [Finmap.empty_union] using hwf
    · intro y sY lin' hyLin ih Delta' Gamma' hdDelta hdGamma hfr hwf
      have hyFull : y ∈ Finmap.insert y sY lin' :=
        Finmap.mem_insert.mpr (Or.inl rfl)
      have hyDelta : y ∉ Delta' := hdDelta y hyFull
      have hyGamma : y ∉ Gamma' := by
        intro hyGamma
        exact hdGamma y ((LCtx.mem_toNL_iff _ _).mpr hyFull) hyGamma
      have hyRestGamma : y ∉ lin'.toNL ∪ Gamma' := by
        rw [Finmap.mem_union, not_or]
        exact ⟨fun hym => hyLin ((LCtx.mem_toNL_iff _ _).mp hym), hyGamma⟩
      have hfreshRest : ∀ x tau,
          (lin'.toNL ∪ Gamma').lookup x = some tau →
          y ∉ Ty.fv tau := by
        intro x tau hx
        by_cases hxlin : x ∈ lin'
        · obtain ⟨sx, hxs⟩ := Finmap.mem_iff.mp hxlin
          have hxtoNL : x ∈ lin'.toNL :=
            (LCtx.mem_toNL_iff _ _).mpr hxlin
          rw [Finmap.lookup_union_left hxtoNL,
            LCtx.toNL_lookup _ _ _ hxs] at hx
          obtain rfl := Option.some.inj hx
          have hxy : x ≠ y := by
            intro hxy
            subst x
            exact hyLin hxlin
          exact hfr.fresh_lin y hyFull x sx
            (by rw [Finmap.lookup_insert_of_ne _ hxy]; exact hxs)
        · have hxnotToNL : x ∉ lin'.toNL := fun hm =>
            hxlin ((LCtx.mem_toNL_iff _ _).mp hm)
          rw [Finmap.lookup_union_right hxnotToNL] at hx
          exact hfr.fresh_ε y hyFull x tau hx
      have houterOne : V2.CtxWF' Delta'
          (Finmap.insert y (.space sY) (lin'.toNL ∪ Gamma')) := by
        rw [← toNL_insert_union]
        exact hwf
      have hone : V2.CtxWF' (Finmap.insert y sY Delta')
          (lin'.toNL ∪ Gamma') :=
        ctxWF'_unpromote_one hyDelta hyRestGamma
          (fun x s hx => hfr.fresh_Δ y hyFull x s hx)
          hfreshRest
          (hfr.fresh_lin y hyFull y sY (Finmap.lookup_insert lin'))
          houterOne
      have hdDelta' : Finmap.Disjoint lin'
          (Finmap.insert y sY Delta') := by
        intro x hxlin hxins
        rcases Finmap.mem_insert.mp hxins with rfl | hxDelta
        · exact hyLin hxlin
        · exact hdDelta x (Finmap.mem_insert.mpr (Or.inr hxlin)) hxDelta
      have hdGamma' : Finmap.Disjoint lin'.toNL Gamma' := by
        intro x hxlin
        exact hdGamma x ((LCtx.mem_toNL_iff _ _).mpr
          (Finmap.mem_insert.mpr (Or.inr
            ((LCtx.mem_toNL_iff _ _).mp hxlin))))
      have hfr' : PromoteFresh lin' (Finmap.insert y sY Delta') Gamma' := by
        constructor
        · intro z hz x s hx
          by_cases hxy : x = y
          · subst x
            rw [Finmap.lookup_insert] at hx
            obtain rfl := Option.some.inj hx
            exact hfr.fresh_lin z
              (Finmap.mem_insert.mpr (Or.inr hz)) y sY
              (Finmap.lookup_insert lin')
          · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
            exact hfr.fresh_Δ z
              (Finmap.mem_insert.mpr (Or.inr hz)) x s hx
        · intro z hz x s hx
          have hxy : x ≠ y := by
            intro hxy
            subst x
            exact hyLin (Finmap.mem_of_lookup_eq_some hx)
          exact hfr.fresh_lin z
            (Finmap.mem_insert.mpr (Or.inr hz)) x s
            (by rw [Finmap.lookup_insert_of_ne _ hxy]; exact hx)
        · intro z hz x tau hx
          exact hfr.fresh_ε z
            (Finmap.mem_insert.mpr (Or.inr hz)) x tau hx
      have hout := ih (Finmap.insert y sY Delta') Gamma'
        hdDelta' hdGamma' hfr' hone
      rw [union_insert_of_not_mem hyLin] at hout
      rw [← Finmap.insert_union]
      exact hout
  exact hall lin Delta Gamma hdisjDelta hdisjGamma hfresh h

end RawLocalCtxWFPromotion
end GLang
