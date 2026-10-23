import GLang.Proofs.Value.Partial.PartialValueRuntimeRelation

/-! Runtime normalization and coherent-family transport for the partial
logical relation. Raw callbacks remain unchanged until explicitly reified. -/
namespace GLang.PartialValueDomains
universe u
open PaperValueDomains

theorem partialRuntimeRelated_symm (τ : ValTy)
    (T U : Except DimError (PartialValType τ)) (v w : ValValSem)
    (h : PartialRuntimeRelated τ T U v w) : PartialRuntimeRelated τ U T w v := by
  cases τ with
  | space s =>
    cases v <;> cases w <;> try exact False.elim h
    exact partialRelated_symm _ _ _ _ _ h
  | piTy d c =>
    cases T <;> cases U <;> cases v <;> cases w <;> try exact False.elim h
    rename_i T U A f B g
    rcases T with ⟨D,F⟩
    rcases U with ⟨E,G⟩
    obtain ⟨hA,hB,hr⟩ := h
    refine ⟨hB,hA,?_⟩
    intro a b hab
    exact PartialRel.symm (fun x y hxy => partialRuntimeRelated_symm c _ _ x y hxy)
      (hr b a (partialRelated_symm d _ _ _ _ hab))
termination_by sizeOf τ

theorem partialRuntime_normalize_result_right (τ : ValTy)
    (T U : Except DimError (PartialValType τ)) (r s : Except DimError ValValSem)
    (h : PartialRel (PartialRuntimeRelated τ T U) r s) :
    PartialRel (PartialRuntimeRelated τ T U) r
      ((s.bind τ.carrierFromVal).map τ.carrierToVal) := by
  cases r with
  | error e =>
    cases s with
    | error e' => exact h
    | ok v => exact False.elim h
  | ok v =>
    cases s with
    | error e => exact False.elim h
    | ok w =>
      cases τ with
      | space t =>
        cases v <;> cases w <;> try exact False.elim h
        exact h
      | piTy d c =>
        cases T <;> cases U <;> cases v <;> cases w <;> try exact False.elim h
        rename_i T U A f B g
        rcases T with ⟨D,F⟩
        rcases U with ⟨E,G⟩
        obtain ⟨hA,hB,hr⟩ := h
        subst A; subst B
        simp only [Except.bind,ValTy.carrierFromVal,Except.map,ValTy.carrierToVal]
        refine ⟨rfl,rfl,?_⟩
        intro a b hab
        have ih := partialRuntime_normalize_result_right c (F a) (G b) (f a) (g b) (hr a b hab)
        cases hgb : g b <;> simpa only [hgb,Except.bind,Except.map] using ih
termination_by sizeOf τ

theorem partialRuntime_normalize_right (τ : ValTy)
    (T U : Except DimError (PartialValType τ)) (v w : ValValSem)
    (h : PartialRuntimeRelated τ T U v w) (a : τ.carrierEl)
    (ha : τ.carrierFromVal w = .ok a) :
    PartialRuntimeRelated τ T U v (τ.carrierToVal a) := by
  have hh := partialRuntime_normalize_result_right τ T U (.ok v) (.ok w) h
  simpa only [Except.bind,ha,Except.map] using hh

private def RuntimeArgumentClass {I : Type u} (d : ValTy) (D : I → PartialValType d)
    (i : I) (a : d.carrierEl) :=
  {p : I × d.carrierEl // PartialRelated d (.ok (D i)) (.ok (D p.1)) a p.2}

/-- Changing representatives within a coherent family preserves the same
raw runtime relation at arbitrary higher-order types. -/
theorem partialRuntime_family_transport (τ : ValTy) {I : Type u}
    (T : I → Except DimError (PartialValType τ))
    (hc : ∀ i j, PartialCoherent τ (T i) (T j))
    (i j k l : I) (v w : ValValSem)
    (h : PartialRuntimeRelated τ (T i) (T j) v w) :
    PartialRuntimeRelated τ (T k) (T l) v w := by
  classical
  by_cases hf : ∃ i err, T i = .error err
  · obtain ⟨a,e,ha⟩ := hf
    have hi : T i = .error e := partialCoherent_error (ha ▸ hc a i)
    rw [hi] at h
    cases τ <;> cases v <;> cases w <;> exact False.elim h
  · have hs : ∀ i, ∃ t, T i = .ok t := by
      intro i
      cases ht : T i with
      | error e => exact False.elim (hf ⟨i,e,ht⟩)
      | ok t => exact ⟨t,rfl⟩
    let S : I → PartialValType τ := fun i => Classical.choose (hs i)
    have hS : ∀ i, T i = .ok (S i) := fun i => Classical.choose_spec (hs i)
    cases τ with
    | space s =>
      cases v <;> cases w <;> try exact False.elim h
      exact ((partialFamily_laws (.space s) T hc).transport i j k l _ _).1 h
    | piTy d c =>
      rw [hS i,hS j] at h
      rw [hS k,hS l]
      cases v <;> cases w <;> try exact False.elim h
      rename_i A f B g
      obtain ⟨hA,hB,hfg⟩ := h
      subst A; subst B
      let D : I → PartialValType d := fun i => (S i).1
      let F : I → d.carrierEl → Except DimError (PartialValType c) := fun i => (S i).2
      have hdom : ∀ i j, PartialCoherent d (.ok (D i)) (.ok (D j)) := by
        intro i j
        have h := hc i j
        rw [hS i,hS j] at h
        exact h.1
      have hfib : ∀ i j a b, PartialRelated d (.ok (D i)) (.ok (D j)) a b →
          PartialCoherent c (F i a) (F j b) := by
        intro i j a b hab
        have h := hc i j
        rw [hS i,hS j] at h
        exact h.2 a b hab
      have hd := partialFamily_laws d (fun i => .ok (D i)) hdom
      refine ⟨rfl,rfl,?_⟩
      intro a b hab
      have hab0 := (hd.transport k l i j a b).1 hab
      have haa := hd.trans k l k a b a hab (partialRelated_symm d _ _ _ _ hab)
      let aa : RuntimeArgumentClass d D k a := ⟨⟨i,a⟩,(hd.transport k k k i a a).1 haa⟩
      let bb : RuntimeArgumentClass d D k a := ⟨⟨j,b⟩,(hd.transport k l k j a b).1 hab⟩
      let aa' : RuntimeArgumentClass d D k a := ⟨⟨k,a⟩,haa⟩
      let bb' : RuntimeArgumentClass d D k a := ⟨⟨l,b⟩,hab⟩
      have hclass : ∀ p q : RuntimeArgumentClass d D k a,
          PartialCoherent c (F p.val.1 p.val.2) (F q.val.1 q.val.2) := by
        intro p q
        exact hfib _ _ _ _ (hd.trans _ _ _ _ _ _
          (partialRelated_symm d _ _ _ _ p.property) q.property)
      have hr := hfg a b hab0
      cases he : f a <;> cases he' : g b <;> simp only [he,he',PartialRel] at hr ⊢
      exact partialRuntime_family_transport c
        (fun p : RuntimeArgumentClass d D k a => F p.val.1 p.val.2)
        hclass aa bb aa' bb' _ _ hr
termination_by sizeOf τ

/-- Raw runtime relations compose inside a coherent type family. -/
theorem partialRuntime_family_trans (τ : ValTy) {I : Type u}
    (T : I → Except DimError (PartialValType τ))
    (hc : ∀ i j, PartialCoherent τ (T i) (T j))
    (i j k : I) (v w z : ValValSem)
    (h : PartialRuntimeRelated τ (T i) (T j) v w)
    (h' : PartialRuntimeRelated τ (T j) (T k) w z) :
    PartialRuntimeRelated τ (T i) (T k) v z := by
  classical
  by_cases hf : ∃ i err, T i = .error err
  · obtain ⟨a,e,ha⟩ := hf
    have hi : T i = .error e := partialCoherent_error (ha ▸ hc a i)
    rw [hi] at h
    cases τ <;> cases v <;> cases w <;> exact False.elim h
  · have hs : ∀ i, ∃ t, T i = .ok t := by
      intro i
      cases ht : T i with
      | error e => exact False.elim (hf ⟨i,e,ht⟩)
      | ok t => exact ⟨t,rfl⟩
    let S : I → PartialValType τ := fun i => Classical.choose (hs i)
    have hS : ∀ i, T i = .ok (S i) := fun i => Classical.choose_spec (hs i)
    cases τ with
    | space s =>
      cases v <;> cases w <;> cases z <;> try exact False.elim h
      all_goals try exact False.elim h'
      exact (partialFamily_laws (.space s) T hc).trans i j k _ _ _ h h'
    | piTy d c =>
      rw [hS i,hS j] at h
      rw [hS j,hS k] at h'
      rw [hS i,hS k]
      cases v <;> cases w <;> cases z <;> try exact False.elim h
      all_goals try exact False.elim h'
      rename_i A f B g C r
      obtain ⟨hA,hB,hfg⟩ := h
      obtain ⟨_,hC,hgr⟩ := h'
      subst A; subst B; subst C
      let D : I → PartialValType d := fun i => (S i).1
      let F : I → d.carrierEl → Except DimError (PartialValType c) := fun i => (S i).2
      have hdom : ∀ i j, PartialCoherent d (.ok (D i)) (.ok (D j)) := by
        intro i j
        have h := hc i j
        rw [hS i,hS j] at h
        exact h.1
      have hfib : ∀ i j a b, PartialRelated d (.ok (D i)) (.ok (D j)) a b →
          PartialCoherent c (F i a) (F j b) := by
        intro i j a b hab
        have h := hc i j
        rw [hS i,hS j] at h
        exact h.2 a b hab
      have hd := partialFamily_laws d (fun i => .ok (D i)) hdom
      refine ⟨rfl,rfl,?_⟩
      intro a b hab
      have hab0 := (hd.transport i k i j a b).1 hab
      have hbb := hd.trans k i k b a b (partialRelated_symm d _ _ _ _ hab) hab
      have hbb0 := (hd.transport k k j k b b).1 hbb
      have haa := hd.trans i k i a b a hab (partialRelated_symm d _ _ _ _ hab)
      let aa : RuntimeArgumentClass d D i a := ⟨⟨i,a⟩,haa⟩
      let bb : RuntimeArgumentClass d D i a := ⟨⟨j,b⟩,hab0⟩
      let cc : RuntimeArgumentClass d D i a := ⟨⟨k,b⟩,hab⟩
      have hclass : ∀ p q : RuntimeArgumentClass d D i a,
          PartialCoherent c (F p.val.1 p.val.2) (F q.val.1 q.val.2) := by
        intro p q
        exact hfib _ _ _ _ (hd.trans _ _ _ _ _ _
          (partialRelated_symm d _ _ _ _ p.property) q.property)
      have h1 := hfg a b hab0
      have h2 := hgr b b hbb0
      cases hf : f a <;> cases hg : g b <;> cases hr : r b <;>
        simp only [hf,hg,hr,PartialRel] at h1 h2 ⊢
      exact partialRuntime_family_trans c
        (fun p : RuntimeArgumentClass d D i a => F p.val.1 p.val.2)
        hclass aa bb cc _ _ _ h1 h2
termination_by sizeOf τ

end GLang.PartialValueDomains
