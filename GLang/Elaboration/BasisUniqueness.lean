import GLang.Elaboration.Uniqueness
import GLang.Elaboration.ErasureLemmas

namespace GLang

/-- Opening at a common fresh name reflects equality of basis bodies. -/
theorem Basis.eq_of_openVar_eq {b b' : Basis} (x : Name)
    (hx : x ∉ b.fv) (hx' : x ∉ b'.fv)
    (he : Basis.openVar x b = Basis.openVar x b') : b = b' := by
  have h := congrArg (Basis.closeRec 0 x) he
  simpa only [Basis.openVar, Basis.close_openVar x b hx,
    Basis.close_openVar x b' hx'] using h

private theorem typed_list_erase_unique {ε s t} {es fs : List Term}
    (he : ∀ e ∈ es, Nonempty (HasType ∅ ε e (.space s)))
    (hf : ∀ f ∈ fs, Nonempty (HasType ∅ ε f (.space t)))
    (hm : es.map Term.erase = fs.map Term.erase) : es = fs := by
  induction es generalizing fs with
  | nil => simpa using hm.symm
  | cons e es ih =>
    cases fs with
    | nil => simp at hm
    | cons f fs =>
      simp only [List.map_cons, List.cons.injEq] at hm
      have hh := HasType.annotation_unique_of_disjoint
        (fun _ hx => (Finmap.notMem_empty hx).elim)
        (he e (by simp)).some (hf f (by simp)).some hm.1
      exact congrArg₂ List.cons hh.1
        (ih (fun e he' => he e (by simp [he']))
          (fun f hf' => hf f (by simp [hf'])) hm.2)

theorem Basis.BasisValid.annotation_unique {ε b b'}
    (h : Basis.BasisValid ε b) (h' : Basis.BasisValid ε b')
    (he : b.erase = b'.erase) : b = b' := by
  induction h generalizing b' with
  | empty => cases h' <;> simp_all [Basis.erase]
  | one => cases h' <;> simp_all [Basis.erase]
  | dual hb ht ih =>
    cases h' <;> simp only [Basis.erase, Surface.Basis.dual.injEq, reduceCtorEq] at he
    rename_i c ht' hc
    exact congrArg Basis.dual (ih hc he)
  | dsum ha hb ht hu iha ihb =>
    cases h' <;> simp only [Basis.erase, Surface.Basis.dsum.injEq, reduceCtorEq] at he
    rename_i c d ht' hu' hc hd
    exact congrArg₂ Basis.dsum (iha hc he.1) (ihb hd he.2)
  | tprod ha hb ht hu iha ihb =>
    cases h' <;> simp only [Basis.erase, Surface.Basis.tprod.injEq, reduceCtorEq] at he
    rename_i c d ht' hu' hc hd
    exact congrArg₂ Basis.tprod (iha hc he.1) (ihb hd he.2)
  | proj_ker ha hb ht hu he' iha ihb =>
    cases h' <;> simp only [Basis.erase, Space.erase, Surface.Basis.proj.injEq,
      Surface.Space.ker.injEq, reduceCtorEq, false_and] at he
    rename_i s t e c d ht' hu' hc hd hf
    obtain ⟨rfl, hty⟩ := HasType.annotation_unique_of_disjoint
      (fun _ hx => (Finmap.notMem_empty hx).elim) he'.some hf.some he.1
    cases hty
    obtain rfl := iha hc he.2.1
    obtain rfl := ihb hd he.2.2
    rfl
  | proj_coker ha hb ht hu he' iha ihb =>
    cases h' <;> simp only [Basis.erase, Space.erase, Surface.Basis.proj.injEq,
      Surface.Space.coker.injEq, reduceCtorEq, false_and] at he
    rename_i s t e c d ht' hu' hc hd hf
    obtain ⟨rfl, hty⟩ := HasType.annotation_unique_of_disjoint
      (fun _ hx => (Finmap.notMem_empty hx).elim) he'.some hf.some he.1
    cases hty
    obtain rfl := iha hc he.2.1
    obtain rfl := ihb hd he.2.2
    rfl
  | proj_img ha hb ht hu he' iha ihb =>
    cases h' <;> simp only [Basis.erase, Space.erase, Surface.Basis.proj.injEq,
      Surface.Space.img.injEq, reduceCtorEq, false_and] at he
    rename_i s t e c d ht' hu' hc hd hf
    obtain ⟨rfl, hty⟩ := HasType.annotation_unique_of_disjoint
      (fun _ hx => (Finmap.notMem_empty hx).elim) he'.some hf.some he.1
    cases hty
    obtain rfl := iha hc he.2.1
    obtain rfl := ihb hd he.2.2
    rfl
  | proj_coimg ha hb ht hu he' iha ihb =>
    cases h' <;> simp only [Basis.erase, Space.erase, Surface.Basis.proj.injEq,
      Surface.Space.coimg.injEq, reduceCtorEq, false_and] at he
    rename_i s t e c d ht' hu' hc hd hf
    obtain ⟨rfl, hty⟩ := HasType.annotation_unique_of_disjoint
      (fun _ hx => (Finmap.notMem_empty hx).elim) he'.some hf.some he.1
    cases hty
    obtain rfl := iha hc he.2.1
    obtain rfl := ihb hd he.2.2
    rfl
  | image hb ht he' ih =>
    cases h' <;> simp only [Basis.erase, Surface.Basis.image.injEq, reduceCtorEq] at he
    rename_i c s t e ht' hc hf
    exact congrArg Basis.image (ih hc he)
  | terms hb ht hs hes hn ih =>
    cases h' <;> simp only [Basis.erase, Surface.Basis.terms.injEq, reduceCtorEq] at he
    rename_i s es c ht' hn' hc hs' hes'
    obtain rfl := ih hc he.2
    have hspace := Ty.space.inj (ht.symm.trans ht')
    cases hspace
    obtain rfl := typed_list_erase_unique hes hes' he.1
    rfl
  | @frame ε a b L ha hb iha ihb =>
    cases h' <;> simp only [Basis.erase, Surface.Basis.frame.injEq, reduceCtorEq] at he
    rename_i c d L' hc hd
    obtain rfl := iha hc he.1
    obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ L' ∪ b.fv ∪ d.fv)
    simp only [Finset.mem_union, not_or] at hx
    have hbody := ihb x hx.1.1.1 (hd x hx.1.1.2)
      (by simp only [Basis.openVar, Basis.erase_openRec, he.2])
    exact congrArg (Basis.frame a) (Basis.eq_of_openVar_eq x hx.1.2 hx.2 hbody)

end GLang
