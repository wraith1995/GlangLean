import GLang.Elaboration.Elaboration

/-! Context embeddings for elaboration. A surface linear assumption may already
be nonlinear internally. This permits surface promotion without demoting an
internal declaration or reconstructing its hidden dependencies. -/
namespace GLang
theorem Surface.LCtx.toNL_lookup (lin : Surface.LCtx) (x : Name) (s : Surface.Space)
    (h : lin.lookup x = some s) : lin.toNL.lookup x = some (.space s) := by
  rw [Finmap.lookup_eq_some_iff] at h ⊢
  show (⟨x, .space s⟩ : Σ _ : Name, Surface.Ty) ∈
    lin.entries.map (fun e : Σ _ : Name, Surface.Space => ⟨e.1, Surface.Ty.space e.2⟩)
  exact Multiset.mem_map.mpr ⟨⟨x,s⟩,h,rfl⟩

namespace SurfaceElaboration

structure ContextEmbedding (d : Surface.LCtx) (g : Surface.NLCtx)
    (D : LCtx) (E : NLCtx) : Prop where
  nonlinear : ∀ x t, g.lookup x = some t →
    ∃ T, E.lookup x = some T ∧ T.erase = t
  linear : ∀ x s, d.lookup x = some s →
    (∃ S, D.lookup x = some S ∧ S.erase = s) ∨
    (∃ S, E.lookup x = some (.space S) ∧ S.erase = s)
  support : ∀ x S, D.lookup x = some S → d.lookup x = some S.erase

theorem ContextEmbedding.refl (D : LCtx) (E : NLCtx) :
    ContextEmbedding D.erase E.erase D E := by
  refine ⟨?_, ?_, ?_⟩
  · intro x t ht; exact (sourceMap_lookup_some _ _ _ _).mp ht
  · intro x s hs; exact Or.inl ((sourceMap_lookup_some _ _ _ _).mp hs)
  · intro x s hs; exact (sourceMap_lookup_some _ _ _ _).mpr ⟨s, hs, rfl⟩

theorem ContextEmbedding.empty_linear {g D E}
    (h : ContextEmbedding ∅ g D E) : D = ∅ := by
  apply Finmap.ext_lookup
  intro x
  cases hx : D.lookup x with
  | none => rfl
  | some S => have hh := h.support x S hx; simp at hh

theorem ContextEmbedding.with_empty_linear {d g D E}
    (h : ContextEmbedding d g D E) : ContextEmbedding ∅ g ∅ E := by
  refine ⟨h.nonlinear, ?_, ?_⟩ <;> intro x s hs <;> simp at hs

/-- Restriction changes only which linear resources remain, never their types. -/
noncomputable def restrictSource {A : Type} (m : Finmap (fun _ : Name => A))
    (keys : Finset Name) : Finmap (fun _ : Name => A) :=
  Finmap.keysLookupEquiv.symm ⟨(m.keys ∩ keys,
    fun x => if x ∈ keys then m.lookup x else none), by
      intro x
      by_cases hx : x ∈ keys <;> simp [hx, Finmap.lookup_isSome, Finmap.mem_keys]⟩

@[simp] theorem restrictSource_lookup {A : Type} (m : Finmap (fun _ : Name => A))
    (keys : Finset Name) (x : Name) :
    (restrictSource m keys).lookup x = if x ∈ keys then m.lookup x else none := by
  let p : {q : Finset Name × (Name → Option A) //
      ∀ z, (q.2 z).isSome ↔ z ∈ q.1} :=
    ⟨(m.keys ∩ keys, fun z => if z ∈ keys then m.lookup z else none), by
      intro z
      by_cases hz : z ∈ keys <;> simp [hz, Finmap.lookup_isSome, Finmap.mem_keys]⟩
  exact congrArg (fun q => q.val.2 x) (Finmap.keysLookupEquiv.apply_symm_apply p)

theorem restrictSource_lookup_some {A : Type} {m : Finmap (fun _ : Name => A)}
    {keys : Finset Name} {x a} :
    (restrictSource m keys).lookup x = some a ↔ x ∈ keys ∧ m.lookup x = some a := by
  rw [restrictSource_lookup]
  split <;> simp_all

/-- Formation alone supplies scope; namespace disjointness is the remaining
independent part of flat context well-formedness. -/
theorem contextWF_of_formed {D : LCtx} {E : NLCtx} (hd : ∀ x, x ∈ D → x ∉ E)
    (hv : SourceCtxValid D E) : Metatheory.SourceContextWF D E := by
  refine ⟨⟨hd, ?_, ?_⟩, ⟨hv⟩⟩
  · intro x s hs y hy
    exact Finmap.mem_keys.mp ((hv.linear x s hs).fv_closure hy)
  · intro x t ht y hy
    exact Finmap.mem_keys.mp ((hv.nonlinear x t ht).2.fv_closure hy)

theorem restrictSource_wf {D E} (hw : Metatheory.SourceContextWF D E) (keys : Finset Name) :
    Metatheory.SourceContextWF (restrictSource D keys) E := by
  obtain ⟨hv⟩ := hw.formed
  apply contextWF_of_formed
  · intro x hx hy
    obtain ⟨s, hs⟩ := Finmap.mem_iff.mp hx
    exact hw.scoping.disjoint x
      (Finmap.mem_of_lookup_eq_some (restrictSource_lookup_some.mp hs).2) hy
  · exact ⟨fun x s hs => hv.linear x s (restrictSource_lookup_some.mp hs).2,
      hv.nonlinear⟩

theorem ContextEmbedding.restrict {d g D E} (h : ContextEmbedding d g D E)
    (d' : Surface.LCtx) (hsub : ∀ x s, d'.lookup x = some s → d.lookup x = some s) :
    ContextEmbedding d' g (restrictSource D d'.keys) E := by
  refine ⟨h.nonlinear, ?_, ?_⟩
  · intro x s hs
    rcases h.linear x s (hsub x s hs) with ⟨S,hS,he⟩ | ⟨S,hS,he⟩
    · exact Or.inl ⟨S, restrictSource_lookup_some.mpr
        ⟨Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hs), hS⟩, he⟩
    · exact Or.inr ⟨S,hS,he⟩
  · intro x S hS
    obtain ⟨hx, hS⟩ := restrictSource_lookup_some.mp hS
    obtain ⟨s, hs⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hx)
    have he := (hsub x s hs).symm.trans (h.support x S hS)
    cases Option.some.inj he
    exact hs

theorem ContextEmbedding.split {d₀ d₁ g D E}
    (h : ContextEmbedding (d₀ ∪ d₁) g D E) (hd : Finmap.Disjoint d₀ d₁) :
    D = restrictSource D d₀.keys ∪ restrictSource D d₁.keys ∧
    Finmap.Disjoint (restrictSource D d₀.keys) (restrictSource D d₁.keys) ∧
    ContextEmbedding d₀ g (restrictSource D d₀.keys) E ∧
    ContextEmbedding d₁ g (restrictSource D d₁.keys) E := by
  have h₀ := h.restrict d₀ (fun x s hs => by
    rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hs)]; exact hs)
  have h₁ := h.restrict d₁ (fun x s hs => by
    rw [Finmap.lookup_union_right
      (fun hx => hd x hx (Finmap.mem_of_lookup_eq_some hs))]; exact hs)
  refine ⟨?_, ?_, h₀, h₁⟩
  · apply Finmap.ext_lookup
    intro x
    by_cases hx : x ∈ d₀
    · have hxk := Finmap.mem_keys.mpr hx
      by_cases hD : x ∈ D
      · have hr : x ∈ restrictSource D d₀.keys := by
          obtain ⟨s,hs⟩ := Finmap.mem_iff.mp hD
          exact Finmap.mem_of_lookup_eq_some (restrictSource_lookup_some.mpr ⟨hxk,hs⟩)
        simp [Finmap.lookup_union_left hr, hxk]
      · have hn := Finmap.lookup_eq_none.mpr hD
        have hr : x ∉ restrictSource D d₀.keys := by
          intro hm; obtain ⟨s,hs⟩ := Finmap.mem_iff.mp hm
          simp [hn] at hs
        rw [Finmap.lookup_union_right hr]
        simp [hn]
    · have hxk : x ∉ d₀.keys := fun hk => hx (Finmap.mem_keys.mp hk)
      have hr : x ∉ restrictSource D d₀.keys := by
        intro hm; obtain ⟨s,hs⟩ := Finmap.mem_iff.mp hm
        simp [hxk] at hs
      rw [Finmap.lookup_union_right hr, restrictSource_lookup]
      by_cases hx1 : x ∈ d₁.keys
      · simp [hx1]
      · simp only [if_neg hx1]
        apply Finmap.lookup_eq_none.mpr
        intro hm; obtain ⟨s,hs⟩ := Finmap.mem_iff.mp hm
        have hu := Finmap.mem_union.mp (Finmap.mem_of_lookup_eq_some (h.support x s hs))
        exact hu.elim hx (fun hm => hx1 (Finmap.mem_keys.mpr hm))
  · intro x hx hy
    obtain ⟨s,hs⟩ := Finmap.mem_iff.mp hx
    obtain ⟨t,ht⟩ := Finmap.mem_iff.mp hy
    exact hd x (Finmap.mem_keys.mp (restrictSource_lookup_some.mp hs).1)
      (Finmap.mem_keys.mp (restrictSource_lookup_some.mp ht).1)

/-- A surface promotion is absorbed by the existing nonlinear embedding. -/
theorem ContextEmbedding.promote {lin d g D E}
    (h : ContextEmbedding d ((Surface.LCtx.toNL lin) ∪ g) D E)
    (hd : Finmap.Disjoint lin d) (hg : Finmap.Disjoint (Surface.LCtx.toNL lin) g) :
    ContextEmbedding (lin ∪ d) g D E := by
  refine ⟨?_, ?_, ?_⟩
  · intro x t ht
    apply h.nonlinear x t
    rw [Finmap.lookup_union_right
      (fun hx => hg x hx (Finmap.mem_of_lookup_eq_some ht))]
    exact ht
  · intro x s hs
    by_cases hx : x ∈ lin
    · obtain ⟨s', hs'⟩ := Finmap.mem_iff.mp hx
      rw [Finmap.lookup_union_left hx, hs'] at hs
      cases Option.some.inj hs
      have hn := Surface.LCtx.toNL_lookup lin x s hs'
      obtain ⟨T,hT,he⟩ := h.nonlinear x (.space s)
        (by rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hn)]; exact hn)
      cases T with
      | space S => exact Or.inr ⟨S,hT,Surface.Ty.space.inj he⟩
      | piTy a b => simp [Ty.erase] at he
    · rw [Finmap.lookup_union_right hx] at hs
      exact h.linear x s hs
  · intro x S hS
    have hh := h.support x S hS
    rw [Finmap.lookup_union_right (fun hx => hd x hx (Finmap.mem_of_lookup_eq_some hh))]
    exact hh

/-- Extend both linear contexts with the same visible annotation. -/
theorem ContextEmbedding.insert_linear {d g D E s S x}
    (h : ContextEmbedding d g D E) (he : S.erase = s) :
    ContextEmbedding (Finmap.insert x s d) g (Finmap.insert x S D) E := by
  refine ⟨h.nonlinear, ?_, ?_⟩
  · intro y t ht
    by_cases hy : y = x
    · subst y
      simp only [Finmap.lookup_insert, Option.some.injEq] at ht
      subst t
      exact Or.inl ⟨S, Finmap.lookup_insert _, he⟩
    · rw [Finmap.lookup_insert_of_ne _ hy] at ht
      rcases h.linear y t ht with ⟨T,hT,heT⟩ | ⟨T,hT,heT⟩
      · exact Or.inl ⟨T, by rw [Finmap.lookup_insert_of_ne _ hy]; exact hT, heT⟩
      · exact Or.inr ⟨T,hT,heT⟩
  · intro y T hT
    by_cases hy : y = x
    · subst y
      simp only [Finmap.lookup_insert, Option.some.injEq] at hT
      subst T
      simp [he]
    · rw [Finmap.lookup_insert_of_ne _ hy] at hT ⊢
      exact h.support y T hT

/-- Extend nonlinear contexts together, choosing a name outside the surface
linear context so existing linear references retain their interpretation. -/
theorem ContextEmbedding.insert_nonlinear {d g D E t T x}
    (h : ContextEmbedding d g D E) (hx : x ∉ d) (he : T.erase = t) :
    ContextEmbedding d (Finmap.insert x t g) D (Finmap.insert x T E) := by
  refine ⟨?_, ?_, h.support⟩
  · intro y a ha
    by_cases hy : y = x
    · subst y
      simp only [Finmap.lookup_insert, Option.some.injEq] at ha
      subst a
      exact ⟨T, Finmap.lookup_insert _, he⟩
    · rw [Finmap.lookup_insert_of_ne _ hy] at ha
      obtain ⟨A,hA,heA⟩ := h.nonlinear y a ha
      exact ⟨A, by rw [Finmap.lookup_insert_of_ne _ hy]; exact hA, heA⟩
  · intro y a ha
    have hy : y ≠ x := fun heq => hx (heq ▸ Finmap.mem_of_lookup_eq_some ha)
    rcases h.linear y a ha with ⟨A,hA,heA⟩ | ⟨A,hA,heA⟩
    · exact Or.inl ⟨A,hA,heA⟩
    · exact Or.inr ⟨A, by rw [Finmap.lookup_insert_of_ne _ hy]; exact hA, heA⟩

theorem wf_empty_linear {D E} (h : Metatheory.SourceContextWF D E) :
    Metatheory.SourceContextWF ∅ E := by
  obtain ⟨hv⟩ := h.formed
  apply contextWF_of_formed (fun _ hx => (Finmap.notMem_empty hx).elim)
  exact ⟨fun _ _ hx => by simp at hx, hv.nonlinear⟩

theorem wf_insert_linear {D E x S} (h : Metatheory.SourceContextWF D E)
    (hx : x ∉ E) (hvS : SValid E S) :
    Metatheory.SourceContextWF (Finmap.insert x S D) E := by
  obtain ⟨hv⟩ := h.formed
  apply contextWF_of_formed
  · intro y hy
    rcases Finmap.mem_insert.mp hy with rfl | hy
    · exact hx
    · exact h.scoping.disjoint y hy
  · refine ⟨?_, hv.nonlinear⟩
    intro y s hs
    by_cases hy : y = x
    · subst y
      simp only [Finmap.lookup_insert, Option.some.injEq] at hs
      cases hs
      exact hvS
    · rw [Finmap.lookup_insert_of_ne _ hy] at hs
      exact hv.linear y s hs

theorem wf_insert_nonlinear {D E x T k} (h : Metatheory.SourceContextWF D E)
    (hxD : x ∉ D) (hxE : x ∉ E) (hvT : TValid E T k) :
    Metatheory.SourceContextWF D (Finmap.insert x T E) := by
  obtain ⟨hv⟩ := h.formed
  apply contextWF_of_formed
  · intro y hy hm
    rcases Finmap.mem_insert.mp hm with rfl | hm
    · exact hxD hy
    · exact h.scoping.disjoint y hy hm
  · refine ⟨fun y s hs => SValid.weakenInsertNL x T hxE (hv.linear y s hs), ?_⟩
    intro y t ht
    by_cases hy : y = x
    · subst y
      simp only [Finmap.lookup_insert, Option.some.injEq] at ht
      cases ht
      exact ⟨k, TValid.weakenInsertNL x T hxE hvT⟩
    · rw [Finmap.lookup_insert_of_ne _ hy] at ht
      obtain ⟨j,hj⟩ := hv.nonlinear y t ht
      exact ⟨j,TValid.weakenInsertNL x T hxE hj⟩

noncomputable def resultValid {D E e T} (hw : Metatheory.SourceContextWF D E)
    (h : HasType D E e T) : Σ k, TValid E T k :=
  Graded.hasType_regular hw.scoping.disjoint
    (Graded.ctxValid_tr hw.scoping.disjoint hw.formed.some.linear hw.formed.some.nonlinear) h

/-- Align an elaborated term's result with an independently elaborated expected
type. The existing annotation-uniqueness theorem justifies the equality. -/
noncomputable def alignResult {D E e T U k}
    (hw : Metatheory.SourceContextWF D E) (h : HasType D E e T)
    (hu : TValid E U k) (he : T.erase = U.erase) : HasType D E e U := by
  have hh := TValid.annotation_unique (resultValid hw h).2 hu he
  cases hh
  exact h

private theorem singleton_support {g D E x s y S}
    (h : ContextEmbedding (Finmap.singleton x s) g D E)
    (hy : D.lookup y = some S) : y = x := by
  have hh := Finmap.mem_of_lookup_eq_some (h.support y S hy)
  simpa using hh

theorem ContextEmbedding.singleton_linear {g D E x s S}
    (h : ContextEmbedding (Finmap.singleton x s) g D E)
    (hx : D.lookup x = some S) : D = Finmap.singleton x S := by
  apply Finmap.ext_lookup
  intro y
  by_cases hy : y = x
  · subst y; simpa using hx
  · have hD : D.lookup y = none := by
      cases hh : D.lookup y with
      | none => rfl
      | some T => exact (hy (singleton_support h hh)).elim
    have hs : (Finmap.singleton x S : LCtx).lookup y = none :=
      Finmap.lookup_eq_none.mpr (by simpa using hy)
    rw [hD, hs]

theorem ContextEmbedding.singleton_nonlinear {g D E x s S}
    (h : ContextEmbedding (Finmap.singleton x s) g D E)
    (hw : Metatheory.SourceContextWF D E)
    (hx : E.lookup x = some (.space S)) : D = ∅ := by
  apply Finmap.ext_lookup
  intro y
  cases hy : D.lookup y with
  | none => rfl
  | some T =>
    have hh := singleton_support h hy
    subst y
    exact (hw.scoping.disjoint x (Finmap.mem_of_lookup_eq_some hy)
      (Finmap.mem_of_lookup_eq_some hx)).elim

end SurfaceElaboration
end GLang
