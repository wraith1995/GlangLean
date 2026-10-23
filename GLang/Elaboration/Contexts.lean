import GLang.Surface.Judgments
import GLang.Elaboration.BasisErasure
import GLang.Annotated.Judgments

/-! Pointwise erasure of finite typing contexts. -/
namespace GLang

def sourceMap {α β : Type} (f : α → β) (Γ : @Finmap Name (fun _ => α)) :
    @Finmap Name (fun _ => β) where
  entries := Γ.entries.map (fun e => ⟨e.1, f e.2⟩)
  nodupKeys := by
    rw [← Multiset.nodup_keys]
    change ((Γ.entries.map _).map Sigma.fst).Nodup
    simpa only [Multiset.map_map] using Multiset.nodup_keys.mpr Γ.nodupKeys

theorem sourceMap_lookup_some {α β : Type} (f : α → β)
    (Γ : @Finmap Name (fun _ => α)) (x : Name) (b : β) :
    (sourceMap f Γ).lookup x = some b ↔ ∃ a, Γ.lookup x = some a ∧ f a = b := by
  simp only [Finmap.lookup_eq_some_iff, sourceMap, Multiset.mem_map]
  constructor
  · rintro ⟨⟨y,a⟩, ha, he⟩
    cases he
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨x,a⟩, ha, rfl⟩

@[simp] theorem sourceMap_lookup {α β : Type} (f : α → β)
    (Γ : @Finmap Name (fun _ => α)) (x : Name) :
    (sourceMap f Γ).lookup x = (Γ.lookup x).map f := by
  cases h : Γ.lookup x with
  | some a => exact (sourceMap_lookup_some f Γ x _).mpr ⟨a, h, rfl⟩
  | none =>
    cases h' : (sourceMap f Γ).lookup x with
    | none => rfl
    | some b =>
      obtain ⟨a, ha, _⟩ := (sourceMap_lookup_some f Γ x b).mp h'
      simp [h] at ha

@[simp] theorem sourceMap_mem {α β : Type} (f : α → β)
    (Γ : @Finmap Name (fun _ => α)) (x : Name) :
    x ∈ sourceMap f Γ ↔ x ∈ Γ := by
  simp only [Finmap.mem_iff, sourceMap_lookup_some]
  aesop

@[simp] theorem sourceMap_empty {α β : Type} (f : α → β) :
    sourceMap f ∅ = ∅ := by
  apply Finmap.ext_lookup
  intro x
  simp

@[simp] theorem sourceMap_insert {α β : Type} (f : α → β)
    (Γ : @Finmap Name (fun _ => α)) (x : Name) (a : α) :
    sourceMap f (Finmap.insert x a Γ) = Finmap.insert x (f a) (sourceMap f Γ) := by
  apply Finmap.ext_lookup
  intro y
  by_cases h : y = x
  · subst y; simp
  · simp [Finmap.lookup_insert_of_ne _ h]

@[simp] theorem sourceMap_singleton {α β : Type} (f : α → β) (x : Name) (a : α) :
    sourceMap f (Finmap.singleton x a) = Finmap.singleton x (f a) := by
  apply Finmap.ext_lookup
  intro y
  by_cases h : y = x
  · subst y; simp
  · have ha : (@Finmap.singleton Name (fun _ => α) x a).lookup y = none :=
      Finmap.lookup_eq_none.mpr (by simpa using h)
    have hb : (@Finmap.singleton Name (fun _ => β) x (f a)).lookup y = none :=
      Finmap.lookup_eq_none.mpr (by simpa using h)
    simp [ha, hb]

@[simp] theorem sourceMap_union {α β : Type} (f : α → β)
    (Γ Δ : @Finmap Name (fun _ => α)) :
    sourceMap f (Γ ∪ Δ) = sourceMap f Γ ∪ sourceMap f Δ := by
  apply Finmap.ext_lookup
  intro x
  by_cases h : x ∈ Γ
  · simp [Finmap.lookup_union_left h, Finmap.lookup_union_left ((sourceMap_mem f Γ x).mpr h)]
  · simp [Finmap.lookup_union_right h,
      Finmap.lookup_union_right (fun hx => h ((sourceMap_mem f Γ x).mp hx))]

theorem sourceMap_disjoint {α β : Type} (f : α → β)
    {Γ Δ : @Finmap Name (fun _ => α)} (h : Finmap.Disjoint Γ Δ) :
    Finmap.Disjoint (sourceMap f Γ) (sourceMap f Δ) := by
  intro x hx hy
  exact h x ((sourceMap_mem f Γ x).mp hx) ((sourceMap_mem f Δ x).mp hy)

abbrev LCtx.erase (Δ : LCtx) : Surface.LCtx := sourceMap Space.erase Δ
abbrev NLCtx.erase (ε : NLCtx) : Surface.NLCtx := sourceMap Ty.erase ε

end GLang
