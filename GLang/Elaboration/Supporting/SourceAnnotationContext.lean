import GLang.Elaboration.Erasure
import GLang.Annotated.Judgments

/-!
# Infrastructure for source annotation uniqueness

Promotion changes the linear/nonlinear partition. A uniqueness induction
therefore compares the types assigned to names, not identical partitions.
`SourceBinding` records that common assignment without forgetting a possible
collision between the two contexts. The variable case below is fully proved,
including arbitrary promotion chains. The companion `SourceAnnotationUniqueness` proves full mutually recursive
space/type/term coherence using these invariants.
-/

namespace GLang

/-- The type assigned to a free name by either component of a source context. -/
def SourceBinding (Δ : LCtx) (ε : NLCtx) (x : Name) (τ : Ty) : Prop :=
  (∃ s, Δ.lookup x = some s ∧ τ = .space s) ∨ ε.lookup x = some τ

/-- Promotion preserves the name/type assignment, not just the set of names. -/
theorem SourceBinding.promote_iff (lin Δ : LCtx) (ε : NLCtx) (x : Name) (τ : Ty)
    (hdΔ : Finmap.Disjoint lin Δ) (hdε : Finmap.Disjoint lin.toNL ε) :
    SourceBinding (lin ∪ Δ) ε x τ ↔ SourceBinding Δ (lin.toNL ∪ ε) x τ := by
  by_cases hx : x ∈ lin
  · obtain ⟨s, hs⟩ := Finmap.mem_iff.mp hx
    have hxt : x ∈ lin.toNL := (LCtx.mem_toNL_iff lin x).mpr hx
    have hΔ : Δ.lookup x = none := Finmap.lookup_eq_none.mpr (hdΔ x hx)
    have hε : ε.lookup x = none := Finmap.lookup_eq_none.mpr (hdε x hxt)
    have ht := lin.toNL_lookup x s hs
    simp [SourceBinding, Finmap.lookup_union_left hx, Finmap.lookup_union_left hxt,
      hs, ht, hΔ, hε, eq_comm]
  · have hxt : x ∉ lin.toNL := fun h => hx ((LCtx.mem_toNL_iff lin x).mp h)
    simp only [SourceBinding, Finmap.lookup_union_right hx, Finmap.lookup_union_right hxt]

/-- Each branch of a linear split preserves its assignments in the whole context. -/
theorem SourceBinding.split_iff (Δ₀ Δ₁ : LCtx) (ε : NLCtx) (x : Name) (τ : Ty)
    (hd : Finmap.Disjoint Δ₀ Δ₁) :
    SourceBinding (Δ₀ ∪ Δ₁) ε x τ ↔
      SourceBinding Δ₀ ε x τ ∨ SourceBinding Δ₁ ε x τ := by
  by_cases hx : x ∈ Δ₀
  · have h₁ : Δ₁.lookup x = none := Finmap.lookup_eq_none.mpr (hd x hx)
    simp [SourceBinding, Finmap.lookup_union_left hx, h₁]
  · have h₀ : Δ₀.lookup x = none := Finmap.lookup_eq_none.mpr hx
    simp [SourceBinding, Finmap.lookup_union_right hx, h₀, or_comm]

/-- Variable typing records an actual context binding, even through promotion. -/
theorem HasType.var_sourceBinding {Δ : LCtx} {ε : NLCtx} {x : Name} {τ : Ty}
    (h : HasType Δ ε (.var x) τ) : SourceBinding Δ ε x τ :=
  match h with
  | .var_lin => Or.inl ⟨_, Finmap.lookup_singleton_eq, rfl⟩
  | .var_nlin hl => Or.inr hl
  | .promote lin _ hdε _ h => by
    rcases h.var_sourceBinding with ⟨s, hs, rfl⟩ | hs
    · by_cases hx : x ∈ lin
      · rw [Finmap.lookup_union_left hx] at hs
        apply Or.inr
        rw [Finmap.lookup_union_left ((LCtx.mem_toNL_iff lin x).mpr hx)]
        exact lin.toNL_lookup x s hs
      · rw [Finmap.lookup_union_right hx] at hs
        exact Or.inl ⟨s, hs, rfl⟩
    · apply Or.inr
      rw [Finmap.lookup_union_right]
      · exact hs
      · intro hx
        exact hdε x hx (Finmap.mem_of_lookup_eq_some hs)

/-- Disjoint context components assign at most one type to a name. -/
theorem SourceBinding.functional {Δ : LCtx} {ε : NLCtx} {x : Name} {τ₁ τ₂ : Ty}
    (hd : ∀ y, y ∈ Δ → y ∉ ε)
    (h₁ : SourceBinding Δ ε x τ₁) (h₂ : SourceBinding Δ ε x τ₂) : τ₁ = τ₂ := by
  rcases h₁ with ⟨s₁, hs₁, rfl⟩ | h₁
  · rcases h₂ with ⟨s₂, hs₂, rfl⟩ | h₂
    · have he := Option.some.inj (hs₁.symm.trans hs₂)
      exact congrArg Ty.space he
    · exact (hd x (Finmap.mem_of_lookup_eq_some hs₁)
        (Finmap.mem_of_lookup_eq_some h₂)).elim
  · rcases h₂ with ⟨s₂, hs₂, rfl⟩ | h₂
    · exact (hd x (Finmap.mem_of_lookup_eq_some hs₂)
        (Finmap.mem_of_lookup_eq_some h₁)).elim
    · exact Option.some.inj (h₁.symm.trans h₂)

/-- The variable result type is unique in a context with disjoint namespaces. -/
theorem HasType.var_type_unique {Δ : LCtx} {ε : NLCtx} {x : Name} {τ₁ τ₂ : Ty}
    (hd : ∀ y, y ∈ Δ → y ∉ ε)
    (h₁ : HasType Δ ε (.var x) τ₁) (h₂ : HasType Δ ε (.var x) τ₂) : τ₁ = τ₂ :=
  SourceBinding.functional hd h₁.var_sourceBinding h₂.var_sourceBinding

/-- Agreement of any name bound in both contexts; partitions may differ. -/
def SourceCtxCompatible (Δ₁ : LCtx) (ε₁ : NLCtx) (Δ₂ : LCtx) (ε₂ : NLCtx) : Prop :=
  ∀ x τ₁ τ₂, SourceBinding Δ₁ ε₁ x τ₁ → SourceBinding Δ₂ ε₂ x τ₂ → τ₁ = τ₂

/-- Compatibility restricts along binding inclusions in either context. -/
theorem SourceCtxCompatible.mono {Δ₁ ε₁ Δ₂ ε₂ Δ₁' ε₁' Δ₂' ε₂'}
    (h : SourceCtxCompatible Δ₁ ε₁ Δ₂ ε₂)
    (h₁ : ∀ x τ, SourceBinding Δ₁' ε₁' x τ → SourceBinding Δ₁ ε₁ x τ)
    (h₂ : ∀ x τ, SourceBinding Δ₂' ε₂' x τ → SourceBinding Δ₂ ε₂ x τ) :
    SourceCtxCompatible Δ₁' ε₁' Δ₂' ε₂' :=
  fun x τ₁ τ₂ b₁ b₂ => h x τ₁ τ₂ (h₁ x τ₁ b₁) (h₂ x τ₂ b₂)

/-- A source derivation is core when its last rule is not promotion. -/
def HasType.IsCore {Δ ε e τ} (h : HasType Δ ε e τ) : Prop :=
  match h with
  | .promote _ _ _ _ _ => False
  | _ => True

/-- Inversion retaining the assignment of every free name across promotion. -/
structure HasType.CoreView (Δ : LCtx) (ε : NLCtx) (e : Term) (τ : Ty) where
  lin : LCtx
  nonlin : NLCtx
  derivation : HasType lin nonlin e τ
  isCore : derivation.IsCore
  binding : ∀ x υ, SourceBinding lin nonlin x υ → SourceBinding Δ ε x υ

/-- Remove a finite chain of final promotion rules, preserving name/type bindings. -/
def HasType.coreView {Δ ε e τ} (h : HasType Δ ε e τ) : CoreView Δ ε e τ :=
  match h with
  | .promote lin hdΔ hdε _ h =>
      let v := h.coreView
      ⟨v.lin, v.nonlin, v.derivation, v.isCore, fun x υ b =>
        (SourceBinding.promote_iff lin _ _ x υ hdΔ hdε).mp (v.binding x υ b)⟩
  | .zero h0 => ⟨Δ, ε, .zero h0, True.intro, fun _ _ b => b⟩
  | .smul h0 h1 h2 h3 => ⟨_, _, .smul h0 h1 h2 h3, True.intro, fun _ _ b => b⟩
  | .add h0 h1 h2 => ⟨_, _, .add h0 h1 h2, True.intro, fun _ _ b => b⟩
  | .inner h0 => ⟨_, _, .inner h0, True.intro, fun _ _ b => b⟩
  | .real_lit h0 => ⟨∅, ε, .real_lit h0, True.intro, fun _ _ b => b⟩
  | .app_linear h0 h1 h2 h3 h4 => ⟨_, _, .app_linear h0 h1 h2 h3 h4, True.intro, fun _ _ b => b⟩
  | .app_inner h0 h1 h2 h3 => ⟨_, _, .app_inner h0 h1 h2 h3, True.intro, fun _ _ b => b⟩
  | .app_nonlinear h0 h1 => ⟨_, _, .app_nonlinear h0 h1, True.intro, fun _ _ b => b⟩
  | .var_lin => ⟨_, ε, .var_lin, True.intro, fun _ _ b => b⟩
  | .var_nlin h0 => ⟨_, _, .var_nlin h0, True.intro, fun _ _ b => b⟩
  | .pinv_tensor h0 h1 h2 => ⟨_, _, .pinv_tensor h0 h1 h2, True.intro, fun _ _ b => b⟩
  | .pinv_dual h0 h1 => ⟨_, _, .pinv_dual h0 h1, True.intro, fun _ _ b => b⟩
  | .dsumE h0 h1 h2 h3 => ⟨_, _, .dsumE h0 h1 h2 h3, True.intro, fun _ _ b => b⟩
  | .tprodE h0 h1 h2 h3 h4 => ⟨_, _, .tprodE h0 h1 h2 h3 h4, True.intro, fun _ _ b => b⟩
  | .llam_real h0 h1 h2 => ⟨_, _, .llam_real h0 h1 h2, True.intro, fun _ _ b => b⟩
  | .llam_tensor h0 h1 h2 h3 h4 => ⟨_, _, .llam_tensor h0 h1 h2 h3 h4, True.intro, fun _ _ b => b⟩
  | .embed h0 => ⟨_, _, .embed h0, True.intro, fun _ _ b => b⟩
  | .nllam h0 h1 h2 => ⟨_, _, .nllam h0 h1 h2, True.intro, fun _ _ b => b⟩

/-- Forgetting linear bindings preserves compatibility. -/
theorem SourceCtxCompatible.nonlin {Δ₁ ε₁ Δ₂ ε₂}
    (h : SourceCtxCompatible Δ₁ ε₁ Δ₂ ε₂) : SourceCtxCompatible ∅ ε₁ ∅ ε₂ := by
  apply h.mono <;> intro x τ b <;> rcases b with ⟨s, hs, _⟩ | b
  all_goals first | simp at hs | exact Or.inr b

/-- Common fresh linear extension preserves compatibility. -/
theorem SourceCtxCompatible.insertLin {Δ₁ ε₁ Δ₂ ε₂}
    (h : SourceCtxCompatible Δ₁ ε₁ Δ₂ ε₂) (x : Name) (s : Space)
    (hx₁ : x ∉ ε₁) (hx₂ : x ∉ ε₂) :
    SourceCtxCompatible (Finmap.insert x s Δ₁) ε₁ (Finmap.insert x s Δ₂) ε₂ := by
  intro y τ₁ τ₂ b₁ b₂
  by_cases hy : y = x
  · subst y
    have hε₁ := Finmap.lookup_eq_none.mpr hx₁
    have hε₂ := Finmap.lookup_eq_none.mpr hx₂
    simp [SourceBinding, hε₁, hε₂] at b₁ b₂
    exact b₁.trans b₂.symm
  · apply h y τ₁ τ₂
    · simpa only [SourceBinding, Finmap.lookup_insert_of_ne _ hy] using b₁
    · simpa only [SourceBinding, Finmap.lookup_insert_of_ne _ hy] using b₂

/-- Common fresh nonlinear extension preserves compatibility. -/
theorem SourceCtxCompatible.insertNL {Δ₁ ε₁ Δ₂ ε₂}
    (h : SourceCtxCompatible Δ₁ ε₁ Δ₂ ε₂) (x : Name) (τ : Ty)
    (hx₁ : x ∉ Δ₁) (hx₂ : x ∉ Δ₂) :
    SourceCtxCompatible Δ₁ (Finmap.insert x τ ε₁) Δ₂ (Finmap.insert x τ ε₂) := by
  intro y τ₁ τ₂ b₁ b₂
  by_cases hy : y = x
  · subst y
    have hΔ₁ := Finmap.lookup_eq_none.mpr hx₁
    have hΔ₂ := Finmap.lookup_eq_none.mpr hx₂
    simp [SourceBinding, hΔ₁, hΔ₂] at b₁ b₂
    exact b₁.symm.trans b₂
  · apply h y τ₁ τ₂
    · simpa only [SourceBinding, Finmap.lookup_insert_of_ne _ hy] using b₁
    · simpa only [SourceBinding, Finmap.lookup_insert_of_ne _ hy] using b₂

/-- Restrict the linear contexts to either branch of a disjoint split. -/
theorem SourceCtxCompatible.split {Δ₀ Δ₁ ε Δ₀' Δ₁' ε'}
    (h : SourceCtxCompatible (Δ₀ ∪ Δ₁) ε (Δ₀' ∪ Δ₁') ε')
    (hd : Finmap.Disjoint Δ₀ Δ₁) (hd' : Finmap.Disjoint Δ₀' Δ₁') :
    SourceCtxCompatible Δ₀ ε Δ₀' ε' ∧ SourceCtxCompatible Δ₁ ε Δ₁' ε' := by
  constructor
  · exact h.mono
      (fun x τ b => (SourceBinding.split_iff _ _ _ x τ hd).mpr (Or.inl b))
      (fun x τ b => (SourceBinding.split_iff _ _ _ x τ hd').mpr (Or.inl b))
  · exact h.mono
      (fun x τ b => (SourceBinding.split_iff _ _ _ x τ hd).mpr (Or.inr b))
      (fun x τ b => (SourceBinding.split_iff _ _ _ x τ hd').mpr (Or.inr b))

/-- Compatibility is symmetric. -/
theorem SourceCtxCompatible.symm {Δ₁ ε₁ Δ₂ ε₂}
    (h : SourceCtxCompatible Δ₁ ε₁ Δ₂ ε₂) : SourceCtxCompatible Δ₂ ε₂ Δ₁ ε₁ :=
  fun x τ₂ τ₁ b₂ b₁ => (h x τ₁ τ₂ b₁ b₂).symm

/-- Restrict only the left context to the branches of a disjoint split. -/
theorem SourceCtxCompatible.splitLeft {Δ₀ Δ₁ ε Δ' ε'}
    (h : SourceCtxCompatible (Δ₀ ∪ Δ₁) ε Δ' ε') (hd : Finmap.Disjoint Δ₀ Δ₁) :
    SourceCtxCompatible Δ₀ ε Δ' ε' ∧ SourceCtxCompatible Δ₁ ε Δ' ε' :=
  ⟨h.mono (fun x τ b => (SourceBinding.split_iff _ _ _ x τ hd).mpr (Or.inl b))
      (fun _ _ b => b),
   h.mono (fun x τ b => (SourceBinding.split_iff _ _ _ x τ hd).mpr (Or.inr b))
      (fun _ _ b => b)⟩

/-- Restrict only the right context to the branches of a disjoint split. -/
theorem SourceCtxCompatible.splitRight {Δ ε Δ₀' Δ₁' ε'}
    (h : SourceCtxCompatible Δ ε (Δ₀' ∪ Δ₁') ε') (hd : Finmap.Disjoint Δ₀' Δ₁') :
    SourceCtxCompatible Δ ε Δ₀' ε' ∧ SourceCtxCompatible Δ ε Δ₁' ε' :=
  ⟨(h.symm.splitLeft hd).1.symm, (h.symm.splitLeft hd).2.symm⟩

end GLang
