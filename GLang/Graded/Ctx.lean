import GLang.Graded.Rig
import GLang.Annotated.Judgments

namespace GLang.Graded

open GLang

/-- Graded context (function model, not a `Finmap`). -/
abbrev GCtx := Name → Option (GGrade × Ty)

/-- Translate the two-context world into ONE graded context:
    linear `x : s` ↦ grade `1` at type `.space s`; nonlinear `x : τ` ↦ grade `ω`. -/
def tr (Δ : LCtx) (ε : NLCtx) : GCtx := fun x =>
  match Δ.lookup x with
  | some s => some (.one, .space s)
  | none   => match ε.lookup x with
              | some τ => some (.omega, τ)
              | none   => none

/-- Two split branches AGREE on the type of every var present in BOTH. -/
def TypeAgree (Γ₀ Γ₁ : GCtx) : Prop :=
  ∀ x g₀ τ₀ g₁ τ₁, Γ₀ x = some (g₀, τ₀) → Γ₁ x = some (g₁, τ₁) → τ₀ = τ₁

-- Exposes ONLY ω (parameter) bindings to type formation. Grade-0 is NOT type-visible.

def typeCtxOmega (Γ : GCtx) : Name → Option Ty := fun x =>
  match Γ x with
  | some (.omega, τ) => some τ
  | _                => none

/-- Pointwise context weakening (types fixed, grades weaken). -/
def GCtx.Wk (Γ Γ' : GCtx) : Prop := ∀ x,
  match Γ x, Γ' x with
  | none, none => True
  | some (g, τ), some (g', τ') => τ = τ' ∧ GGrade.Wk g g'
  | _, _ => False

/-- Pointwise context addition on a single position: both present ⇒ `GGrade.add`,
    keeping the LEFT type; one present ⇒ that one; else none. -/
def gadd : Option (GGrade × Ty) → Option (GGrade × Ty) → Option (GGrade × Ty)
  | none, o => o
  | some p, none => some p
  | some (g₀, τ₀), some (g₁, _) => some (GGrade.add g₀ g₁, τ₀)

/-- Graded context addition (pointwise `gadd`). -/
def GCtx.add (Γ₀ Γ₁ : GCtx) : GCtx := fun x => gadd (Γ₀ x) (Γ₁ x)

/-- `f ⊑ g`: `g` agrees with `f` wherever `f` is defined (`g` may expose MORE). -/
def SubMap (f g : Name → Option Ty) : Prop := ∀ x τ, f x = some τ → g x = some τ

/-! ## `promote` is a grade-weakening (resource side), with NO freshness. -/

/-- `promote : HasType (lin ∪ Δ) ε' e τ → HasType Δ (lin.toNL ∪ ε') e τ` moves
    `lin` from linear to nonlinear. Under `tr` that is EXACTLY a `1→ω` bump on
    `lin`, types preserved — needing only the disjointness `lin ∩ Δ = ∅` that
    `promote` already carries. **No `PromoteFresh`.** -/
theorem tr_promote_wk (lin Δ : LCtx) (ε' : NLCtx)
    (hdisjΔ : Finmap.Disjoint lin Δ) :
    GCtx.Wk (tr (lin ∪ Δ) ε') (tr Δ (lin.toNL ∪ ε')) := by
  intro x
  simp only [tr]
  cases hlin : lin.lookup x with
  | some s =>
      have hxlin : x ∈ lin := Finmap.mem_of_lookup_eq_some hlin
      have hxΔ : x ∉ Δ := fun h => (hdisjΔ x hxlin) h
      have hΔnone : Δ.lookup x = none := Finmap.lookup_eq_none.mpr hxΔ
      have hunionL : (lin ∪ Δ).lookup x = some s := by
        rw [Finmap.lookup_union_left hxlin]; exact hlin
      have htoNL : (lin.toNL).lookup x = some (.space s) := LCtx.toNL_lookup lin x s hlin
      have hunionR : (lin.toNL ∪ ε').lookup x = some (.space s) := by
        rw [Finmap.lookup_union_left ((LCtx.mem_toNL_iff lin x).mpr hxlin)]; exact htoNL
      rw [hunionL, hΔnone, hunionR]
      exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  | none =>
      have hxnotlin : x ∉ lin := Finmap.lookup_eq_none.mp hlin
      have hunionL : (lin ∪ Δ).lookup x = Δ.lookup x := by
        rw [Finmap.lookup_union_right hxnotlin]
      have hxnottoNL : x ∉ lin.toNL := fun h => hxnotlin ((LCtx.mem_toNL_iff lin x).mp h)
      have hunionR : (lin.toNL ∪ ε').lookup x = ε'.lookup x := by
        rw [Finmap.lookup_union_right hxnottoNL]
      rw [hunionL, hunionR]
      cases Δ.lookup x with
      | some s' => exact ⟨rfl, GGrade.Wk.refl _⟩
      | none => cases ε'.lookup x with
                | some τ => exact ⟨rfl, GGrade.Wk.refl _⟩
                | none => trivial

/-- **The ω-only refinement.** `promote` WEAKENS the type-formation context — never
    strengthens it. Under ω-only resurrection, `promote` (`z : 1→ω`) makes `lin`
    newly type-visible, so the outer type-context is a `SubMap`-superset of the
    inner. Needs only `promote`'s disjointness; NO `PromoteFresh`. -/
theorem typeCtxOmega_promote_weakens (lin Δ : LCtx) (ε' : NLCtx)
    (_hdisjΔ : Finmap.Disjoint lin Δ) :
    SubMap (typeCtxOmega (tr (lin ∪ Δ) ε')) (typeCtxOmega (tr Δ (lin.toNL ∪ ε'))) := by
  intro x τ hx
  simp only [typeCtxOmega, tr] at hx ⊢
  cases hlu : (lin ∪ Δ).lookup x with
  | some s => rw [hlu] at hx; simp at hx
  | none =>
      rw [hlu] at hx
      cases hε : ε'.lookup x with
      | none => rw [hε] at hx; simp at hx
      | some τ' =>
          rw [hε] at hx
          simp only [Option.some.injEq] at hx
          have hxnl : x ∉ lin := fun h => by
            have : (lin ∪ Δ).lookup x ≠ none := by
              rw [Finmap.lookup_union_left h]; exact Finmap.lookup_eq_none.not.mpr (by simp [h])
            exact this hlu
          have hxnottoNL : x ∉ lin.toNL := fun h => hxnl ((LCtx.mem_toNL_iff lin x).mp h)
          have hxnotΔ : x ∉ Δ := fun h => by
            have : (lin ∪ Δ).lookup x ≠ none := by
              rw [Finmap.lookup_union_right (fun hh => hxnl hh)]
              exact Finmap.lookup_eq_none.not.mpr (by simp [h])
            exact this hlu
          rw [Finmap.lookup_eq_none.mpr hxnotΔ, Finmap.lookup_union_right hxnottoNL, hε]
          simp [hx]

end GLang.Graded
