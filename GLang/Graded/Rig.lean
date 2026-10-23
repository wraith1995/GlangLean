import Mathlib.Tactic

namespace GLang.Graded

/-- Resource grades: `0` (unused / type-only), `1` (linear), `ω` (unrestricted). -/
inductive GGrade | zero | one | omega
deriving DecidableEq

namespace GGrade

/-! ## Addition (context split / duplication) -/

/-- Grade addition: `0` is the identity, `1 + 1 = ω`, `ω` absorbs. -/
def add : GGrade → GGrade → GGrade
  | .zero,  g      => g
  | .one,   .zero  => .one
  | .one,   .one   => .omega
  | .one,   .omega => .omega
  | .omega, _      => .omega

@[simp] theorem zero_add (g : GGrade) : add .zero g = g := rfl

@[simp] theorem add_zero (g : GGrade) : add g .zero = g := by
  cases g <;> rfl

@[simp] theorem omega_add (g : GGrade) : add .omega g = .omega := rfl

@[simp] theorem add_omega (g : GGrade) : add g .omega = .omega := by cases g <;> rfl

theorem add_comm (a b : GGrade) : add a b = add b a := by
  cases a <;> cases b <;> rfl

theorem add_assoc (a b c : GGrade) : add (add a b) c = add a (add b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## Multiplication (scaling) -/

/-- Grade multiplication (scaling): `0 · _ = 0`, `1 · g = g`, `ω` scales
    nonzero grades to `ω`. -/
def mul : GGrade → GGrade → GGrade
  | .zero,  _      => .zero
  | .one,   g      => g
  | .omega, .zero  => .zero
  | .omega, .one   => .omega
  | .omega, .omega => .omega

@[simp] theorem zero_mul (g : GGrade) : mul .zero g = .zero := rfl

@[simp] theorem one_mul (g : GGrade) : mul .one g = g := rfl

@[simp] theorem mul_zero (g : GGrade) : mul g .zero = .zero := by
  cases g <;> rfl

@[simp] theorem mul_one (g : GGrade) : mul g .one = g := by
  cases g <;> rfl

/-! ## The weakening / promotion order -/

/-- Grade weakening: reflexive, plus the single promotion step `1 ⊑ ω`. -/
def Wk (g g' : GGrade) : Prop := g = g' ∨ (g = .one ∧ g' = .omega)

@[refl] theorem Wk.refl (g : GGrade) : Wk g g := Or.inl rfl

theorem Wk.trans {a b c : GGrade} (h₁ : Wk a b) (h₂ : Wk b c) : Wk a c := by
  rcases h₁ with rfl | ⟨rfl, rfl⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨h, _⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd h (by decide)

/-- `add` is monotone under `Wk`: weakening both summands weakens the sum. -/
theorem add_wk_mono {a a' b b' : GGrade}
    (ha : Wk a a') (hb : Wk b b') : Wk (add a b) (add a' b') := by
  rcases ha with rfl | ⟨rfl, rfl⟩ <;> rcases hb with rfl | ⟨rfl, rfl⟩
  · exact Wk.refl _
  · cases a
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
  · cases b
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Wk.refl _

end GGrade
end GLang.Graded
