import GLang.Numerics.SVD.ValueNumericalInputs

/-! Checked access for finite value payloads and local stacks.
These helpers never interpret a failed read as zero or a default value. -/
namespace GLang

namespace FlatArray

/-- Read a runtime index, returning a dimension error outside the stored payload. -/
def readChecked (a : FlatArray) (i : Nat) : Except DimError ℝ :=
  if h : i < a.length then .ok (a.data ⟨i, h⟩) else .error .mismatch

@[simp] theorem readChecked_of_lt (a : FlatArray) (i : Nat) (h : i < a.length) :
    a.readChecked i = .ok (a.data ⟨i, h⟩) := by
  simp [readChecked, h]

@[simp] theorem readChecked_of_ge (a : FlatArray) (i : Nat) (h : a.length ≤ i) :
    a.readChecked i = .error .mismatch := by
  simp [readChecked, Nat.not_lt.mpr h]

theorem readChecked_eq_get_of_lt (a : FlatArray) (i : Nat) (h : i < a.length) :
    a.readChecked i = .ok (a.get i) := by
  simp [readChecked, get, h]

theorem readChecked_error_iff (a : FlatArray) (i : Nat) :
    a.readChecked i = .error .mismatch ↔ a.length ≤ i := by
  by_cases h : i < a.length
  · simp [readChecked, h, Nat.not_le.mpr h]
  · simp [readChecked, h, Nat.le_of_not_gt h]

/-- A checked successful read certifies both the bound and the precise stored value. -/
theorem readChecked_ok_iff (a : FlatArray) (i : Nat) (r : ℝ) :
    a.readChecked i = .ok r ↔ ∃ h : i < a.length, a.data ⟨i, h⟩ = r := by
  by_cases h : i < a.length <;> simp [readChecked, h]

end FlatArray

namespace StrictValueAccess

/-- Checked stack lookup; the element type need not have a default inhabitant. -/
def lookup {α : Type u} (xs : List α) (i : Nat) : Except DimError α :=
  match xs[i]? with
  | some x => .ok x
  | none => .error .mismatch

@[simp] theorem lookup_of_lt {α : Type u} (xs : List α) (i : Nat) (h : i < xs.length) :
    lookup xs i = .ok xs[i] := by
  simp [lookup, h]

@[simp] theorem lookup_of_ge {α : Type u} (xs : List α) (i : Nat) (h : xs.length ≤ i) :
    lookup xs i = .error .mismatch := by
  simp [lookup, Nat.not_lt.mpr h]

/-- Valid stack accesses preserve the earlier default-based lookup result. -/
theorem lookup_eq_getD_of_lt {α : Type u} (xs : List α) (i : Nat) (fallback : α)
    (h : i < xs.length) : lookup xs i = .ok (xs.getD i fallback) := by
  simp [lookup, List.getD, h]

end StrictValueAccess
end GLang
