
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

namespace GLang

/-- A genuinely finite, one-dimensional C-order array. -/
structure FlatArray where
  length : Nat
  data : Fin length → ℝ

namespace FlatArray

/-- Construct a finite array of a prescribed length from a zero-extended
coordinate formula. Only the first `n` coordinates are stored. -/
def ofFn (n : Nat) (f : Nat → ℝ) : FlatArray :=
  ⟨n, fun i => f i.val⟩

/-- The empty array. -/
def empty : FlatArray := ofFn 0 (fun _ => 0)

/-- A zero-filled array of length `n`. -/
def zeros (n : Nat) : FlatArray := ofFn n (fun _ => 0)

/-- Zero-extended observation of a finite array. -/
def get (a : FlatArray) (i : Nat) : ℝ :=
  if h : i < a.length then a.data ⟨i, h⟩ else 0

instance : CoeFun FlatArray (fun _ => Nat → ℝ) := ⟨get⟩

/-- Resize by zero-extended lookup. The result stores exactly `n` entries. -/
def resize (n : Nat) (a : FlatArray) : FlatArray := ofFn n a.get

@[simp] theorem length_resize (n : Nat) (a : FlatArray) :
    (resize n a).length = n := rfl

@[simp] theorem length_ofFn (n : Nat) (f : Nat → ℝ) :
    (ofFn n f).length = n := rfl

@[simp] theorem get_ofFn_lt (n : Nat) (f : Nat → ℝ) (i : Nat)
    (h : i < n) : (ofFn n f).get i = f i := by
  simp [get, ofFn, h]

@[simp] theorem get_ofFn_ge (n : Nat) (f : Nat → ℝ) (i : Nat)
    (h : n ≤ i) : (ofFn n f).get i = 0 := by
  simp [get, ofFn, Nat.not_lt.mpr h]

@[simp] theorem get_ofFn (n : Nat) (f : Nat → ℝ) (i : Nat) :
    (ofFn n f).get i = if i < n then f i else 0 := by
  split <;> simp_all [get, ofFn]

@[simp] theorem get_empty (i : Nat) : empty.get i = 0 := by
  simp [empty]

@[simp] theorem get_zeros (n i : Nat) : (zeros n).get i = 0 := by
  simp [zeros]

/-- Extensionality on the stored finite coordinates. -/
@[ext (iff := false)] theorem ext {a b : FlatArray}
    (hlen : a.length = b.length)
    (hdata : ∀ i : Fin a.length,
      a.data i = b.data ⟨i.val, hlen ▸ i.isLt⟩) : a = b := by
  cases a with
  | mk an adata =>
      cases b with
      | mk bn bdata =>
          dsimp at hlen hdata
          subst bn
          have hfun : adata = bdata := by
            funext i
            simpa using hdata i
          cases hfun
          rfl

/-- Two finite arrays of the same length are equal when their zero extensions
agree everywhere. -/
theorem ext_get {a b : FlatArray} (hlen : a.length = b.length)
    (hget : ∀ i, a.get i = b.get i) : a = b := by
  apply ext hlen
  intro i
  have ha : i.val < a.length := i.isLt
  have hb : i.val < b.length := by simpa [← hlen] using ha
  simpa [get, ha, hb] using hget i.val

/-- Congruence for finite arrays presented by a length and coordinate formula. -/
theorem ofFn_congr {n m : Nat} {f g : Nat → ℝ} (hlen : n = m)
    (hfg : ∀ i, f i = g i) : ofFn n f = ofFn m g := by
  subst m
  apply ext_get (a := ofFn n f) (b := ofFn n g) rfl
  intro i
  simp [hfg]

/-- Pointwise map, preserving length. -/
def map (f : ℝ → ℝ) (a : FlatArray) : FlatArray :=
  ⟨a.length, fun i => f (a.data i)⟩

/-- Pointwise binary operation. The explicit common length prevents accidental
zip-truncation from becoming part of the semantics. -/
def zipWith (n : Nat) (f : ℝ → ℝ → ℝ)
    (a b : FlatArray) (ha : a.length = n) (hb : b.length = n) : FlatArray :=
  ofFn n (fun i => f (a.get i) (b.get i))

/-- Concatenation, used for direct sums. -/
def append (a b : FlatArray) : FlatArray :=
  ofFn (a.length + b.length) (fun i =>
    if i < a.length then a.get i else b.get (i - a.length))

@[simp] theorem length_append (a b : FlatArray) :
    (append a b).length = a.length + b.length := rfl

/-- Sum all stored coordinates. -/
def sum (a : FlatArray) : ℝ := ∑ i : Fin a.length, a.data i

end FlatArray

/-- A finite flat array whose length is fixed by its semantic value space. -/
abbrev SizedFlatArray (n : Nat) := {a : FlatArray // a.length = n}

namespace SizedFlatArray

/-- Resize an existential flat array into an exactly-sized carrier element. -/
def ofFlat (n : Nat) (a : FlatArray) : SizedFlatArray n :=
  ⟨a.resize n, rfl⟩

/-- The exactly-sized zero array. -/
def zeros (n : Nat) : SizedFlatArray n := ⟨FlatArray.zeros n, rfl⟩

end SizedFlatArray

end GLang
