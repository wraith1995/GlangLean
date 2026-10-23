import GLang.Proofs.Value.Queries.ValueQueryDependencies
/- Semantic finite arrays, dependent functions, environments, and conversions
between bundled and structural values. Type interpretation and expression
denotation are in `Value/TypeInterpretation.lean` and
`Value/ExpressionDenotation.lean`. -/

import GLang.Value.Binding
import GLang.Value.Supporting.StrictTyping
import GLang.Numerics.SVD.ValueSVD
import GLang.Numerics.RREF.ValueRREF
import GLang.Value.Inference
import GLang.Value.Arrays
import GLang.Numerics.SVD.ValueNumericalInputs
import GLang.Proofs.Value.Typing.StrictValueAccess
import GLang.Value.ShapeConditions
import GLang.Numerics.SVD.ValueCanonicalFSV
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Eqns

namespace GLang

/-! ## Partial denotation result. -/

/-! ## `ValTypeSem` — type denotation universe. -/

/-- Type-indexed value-language type denotations. -/
inductive ValTypeSem : Type 1
  | space : ValSpace → Nat → ValTypeSem
  | piTy  : (T : Type) → (T → ValTypeSem) → ValTypeSem

/-- Underlying Lean type of a `ValTypeSem`. A base-space carrier is a finite
    `FlatArray`; its zero-extended coordinate view is `FlatArray.get`.
    Function carriers remain partial dependent Lean functions. -/
def ValTypeSem.El : ValTypeSem → Type
  | .space _ _  => FlatArray
  | .piTy T fam => (y : T) → Except DimError (fam y).El

/-- Default `ValTypeSem` — the empty-space base (in-bounds = never). -/
noncomputable def ValTypeSem.default : ValTypeSem :=
  .space .empty 0

/-- Source space of a `.space`-shaped `ValTypeSem`; `.empty` fallback for
    `.piTy`. Mirrors `HSpace.empty`-style defaults. -/
def ValTypeSem.spaceOf : ValTypeSem → ValSpace
  | .space s _ => s
  | .piTy _ _ => .empty

/-! ## `ValValSem` — value denotation universe. -/

inductive ValValSem : Type 1
  | array : FlatArray → ValValSem
  | fn    : (T : Type) → (T → Except DimError ValValSem) → ValValSem

def ValValSem.arrayOf (n : Nat) (f : Nat → ℝ) : ValValSem :=
  .array (FlatArray.ofFn n f)

theorem ValValSem.arrayOf_congr {n m : Nat} {f g : Nat → ℝ}
    (hlen : n = m) (hfg : ∀ i, f i = g i) :
    ValValSem.arrayOf n f = ValValSem.arrayOf m g := by
  exact congrArg ValValSem.array (FlatArray.ofFn_congr hlen hfg)

/-- Default `ValValSem` — identically-zero flat array. -/
noncomputable def ValValSem.default : ValValSem := .array FlatArray.empty

noncomputable instance : Inhabited ValValSem := ⟨ValValSem.default⟩

def ValValSem.asArray : ValValSem → ValIdx → ℝ
  | .array a => a.get
  | .fn _ _  => fun _ => 0

/-- Extract the partial function view of a `ValValSem`. An array in function
position is a runtime mismatch. -/
noncomputable def ValValSem.asFn :
    ValValSem → (T : Type) ×' (T → Except DimError ValValSem)
  | .fn T f => ⟨T, f⟩
  | .array _ => ⟨PUnit, fun _ => .error .mismatch⟩

@[simp] theorem ValValSem.asArray_array (a : FlatArray) :
    (ValValSem.array a).asArray = a.get := rfl

@[simp] theorem ValValSem.asArray_array_apply (a : FlatArray) (i : ValIdx) :
    (ValValSem.array a).asArray i = a.get i := rfl

@[simp] theorem ValValSem.asArray_fn (T : Type) (f : T → Except DimError ValValSem)
    (i : ValIdx) :
    (ValValSem.fn T f).asArray i = 0 := rfl

@[simp] theorem ValValSem.asArray_arrayOf (n : Nat) (f : Nat → ℝ) (i : Nat) :
    (ValValSem.arrayOf n f).asArray i = if i < n then f i else 0 := by
  simp [ValValSem.arrayOf, ValValSem.asArray]

theorem ValValSem.asArray_arrayOf_lt (n : Nat) (f : Nat → ℝ) (i : Nat)
    (hi : i < n) : (ValValSem.arrayOf n f).asArray i = f i := by
  simp [ValValSem.asArray_arrayOf, hi]

/-- Require a successful denotation to have flat-array shape. -/
def ValValSem.expectArray :
    Except DimError ValValSem → Except DimError FlatArray
  | .error e => .error e
  | .ok (.array a) => .ok a
  | .ok (.fn _ _) => .error .mismatch

/-- Eliminate one successful array operand while preserving any prior error. -/
def ValValSem.bindArray (r : Except DimError ValValSem)
    (k : FlatArray → Except DimError ValValSem) : Except DimError ValValSem :=
  match r with
  | .error e => .error e
  | .ok (.array a) => k a
  | .ok (.fn _ _) => .error .mismatch

/-- Eliminate two successful array operands, left to right. -/
def ValValSem.bindArrays (r₀ r₁ : Except DimError ValValSem)
    (k : FlatArray → FlatArray → Except DimError ValValSem) :
    Except DimError ValValSem :=
  ValValSem.bindArray r₀ fun a₀ =>
    ValValSem.bindArray r₁ fun a₁ => k a₀ a₁

/-- Eliminate three successful array operands, left to right. -/
def ValValSem.bindArrays3 (r₀ r₁ r₂ : Except DimError ValValSem)
    (k : FlatArray → FlatArray → FlatArray → Except DimError ValValSem) :
    Except DimError ValValSem :=
  ValValSem.bindArray r₀ fun a₀ =>
    ValValSem.bindArray r₁ fun a₁ =>
    ValValSem.bindArray r₂ fun a₂ => k a₀ a₁ a₂

/-- Sequence a syntactic family of value denotations, requiring every member
to be an array. This is used by `vsum`; on well-typed families its output has
the same length and order as the input list. -/
def ValValSem.sequenceArrays :
    List (Except DimError ValValSem) → Except DimError (List FlatArray)
  | [] => .ok []
  | r :: rs =>
      match r with
      | .error e => .error e
      | .ok (.fn _ _) => .error .mismatch
      | .ok (.array a) =>
          match ValValSem.sequenceArrays rs with
          | .error e => .error e
          | .ok as => .ok (a :: as)

/-! ## Bridge helpers: `fromEl` / `toEl`.

These move between `T.El`-typed Lean values and the untyped `ValValSem`
universe, parallel to `HType.embed` / `HType.extract`
(`GLang/Denot.lean:516-543`). -/

noncomputable def ValIdx.truncate (P : ValIdx → Prop) (f : ValIdx → ℝ) :
    ValIdx → ℝ :=
  fun i => haveI := Classical.dec (P i); if P i then f i else 0

@[simp] theorem ValIdx.truncate_OOB (P : ValIdx → Prop) (f : ValIdx → ℝ)
    (i : ValIdx) (hi : ¬ P i) : ValIdx.truncate P f i = 0 := by
  simp only [ValIdx.truncate]; rw [if_neg hi]

theorem ValIdx.truncate_inBounds (P : ValIdx → Prop) (f : ValIdx → ℝ)
    (i : ValIdx) (hi : P i) : ValIdx.truncate P f i = f i := by
  simp only [ValIdx.truncate]; rw [if_pos hi]

/-- Lift an element of `T.El` into the untyped `ValValSem` world. At a
    `.space` leaf the carrier is a finite `FlatArray`, which is resized to the
    semantic dimension `n`: excess entries are discarded and missing entries
    are supplied as zero. Thus the embedded array has exactly the requested
    finite length. Recursion is on `T : ValTypeSem`. -/
noncomputable def ValValSem.fromEl : (T : ValTypeSem) → T.El → ValValSem
  | .space _ n, a => .array (a.resize n)
  | .piTy T fam, g =>
      .fn T (fun y => (g y).map (ValValSem.fromEl (fam y)))

/-- Reify a typed semantic value without ever resizing a flat array.

At a base space the stored length must already be the semantic dimension; a
mismatch remains an observable `DimError`.  At a Π the check is delayed to
each successful callback result, since a function cannot be inspected
eagerly.  In particular, this is the conversion used by higher-order reshape:
it may reject a malformed carrier value, but it never pads or truncates one. -/
noncomputable def ValValSem.fromElChecked : (T : ValTypeSem) →
    T.El → Except DimError ValValSem
  | .space _ n, a =>
      if a.length = n then .ok (.array a) else .error .mismatch
  | .piTy T fam, g =>
      .ok (.fn T (fun y => (g y).bind (ValValSem.fromElChecked (fam y))))

@[simp] theorem ValValSem.fromElChecked_space_of_length
    (s : ValSpace) (n : Nat) (a : FlatArray) (h : a.length = n) :
    ValValSem.fromElChecked (.space s n) a = .ok (.array a) := by
  simp [ValValSem.fromElChecked, h]

@[simp] theorem ValValSem.fromElChecked_space_of_length_ne
    (s : ValSpace) (n : Nat) (a : FlatArray) (h : a.length ≠ n) :
    ValValSem.fromElChecked (.space s n) a = .error .mismatch := by
  simp [ValValSem.fromElChecked, h]

/-- Extract a `T.El`-typed Lean value from a `ValValSem`. On `.space` the
    finite array is returned directly; callers that need exact semantic length
    use `fromElChecked`, while `fromEl` performs resizing. The `.piTy / .fn`
    cross-case uses `Classical.dec` on type equality (parallel to
    `HType.extract`'s `.sec / .pi` cross-case). -/
noncomputable def ValValSem.toEl :
    (T : ValTypeSem) → ValValSem → Except DimError T.El
  | .space _ _,  .array a  => .ok a
  | .space _ _,  .fn _ _   => .error .mismatch
  | .piTy _T _fam, .array _  => .error .mismatch
  | .piTy T fam, .fn T' f  =>
      haveI := Classical.dec (T = T')
      if h : T = T' then
        .ok (fun y : T =>
          match f (h ▸ y) with
          | .error e => .error e
          | .ok v => ValValSem.toEl (fam y) v)
      else
        .error .mismatch

/-- On a `.space` carrier, `toEl` returns the stored finite array without
    resizing it. A function-shaped value is a mismatch. -/
@[simp] theorem ValValSem.toEl_space_array (s : ValSpace) (n : Nat)
    (a : FlatArray) : ValValSem.toEl (.space s n) (.array a) = .ok a := rfl

@[simp] theorem ValValSem.toEl_space_fn (s : ValSpace) (n : Nat)
    (T : Type) (f : T → Except DimError ValValSem) :
    ValValSem.toEl (.space s n) (.fn T f) = .error .mismatch := rfl

/-- Case-split simplifier for extraction from a base semantic space. -/
@[simp] theorem ValValSem.toEl_space (s : ValSpace) (n : Nat) (v : ValValSem) :
    ValValSem.toEl (.space s n) v =
      match v with
      | .array a => .ok a
      | .fn _ _ => .error .mismatch := by
  cases v <;> rfl

/-- Exact-length semantic decoding. -/
noncomputable def ValValSem.toElChecked :
    (T : ValTypeSem) → ValValSem → Except DimError T.El
  | .space _ n, .array a =>
      if a.length = n then .ok a else .error .mismatch
  | .space _ _, .fn _ _ => .error .mismatch
  | .piTy _ _, .array _ => .error .mismatch
  | .piTy T fam, .fn T' f =>
      haveI := Classical.dec (T = T')
      if h : T = T' then
        .ok (fun y : T => (f (h ▸ y)).bind (ValValSem.toElChecked (fam y)))
      else .error .mismatch

@[simp] theorem ValValSem.toElChecked_space_of_length
    (s : ValSpace) (n : Nat) (a : FlatArray) (h : a.length = n) :
    toElChecked (.space s n) (.array a) = .ok a := by
  simp [toElChecked, h]

@[simp] theorem ValValSem.toElChecked_space_of_length_ne
    (s : ValSpace) (n : Nat) (a : FlatArray) (h : a.length ≠ n) :
    toElChecked (.space s n) (.array a) = .error .mismatch := by
  simp [toElChecked, h]

/-- Successful base decoding guarantees the exact semantic dimension. -/
theorem ValValSem.toElChecked_space_success
    (s : ValSpace) (n : Nat) (v : ValValSem) (a : FlatArray)
    (h : toElChecked (.space s n) v = .ok a) :
    v = .array a ∧ a.length = n := by
  cases v with
  | array b =>
      simp only [toElChecked] at h
      split at h
      · cases h
        exact ⟨rfl, by assumption⟩
      · contradiction
  | fn T f => contradiction

theorem ValValSem.toElChecked_eq_toEl_space
    (s : ValSpace) (n : Nat) (a : FlatArray) (h : a.length = n) :
    toElChecked (.space s n) (.array a) = toEl (.space s n) (.array a) := by
  simp [h]

/-- Higher-order results remain suspended, with exact decoding at every returned fiber. -/
@[simp] theorem ValValSem.toElChecked_pi_fn (T : Type) (fam : T → ValTypeSem)
    (f : T → Except DimError ValValSem) :
    toElChecked (.piTy T fam) (.fn T f) =
      .ok (fun y => (f y).bind (toElChecked (fam y))) := by
  simp [toElChecked]

/-- Validate the immediate application domain without changing higher-order
callback identity. Base arrays must have exactly the declared dimension;
function arguments retain the existing semantic carrier decoder. -/
noncomputable def ValValSem.toElDomainChecked (T : ValTypeSem) (v : ValValSem) :
    Except DimError T.El :=
  match T with
  | .space s n => toElChecked (.space s n) v
  | .piTy A fam => toEl (.piTy A fam) v

@[simp] theorem ValValSem.toElDomainChecked_space (s : ValSpace) (n : Nat)
    (v : ValValSem) :
    toElDomainChecked (.space s n) v = toElChecked (.space s n) v := rfl

@[simp] theorem ValValSem.toElDomainChecked_pi (A : Type) (fam : A → ValTypeSem)
    (v : ValValSem) :
    toElDomainChecked (.piTy A fam) v = toEl (.piTy A fam) v := rfl

/-- Exact base-domain decoding preserves valid arguments without resizing. -/
theorem ValValSem.toElDomainChecked_eq_toEl_space
    (s : ValSpace) (n : Nat) (a : FlatArray) (h : a.length = n) :
    toElDomainChecked (.space s n) (.array a) = toEl (.space s n) (.array a) :=
  toElChecked_eq_toEl_space s n a h

theorem ValValSem.toElDomainChecked_success_toEl (T : ValTypeSem) (v : ValValSem)
    (a : T.El) (h : toElDomainChecked T v = .ok a) : toEl T v = .ok a := by
  cases T with
  | space s n =>
      obtain ⟨rfl, _⟩ := toElChecked_space_success s n v a h
      rfl
  | piTy A fam => exact h

/-- Runtime scalar observation rejects function values and out-of-bounds indices. -/
def ValValSem.readChecked (v : ValValSem) (i : Nat) : Except DimError ℝ :=
  match v with
  | .array a => a.readChecked i
  | .fn _ _ => .error .mismatch

/-- Scalar observation preserves an existing evaluation failure. -/
def ValValSem.readResultChecked (r : Except DimError ValValSem) (i : Nat) :
    Except DimError ℝ := r.bind (fun v => v.readChecked i)

@[simp] theorem ValValSem.readChecked_array (a : FlatArray) (i : Nat) :
    readChecked (.array a) i = a.readChecked i := rfl

@[simp] theorem ValValSem.readChecked_fn (A : Type)
    (f : A → Except DimError ValValSem) (i : Nat) :
    readChecked (.fn A f) i = .error .mismatch := rfl

@[simp] theorem ValValSem.readResultChecked_error (e : DimError) (i : Nat) :
    readResultChecked (.error e) i = .error e := rfl

/-! ## `ValEnvSem` — function-typed environment (choice §6.B). -/

/-- Value-language semantic environment: a function from names to
    `ValValSem`. Parallel to `ValEnv := VName → ValBinding` in
    `ValueDenot.lean`. -/
abbrev ValEnvSem := VName → ValValSem

namespace ValEnvSem

/-- Empty environment: every name maps to the zero array. -/
def empty : ValEnvSem := fun _ => .array FlatArray.empty

/-- Update an environment at a name with a `ValValSem`. -/
def update (ρ : ValEnvSem) (x : VName) (v : ValValSem) : ValEnvSem :=
  fun y => if y = x then v else ρ y

@[simp] theorem update_same (ρ : ValEnvSem) (x : VName) (v : ValValSem) :
    ρ.update x v x = v := by simp [update]

@[simp] theorem update_other (ρ : ValEnvSem) (x y : VName) (v : ValValSem)
    (h : y ≠ x) : ρ.update x v y = ρ y := by simp [update, h]

/-- Extract the array view of a binding by name. Mirrors
    `ValEnv.lookupArr`. -/
def lookupArr (ρ : ValEnvSem) (x : VName) (i : ValIdx) : ℝ :=
  (ρ x).asArray i

/-- Bind a name to an array-shaped value. -/
def updateArr (ρ : ValEnvSem) (x : VName) (a : FlatArray) : ValEnvSem :=
  ρ.update x (.array a)

@[simp] theorem updateArr_same (ρ : ValEnvSem) (x : VName) (a : FlatArray) :
    ρ.updateArr x a x = .array a := by simp [updateArr, update]

@[simp] theorem updateArr_other (ρ : ValEnvSem) (x y : VName) (a : FlatArray)
    (h : y ≠ x) : ρ.updateArr x a y = ρ y := by simp [updateArr, update, h]

end ValEnvSem

abbrev FFSOracleSem := ValEnvSem → List ValTy → List ValValSem → FFSOracle

/-- The environment-INDEPENDENT embedding of a syntactic oracle. -/
@[reducible] def FFSOracleSem.const (orc : FFSOracle) : FFSOracleSem := fun _ _ _ => orc

theorem FFSOracleSem.const_apply (orc : FFSOracle) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) : FFSOracleSem.const orc ρ Γ Δ = orc := rfl

/-! ## Fresh names and structural carriers -/

/-- A deterministic fresh name for a finite set (D2 for the denotation FUNCTION:
    the binder body, locally-nameless, is opened at this name). `noncomputable`
    via `Classical.choose`; soundness only needs that the choice is fresh, and the
    result is independent of which fresh name via `env`-irrelevance. -/
noncomputable def freshFor (s : Finset VName) : VName :=
  (Infinite.exists_notMem_finset s).choose

theorem freshFor_notMem (s : Finset VName) : freshFor s ∉ s :=
  (Infinite.exists_notMem_finset s).choose_spec

/-- The structural Lean carrier of a `ValTy`: every `.space` leaf is a finite
    `FlatArray`, and `.piTy` is the non-dependent partial arrow.
    Env-independent: `(denotValTy orc ρ τ).El = τ.carrierEl`
    (`denotValTy_El_eq_carrierEl`, proved in `ValueSoundnessSem.lean`). -/
def ValTy.carrierEl : ValTy → Type
  | .space _    => FlatArray
  | .piTy τ₀ τ₁ => τ₀.carrierEl → Except DimError τ₁.carrierEl

/-- Decode an untyped semantic value at the structural carrier of a `ValTy`. -/
noncomputable def ValTy.carrierFromVal :
    (τ : ValTy) → ValValSem → Except DimError τ.carrierEl
  | .space _, .array a => .ok a
  | .space _, .fn _ _ => .error .mismatch
  | .piTy _ _, .array _ => .error .mismatch
  | .piTy τ₀ τ₁, .fn T f =>
      haveI := Classical.dec (T = τ₀.carrierEl)
      if h : T = τ₀.carrierEl then
        .ok (fun a =>
          match f (h ▸ a) with
          | .error e => .error e
          | .ok v => ValTy.carrierFromVal τ₁ v)
      else .error .mismatch

/-- Domain-aware application at a structural `ValTy` carrier. -/
noncomputable def ValValSem.applyCarrier (dom : ValTy) (funVal argVal : ValValSem) :
    Except DimError ValValSem :=
  match funVal with
  | .array _ => .error .mismatch
  | .fn T f =>
      haveI := Classical.dec (T = dom.carrierEl)
      if h : T = dom.carrierEl then
        match ValTy.carrierFromVal dom argVal with
        | .error e => .error e
        | .ok arg => f (h ▸ arg)
      else .error .mismatch

noncomputable def ValValSem.applyVal :
    ValValSem → ValValSem → Except DimError ValValSem
  | .fn T f, arg =>
      haveI := Classical.dec (T = FlatArray)
      if h : T = FlatArray then
        match arg with
        | .array a => f (h ▸ a)
        | .fn _ _ => .error .mismatch
      else .error .mismatch
  | .array _, _ => .error .mismatch

/-- Embed a structural-carrier value `τ.carrierEl` into the untyped
    `ValValSem` world (env-independent). `.space` leaves are raw arrays;
    `.piTy` is a genuine Lean function over the sub-carriers. Parallels
    `ValValSem.fromEl` but keyed on the env-independent `ValTy.carrierEl`
    (so no `ρ`/`ValTypeSem` is needed inside the kindSize recursor). -/
noncomputable def ValTy.carrierToVal : (τ : ValTy) → τ.carrierEl → ValValSem
  | .space _,    a => .array a
  | .piTy τ₀ τ₁, g =>
      .fn τ₀.carrierEl (fun a => (g a).map (ValTy.carrierToVal τ₁))

/-- Apply an untyped function value to an argument already decoded at a
specific semantic carrier.  This is the low-level, exception-preserving
counterpart of `ValValSem.toEl`; it is kept here so higher-order reshape can
apply its source function without discarding the raw source argument used to
index a dependent codomain. -/
noncomputable def ValValSem.applyTyped {T : Type} (funVal : ValValSem) (arg : T) :
    Except DimError ValValSem :=
  match funVal with
  | .array _ => .error .mismatch
  | .fn T' f =>
      haveI := Classical.dec (T = T')
      if h : T = T' then f (h ▸ arg) else .error .mismatch

@[simp] theorem ValValSem.applyTyped_fn {T : Type}
    (f : T → Except DimError ValValSem) (arg : T) :
    (ValValSem.fn T f).applyTyped arg = f arg := dif_pos rfl

end GLang
