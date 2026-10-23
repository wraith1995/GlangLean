import GLang.Proofs.Value.Partial.PartialValueApplicationRuntime

/-! Dimension guards, array checks, and argument decoding for value evaluation. -/
namespace GLang
namespace PartialValueEval

/-- Numeric view used only after the enclosing dimension guard succeeds. -/
def numbers (q : PartialFFSOracle) : FFSOracle := fun p s e =>
  match q p s e with
  | .ok n => n
  | .error _ => 0

def dimensions (q : PartialFFSOracle) : List ValSpace → Except DimError Unit
  | [] => .ok ()
  | s :: ss => do
      let _ ← s.dofPartial q
      dimensions q ss

/-- Failed dimensions never enter the numeric formula. The fallback in
`numbers` is an internal view, not an interpretation of a failed query. -/
def withDimensions (q : PartialFFSOracle) (ss : List ValSpace)
    (f : FFSOracle → Except DimError ValValSem) : Except DimError ValValSem :=
  match dimensions q ss with
  | .error e => .error e
  | .ok () => f (numbers q)

theorem numbers_ok (q : PartialFFSOracle) (p : ValFFSProp) (s : ValSpace)
    (e : ValExpr) (n : Nat) (h : q p s e = .ok n) : numbers q p s e = n := by
  simp [numbers, h]

theorem dof_numbers (q : PartialFFSOracle) (s : ValSpace) (n : Nat)
    (h : s.dofPartial q = .ok n) : s.dof (numbers q) = n :=
  ValSpace.dofPartial_success q (numbers q) (numbers_ok q) s n h

/-- A successful guard supplies a successful partial dimension for every
listed space; numeric projection cannot turn one of these failures into zero. -/
theorem dimensions_ok_iff (q : PartialFFSOracle) (ss : List ValSpace) :
    dimensions q ss = .ok () ↔ ∀ s ∈ ss, ∃ n, s.dofPartial q = .ok n := by
  induction ss with
  | nil => simp [dimensions]
  | cons s ss ih =>
      cases hs : s.dofPartial q <;>
        simp [dimensions, hs, bind, Except.bind, ih]

/-- One failed dimension blocks the entire numerical primitive. -/
theorem withDimensions_error (q : PartialFFSOracle) (ss : List ValSpace)
    (f : FFSOracle → Except DimError ValValSem) {s : ValSpace}
    (hs : s ∈ ss) (he : s.dofPartial q = .error .mismatch) :
    withDimensions q ss f = .error .mismatch := by
  cases h : dimensions q ss with
  | error e => cases e; simp [withDimensions, h]
  | ok u =>
      cases u
      obtain ⟨n, hn⟩ := (dimensions_ok_iff q ss).mp h s hs
      rw [he] at hn
      contradiction

/-- Validate an immediate application domain, preserving higher-order callback
identity. Returned function fibers are checked by the result-checking layer. -/
noncomputable def decodeDomain (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (d : ValTy) (v : ValValSem) :
    Except DimError d.carrierEl :=
  match denotValTyPartial orc ρ Γ Δ d with
  | .error e => .error e
  | .ok T =>
      match d, T, d.carrierFromVal v with
      | .space _, n, .ok a => if a.length = n then .ok a else .error .mismatch
      | .piTy _ _, _, r => r
      | .space _, _, .error e => .error e

end PartialValueEval

end GLang
