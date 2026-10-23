import GLang.Value.TypeInterpretation
import GLang.Proofs.Adequacy.Total.DirectOracle
import Lean

open GLang
noncomputable section

private def failing : PartialFFSOracleSem := fun _ _ _ _ _ _ => .error .mismatch
private def subspace : ValSpace := .ffs .kernel (.tprod .real .real) (.rlit 0)

-- Errors survive a nested sum/product, and then the enclosing value type.
example (ρ : ValEnvSem) :
    denotValTyPartial failing ρ [] [] (.space (.tprod .real (.dsum .empty subspace))) =
      .error .mismatch := by
  simp [denotValTyPartial, failing, subspace, ValSpace.dofPartial,
    ValSpace.shpOfPartial, bind, pure, Except.bind, Except.pure]

-- A failed domain propagates before any function value is admitted.
example (ρ : ValEnvSem) :
    denotValTyPartial failing ρ [] [] (.piTy (.space subspace) (.space .real)) =
      .error .mismatch := by
  simp [denotValTyPartial, failing, subspace, ValSpace.dofPartial,
    ValSpace.shpOfPartial, bind, Except.bind]

-- A failed codomain is suspended: constructing a function is successful, but
-- every actual application returns error. No rank-zero space is manufactured.
example (ρ : ValEnvSem) (f : FlatArray → Except DimError FlatArray) :
    checkValTyPartial failing ρ [] [] (.piTy (.space .real) (.space subspace)) f =
      .ok (fun _ => .error .mismatch) := by
  simp [checkValTyPartial, denotValTyPartial, failing, subspace, ValSpace.dofPartial,
    ValSpace.shpOfPartial, PartialValType.check, PartialValType.piTy,
    bind, pure, Except.bind, Except.pure]

-- The exact original argument, including its coordinates, selects the fiber.
private def byArgument : PartialFFSOracleSem := fun _ _ Δ _ _ _ =>
  match Δ with
  | .array a :: _ => if a.get 0 = 0 then .error .mismatch else .ok 2
  | _ => .error .mismatch

example (ρ : ValEnvSem) :
    denotValTyPartial byArgument ρ [] [] (.piTy (.space .real) (.space subspace)) =
      .ok (PartialValType.piTy (PartialValType.space .real 1) (fun a : FlatArray =>
        if a.get 0 = 0 then .error .mismatch else .ok (PartialValType.space subspace 2))) := by
  simp only [denotValTyPartial, ValSpace.dofPartial, ValSpace.shpOfPartial, subspace,
    byArgument, ValTy.carrierToVal, bind, pure, Except.bind, Except.pure]
  apply congrArg Except.ok
  apply congrArg (PartialValType.piTy (PartialValType.space .real 1))
  funext a
  by_cases h : a.get 0 = 0 <;> simp [h]

-- Failed fibers reject even a callback whose returned array would otherwise
-- have a plausible size. Successful fibers retain exact-length validation.
example (f : FlatArray → Except DimError FlatArray) :
    PartialValType.check
      (PartialValType.piTy (PartialValType.space .real 1)
        (c := .space .real)
        (fun a => if a.get 0 = 0 then .error .mismatch else .ok (PartialValType.space .real 2))) f =
      .ok (fun a => if a.get 0 = 0 then .error .mismatch else
        match f a with
        | .error e => .error e
        | .ok b => if b.length = 2 then .ok b else .error .mismatch) := by
  apply congrArg Except.ok
  funext a
  by_cases h : a.get 0 = 0
  · simp [h]
  · simp only [PartialValType.check, if_neg h, PartialValType.space]
    cases f a <;> rfl

example (f : (FlatArray → Except DimError FlatArray) → Except DimError FlatArray) :
    PartialValType.check
      (PartialValType.piTy
        (PartialValType.piTy (PartialValType.space .real 1)
          (fun _ => .ok (PartialValType.space .real 1)))
        (fun _ => .ok (PartialValType.space .real 1))) f =
      .ok (fun g => match f g with
        | .error e => .error e
        | .ok b => if b.length = 1 then .ok b else .error .mismatch) := by
  simp only [PartialValType.space]
  apply congrArg Except.ok
  funext g
  cases f g <;> rfl

-- A zero-dimensional successful type still admits the genuine empty array.
example (ρ : ValEnvSem) :
    checkValTyPartial failing ρ [] [] (.space .empty) FlatArray.empty =
      .ok FlatArray.empty := by
  simp [checkValTyPartial, denotValTyPartial, ValSpace.dofPartial, ValSpace.shpOfPartial,
    PartialValType.check, PartialValType.space, FlatArray.empty]

-- Concrete failing audit witness; this deliberately tests just the strict
-- query boundary. It is not a replacement for the recursive direct oracle.
private def badMatrix : ValExpr := .mtm 1 1 .empty .real
  (.zero (.tprod .real .real)) (.zero (.tprod .real .real))

example (ρ : ValEnvSem) :
    checkValTyPartial
      (fun ρ Γ Δ p _ e => ffsDimensionPartial p (.ok [1, 1])
        (denotValB_semS directOracle ρ Γ Δ e))
      ρ [] [] (.space (.ffs .kernel (.tprod .real .real) badMatrix))
      (FlatArray.zeros 1) = .error .mismatch := by
  have hbad : denotValB_semS directOracle ρ [] [] badMatrix = .error .mismatch := by
    simp [badMatrix, denotValB_semS, ValValSem.bindArrays, ValValSem.bindArray,
      ValValSem.arrayOf, ValueShape.mtm, ValExpr.inferSpaceCtx]
  simp [checkValTyPartial, denotValTyPartial, ValSpace.dofPartial,
    ValSpace.shpOfPartial, hbad]

open Lean Elab Command
elab "check_partial_type_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``PartialValType.spaceDomainEquiv, ``PartialValType.apply_failed_fiber,
      ``PartialValType.check_sound, ``PartialValType.check_idempotent, ``checkValTyPartial_sound,
      ``denotValTyPartial_pi_ok, ``denotValTyPartial_pi_domain_error] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected partial type interpretation axiom {n}: {ax}"
  logInfo "Partial type interpretation and recursive result checking add no axioms."
check_partial_type_axioms
