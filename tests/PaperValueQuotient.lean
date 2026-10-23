import GLang.Proofs.Value.Presentation.PaperValueQuotient
import Lean

open GLang GLang.PaperValueDomains GLang.PaperValueDomains.ExtensionalQuotient

-- Representative-independent application works at higher order as well.
example (P Q R : PER FlatArray) (f : ((P.arrow Q).arrow R).Support)
    (a : (P.arrow Q).Support) :
    (P.arrow Q).apply R (Quotient.mk _ f) (Quotient.mk _ a) =
      Quotient.mk _ ⟨f.val a.val, f.property a.val a.val a.property⟩ := rfl

-- Quotienting never identifies a failed computation with a successful one.
example (P : PER FlatArray) (a : P.Support) (e : DimError) :
    (Quotient.mk _ ⟨Except.error e, rfl⟩ : P.result.Domain) ≠
      Quotient.mk _ ⟨Except.ok a.val, a.property⟩ := P.result_error_ne_ok e a

open Lean Elab Command
elab "check_value_quotient_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``PER.supportSetoid, ``PER.result, ``PER.arrow, ``PER.apply,
      ``PER.result_error_eq_iff, ``PER.result_error_ne_ok,
      ``firstOrder_quotient_eq_iff, ``real_functional_related_iff,
      ``fibreShapeOfLeaves, ``arrayFibre_at_rep] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected quotient assumption in {n}: {ax}"
  logInfo "Supported higher-order quotients and fibre shapes use foundations only."

check_value_quotient_axioms
