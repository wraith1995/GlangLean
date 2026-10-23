import GLang.Proofs.Preservation.OperationalApplicationKindAudit
import Lean.Util.CollectAxioms

namespace GLang.RuntimeValue.OperationalApplicationKindAuditTest
noncomputable section

private def emptyValid : ValCtxValid (∅ : ValCtx) := by
  intro x t h
  simp at h

-- The two argument representations differ structurally. Their kinds, rather
-- than their type syntax, are what the proof-only compiler helper requires.
private def functionValid :
    ValTValid ∅ (.piTy (.space .real) (.space .real)) (.arrow .base .base) :=
  .piTy ∅ (.space .real) (fun _ _ => .space .real)

private def functionTyped :
    ValHasType ∅ (.vlam (.space .real) (.space .real) (.bvar 0))
      (.piTy (.space .real) (.space .real)) :=
  .vlam ∅ functionValid (fun _ _ => .var (by simp))

example : ValHasType ∅
    (.applyAt (.vlam (.space .real) (.space .real) (.bvar 0))
      (.zero (.tprod .real .real)) (.space (.dsum .empty .real)))
    (.space (.dsum .empty .real)) :=
  applyAt_function_sameKind emptyValid functionTyped
    (.of_type (.zero (.tprod .real .real))) functionValid rfl
    (.space (.dsum .empty .real))

example : Basis.tof (.frame .one .one) ≠
    .space (Basis.sof (.frame .one .one)) := by simp [Basis.tof]

#print axioms GLang.RuntimeValue.applyAt_function_sameKind
#print axioms GLang.RuntimeValue.operational_kind_or_linearResultSpine
end
end GLang.RuntimeValue.OperationalApplicationKindAuditTest

open Lean Elab Command in
elab "check_application_kind_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``GLang.RuntimeValue.operational_kind_of_context,
      ``GLang.RuntimeValue.applyAt_function_sameKind,
      ``GLang.RuntimeValue.ExprTyped.applyValue,
      ``GLang.RuntimeValue.ExprTyped.applyAt] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "Unexpected application-kind axiom in {name}: {ax}"
  logInfo "Requested-basis kinds and ordinary application typing use foundations only."
check_application_kind_axioms
