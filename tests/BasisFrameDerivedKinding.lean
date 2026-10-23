import GLang.Proofs.Basis.Binding
import GLang.Surface.Judgments
import GLang.Elaboration.BasisErasure
import Lean

open GLang Lean Elab Command

-- Construct arbitrary frames from exactly the two recursive validity premises.
example {ε : NLCtx} {b₀ b₁ : Basis} (L : Finset GLang.Name)
    (h₀ : Basis.BasisValid ε b₀)
    (h₁ : ∀ y, y ∉ L →
      Basis.BasisValid (Finmap.insert y b₀.tof ε) (Basis.openVar y b₁)) :
    Basis.BasisValid ε (.frame b₀ b₁) := .frame L h₀ h₁

-- Their dependent-type validity is a conclusion, not an input.
example {ε : NLCtx} {b₀ b₁ : Basis} (L : Finset GLang.Name)
    (h₀ : Basis.BasisValid ε b₀)
    (h₁ : ∀ y, y ∉ L →
      Basis.BasisValid (Finmap.insert y b₀.tof ε) (Basis.openVar y b₁)) :
    Nonempty (TValid ε (.piTy b₀.tof b₁.tof)
      (.arrow b₀.tof.structuralKind b₁.tof.structuralKind)) :=
  (Basis.BasisValid.frame L h₀ h₁).tof_valid_structural

example {ε : Surface.NLCtx} {b₀ b₁ : Surface.Basis} (L : Finset GLang.Name)
    (h₀ : Surface.Basis.BasisValid ε b₀)
    (h₁ : ∀ y, y ∉ L →
      Surface.Basis.BasisValid (Finmap.insert y b₀.tof ε) (Surface.Basis.openVar y b₁)) :
    Surface.Basis.BasisValid ε (.frame b₀ b₁) := .frame L h₀ h₁

elab "check_frame_kinding_axioms" : command => do
  for n in [``Basis.BasisValid.tof_valid_structural, ``Basis.BasisValid.frame_inv] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected frame-kinding assumption in {n}: {ax}"

check_frame_kinding_axioms
