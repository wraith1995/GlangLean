import GLang.Proofs.Basis.BasisStandardFixed
import Lean

open Lean Elab Command
elab "check_standard_fixed_axioms" : command => do
  for ax in ← Lean.collectAxioms ``GLang.Basis.BasisValid.std_tof_eq do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
      throwError "Unexpected project assumption: {ax}"
check_standard_fixed_axioms

example {ε : GLang.NLCtx} {b0 b1 : GLang.Basis}
    (h : GLang.Basis.BasisValid ε (.frame b0 b1))
    (hs : GLang.Basis.isStd (.frame b0 b1)) :
    GLang.Basis.std (GLang.Basis.tof (.frame b0 b1)) = .frame b0 b1 :=
  h.std_tof_eq hs
#print axioms GLang.Basis.BasisValid.std_tof_eq
