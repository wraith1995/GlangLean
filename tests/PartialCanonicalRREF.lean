import GLang.Proofs.Adequacy.Raw.Terms.RawTermsRREFLexInd
import GLang.Proofs.Value.DenotationChecks
import Lean

/-! Canonical RREF results and the live numerical/source connection. -/
open GLang Lean Elab Command

/-- At deficient rank the auxiliary row operation is deliberately not canonical. -/
private noncomputable def zeroDecomposition (t : ℝ) (ht : t ≠ 0) : RREFDecomposition 1 1 where
  rank := 0
  rank_le_m := Nat.zero_le _
  rank_le_n := Nat.zero_le _
  R := 0
  pivots := Fin.elim0
  E := fun _ _ => t
  E_inv := fun _ _ => t⁻¹
  E_left_inv := by
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, ht]
  pivots_strict_mono := fun i => i.elim0
  pivot_entries_one := fun i => i.elim0
  pivot_columns_zero := fun i => i.elim0
  zero_rows_below := by intros; rfl
  left_of_pivot_zero := fun i => i.elim0

example : (zeroDecomposition 1 (by norm_num)).E_inv ≠
    (zeroDecomposition 2 (by norm_num)).E_inv := by
  intro he
  have hc := congrFun (congrFun he 0) 0
  norm_num [zeroDecomposition] at hc

example : (matrixRREF (0 : Matrix (Fin 1) (Fin 1) ℝ)).R = 0 :=
  matrixRREF_unique _ (zeroDecomposition 2 (by norm_num)) (by
    simp [zeroDecomposition])

elab "check_canonical_rref_bridge" : command => do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``RREFDecomposition.reduced_eq, ``RREFDecomposition.pivots_eq,
      ``matrixRREF_unique, ``matrixRREF_idempotent,
      ``termsRREFRepMatrix_eq_reduced_tail, ``termsRREFRepMatrix_eq_of_decomposition,
      ``standardRREFLexInd_proved, ``rref_pivot_columns_eq_lexInd_of_decomposition] do
    unless (← getConstInfo n) matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless standard.contains ax do
        throwError "Unexpected RREF assumption in {n}: {ax}"
  for (src, dst) in [(``GLang.denotValB_partial, ``termsRREFRepDenot),
      (``termsRREFRepDenot, ``termsRREFRepMatrix),
      (``termsRREFRepMatrix, ``matrixRREF),
      (``matrixRREF, ``GLang.Matrix.rref)] do
    -- Recursive evaluators are compiled through generated helper definitions.
    let mut pending := [src]
    let mut seen : NameSet := {}
    let mut found := false
    while !pending.isEmpty && !found do
      let name := pending.head!
      pending := pending.tail!
      if name == dst then
        found := true
      else if !seen.contains name then
        seen := seen.insert name
        if let some body := (← getConstInfo name).value? then
          for dep in body.getUsedConstants do
            if dep == dst || src.isPrefixOf dep then
              pending := dep :: pending
    unless found do
      throwError "RREF implementation disconnected: {src} does not use {dst}"
  logInfo "RREF uniqueness, idempotence, operational choice independence, and exact LexInd correspondence: foundations only."

check_canonical_rref_bridge
#print axioms GLang.matrixRREF_idempotent
#print axioms GLang.termsRREFRepMatrix_eq_of_decomposition
