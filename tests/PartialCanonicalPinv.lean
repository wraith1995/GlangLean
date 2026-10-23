import GLang.Numerics.Pseudoinverse.PseudoInverseCanonical
import GLang.Metatheory
import Lean

/-! Check numerical choice independence and the live adequacy dependency paths. -/
open GLang Lean Elab Command
open scoped Matrix

-- A nonorthonormal domain metric changes the minimum-norm solution.
-- This rectangular example catches a missing metric factor or ordinary inverse substitution.
private theorem weighted_example : WeightedPenrose
    (!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ)
    (!![(4/5 : ℝ); (1/5 : ℝ)] : Matrix (Fin 2) (Fin 1) ℝ)
    (Matrix.diagonal ![1, 4]) 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two]

example : matrixGSVDPinv (!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ)
    (Matrix.diagonal ![1, 4]) 1 =
    (!![(4/5 : ℝ); (1/5 : ℝ)] : Matrix (Fin 2) (Fin 1) ℝ) := by
  have hG : (Matrix.diagonal (![1, 4] : Fin 2 → ℝ)).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i <;> norm_num
  exact (matrixGSVDPinv_weightedPenrose _ _ _ hG Matrix.PosDef.one).unique
    hG Matrix.PosDef.one weighted_example

-- The rank-zero case works for arbitrary rectangular dimensions, including empty indices.
example (m n : Nat) : matrixSVDPinv (0 : Matrix (Fin m) (Fin n) ℝ) = 0 := by
  apply (matrixSVDPinv_weightedPenrose _).unique Matrix.PosDef.one Matrix.PosDef.one
  constructor <;> simp

example : ¬ WeightedPenrose
    (!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ)
    (!![(1/2 : ℝ); (1/2 : ℝ)] : Matrix (Fin 2) (Fin 1) ℝ)
    (Matrix.diagonal ![1, 4]) 1 := by
  intro h
  have bad := congrFun (congrFun h.ba_self 0) 1
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at bad

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
elab "check_canonical_pinv_bridge" : command => do
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``WeightedPenrose.unique, ``GSVDecomposition.weightedPenrose,
      ``matrixGSVDPinv_eq_of_decomposition, ``matrixSVDPinv_eq_of_decomposition,
      ``matrixGSVDPinv_identity, ``matrixSVDPinv_transpose,
      ``IsListBasis.coordMatrix_mooreInv_eq_matrixSVDPinv_transpose,
      ``IsListBasis.coordMatrix_mooreInv_eq_matrixGSVDPinv] do
    unless (← getConstInfo n) matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless standard.contains ax do
        throwError "Unexpected pseudoinverse assumption in {n}: {ax}"
  for (src, dst) in [(``GLang.denotValB_partial, ``matrixSVDPinv),
      (``GLang.denotValB_partial, ``matrixGSVDPinv),
      (``Metatheory.termAdequacy, ``IsListBasis.coordMatrix_mooreInv_eq_matrixSVDPinv_transpose),
      (``Metatheory.termAdequacy, ``IsListBasis.coordMatrix_mooreInv_eq_matrixGSVDPinv)] do
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
            if dep == dst || (`GLang).isPrefixOf dep ||
                dep.toString.startsWith "_private.GLang" then
              pending := dep :: pending
    unless found do
      throwError "Pseudoinverse connection missing: {src} does not use {dst}"
  logInfo "Pseudoinverses: choice independence, metric checks, and live public adequacy bridges verified."

check_canonical_pinv_bridge
