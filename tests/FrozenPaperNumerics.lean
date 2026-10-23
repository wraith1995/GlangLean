import GLang.Paper
import GLang.Proofs.Adequacy.Raw.Terms.RawTermsRREFLexInd
import Lean

/-! Frozen numerical formulas and their use by the actual public proofs. -/
open GLang Lean Elab Command
open PaperNumericalResults
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 0

example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric) (μ : ℝ)
    (hμ : ¬ Module.End.HasEigenvalue S μ) :
    BasisSpectral.spectralProjector S μ = 0 := by
  rw [spectralProjector_eq_guardedPolynomial S hS μ, if_neg hμ]

section Spectra
variable (V W : HSpace)
local instance : InnerProductSpace.Core ℝ V.carrier := V.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ W.carrier := W.innerIsIP.toIPSCore
local instance : NormedAddCommGroup W.carrier := W.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance
example (A : V.carrier →ₗ[ℝ] W.carrier) (μ : ℝ) :
    μ ∈ BasisPairedSpectral.values V W A ↔
      Module.End.HasEigenvalue (LinearMap.adjoint A ∘ₗ A) μ ∨
      Module.End.HasEigenvalue (A ∘ₗ LinearMap.adjoint A) μ :=
  BasisPairedSpectral.mem_values V W A μ
example (A : V.carrier →ₗ[ℝ] W.carrier) :
    (BasisPairedSpectral.values V W A).Nodup :=
  BasisPairedSpectral.values_nodup V W A
end Spectra

example (N K : ℕ) (a c : ℕ → ℝ) :
    termsRREFRepMatrix N K a c = denotAsMatrix N N c *
      (Matrix.of (fun i j =>
        (matrixRREF (termsCandidateMatrix N K a)).R i (Fin.natAdd K j))).transpose :=
  termsRREFRepMatrix_eq_reduced_tail N K a c
example (K : ℕ) (a : ℕ → ℝ) :
    termsCandidateMatrix 0 K a * termsCandidateRightInverse 0 K = 1 :=
  termsCandidateMatrix_rightInverse 0 K a

elab "check_frozen_numerical_proofs" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``spectralProjector_eq_guardedPolynomial, ``projectedBasisColumns,
      ``pseudoinverse_paired, ``pseudoinverse_standard, ``mooreInverse_coordinates_paired,
      ``pseudoinverse_orthonormalColumns,
      ``standardRREFLexInd_proved, ``termsRREFRepMatrix_eq_of_decomposition] do
    unless (← getConstInfo n) matches .thmInfo _ do
      throwError "Expected a theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected numerical assumption in {n}: {ax}"
  -- The public adequacy proof must actually use the exact ordered-vector and
  -- coordinate-inverse results; their mere presence in the import is insufficient.
  let mut pending := [``Metatheory.termAdequacy, ``Metatheory.cobAdequacy,
    ``Metatheory.dimensionAdequacy]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !seen.contains n then
      seen := seen.insert n
      let info ← getConstInfo n
      let deps := info.type.getUsedConstants ++
        (info.value?.map (·.getUsedConstants) |>.getD #[])
      for dep in deps do
        if (`GLang).isPrefixOf dep || dep.toString.startsWith "_private.GLang." then
          pending := dep :: pending
  for n in [``ValuePairedSVD.U_ofCoords, ``ValuePairedSVD.UI_ofCoords,
      ``ValuePairedSVD.V_ofCoords, ``ValuePairedSVD.VI_ofCoords,
      ``standardRREFLexInd_proved, ``IsListBasis.coordMatrix_mooreInv_eq_matrixGSVDPinv] do
    unless seen.contains n do
      throwError "Public adequacy no longer uses numerical correspondence {n}"
  logInfo "Frozen numerical formulas: proved from standard foundations and used by public adequacy."

check_frozen_numerical_proofs
