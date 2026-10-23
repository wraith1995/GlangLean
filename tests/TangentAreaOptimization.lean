import GLang.Examples.TangentAreaOptimization
import Mathlib.LinearAlgebra.Basis.Fin
import Lean

open GLang GLang.Examples.TangentCoordinates
open Lean Elab Command

private theorem pointDim (q : PartialFFSOracle) :
    pointSV.dofPartial q = .ok 2 := by
  simp [pointSV, ValSpace.dofPartial, ValSpace.shpOfPartial,
    bind, Except.bind, pure, Except.pure]

example (orc : PartialFFSOracleSem) (ρ : ValEnvSem) :
    denotValB_partial orc ρ [] []
      (optimizedAreaCode pointSV .real (.delta 0 pointSV) (.delta 1 pointSV)) =
      .ok (.array (FlatArray.ofFn 1 (fun _ => 1))) := by
  convert optimizedAreaCode_eval (orc := orc) (ρ := ρ) (av := .real) (pointDim _) (by simp [ValSpace.dofPartial, ValSpace.shpOfPartial])
    (PartialAdequacy.delta_ok (pointDim _) 0)
    (PartialAdequacy.delta_ok (pointDim _) 1) rfl rfl using 1 <;> norm_num

example (orc : PartialFFSOracleSem) (ρ : ValEnvSem) :
    denotValB_partial orc ρ [] []
      (optimizedAreaCode pointSV .real (.delta 1 pointSV) (.delta 0 pointSV)) =
      .ok (.array (FlatArray.ofFn 1 (fun _ => -1))) := by
  convert optimizedAreaCode_eval (orc := orc) (ρ := ρ) (av := .real) (pointDim _) (by simp [ValSpace.dofPartial, ValSpace.shpOfPartial])
    (PartialAdequacy.delta_ok (pointDim _) 1)
    (PartialAdequacy.delta_ok (pointDim _) 0) rfl rfl using 1 <;> norm_num

example (orc : PartialFFSOracleSem) (ρ : ValEnvSem) :
    denotValB_partial orc ρ [] [] (areaCoordinate .real 0 (.rlit 2)) =
      .error .mismatch :=
  areaCoordinate_dimension_error (by simp [ValSpace.dofPartial, ValSpace.shpOfPartial]) 0

example (orc : PartialFFSOracleSem) (ρ : ValEnvSem) :
    denotValB_partial orc ρ [] []
      (optimizedAreaCode pointSV .empty (.delta 0 pointSV) (.delta 1 pointSV)) =
      .error .mismatch :=
  optimizedAreaCode_output_error (pointDim _) (by simp [ValSpace.dofPartial, ValSpace.shpOfPartial])
    (PartialAdequacy.delta_ok (pointDim _) 0)
    (PartialAdequacy.delta_ok (pointDim _) 1) rfl rfl

-- Closed source-level regression: checked compilation of the literal
-- projected area in its completed 00,01,10,11 basis admits the replacement.
private def planeE₀ : GLang.Term := .dsumE (.real 1) (.real 0)
private def planeE₁ : GLang.Term := .dsumE (.real 0) (.real 1)

example (ρ : ValEnvSem) :
    ∃ original av,
      Operational.Term ∅ ∅ ∅ (projectedArea Examples.Paper.R2 planeE₀ planeE₁)
        (projectedAreaBasis pointBasis planeE₀ planeE₁) original (.space av) ∧
      Adequacy.PartialDirect.evalVal ρ [] [] original =
        Adequacy.PartialDirect.evalVal ρ [] []
          (optimizedAreaCode pointSV av (.delta 0 pointSV) (.delta 1 pointSV)) := by
  have h₀ : denotTerm ⟨∅⟩ planeE₀ =
      .hil ⟨denotSpace ⟨∅⟩ Examples.Paper.R2, Module.Basis.finTwoProd ℝ 0⟩ := by
    simp only [Module.Basis.finTwoProd_zero]
    rfl
  have h₁ : denotTerm ⟨∅⟩ planeE₁ =
      .hil ⟨denotSpace ⟨∅⟩ Examples.Paper.R2, Module.Basis.finTwoProd ℝ 1⟩ := by
    simp only [Module.Basis.finTwoProd_one]
    rfl
  have ht₀ : HasType ∅ ∅ planeE₀ (.space Examples.Paper.R2) :=
    .dsumE .real .real (.real_lit 1) (.real_lit 0)
  have ht₁ : HasType ∅ ∅ planeE₁ (.space Examples.Paper.R2) :=
    .dsumE .real .real (.real_lit 0) (.real_lit 1)
  apply measuredArea_optimizedCompilation (base := pointBasis)
    IofFresh.empty Examples.Paper.svR2
    (PartialAdequacy.Consistent.empty PartialDirectOracle.oracle ρ)
    (.dsum .one .one rfl rfl) rfl ht₀ ht₁ ht₀ ht₁
    (Module.Basis.finTwoProd ℝ) h₀ h₁
    (FlatArray.ofFn 2 (fun j => if j = 0 ∧ 0 < 2 then 1 else 0))
    (FlatArray.ofFn 2 (fun j => if j = 1 ∧ 1 < 2 then 1 else 0)) rfl rfl
    (by
      convert h₀ using 1 <;> norm_num
      exact ⟨rfl, heq_of_eq (Module.Basis.finTwoProd_zero ℝ)⟩)
    (by
      convert h₁ using 1 <;> norm_num
      exact ⟨rfl, heq_of_eq (Module.Basis.finTwoProd_one ℝ)⟩) (pointDim _)
    (PartialAdequacy.delta_ok (pointDim _) 0)
    (PartialAdequacy.delta_ok (pointDim _) 1)

-- Honest rank-two failure boundary: a length-one scalar is not accepted
-- as a two-coordinate input even with a valid declared rank-two space.
example (orc : PartialFFSOracleSem) (ρ : ValEnvSem) :
    denotValB_partial orc ρ [] [] (areaCoordinate pointSV 0 (.delta 0 .real)) =
      .error .mismatch :=
  areaCoordinate_length_error (pointDim _)
    (PartialAdequacy.delta_ok (n := 1)
      (by simp [ValSpace.dofPartial, ValSpace.shpOfPartial]) 0)
    (by decide) 0

elab "check_tangent_area_foundations" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``optimizedAreaCode_arithmetic, ``areaPolynomial_eval,
      ``optimizedAreaCode_eval, ``areaCoordinate_dimension_error,
      ``areaCoordinate_length_error, ``optimizedAreaCode_output_error,
      ``antisymMap_projection, ``areaGenerator_ne_zero,
      ``antisymMap_coordinates, ``antisymMap_range_span, ``projectedArea_lexInd,
      ``applyUncurry2NonReal_denot_tmul, ``antiSymLinear_denot, ``areaSpace_denot,
      ``projectedArea_denot, ``projectedAreaBasis_denot,
      ``measuredArea_optimization_correct, ``measuredArea_optimizedCompilation,
      ``rankTwo_operand_denot, ``tangentMeasuredArea_optimizedCompilation] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected dependency in {n}: {ax}"
  logInfo "Area arithmetic, live evaluator checks, normalization and LexInd: foundations only."

check_tangent_area_foundations
