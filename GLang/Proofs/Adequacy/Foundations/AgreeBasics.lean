import GLang.Proofs.Adequacy.Foundations.Agree
import GLang.Proofs.Adequacy.Foundations.Dims
import GLang.Proofs.Source.Soundness

namespace GLang

/-! ## Kind discipline -/

/-- `LegacyAgree` at a space type forces a space value type. -/
theorem LegacyAgree.space_kind {orc : FFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} {Δs : List DVal}
    {Γv : List ValTy} {Δv : List ValValSem} {s : GLang.Space} {τv : ValTy} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : LegacyAgree orc σ ρ Δs Γv Δv (.space s) τv B x y) : ∃ sv, τv = .space sv := by
  cases τv with
  | space sv => exact ⟨sv, rfl⟩
  | piTy _ _ => cases y <;> simp [LegacyAgree] at h

/-- `LegacyAgree` at a Π type forces a Π value type. -/
theorem LegacyAgree.piTy_kind {orc : FFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} {Δs : List DVal}
    {Γv : List ValTy} {Δv : List ValValSem} {τ₀ τ₁ : GLang.Ty} {τv : ValTy} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : LegacyAgree orc σ ρ Δs Γv Δv (.piTy τ₀ τ₁) τv B x y) : ∃ τv₀ τv₁, τv = .piTy τv₀ τv₁ := by
  cases τv with
  | space _ => cases y <;> simp [LegacyAgree] at h
  | piTy τv₀ τv₁ => exact ⟨τv₀, τv₁, rfl⟩

/-- At base kind the value denotation is an array (a function never agrees at base kind). -/
theorem LegacyAgree.space_array {orc : FFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} {Δs : List DVal}
    {Γv : List ValTy} {Δv : List ValValSem} {s : GLang.Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : LegacyAgree orc σ ρ Δs Γv Δv (.space s) (.space sv) B x y) : ∃ a, y = .array a := by
  cases y with
  | array a => exact ⟨a, rfl⟩
  | fn _ _ => simp [LegacyAgree] at h

/-! ## The base-kind clause -/

/-- Unfolding of the base-kind clause of `def:agree`. -/
theorem LegacyAgree.space_iff {orc : FFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} {Δs : List DVal}
    {Γv : List ValTy} {Δv : List ValValSem} {s : GLang.Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {a : FlatArray} :
    LegacyAgree orc σ ρ Δs Γv Δv (.space s) (.space sv) B x (.array a) ↔
      (B.atSpace (denotSpaceAux σ Δs s)).length = ValSpace.dof (orc ρ Γv Δv) sv ∧
      a.length = ValSpace.dof (orc ρ Γv Δv) sv ∧
      x.atSpace (denotSpaceAux σ Δs s) =
        ∑ i : Fin (ValSpace.dof (orc ρ Γv Δv) sv),
          a.get i.val • (B.atSpace (denotSpaceAux σ Δs s)).getD i.val 0 := by
  simp only [LegacyAgree]

/-- The two length pins of `def:agree` at base kind: the basis vector list and the flat
    array both have the SEMANTIC dimension `dof (orc ρ Γv Δv) sv`. -/
theorem LegacyAgree.length {orc : FFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} {Δs : List DVal}
    {Γv : List ValTy} {Δv : List ValValSem} {s : GLang.Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {a : FlatArray}
    (h : LegacyAgree orc σ ρ Δs Γv Δv (.space s) (.space sv) B x (.array a)) :
    (B.atSpace (denotSpaceAux σ Δs s)).length = ValSpace.dof (orc ρ Γv Δv) sv ∧
    a.length = ValSpace.dof (orc ρ Γv Δv) sv :=
  ⟨(LegacyAgree.space_iff.mp h).1, (LegacyAgree.space_iff.mp h).2.1⟩

/-- The coefficient identity of `def:agree` at base kind: `x` is the expansion of the array
    in the basis vectors. -/
theorem LegacyAgree.coords {orc : FFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} {Δs : List DVal}
    {Γv : List ValTy} {Δv : List ValValSem} {s : GLang.Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {a : FlatArray}
    (h : LegacyAgree orc σ ρ Δs Γv Δv (.space s) (.space sv) B x (.array a)) :
    x.atSpace (denotSpaceAux σ Δs s) =
      ∑ i : Fin (ValSpace.dof (orc ρ Γv Δv) sv),
        a.get i.val • (B.atSpace (denotSpaceAux σ Δs s)).getD i.val 0 :=
  (LegacyAgree.space_iff.mp h).2.2

/-! ## The `zero` arm -/

/-- **`zero` arm content** (`S.Term.zero` × `OpStep.zero`): `⟦0_s⟧σ ≡_B ⟦0_sv⟧ρ` for ANY basis
    denotation `B` whose vector list at `⟦s⟧σ` has the semantic length of `sv`. The value side
    is `denotValB_semS`'s `.zero` arm (`arrayOf (dof sv) 0`), the source side is the zero
    vector of `⟦s⟧σ`, and the expansion of the zero array is `0`. -/
theorem LegacyAgree.zero {orc : FFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} {s : GLang.Space}
    {sv : ValSpace} {B : BasisDenot}
    (hlen : (B.atSpace (denotSpace σ s)).length = ValSpace.dof (orc ρ [] []) sv) :
    LegacyResultAgree orc σ ρ [] [] [] (.space s) (.space sv) B (denotTerm σ (.zero s))
      (denotValB_semS orc ρ [] [] (.zero sv)) := by
  unfold LegacyResultAgree
  rw [denotValB_semS.eq_4]
  refine ⟨_, rfl, ?_⟩
  simp only [ValExpr.inferSpaceCtx, ValValSem.arrayOf]
  rw [LegacyAgree.space_iff]
  refine ⟨hlen, FlatArray.length_ofFn _ _, ?_⟩
  -- source side: the zero vector
  have hsrc : (denotTerm σ (.zero s)).atSpace (denotSpaceAux σ [] s) = 0 := by
    show (DVal.hil ⟨denotSpaceAux σ [] s, (0 : (denotSpaceAux σ [] s).carrier)⟩).atSpace
      (denotSpaceAux σ [] s) = 0
    exact DVal.atSpace_hil_self _ _
  rw [hsrc]
  symm
  apply Finset.sum_eq_zero
  intro i _
  rw [FlatArray.get_ofFn_lt _ _ _ i.isLt, zero_smul]

end GLang
