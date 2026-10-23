import GLang.Proofs.Adequacy.Foundations.Strengthened

namespace GLang

/-! ## `shpOf` / `dof` unfolding -/

@[simp] theorem ValSpace.dof_ffs (orc : FFSOracle) (p : ValFFSProp) (s : ValSpace) (w : ValExpr) :
    ValSpace.dof orc (.ffs p s w) = orc p s w := by
  simp [ValSpace.dof]

/-- Every non-tensor value space has a one-element shape (`rnk = 0`). -/
theorem ValSpace.shpOf_length_one (orc : FFSOracle) :
    ∀ s : ValSpace, (∀ s₀ s₁, s ≠ .tprod s₀ s₁) → (ValSpace.shpOf orc s).length = 1
  | .empty, _ => by simp
  | .real, _ => by simp
  | .dsum _ _, _ => by simp
  | .tprod s₀ s₁, h => absurd rfl (h s₀ s₁)
  | .ffs _ _ _, _ => by simp

/-! ## `dof ≤ dofUB` under the oracle contract -/

/-- `ffsDim` on a non-2-element shape is `0` (the fallback arm). -/
theorem ffsDim_singleton (p : ValFFSProp) (d r : Nat) : ffsDim p [d] r = 0 := by
  cases p <;> rfl

/-- The FFS leaf over a tensor parent, given the factor bounds: bound the oracle by
    `hspec.bound` (rank ≤ ambient, `ffsDimUB p [d₀, d₁]`) and the ambient factor by the IH. -/
theorem ValSpace.dof_ffs_tprod_le {orc : FFSOracleSem} (hspec : OracleSpec orc) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (p : ValFFSProp) (s₀ s₁ : ValSpace) (w : ValExpr)
    (ih₀ : ValSpace.dof (orc ρ Γ Δ) s₀ ≤ ValSpace.dofUB s₀)
    (ih₁ : ValSpace.dof (orc ρ Γ Δ) s₁ ≤ ValSpace.dofUB s₁) :
    ValSpace.dof (orc ρ Γ Δ) (.ffs p (.tprod s₀ s₁) w) ≤ ValSpace.dofUB (.ffs p (.tprod s₀ s₁) w) := by
  rw [ValSpace.dof_ffs]
  refine (hspec.bound ρ Γ Δ p (.tprod s₀ s₁) w).trans ?_
  simp only [ValSpace.shpOf_tprod]
  cases p
  · simp only [ffsDimUB, ValSpace.dofUB]; exact ih₀
  · simp only [ffsDimUB, ValSpace.dofUB]; exact ih₀
  · simp only [ffsDimUB, ValSpace.dofUB]; exact ih₁
  · simp only [ffsDimUB, ValSpace.dofUB]; exact ih₁

/-- The FFS leaf over a NON-tensor parent: the parent shape is a singleton, so `ffsDimUB` is
    `0` and `hspec.bound` gives dimension `0`. -/
theorem ValSpace.dof_ffs_nontprod_le {orc : FFSOracleSem} (hspec : OracleSpec orc) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (p : ValFFSProp) (s : ValSpace) (w : ValExpr)
    (hs : ∀ s₀ s₁, s ≠ .tprod s₀ s₁) :
    ValSpace.dof (orc ρ Γ Δ) (.ffs p s w) ≤ ValSpace.dofUB (.ffs p s w) := by
  rw [ValSpace.dof_ffs]
  refine (hspec.bound ρ Γ Δ p s w).trans ?_
  cases s with
  | tprod s₀ s₁ => exact absurd rfl (hs s₀ s₁)
  | empty => simp only [ValSpace.shpOf_empty, ffsDimUB_singleton]; exact Nat.zero_le _
  | real => simp only [ValSpace.shpOf_real, ffsDimUB_singleton]; exact Nat.zero_le _
  | dsum _ _ => simp only [ValSpace.shpOf_dsum, ffsDimUB_singleton]; exact Nat.zero_le _
  | ffs _ _ _ => simp only [ValSpace.shpOf_ffs, ffsDimUB_singleton]; exact Nat.zero_le _

theorem ffsDim_operandRank_le_ffsDimUB (orc : FFSOracleSem) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (p : ValFFSProp) (s : ValSpace) (w : ValExpr) :
    ffsDim p (ValSpace.shpOf (orc ρ Γ Δ) s) (ffsOperandRank orc ρ Γ Δ s w)
      ≤ ffsDimUB p (ValSpace.shpOf (orc ρ Γ Δ) s) := by
  unfold ffsOperandRank
  split
  · rename_i d₀ d₁ hd
    rw [hd]
    split
    · exact ffsDim_le_ffsDimUB p d₀ d₁ _
        (Matrix.rank_le_height _) (Matrix.rank_le_width _)
    · exact ffsDim_le_ffsDimUB p d₀ d₁ 0 (Nat.zero_le _) (Nat.zero_le _)
  · rename_i hne
    match hs : ValSpace.shpOf (orc ρ Γ Δ) s with
    | [] => cases p <;> exact Nat.le_refl _
    | [d] => rw [ffsDim_singleton, ffsDimUB_singleton]
    | [d₀, d₁] => exact absurd hs (hne d₀ d₁)
    | _ :: _ :: _ :: _ => cases p <;> exact Nat.le_refl _

theorem ValSpace.dof_le_dofUB {orc : FFSOracleSem} (hspec : OracleSpec orc) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) :
    ∀ sv : ValSpace, ValSpace.dof (orc ρ Γ Δ) sv ≤ ValSpace.dofUB sv
  | .empty => by simp [ValSpace.dofUB]
  | .real => by simp [ValSpace.dofUB]
  | .dsum s₀ s₁ => by
      simp only [ValSpace.dof_dsum, ValSpace.dofUB]
      exact Nat.add_le_add (ValSpace.dof_le_dofUB hspec ρ Γ Δ s₀)
        (ValSpace.dof_le_dofUB hspec ρ Γ Δ s₁)
  | .tprod s₀ s₁ => by
      simp only [ValSpace.dof_tprod, ValSpace.dofUB]
      exact Nat.mul_le_mul (ValSpace.dof_le_dofUB hspec ρ Γ Δ s₀)
        (ValSpace.dof_le_dofUB hspec ρ Γ Δ s₁)
  | .ffs p (.tprod s₀ s₁) w =>
      ValSpace.dof_ffs_tprod_le hspec ρ Γ Δ p s₀ s₁ w
        (ValSpace.dof_le_dofUB hspec ρ Γ Δ s₀) (ValSpace.dof_le_dofUB hspec ρ Γ Δ s₁)
  | .ffs p .empty w => ValSpace.dof_ffs_nontprod_le hspec ρ Γ Δ p _ w (fun _ _ h => by cases h)
  | .ffs p .real w => ValSpace.dof_ffs_nontprod_le hspec ρ Γ Δ p _ w (fun _ _ h => by cases h)
  | .ffs p (.dsum _ _) w =>
      ValSpace.dof_ffs_nontprod_le hspec ρ Γ Δ p _ w (fun _ _ h => by cases h)
  | .ffs p (.ffs _ _ _) w =>
      ValSpace.dof_ffs_nontprod_le hspec ρ Γ Δ p _ w (fun _ _ h => by cases h)

/-- A general transitive corollary of `dof_le_dofUB`: any external upper bound
    on `dofUB sv` also bounds the semantic dimension.  The live `llam` rules use
    `dof_le_dofUB` directly because their family is indexed by the exact bound. -/
theorem ValSpace.dof_le_of_dofUB_le {orc : FFSOracleSem} (hspec : OracleSpec orc)
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem) {sv : ValSpace} {n : Nat}
    (hn : ValSpace.dofUB sv ≤ n) : ValSpace.dof (orc ρ Γ Δ) sv ≤ n :=
  (ValSpace.dof_le_dofUB hspec ρ Γ Δ sv).trans hn

end GLang
