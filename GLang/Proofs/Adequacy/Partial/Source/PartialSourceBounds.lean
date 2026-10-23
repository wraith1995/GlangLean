import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectLocality
import GLang.Proofs.Adequacy.Foundations.Dims

namespace GLang.PartialAdequacy

/-- A successful query is bounded by its actual, successfully interpreted matrix shape. -/
theorem oracle_success_bound (rho : ValEnvSem) (G : List ValTy) (D : List ValValSem)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr) {n : Nat}
    (h : PartialDirectOracle.oracle rho G D p s e = .ok n) :
    ∃ sh, s.shpOfPartial (PartialDirectOracle.oracle rho G D) = .ok sh ∧
      n ≤ ffsDimUB p sh := by
  have hf := PartialDirectLocality.finite_of_success h
  rw [PartialDirectLocality.oracle_eq rho G D p s e hf] at h
  cases hs : s.shpOfPartial (PartialDirectOracle.oracle rho G D) with
  | error err => simp [hs, ffsDimensionPartial, bind, Except.bind, pure, Except.pure] at h
  | ok sh =>
    refine ⟨sh, rfl, ?_⟩
    cases he : denotValB_partial PartialDirectOracle.oracle rho G D e with
    | error err => simp [hs, he, ffsDimensionPartial, bind, Except.bind, pure, Except.pure] at h
    | ok v =>
      cases v with
      | fn A f => cases sh <;> simp [hs, he, ffsDimensionPartial, ffsOperandRankPartial, bind, Except.bind, pure, Except.pure] at h
      | array a =>
        cases sh with
        | nil => simp [hs, he, ffsDimensionPartial, ffsOperandRankPartial, bind, Except.bind] at h
        | cons m tail =>
          cases tail with
          | nil => simp [hs, he, ffsDimensionPartial, ffsOperandRankPartial, bind, Except.bind] at h
          | cons k tail =>
            cases tail with
            | cons x xs => simp [hs, he, ffsDimensionPartial, ffsOperandRankPartial, bind, Except.bind] at h
            | nil =>
              by_cases hlen : a.length = m*k
              · simp only [hs, he, ffsDimensionPartial, ffsOperandRankPartial, if_pos hlen,
                  bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
                subst n
                exact ffsDim_le_ffsDimUB p m k _ (Matrix.rank_le_height _) (Matrix.rank_le_width _)
              · simp [hs, he, ffsDimensionPartial, ffsOperandRankPartial, hlen, bind, Except.bind] at h

/-- Successful partial dimensions fit the syntax-indexed finite assembly family. -/
theorem dof_success_le (rho : ValEnvSem) (G : List ValTy) (D : List ValValSem) :
    ∀ (sv : ValSpace) (n : Nat),
      sv.dofPartial (PartialDirectOracle.oracle rho G D) = .ok n → n ≤ sv.dofUB
  | .empty, n, h => by
      simp [ValSpace.dofPartial, ValSpace.shpOfPartial, bind, Except.bind, pure, Except.pure] at h
      subst n
      exact le_rfl
  | .real, n, h => by
      simp [ValSpace.dofPartial, ValSpace.shpOfPartial, bind, Except.bind, pure, Except.pure] at h
      subst n
      exact le_rfl
  | .dsum a b, n, h => by
      cases ha : a.dofPartial (PartialDirectOracle.oracle rho G D) <;>
        cases hb : b.dofPartial (PartialDirectOracle.oracle rho G D) <;>
        simp [ValSpace.dofPartial, ValSpace.shpOfPartial, ha, hb, bind, Except.bind, pure, Except.pure] at h
      next m k =>
        subst n
        exact Nat.add_le_add (dof_success_le rho G D a m ha) (dof_success_le rho G D b k hb)
  | .tprod a b, n, h => by
      cases ha : a.dofPartial (PartialDirectOracle.oracle rho G D) <;>
        cases hb : b.dofPartial (PartialDirectOracle.oracle rho G D) <;>
        simp [ValSpace.dofPartial, ValSpace.shpOfPartial, ha, hb, bind, Except.bind, pure, Except.pure] at h
      next m k =>
        subst n
        exact Nat.mul_le_mul (dof_success_le rho G D a m ha) (dof_success_le rho G D b k hb)
  | .ffs p s e, n, h => by
      cases hq : PartialDirectOracle.oracle rho G D p s e with
      | error err => simp [ValSpace.dofPartial, ValSpace.shpOfPartial, hq, bind, Except.bind] at h
      | ok v =>
        simp [ValSpace.dofPartial, ValSpace.shpOfPartial, hq, bind, Except.bind, pure, Except.pure] at h
        subst n
        obtain ⟨sh, hs, hv⟩ := oracle_success_bound rho G D p s e hq
        cases s with
        | empty =>
          simp [ValSpace.shpOfPartial] at hs
          subst sh
          simp only [ffsDimUB_singleton] at hv
          omega
        | real =>
          simp [ValSpace.shpOfPartial] at hs
          subst sh
          simp only [ffsDimUB_singleton] at hv
          omega
        | dsum a b =>
          cases ha : a.dofPartial (PartialDirectOracle.oracle rho G D) <;>
            cases hb : b.dofPartial (PartialDirectOracle.oracle rho G D) <;>
            simp [ValSpace.shpOfPartial, ha, hb, bind, Except.bind, pure, Except.pure] at hs
          next m k =>
            subst sh
            simp only [ffsDimUB_singleton] at hv
            omega
        | ffs p' s' e' =>
          cases hq' : PartialDirectOracle.oracle rho G D p' s' e' <;>
            simp [ValSpace.shpOfPartial, hq', bind, Except.bind, pure, Except.pure] at hs
          next m =>
            subst sh
            simp only [ffsDimUB_singleton] at hv
            omega
        | tprod a b =>
          cases ha : a.dofPartial (PartialDirectOracle.oracle rho G D) <;>
            cases hb : b.dofPartial (PartialDirectOracle.oracle rho G D) <;>
            simp [ValSpace.shpOfPartial, ha, hb, bind, Except.bind, pure, Except.pure] at hs
          next m k =>
            subst sh
            have hma := dof_success_le rho G D a m ha
            have hkb := dof_success_le rho G D b k hb
            cases p <;> simp only [ffsDimUB, ValSpace.dofUB] at hv ⊢
            · exact hv.trans hma
            · exact hv.trans hma
            · exact hv.trans hkb
            · exact hv.trans hkb
termination_by sv => sizeOf sv

end GLang.PartialAdequacy
