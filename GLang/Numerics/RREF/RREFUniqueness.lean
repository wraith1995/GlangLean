import GLang.Numerics.RREF.ValueRREFDefs
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Sort

/-! Uniqueness of reduced form and ordered pivots. The auxiliary row-operation
matrix need not be unique; only the observable reduced form is canonical. -/
namespace GLang.RREFDecomposition
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Reducing a factored matrix recovers its recorded reduced form. -/
theorem reduce_factor {m n : ℕ} (g : RREFDecomposition m n)
    (A : Matrix (Fin m) (Fin n) ℝ) (ha : A = g.E * g.R) :
    g.E_inv * A = g.R := by
  rw [ha, ← Matrix.mul_assoc, g.E_left_inv, Matrix.diagonal_one, Matrix.one_mul]

/-- At a pivot column, a row combination reads its corresponding coefficient. -/
theorem combination_pivot {m n : ℕ} (h : RREFDecomposition m n)
    (M : Matrix (Fin m) (Fin m) ℝ) (i : Fin m) (q : Fin h.rank) :
    (M * h.R) i (h.pivots q) = M i (Fin.castLE h.rank_le_m q) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.castLE h.rank_le_m q)]
  · have hp : h.R (Fin.castLE h.rank_le_m q) (h.pivots q) = 1 := h.pivot_entries_one q
    rw [hp, mul_one]
  · intro k _ hk
    rw [h.pivot_columns_zero q k (fun he => hk (Fin.ext he)), mul_zero]
  · simp

/-- A pivot of one reduced row family must occur in every reduced row family
that spans it. This uses the leading-entry condition, not just rank. -/
theorem pivot_mem_of_mul {m n : ℕ} (g h : RREFDecomposition m n)
    (M : Matrix (Fin m) (Fin m) ℝ) (he : g.R = M * h.R) (p : Fin g.rank) :
    ∃ q : Fin h.rank, h.pivots q = g.pivots p := by
  classical
  by_contra hn
  have hz : g.R (Fin.castLE g.rank_le_m p) (g.pivots p) = 0 := by
    rw [he, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < h.rank
    · let q : Fin h.rank := ⟨k.val, hk⟩
      have hne : h.pivots q ≠ g.pivots p := fun eq => hn ⟨q, eq⟩
      rcases lt_or_gt_of_ne (show (h.pivots q).val ≠ (g.pivots p).val from
        fun eq => hne (Fin.ext eq)) with hl | hr
      · have hc : M (Fin.castLE g.rank_le_m p) k = 0 := by
          have hh := combination_pivot h M (Fin.castLE g.rank_le_m p) q
          rw [← he] at hh
          have hz : g.R (Fin.castLE g.rank_le_m p) (h.pivots q) = 0 :=
            g.left_of_pivot_zero p (h.pivots q) hl
          rw [hz] at hh
          exact hh.symm
        rw [hc, zero_mul]
      · have hh := h.left_of_pivot_zero q (g.pivots p) hr
        change h.R k (g.pivots p) = 0 at hh
        rw [hh, mul_zero]
    · rw [h.zero_rows_below k (Nat.le_of_not_gt hk), mul_zero]
  have hp := g.pivot_entries_one p
  exact one_ne_zero (hp.symm.trans hz)

/-- Equal row spans force exactly the same increasing pivot enumeration. -/
theorem pivot_list_eq {m n : ℕ} (g h : RREFDecomposition m n)
    (M N : Matrix (Fin m) (Fin m) ℝ) (hg : g.R = M * h.R) (hh : h.R = N * g.R) :
    List.ofFn g.pivots = List.ofFn h.pivots := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·))
  · rw [List.pairwise_ofFn]
    exact g.pivots_strict_mono
  · rw [List.pairwise_ofFn]
    exact h.pivots_strict_mono
  · intro j
    simp only [List.mem_ofFn]
    constructor
    · rintro ⟨p, rfl⟩
      exact pivot_mem_of_mul g h M hg p
    · rintro ⟨q, rfl⟩
      exact pivot_mem_of_mul h g N hh q

/-- Reduced matrices with equal row spans are identical, even at deficient rank. -/
theorem reduced_eq_of_mul {m n : ℕ} (g h : RREFDecomposition m n)
    (M N : Matrix (Fin m) (Fin m) ℝ) (hg : g.R = M * h.R) (hh : h.R = N * g.R) :
    g.R = h.R := by
  classical
  have hl := pivot_list_eq g h M N hg hh
  have hr : g.rank = h.rank := by simpa using congrArg List.length hl
  have hp : ∀ p : Fin g.rank, g.pivots p = h.pivots (Fin.cast hr p) := by
    intro p
    have he := congrArg (fun xs : List (Fin n) => xs[p.val]?) hl
    obtain ⟨hk, heq⟩ : ∃ hk : p.val < h.rank,
        g.pivots p = h.pivots ⟨p.val, hk⟩ := by simpa using he
    exact heq
  ext i j
  by_cases hi : i.val < g.rank
  · let p : Fin g.rank := ⟨i.val, hi⟩
    have hcoeff : ∀ k : Fin m, k.val < h.rank →
        M i k = if i = k then 1 else 0 := by
      intro k hk
      let q : Fin g.rank := ⟨k.val, hr ▸ hk⟩
      have hc := combination_pivot h M i (Fin.cast hr q)
      rw [← hg, ← hp q] at hc
      by_cases hik : i = k
      · subst k
        simpa [q] using hc.symm.trans (g.pivot_entries_one q)
      · rw [if_neg hik]
        exact hc.symm.trans (g.pivot_columns_zero q i
          (fun eq => hik (Fin.ext eq)))
    rw [hg, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hcoeff i (hr ▸ hi), if_pos rfl, one_mul]
    · intro k _ hk
      by_cases hkr : k.val < h.rank
      · rw [hcoeff k hkr, if_neg (Ne.symm hk), zero_mul]
      · rw [h.zero_rows_below k (Nat.le_of_not_gt hkr), mul_zero]
    · simp
  · rw [g.zero_rows_below i (Nat.le_of_not_gt hi),
      h.zero_rows_below i (hr ▸ Nat.le_of_not_gt hi)]

/-- Any two valid decompositions of the same matrix have identical reduced forms. -/
theorem reduced_eq {m n : ℕ} (g h : RREFDecomposition m n)
    (A : Matrix (Fin m) (Fin n) ℝ) (hg : A = g.E * g.R) (hh : A = h.E * h.R) :
    g.R = h.R := by
  apply reduced_eq_of_mul g h (g.E_inv * h.E) (h.E_inv * g.E)
  · rw [Matrix.mul_assoc, ← hh, g.reduce_factor A hg]
  · rw [Matrix.mul_assoc, ← hg, h.reduce_factor A hh]

/-- The canonical pivot list is independent of the decomposition witness. -/
theorem pivots_eq {m n : ℕ} (g h : RREFDecomposition m n)
    (A : Matrix (Fin m) (Fin n) ℝ) (hg : A = g.E * g.R) (hh : A = h.E * h.R) :
    List.ofFn g.pivots = List.ofFn h.pivots := by
  apply pivot_list_eq g h (g.E_inv * h.E) (h.E_inv * g.E)
  · rw [Matrix.mul_assoc, ← hh, g.reduce_factor A hg]
  · rw [Matrix.mul_assoc, ← hg, h.reduce_factor A hh]

/-- When the input has a right inverse, even the inverse row-operation matrix
is fixed by the reduced form. No such claim is made at deficient row rank. -/
theorem inverse_eq_reduced_mul {m n : ℕ} (g : RREFDecomposition m n)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (ha : A = g.E * g.R) (hab : A * B = 1) : g.E_inv = g.R * B := by
  calc
    g.E_inv = g.E_inv * (A * B) := by rw [hab, Matrix.mul_one]
    _ = g.R * B := by rw [← Matrix.mul_assoc, g.reduce_factor A ha]

/-- Full-row-rank inputs have a choice-independent inverse row operation. -/
theorem inverse_eq {m n : ℕ} (g h : RREFDecomposition m n)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (hg : A = g.E * g.R) (hh : A = h.E * h.R) (hab : A * B = 1) :
    g.E_inv = h.E_inv := by
  rw [g.inverse_eq_reduced_mul A B hg hab, h.inverse_eq_reduced_mul A B hh hab,
    g.reduced_eq h A hg hh]
end GLang.RREFDecomposition
