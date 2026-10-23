import GLang.Numerics.RREF.ValueRREFDefs

/-! Constructive column-extension invariants for RREF existence. -/
namespace GLang
open scoped BigOperators

namespace RREFDecomposition

/-- Append a reduced column with no entries below the existing pivot rows.
No new pivot or row operation is required. -/
def appendDependent {m n : Nat} (g : RREFDecomposition m n)
    (c : Fin m → ℝ) (hc : ∀ i : Fin m, g.rank ≤ i.val → c i = 0) :
    RREFDecomposition m (n + 1) where
  rank := g.rank
  rank_le_m := g.rank_le_m
  rank_le_n := Nat.le.step g.rank_le_n
  R := fun i => Fin.lastCases (c i) (g.R i)
  pivots := fun q => (g.pivots q).castSucc
  E := g.E
  E_inv := g.E_inv
  E_left_inv := g.E_left_inv
  pivots_strict_mono := g.pivots_strict_mono
  pivot_entries_one := by
    intro q
    simpa using g.pivot_entries_one q
  pivot_columns_zero := by
    intro q k hk
    simpa using g.pivot_columns_zero q k hk
  zero_rows_below := by
    intro i hi j
    induction j using Fin.lastCases with
    | last => simpa using hc i hi
    | cast j => simpa using g.zero_rows_below i hi j
  left_of_pivot_zero := by
    intro q j hj
    induction j using Fin.lastCases with
    | last => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt (g.pivots q).isLt) hj)
    | cast j => simpa using g.left_of_pivot_zero q j hj

/-- For a finite square row transformation, the recorded left inverse is
also a right inverse. -/
theorem right_inv {m n : Nat} (g : RREFDecomposition m n) : g.E * g.E_inv = 1 := by
  apply mul_eq_one_comm.mp
  simpa only [Matrix.diagonal_one] using g.E_left_inv

/-- Applying the inverse row transformation to the new column produces the
unique reduced column with the required factorization. -/
theorem appendDependent_factor {m n : Nat}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : RREFDecomposition m n)
    (hprefix : (fun i j => A i j.castSucc) = g.E * g.R)
    (hc : ∀ i : Fin m, g.rank ≤ i.val →
      (g.E_inv.mulVec (fun k => A k (Fin.last n))) i = 0) :
    A = (g.appendDependent _ hc).E * (g.appendDependent _ hc).R := by
  ext i j
  induction j using Fin.lastCases with
  | cast j =>
      have h := congrFun (congrFun hprefix i) j
      simpa [appendDependent, Matrix.mul_apply] using h
  | last =>
      have h := congrFun (Matrix.mulVec_mulVec
        (fun k => A k (Fin.last n)) g.E g.E_inv) i
      rw [g.right_inv, Matrix.one_mulVec] at h
      simpa [appendDependent, Matrix.mul_apply, Matrix.mulVec] using h.symm

/-- Constructive successor case whenever the new reduced column has no
residual below the existing pivot rows. -/
theorem exists_append_of_tail_zero {m n : Nat}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : RREFDecomposition m n)
    (hprefix : (fun i j => A i j.castSucc) = g.E * g.R)
    (hc : ∀ i : Fin m, g.rank ≤ i.val →
      (g.E_inv.mulVec (fun k => A k (Fin.last n))) i = 0) :
    ∃ d : RREFDecomposition m (n + 1), A = d.E * d.R :=
  ⟨g.appendDependent _ hc, g.appendDependent_factor A hprefix hc⟩

/-- Once the prefix already has full row rank, all subsequent columns fall
under the constructive no-new-pivot case. -/
theorem exists_append_of_full_row_rank {m n : Nat}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : RREFDecomposition m n)
    (hprefix : (fun i j => A i j.castSucc) = g.E * g.R)
    (hrank : g.rank = m) :
    ∃ d : RREFDecomposition m (n + 1), A = d.E * d.R := by
  apply g.exists_append_of_tail_zero A hprefix
  intro i hi
  have := i.isLt
  omega

/-- Clear a nonzero coordinate, normalizing it to one, with an explicit inverse. -/
noncomputable def clearColumn {m : Nat} (c : Fin m → ℝ) (q : Fin m) (hq : c q ≠ 0) :
    (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) where
  toFun x i := if i = q then x q / c q else x i - c i * (x q / c q)
  invFun x i := if i = q then c q * x q else x i + c i * x q
  map_add' x y := by
    ext i
    by_cases hi : i = q <;> simp [hi, add_div] <;> ring
  map_smul' a x := by
    ext i
    by_cases hi : i = q <;> simp [hi] <;> ring
  left_inv x := by
    ext i
    by_cases hi : i = q
    · simp [hi]
      field_simp
    · simp [hi]
  right_inv x := by
    ext i
    by_cases hi : i = q <;> simp [hi, hq]

/-- Move a normalized nonzero residual coordinate into the next pivot row. -/
noncomputable def reduceColumn {m : Nat} (c : Fin m → ℝ) (q r : Fin m) (hq : c q ≠ 0) :
    (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) :=
  (clearColumn c q hq).trans (LinearEquiv.funCongrLeft ℝ ℝ (Equiv.swap q r))

theorem clearColumn_self {m : Nat} (c : Fin m → ℝ) (q : Fin m) (hq : c q ≠ 0) :
    clearColumn c q hq c = Pi.single q 1 := by
  ext i
  by_cases hi : i = q <;> simp [clearColumn, Pi.single_apply, hi, hq]

theorem reduceColumn_self {m : Nat} (c : Fin m → ℝ) (q r : Fin m) (hq : c q ≠ 0) :
    reduceColumn c q r hq c = Pi.single r 1 := by
  rw [reduceColumn, LinearEquiv.trans_apply, clearColumn_self]
  ext i
  change (Pi.single q (1 : ℝ) : Fin m → ℝ) ((Equiv.swap q r) i) =
    (Pi.single r (1 : ℝ) : Fin m → ℝ) i
  simp [Pi.single_apply, Equiv.swap_apply_eq_iff]

/-- Earlier pivot-supported columns are fixed by the new row operation. -/
theorem reduceColumn_fixes_prefix {m : Nat} (c : Fin m → ℝ) (q r : Fin m)
    (hq : c q ≠ 0) (hrq : r.val ≤ q.val) (x : Fin m → ℝ)
    (hx : ∀ i : Fin m, r.val ≤ i.val → x i = 0) :
    reduceColumn c q r hq x = x := by
  have hxq := hx q hrq
  have hxr := hx r (Nat.le_refl _)
  ext i
  change (if (Equiv.swap q r) i = q then x q / c q
    else x ((Equiv.swap q r) i) - c ((Equiv.swap q r) i) * (x q / c q)) = x i
  by_cases hiq : i = q
  · subst i
    simp [hxq, hxr]
  · by_cases hir : i = r
    · subst i
      simp [hxq, hxr]
    · rw [Equiv.swap_apply_of_ne_of_ne hiq hir]
      simp [hiq, hxq]

/-- Matrices of an equivalence and its inverse cancel, without determinant reasoning. -/
theorem equivMatrix_mul_inverse {m : Nat} (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) :
    LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' e.symm.toLinearMap = 1 := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
  apply congrArg LinearMap.toMatrix'
  apply LinearMap.ext
  intro x
  exact e.apply_symm_apply x

/-- Append an independent last column after choosing the new pivot row.
The row equivalence is supplied separately; its action is used in factorization. -/
noncomputable def appendIndependent {m n : Nat} (g : RREFDecomposition m n)
    (hr : g.rank < m) (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) :
    RREFDecomposition m (n + 1) where
  rank := g.rank + 1
  rank_le_m := hr
  rank_le_n := Nat.succ_le_succ g.rank_le_n
  R := fun i => Fin.lastCases (if i.val = g.rank then 1 else 0) (g.R i)
  pivots := Fin.lastCases (Fin.last n) (fun q => (g.pivots q).castSucc)
  E := g.E * LinearMap.toMatrix' e.symm.toLinearMap
  E_inv := LinearMap.toMatrix' e.toLinearMap * g.E_inv
  E_left_inv := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc g.E_inv, g.E_left_inv,
      Matrix.diagonal_one, Matrix.one_mul, equivMatrix_mul_inverse]
  pivots_strict_mono := by
    intro i j hij
    induction i using Fin.lastCases with
    | last => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt_succ j.isLt) hij)
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa using (g.pivots i).isLt
      | cast j => simpa using g.pivots_strict_mono i j hij
  pivot_entries_one := by
    intro q
    induction q using Fin.lastCases with
    | last => simp
    | cast q => simpa using g.pivot_entries_one q
  pivot_columns_zero := by
    intro q k hk
    induction q using Fin.lastCases with
    | last => simpa using hk
    | cast q => simpa using g.pivot_columns_zero q k hk
  zero_rows_below := by
    intro i hi j
    induction j using Fin.lastCases with
    | last => simp; omega
    | cast j => simpa using g.zero_rows_below i (by omega) j
  left_of_pivot_zero := by
    intro q j hj
    induction q using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp at hj
      | cast j => simpa using g.zero_rows_below ⟨g.rank, hr⟩ (Nat.le_refl _) j
    | cast q =>
      simp only [Fin.lastCases_castSucc, Fin.val_castSucc] at hj
      induction j using Fin.lastCases with
      | last => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_lt (g.pivots q).isLt) hj)
      | cast j => simpa using g.left_of_pivot_zero q j hj

theorem appendIndependent_factor {m n : Nat}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : RREFDecomposition m n)
    (hr : g.rank < m) (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hprefix : (fun i j => A i j.castSucc) = g.E * g.R)
    (hfix : ∀ j : Fin n, e (fun i => g.R i j) = (fun i => g.R i j))
    (hnew : e (g.E_inv.mulVec (fun i => A i (Fin.last n))) =
      Pi.single ⟨g.rank, hr⟩ 1) :
    A = (g.appendIndependent hr e).E * (g.appendIndependent hr e).R := by
  ext i j
  change A i j = ((g.E * LinearMap.toMatrix' e.symm.toLinearMap).mulVec
    (fun k => Fin.lastCases (if k.val = g.rank then 1 else 0) (g.R k) j)) i
  rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  induction j using Fin.lastCases with
  | cast j =>
      simp only [Fin.lastCases_castSucc]
      have hi : e.symm (fun k => g.R k j) = (fun k => g.R k j) := by
        apply e.injective
        simpa using (hfix j).symm
      change A i j.castSucc = g.E.mulVec (e.symm (fun k => g.R k j)) i
      rw [hi]
      exact congrFun (congrFun hprefix i) j
  | last =>
      simp only [Fin.lastCases_last]
      have hs : (fun k : Fin m => if k.val = g.rank then (1 : ℝ) else 0) =
          Pi.single ⟨g.rank, hr⟩ 1 := by
        ext k
        simp [Pi.single_apply, Fin.ext_iff]
      rw [hs, ← hnew]
      change A i (Fin.last n) = g.E.mulVec
        (e.symm (e (g.E_inv.mulVec (fun k => A k (Fin.last n))))) i
      rw [e.symm_apply_apply, Matrix.mulVec_mulVec, g.right_inv, Matrix.one_mulVec]

/-- The independent-column successor case, constructed from a nonzero tail entry. -/
theorem exists_append_of_tail_nonzero {m n : Nat}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : RREFDecomposition m n)
    (hprefix : (fun i j => A i j.castSucc) = g.E * g.R)
    (q : Fin m) (hrq : g.rank ≤ q.val)
    (hq : (g.E_inv.mulVec (fun k => A k (Fin.last n))) q ≠ 0) :
    ∃ d : RREFDecomposition m (n + 1), A = d.E * d.R := by
  let c := g.E_inv.mulVec (fun k => A k (Fin.last n))
  have hr : g.rank < m := Nat.lt_of_le_of_lt hrq q.isLt
  let r : Fin m := ⟨g.rank, hr⟩
  let e := reduceColumn c q r hq
  refine ⟨g.appendIndependent hr e, g.appendIndependent_factor A hr e hprefix ?_ ?_⟩
  · intro j
    exact reduceColumn_fixes_prefix c q r hq hrq (fun i => g.R i j)
      (fun i hi => g.zero_rows_below i hi j)
  · exact reduceColumn_self c q r hq

/-- Complete constructive successor step: either the new reduced column has
zero tail, or a nonzero tail coordinate supplies the next pivot. -/
theorem exists_append {m n : Nat}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (g : RREFDecomposition m n)
    (hprefix : (fun i j => A i j.castSucc) = g.E * g.R) :
    ∃ d : RREFDecomposition m (n + 1), A = d.E * d.R := by
  classical
  by_cases hz : ∀ i : Fin m, g.rank ≤ i.val →
      (g.E_inv.mulVec (fun k => A k (Fin.last n))) i = 0
  · exact g.exists_append_of_tail_zero A hprefix hz
  · push Not at hz
    obtain ⟨q, hrq, hq⟩ := hz
    exact g.exists_append_of_tail_nonzero A hprefix q hrq hq

end RREFDecomposition

/-- A proved replacement for the existing RREF successor-step boundary.
The statement is identical, and its proof uses no decomposition-existence axiom. -/
theorem Matrix.exists_rrefDecomp_inductive_step_proved {m n : Nat}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (ih : ∀ B : Matrix (Fin m) (Fin n) ℝ,
      ∃ g : RREFDecomposition m n, B = g.E * g.R) :
    ∃ g : RREFDecomposition m (n + 1), A = g.E * g.R := by
  obtain ⟨g, hg⟩ := ih (fun i j => A i j.castSucc)
  exact g.exists_append A hg

end GLang
