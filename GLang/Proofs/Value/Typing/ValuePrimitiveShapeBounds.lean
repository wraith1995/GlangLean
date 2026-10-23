import GLang.Value.ShapeConditions

/-! Every input access used by the guarded finite-array primitives is in bounds. -/

namespace GLang.ValueShape

/-- Every flattened product index decodes to two valid factor indices,
including the vacuous case in which either factor has dimension zero. -/
theorem product_indices {m n i : Nat} (hi : i < m * n) :
    i / n < m ∧ i % n < n := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    simp_all
  exact ⟨(Nat.div_lt_iff_lt_mul hn).2 hi, Nat.mod_lt _ hn⟩

theorem row_index {m n i j : Nat} (hi : i < m) (hj : j < n) :
    n * i + j < m * n := by nlinarith

/-- Transposition only reads stored coordinates. -/
theorem transpose_index {m n i : Nat} (hi : i < n * m) :
    n * (i % m) + i / m < m * n :=
  row_index (product_indices hi).2 (product_indices hi).1

/-- The two direct-sum branches only read their respective summands. -/
theorem sum_indices {m n i : Nat} (hi : i < m + n) :
    (i < m → i < m) ∧ (¬ i < m → i - m < n) := by omega

/-- The four-factor Kronecker permutation preserves all operand bounds. -/
theorem kronecker_indices {m n p q i : Nat} (hi : i < (m * n) * (p * q)) :
    p * ((i / (p * q)) / n) + (i % (p * q)) / q < m * p ∧
      q * ((i / (p * q)) % n) + (i % (p * q)) % q < n * q := by
  obtain ⟨hleft, hright⟩ := product_indices hi
  obtain ⟨hi0, hi1⟩ := product_indices hleft
  obtain ⟨hj0, hj1⟩ := product_indices hright
  exact ⟨row_index hi0 hj0, row_index hi1 hj1⟩

/-- A successful family guard makes the fallback of optional list lookup
unreachable on the active range and validates every summand coordinate. -/
theorem family_lookup {count width : Nat} {arrays : List FlatArray}
    (h : family count width arrays) {i j : Nat} (hi : i < count) (hj : j < width) :
    ∃ a, arrays[i]? = some a ∧ j < a.length := by
  have hi' : i < arrays.length := by rw [h.1]; exact hi
  refine ⟨arrays[i], ?_, ?_⟩
  · exact List.getElem?_eq_getElem hi'
  · rw [h.2 _ (List.getElem_mem hi')]
    exact hj

theorem scale_access {q : FFSOracle} {s : ValSpace} {a b : FlatArray}
    (h : scale q s a b) {i : Nat} (hi : i < ValSpace.dof q s) :
    0 < a.length ∧ i < b.length := by
  rw [h.1, h.2]
  exact ⟨by omega, hi⟩

theorem pair_product_access {q : FFSOracle} {s t : ValSpace} {a b : FlatArray}
    (h : pair q s t a b) {i : Nat}
    (hi : i < ValSpace.dof q s * ValSpace.dof q t) :
    i / ValSpace.dof q t < a.length ∧ i % ValSpace.dof q t < b.length := by
  rw [h.1, h.2]
  exact product_indices hi

theorem tensor_transpose_access {q : FFSOracle} {s t : ValSpace} {a : FlatArray}
    (h : tensor q (.tprod s t) a) {i : Nat}
    (hi : i < ValSpace.dof q t * ValSpace.dof q s) :
    ValSpace.dof q t * (i % ValSpace.dof q s) + i / ValSpace.dof q s < a.length := by
  rw [h]
  exact transpose_index hi

theorem ttv_tensor_access {q : FFSOracle} {c domain out rhs : ValSpace}
    {a b : FlatArray} (h : ttv q c (.tprod domain out) rhs a b)
    {i j : Nat} (hi : i < ValSpace.dof q out) (hj : j < ValSpace.dof q c) :
    ValSpace.dof q out * j + i < a.length ∧ j < b.length := by
  have hd := h.2.1
  have hr := h.2.2
  rw [h.1.1, h.1.2, ValSpace.dof_tprod, hd, hr]
  exact ⟨row_index hj hi, hj⟩

theorem mtm_access {q : FFSOracle} {c leftMiddle out source rightMiddle : ValSpace}
    {a b : FlatArray}
    (h : mtm q c (.tprod leftMiddle out) (.tprod source rightMiddle) a b)
    {i j k : Nat} (hi : i < ValSpace.dof q source)
    (hj : j < ValSpace.dof q out) (hk : k < ValSpace.dof q c) :
    ValSpace.dof q out * k + j < a.length ∧
      ValSpace.dof q c * i + k < b.length := by
  have hl : a.length = ValSpace.dof q leftMiddle * ValSpace.dof q out := h.1.1
  have hr : b.length = ValSpace.dof q source * ValSpace.dof q rightMiddle := h.1.2
  rw [hl, hr, h.2.1, h.2.2]
  exact ⟨row_index hk hj, row_index hi hk⟩

/-- The diagonal blocks read valid coordinates; off-diagonal blocks are
literal mathematical zeros and never read either input. -/
theorem block_indices {m n p q i : Nat} (hi : i < (m + n) * (p + q)) :
    (i / (p + q) < m → i % (p + q) < p →
      p * (i / (p + q)) + i % (p + q) < m * p) ∧
    (¬ i / (p + q) < m → ¬ i % (p + q) < p →
      q * (i / (p + q) - m) + (i % (p + q) - p) < n * q) := by
  refine ⟨fun hr hc => row_index hr hc, ?_⟩
  intro hr hc
  obtain ⟨hrow, hcol⟩ := product_indices hi
  exact row_index (by omega) (by omega)

theorem pair_sum_access {q : FFSOracle} {s t : ValSpace} {a b : FlatArray}
    (h : pair q s t a b) {i : Nat}
    (hi : i < ValSpace.dof q s + ValSpace.dof q t) :
    (i < ValSpace.dof q s → i < a.length) ∧
      (¬ i < ValSpace.dof q s → i - ValSpace.dof q s < b.length) := by
  rw [h.1, h.2]
  exact sum_indices hi

theorem ttv_scalar_access {q : FFSOracle} {c s t : ValSpace} {a b : FlatArray}
    (h : pair q s t a b) (hs : ValSpace.dof q s = ValSpace.dof q c)
    (ht : ValSpace.dof q t = ValSpace.dof q c) {j : Nat}
    (hj : j < ValSpace.dof q c) : j < a.length ∧ j < b.length := by
  rw [h.1, h.2, hs, ht]
  exact ⟨hj, hj⟩

theorem kronecker_access {q : FFSOracle} {s0 s1 t0 t1 : ValSpace}
    {a b : FlatArray} (h : matrices q (.tprod s0 s1) (.tprod t0 t1) a b)
    {i : Nat}
    (hi : i < (ValSpace.dof q s0 * ValSpace.dof q t0) *
      (ValSpace.dof q s1 * ValSpace.dof q t1)) :
    ValSpace.dof q s1 * ((i / (ValSpace.dof q s1 * ValSpace.dof q t1)) /
      ValSpace.dof q t0) + (i % (ValSpace.dof q s1 * ValSpace.dof q t1)) /
      ValSpace.dof q t1 < a.length ∧
    ValSpace.dof q t1 * ((i / (ValSpace.dof q s1 * ValSpace.dof q t1)) %
      ValSpace.dof q t0) + (i % (ValSpace.dof q s1 * ValSpace.dof q t1)) %
      ValSpace.dof q t1 < b.length := by
  rw [h.1, h.2]
  exact kronecker_indices hi

end GLang.ValueShape
