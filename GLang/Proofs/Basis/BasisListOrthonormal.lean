import GLang.Annotated.Denotation

/-! Pure list orthonormality, independent of FSV realization. -/
namespace GLang.BasisFSV

/-- **Key concatenation lemma.** Concatenation of two orthonormal lists
    whose vectors come from mutually orthogonal subspaces is orthonormal. -/
theorem concat_orthonormal (V : HSpace)
    (L₁ L₂ : List V.carrier)
    (h₁ : ∀ i j : Fin L₁.length,
            V.innerProduct (L₁.get i) (L₁.get j) = if i = j then 1 else 0)
    (h₂ : ∀ i j : Fin L₂.length,
            V.innerProduct (L₂.get i) (L₂.get j) = if i = j then 1 else 0)
    (h_cross : ∀ (i : Fin L₁.length) (j : Fin L₂.length),
                V.innerProduct (L₁.get i) (L₂.get j) = 0) :
    ∀ i j : Fin (L₁ ++ L₂).length,
      V.innerProduct ((L₁ ++ L₂).get i) ((L₁ ++ L₂).get j) =
        if i = j then 1 else 0 := by
  intro i j
  have hlen : (L₁ ++ L₂).length = L₁.length + L₂.length := by simp
  -- Case split on which side i and j lie in.
  rcases Nat.lt_or_ge i.1 L₁.length with hi | hi
  · rcases Nat.lt_or_ge j.1 L₁.length with hj | hj
    · -- both in L₁.
      have hgi : (L₁ ++ L₂).get i = L₁.get ⟨i.1, hi⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_left hi]
      have hgj : (L₁ ++ L₂).get j = L₁.get ⟨j.1, hj⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_left hj]
      rw [hgi, hgj, h₁]
      by_cases h_eq : i = j
      · have h_eq' : (⟨i.1, hi⟩ : Fin L₁.length) = ⟨j.1, hj⟩ := by
          apply Fin.ext
          show i.1 = j.1
          exact Fin.val_eq_of_eq h_eq
        rw [if_pos h_eq, if_pos h_eq']
      · have h_neq' : (⟨i.1, hi⟩ : Fin L₁.length) ≠ ⟨j.1, hj⟩ := by
          intro h
          apply h_eq
          apply Fin.ext
          show i.1 = j.1
          have : (⟨i.1, hi⟩ : Fin L₁.length).val = (⟨j.1, hj⟩ : Fin L₁.length).val :=
            Fin.val_eq_of_eq h
          exact this
        rw [if_neg h_eq, if_neg h_neq']
    · -- i in L₁, j in L₂.
      have hj' : j.1 - L₁.length < L₂.length := by
        have : j.1 < L₁.length + L₂.length := by rw [← hlen]; exact j.isLt
        omega
      have hgi : (L₁ ++ L₂).get i = L₁.get ⟨i.1, hi⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_left hi]
      have hgj : (L₁ ++ L₂).get j = L₂.get ⟨j.1 - L₁.length, hj'⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_right hj]
      rw [hgi, hgj, h_cross]
      have h_neq : i ≠ j := by
        intro heq
        have : i.1 = j.1 := Fin.val_eq_of_eq heq
        omega
      rw [if_neg h_neq]
  · rcases Nat.lt_or_ge j.1 L₁.length with hj | hj
    · -- i in L₂, j in L₁.
      have hi' : i.1 - L₁.length < L₂.length := by
        have : i.1 < L₁.length + L₂.length := by rw [← hlen]; exact i.isLt
        omega
      have hgi : (L₁ ++ L₂).get i = L₂.get ⟨i.1 - L₁.length, hi'⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_right hi]
      have hgj : (L₁ ++ L₂).get j = L₁.get ⟨j.1, hj⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_left hj]
      rw [hgi, hgj]
      rw [V.innerIsIP.1, h_cross]
      have h_neq : i ≠ j := by
        intro heq
        have : i.1 = j.1 := Fin.val_eq_of_eq heq
        omega
      rw [if_neg h_neq]
    · -- both in L₂.
      have hi' : i.1 - L₁.length < L₂.length := by
        have : i.1 < L₁.length + L₂.length := by rw [← hlen]; exact i.isLt
        omega
      have hj' : j.1 - L₁.length < L₂.length := by
        have : j.1 < L₁.length + L₂.length := by rw [← hlen]; exact j.isLt
        omega
      have hgi : (L₁ ++ L₂).get i = L₂.get ⟨i.1 - L₁.length, hi'⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_right hi]
      have hgj : (L₁ ++ L₂).get j = L₂.get ⟨j.1 - L₁.length, hj'⟩ := by
        rw [List.get_eq_getElem, List.get_eq_getElem,
            List.getElem_append_right hj]
      rw [hgi, hgj, h₂]
      by_cases h_eq : i = j
      · have h_eq' :
            (⟨i.1 - L₁.length, hi'⟩ : Fin L₂.length) = ⟨j.1 - L₁.length, hj'⟩ := by
          apply Fin.ext
          show i.1 - L₁.length = j.1 - L₁.length
          have : i.1 = j.1 := Fin.val_eq_of_eq h_eq
          omega
        rw [if_pos h_eq, if_pos h_eq']
      · have h_neq' :
            (⟨i.1 - L₁.length, hi'⟩ : Fin L₂.length) ≠ ⟨j.1 - L₁.length, hj'⟩ := by
          intro h
          apply h_eq
          apply Fin.ext
          show i.1 = j.1
          have hh : (⟨i.1 - L₁.length, hi'⟩ : Fin L₂.length).val =
                    (⟨j.1 - L₁.length, hj'⟩ : Fin L₂.length).val :=
            Fin.val_eq_of_eq h
          show i.1 = j.1
          have : i.1 - L₁.length = j.1 - L₁.length := hh
          omega
        rw [if_neg h_eq, if_neg h_neq']

/-- Vacuous orthonormality: every pair in the empty list satisfies the
    Kronecker-delta. -/
theorem nil_orthonormal (V : HSpace) :
    ∀ i j : Fin ([] : List V.carrier).length,
      V.innerProduct (([] : List V.carrier).get i) (([] : List V.carrier).get j) =
        if i = j then 1 else 0 := by
  intro i j
  exact absurd i.isLt (by simp)

end GLang.BasisFSV
