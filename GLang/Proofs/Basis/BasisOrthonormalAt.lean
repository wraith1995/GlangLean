import GLang.Proofs.Source.BasisSoundness
import GLang.Proofs.Progress.Supporting.ProgressStdBasis

/-!
# Recursive orthonormality of standard basis denotations

`BasisDenot.RecursiveOrthonormal` follows the complete semantic basis tree:
vector leaves have identity Gram matrix, while frames require an orthonormal
stored domain basis and orthonormality of every semantic fiber.  This module
proves that every valid syntactically-standard basis has that property.

The proof needs no well-formed-context or environment premise.  `BasisValid`
supplies the cofinite validity fact for a frame body, and denotational
fresh-name irrelevance lets the proof use the same fresh opening for every
fiber.  Expected-type alignment and spanning are deliberately separate and
are supplied by the basis-soundness (`BasisAt`) theorem when the headline
result packages the two facts.
-/

namespace GLang

/-- Opening changes only embedded syntax, so it preserves the structural
`isStd` recognizer.  The binder arm recurses at `k + 1`. -/
theorem Basis.isStd_openRec (x : Name) : ∀ (b : Basis) (k : Nat),
    Basis.isStd (Basis.openRec k (.var x) b) = Basis.isStd b
  | .empty, _ => rfl
  | .one, _ => rfl
  | .dual b, k => by
      simp only [Basis.openRec, Basis.isStd, Basis.isStd_openRec x b k]
  | .dsum b₀ b₁, k => by
      simp only [Basis.openRec, Basis.isStd, Basis.isStd_openRec x b₀ k,
        Basis.isStd_openRec x b₁ k]
  | .tprod b₀ b₁, k => by
      simp only [Basis.openRec, Basis.isStd, Basis.isStd_openRec x b₀ k,
        Basis.isStd_openRec x b₁ k]
  | .proj s b₀ b₁, k => by
      simp only [Basis.openRec, Basis.isStd, Basis.isStd_openRec x b₀ k,
        Basis.isStd_openRec x b₁ k]
  | .image _, _ => rfl
  | .terms _ _ _, _ => rfl
  | .frame b₀ b₁, k => by
      simp only [Basis.openRec, Basis.isStd, Basis.isStd_openRec x b₀ k,
        Basis.isStd_openRec x b₁ (k + 1)]

/-- Opening at a free name preserves the structural `isStd` recognizer. -/
theorem Basis.isStd_openVar (x : Name) (b : Basis) :
    Basis.isStd (Basis.openVar x b) = Basis.isStd b :=
  Basis.isStd_openRec x b 0

/-- A valid, syntactically-standard non-frame denotes an exact vector leaf at
its source space.  This small dependent-shape bridge converts the established
`atSpace` orthonormality theorem into the stored-HSpace clause of
`RecursiveOrthonormal`. -/
private theorem denotBasis_eq_vecs_of_not_frame (sigma : DEnv) (epsilon : NLCtx)
    (b : Basis) (hb : Basis.BasisValid epsilon b)
    (hstd : Basis.isStd b)
    (hnf : ∀ b₀ b₁, b ≠ .frame b₀ b₁) :
    ∃ vs : List (denotSpace sigma (Basis.sof b)).carrier,
      denotBasis sigma b = .vecs (denotSpace sigma (Basis.sof b)) vs := by
  cases b with
  | empty =>
      simp only [denotBasis, Basis.sof, denotSpaceAux]
      exact ⟨[], rfl⟩
  | one =>
      simp only [denotBasis, Basis.sof, denotSpaceAux]
      exact ⟨[(1 : ℝ)], rfl⟩
  | dual _ =>
      simp only [denotBasis, Basis.sof, denotSpace, denotSpaceAux]
      exact ⟨_, rfl⟩
  | dsum _ _ =>
      simp only [denotBasis, Basis.sof, denotSpace, denotSpaceAux]
      exact ⟨_, rfl⟩
  | tprod _ _ =>
      simp only [denotBasis, Basis.sof, denotSpace, denotSpaceAux]
      exact ⟨_, rfl⟩
  | proj s _ _ =>
      cases s with
      | empty | real | dual | dsum | tprod => cases hb
      | ker | coker | img | coimg =>
          simp only [denotBasis, Basis.sof, denotSpace, denotSpaceAux]
          exact ⟨_, rfl⟩
  | image _ => exact False.elim hstd
  | terms _ _ _ => exact False.elim hstd
  | frame b₀ b₁ => exact False.elim (hnf b₀ b₁ rfl)

/-- Every valid syntactically-standard basis denotes a recursively
orthonormal semantic basis.  The frame case checks both the domain basis and
every fiber, recursively through arbitrarily nested dependent frames. -/
theorem denotBasis_recursiveOrthonormal_of_isStd (sigma : DEnv) (epsilon : NLCtx)
    (b : Basis) (hb : Basis.BasisValid epsilon b) (hstd : Basis.isStd b) :
    (denotBasis sigma b).RecursiveOrthonormal := by
  cases b with
  | empty | one | dual | dsum | tprod | proj =>
      obtain ⟨vs, hden⟩ := denotBasis_eq_vecs_of_not_frame sigma epsilon _ hb hstd
        (by intros; exact Basis.noConfusion)
      have horth := denotBasis_orthonormal_of_isStd sigma epsilon _ hb hstd
      rw [hden] at horth ⊢
      dsimp only at horth
      have hat := BasisDenot.atSpace_vecs_self
        (denotSpace sigma (Basis.sof _)) vs
      rw [hat] at horth
      simpa only [BasisDenot.RecursiveOrthonormal] using horth
  | image => exact False.elim hstd
  | terms => exact False.elim hstd
  | frame b₀ b₁ =>
      obtain ⟨hb₀, ⟨L, hbody⟩, _, _, _⟩ := hb.frame_inv
      obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (L ∪ Basis.fv b₁)
      simp only [Finset.mem_union, not_or] at hz
      rcases hz with ⟨hzL, hzb₁⟩
      simp only [denotBasis, BasisDenot.RecursiveOrthonormal]
      constructor
      · exact denotBasis_recursiveOrthonormal_of_isStd sigma epsilon b₀ hb₀ hstd.1
      · intro y
        rw [denotBasisOpenIrrel sigma b₁ (Basis.freshFor b₁) z
          ((denotTy sigma (Basis.tof b₀)).embed y) (Basis.freshFor_spec b₁) hzb₁]
        exact denotBasis_recursiveOrthonormal_of_isStd
          (sigma.bind z ((denotTy sigma (Basis.tof b₀)).embed y))
          (Finmap.insert z (Basis.tof b₀) epsilon) (Basis.openVar z b₁)
          (hbody z hzL) ((Basis.isStd_openVar z b₁).symm ▸ hstd.2)
termination_by Basis.size b
decreasing_by
  all_goals simp_all [Basis.size, Basis.openVar, Basis.size_openVar] <;> omega

theorem stdBasis_orthonormal (sigma : DEnv) (epsilon : NLCtx) (tau : Ty)
    {k : Kind} (htau : TValid epsilon tau k) :
    (denotBasis sigma (Basis.std tau)).RecursiveOrthonormal :=
  denotBasis_recursiveOrthonormal_of_isStd sigma epsilon (Basis.std tau)
    (Basis.std_valid tau htau) (Basis.isStd_std tau)

end GLang
