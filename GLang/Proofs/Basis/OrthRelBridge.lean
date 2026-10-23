

import GLang.Annotated.Denotation

namespace GLang

open scoped TensorProduct

namespace Submodule

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- Membership in `Submodule.orthRel B K` unfolds to `∀ u ∈ K, B v u = 0`.

    This is essentially `Submodule.mem_comap` + `Submodule.mem_dualAnnihilator`.
    Used as the bridge to Mathlib's `Submodule.mem_orthogonal` under any
    `InnerProductSpace` whose inner agrees with `B`. -/
theorem mem_orthRel_iff (K : Submodule ℝ V) (v : V) :
    v ∈ Submodule.orthRel B K ↔ ∀ u ∈ K, B v u = 0 := by
  unfold Submodule.orthRel
  rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]

/-- If `B` is symmetric, `v ∈ orthRel B K` iff `∀ u ∈ K, B u v = 0`. -/
theorem mem_orthRel_iff_symm {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (hsym : ∀ x y, B x y = B y x) (K : Submodule ℝ V) (v : V) :
    v ∈ Submodule.orthRel B K ↔ ∀ u ∈ K, B u v = 0 := by
  rw [mem_orthRel_iff]
  constructor <;> intro h u hu <;> have := h u hu
  · rw [hsym v u] at this; exact this
  · rw [hsym u v] at this; exact this

end Submodule

/-! ## HSpace-level bridge: `Submodule.orthRel V.innerProduct` membership.

These specialise the `Submodule` lemmas above to an `HSpace V`. They're the
form actually used by callers — the `B = V.innerProduct` and `B` is symmetric
+ PD by `V.innerIsIP`. -/

namespace HSpace

/-- For an `HSpace V`, membership in `Submodule.orthRel V.innerProduct K`
    is `∀ u ∈ K, V.innerProduct u v = 0`. (Equivalently by symmetry,
    `V.innerProduct v u = 0`.) -/
theorem mem_orthRel_innerProduct_iff (V : HSpace)
    (K : Submodule ℝ V.carrier) (v : V.carrier) :
    v ∈ Submodule.orthRel V.innerProduct K ↔
      ∀ u ∈ K, V.innerProduct u v = 0 :=
  Submodule.mem_orthRel_iff_symm V.innerIsIP.1 K v

/-- The non-symmetric form of `mem_orthRel_innerProduct_iff`:
    `v ∈ orthRel ↔ ∀ u ∈ K, V.innerProduct v u = 0`. -/
theorem mem_orthRel_innerProduct_iff' (V : HSpace)
    (K : Submodule ℝ V.carrier) (v : V.carrier) :
    v ∈ Submodule.orthRel V.innerProduct K ↔
      ∀ u ∈ K, V.innerProduct v u = 0 :=
  Submodule.mem_orthRel_iff V.innerProduct K v

/-- **PD direct corollary**: if `v ∈ orthRel V.IP K` and `v ∈ K`, then `v = 0`.

    Proof: instantiate `mem_orthRel_innerProduct_iff` at `u := v` to get
    `V.innerProduct v v = 0`, then PD (`V.innerIsIP.2.2`). This is the
    fact (a) (injectivity of `f` restricted to `(ker f)⊥_orthRel`) needed
    by the `.image` case of `denotBasis_isBasis`. -/
theorem zero_of_mem_orthRel_inter (V : HSpace)
    (K : Submodule ℝ V.carrier) (v : V.carrier)
    (h_orth : v ∈ Submodule.orthRel V.innerProduct K) (h_mem : v ∈ K) :
    v = 0 := by
  have h_self : V.innerProduct v v = 0 := by
    rw [mem_orthRel_innerProduct_iff'] at h_orth
    exact h_orth v h_mem
  exact V.innerIsIP.2.2 v h_self

/-! ## `IsCompl` decomposition for `orthRel`.

The `.image` case of `denotBasis_isBasis` needs `IsCompl (orthRel V.IP K) K`
for `K := ker f` — i.e. `V₀.carrier = (orthRel V₀.IP (ker f)) ⊕ ker f` —
so that every `x ∈ V₀` decomposes as `x_orth + x_ker`. Mathlib provides
the analogous fact `Submodule.isCompl_orthogonal_of_hasOrthogonalProjection`
for `Kᗮ` under an `InnerProductSpace` instance; we transport that statement
by showing the two submodules agree pointwise via `mem_orthRel_iff_symm`. -/

/-- **PD-IP corollary**: in an HSpace, `orthRel V.IP K ⊓ K = ⊥`.

    Direct from `zero_of_mem_orthRel_inter`: any `v` in both submodules is
    `0`, so the meet contains only `0`.

    This is fact (a) (injectivity-as-trivial-intersection-with-ker) in the
    form used by `IsCompl`'s `disjoint` field. -/
theorem orthRel_inf_eq_bot (V : HSpace) (K : Submodule ℝ V.carrier) :
    Submodule.orthRel V.innerProduct K ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨h_orth, h_mem⟩ := hv
  rw [Submodule.mem_bot]
  exact zero_of_mem_orthRel_inter V K v h_orth h_mem

end HSpace

end GLang
