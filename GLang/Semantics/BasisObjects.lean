import GLang.Proofs.Basis.Validity
import GLang.Annotated.Denotation
import GLang.Numerics.Spectral.BasisFSV
import GLang.Numerics.RREF.BasisLexInd

/-! Ordered vector lists, dependent frames, and mathematical basis operations. -/
namespace GLang

inductive BasisDenot : Type 1
  /-- A finite indexed sequence of vectors at carrier of `V`. -/
  | vecs : (V : HSpace) → List V.carrier → BasisDenot

  | frame : (T : Type) → (domB : BasisDenot) → (T → BasisDenot) → BasisDenot

noncomputable def BasisDenot.default : BasisDenot :=
  .vecs HSpace.empty []

/-- The DOMAIN basis of a frame (`⟦b₀⟧σ`); `default` on a non-frame (a shape
    mismatch that never occurs on well-typed Π-bases). Backs `LegacyAgree`'s
    Skolemized Π-clause (the retired `AgreeFramePin` witness). -/
noncomputable def BasisDenot.domainBasis : BasisDenot → BasisDenot
  | .frame _ domB _ => domB
  | .vecs _ _ => .default

noncomputable instance : Inhabited BasisDenot := ⟨BasisDenot.default⟩

/-! ## Helpers for `denotBasis`.

These factor the dependent-shape arithmetic (extracting a `List V.carrier`
from a `BasisDenot` at an expected `HSpace V`, building dual / direct-sum
/ tensor-product vectors from sub-basis vectors) out of the main
recursion, so `denotBasis` itself can be written compactly. -/

/-- Extract the `List V.carrier` from a `BasisDenot` at an expected
    `HSpace V`. Falls back to `[]` on shape mismatch:
      * `.frame` doesn't unwrap to a list — return `[]`.
      * `.vecs V'` with `V'.carrier ≠ V.carrier` — return `[]`.

    The shape-mismatch case is a denotation-time guard: well-typed bases
    will never trigger it (soundness lemma will state that
    `denotBasis σ b` is `.vecs (denotSpace σ (sof b)) _` on well-typed
    inputs). -/
noncomputable def BasisDenot.atSpace (V : HSpace) : BasisDenot → List V.carrier
  | .vecs V' vs =>
      haveI := Classical.dec (V'.carrier = V.carrier)
      if h : V'.carrier = V.carrier then vs.map (h ▸ ·) else []
  | .frame _ _ _ => []

/-- The "Riesz musical dual" of a vector `v : V` — the linear functional
    `⟨v, ·⟩ : V →ₗ ℝ` (`V.innerProduct v`). For an orthonormal basis
    this gives the dual basis directly; for non-orthonormal bases the
    Gram matrix mediates (see `dualOfList`). -/
noncomputable def HSpace.flat (V : HSpace) (v : V.carrier) : V.carrier →ₗ[ℝ] ℝ :=
  V.innerProduct v

noncomputable def HSpace.dualOfList (V : HSpace) (vs : List V.carrier) :
    List (HSpace.dual V).carrier :=
  let n := vs.length
  let v : Fin n → V.carrier := fun i => vs.get i
  let G : Matrix (Fin n) (Fin n) ℝ := fun i j => V.innerProduct (v i) (v j)
  let Ginv : Matrix (Fin n) (Fin n) ℝ := G⁻¹
  (List.finRange n).map fun i =>
    (∑ k : Fin n, Ginv i k • V.innerProduct (v k) : V.carrier →ₗ[ℝ] ℝ)

/-- Direct-sum embedding of two basis lists into the `HSpace.dsum V₀ V₁`
    carrier `V₀.carrier × V₁.carrier`. Uses `LinearMap.inl` / `LinearMap.inr`
    (i.e. `(v, 0)` and `(0, w)`); the result is the concatenation. -/
noncomputable def HSpace.dsumOfLists (V₀ V₁ : HSpace)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    List (HSpace.dsum V₀ V₁).carrier :=
  vs₀.map (LinearMap.inl ℝ V₀.carrier V₁.carrier) ++
  vs₁.map (LinearMap.inr ℝ V₀.carrier V₁.carrier)

/-- Tensor-product Kronecker pairing of two basis lists: every
    `v ⊗ₜ w` for `v ∈ vs₀`, `w ∈ vs₁`. -/
noncomputable def HSpace.tprodOfLists (V₀ V₁ : HSpace)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    List (HSpace.tprod V₀ V₁).carrier :=
  let mk : V₀.carrier → V₁.carrier → TensorProduct ℝ V₀.carrier V₁.carrier :=
    fun v w => v ⊗ₜ[ℝ] w
  vs₀.flatMap fun v => vs₁.map (mk v)

/-- Lift each `v ∈ vs` into the subtype of submodule `K`. For elements
    that happen to lie in `K`, return the genuine subtype element
    `⟨v, _⟩`; otherwise drop them (filterMap). This is the bridge from
    `List V.carrier` (what `BasisFSV.fsv{Left,Right}` returns) to
    `List K` (the carrier of `HSpace.ofSubmodule V K`).

    On the FSV-soundness path, every element of `vs` IS in `K` by the
    obligation theorems in `BasisFSV.lean`, so this is the identity-on-
    underlying-vectors. Off-path the dropped elements are an acceptable
    over-conservatism (we'd already be on the ill-typed `_ => .empty`
    fallback by the same argument). -/
noncomputable def HSpace.liftToSubmodule {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Submodule ℝ V) (vs : List V) : List K :=
  vs.filterMap fun v =>
    haveI := Classical.dec (v ∈ K)
    if h : v ∈ K then some ⟨v, h⟩ else none

/-- A canonical fresh name avoiding `Basis.fv b` — used by `denotBasis`'s
    `.frame` arm to open the nameless frame body. `Classical.choice`-extracted
    from `Infinite.exists_notMem_finset`. -/
noncomputable def Basis.freshFor (b : Basis) : Name :=
  (Infinite.exists_notMem_finset (Basis.fv b)).choose

theorem Basis.freshFor_spec (b : Basis) : Basis.freshFor b ∉ Basis.fv b :=
  (Infinite.exists_notMem_finset (Basis.fv b)).choose_spec

end GLang
