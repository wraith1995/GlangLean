

import GLang.Proofs.Basis.Binding
import GLang.Proofs.Source.Wellformed
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import GLang.Proofs.Basis.OrthRelBridge
import GLang.Numerics.Spectral.BasisFSVGSVD

open scoped TensorProduct Matrix

namespace GLang

/-! ## Easy `IsListBasis` cases (used in the main theorem in BasisSoundnessTodo). -/

/-- `[] : List HSpace.empty.carrier` is a basis of the trivial space. -/
theorem isListBasis_empty : IsListBasis HSpace.empty [] := by
  refine ⟨?_, ?_⟩
  · -- LinearIndependent over `Fin 0 → PUnit` (the empty index): vacuously true.
    -- `Fin [].length = Fin 0` has no inhabitants.
    have : IsEmpty (Fin ([] : List HSpace.empty.carrier).length) := by
      simp only [List.length_nil]; exact Fin.isEmpty'
    exact linearIndependent_empty_type
  · -- The range of `Fin 0 → PUnit` is empty, so `span ℝ ∅ = ⊥`. Then `⊥ = ⊤`
    -- in the trivial module `PUnit`.
    apply Submodule.eq_top_iff'.mpr
    intro x
    -- x : PUnit, so x = 0 = ⟨⟩.
    have hx : x = 0 := Subsingleton.elim x 0
    rw [hx]
    exact Submodule.zero_mem _

/-- `[1] : List ℝ` is a basis of `ℝ` as an `ℝ`-module. -/
theorem isListBasis_one : IsListBasis HSpace.real [(1 : ℝ)] := by
  refine ⟨?_, ?_⟩
  · -- `Fin 1 → ℝ`, sending `0 ↦ 1`. Linear independence: `c • 1 = 0 → c = 0`.
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    -- g : Fin 1 → ℝ with ∑ i, g i • (vs.get i) = 0.
    -- vs = [1], so vs.get 0 = 1; sum reduces to g 0 • 1 = 0, hence g 0 = 0.
    fin_cases i
    -- Goal: g 0 = 0. After simp, `hg` directly gives `g 0 = 0`.
    have := hg
    simp at this
    exact this
  · -- span ℝ (range of (fun i : Fin 1 => [1].get i)) = ⊤ in ℝ.
    apply Submodule.eq_top_iff'.mpr
    intro r
    -- The range is `{1}`; show `1 ∈ span ℝ {1}` then `r • 1 ∈ span` since `r • 1 = r`.
    have h1_in_range : (1 : ℝ) ∈ Set.range (fun i : Fin [(1 : ℝ)].length => [(1 : ℝ)].get i) := by
      refine ⟨⟨0, by simp⟩, ?_⟩
      rfl
    have : (1 : ℝ) ∈ Submodule.span ℝ
        (Set.range (fun i : Fin [(1 : ℝ)].length => [(1 : ℝ)].get i)) :=
      Submodule.subset_span h1_in_range
    have hr : r = r • (1 : ℝ) := by simp
    rw [hr]
    exact Submodule.smul_mem _ r this

inductive ExpectedSpace : Type 1
  /-- A single HSpace expectation — matches `BasisDenot.vecs`. -/
  | vecs (V : HSpace) : ExpectedSpace
  /-- A per-fiber HSpace expectation — matches `BasisDenot.frame`.
      `T` must match the `BasisDenot.frame`'s `T` for the predicate
      to be applicable. -/
  | frame (T : Type) (f : T → ExpectedSpace) : ExpectedSpace

/-- Forget the vectors in a basis denotation while retaining its complete recursive
vector/frame space shape. This is the semantic normal form used to compare the canonical
`ExpectedSpace.ofBasis` construction across locally-nameless choices of opening name. -/
noncomputable def ExpectedSpace.ofDenot : BasisDenot → ExpectedSpace
  | .vecs V _ => .vecs V
  | .frame T _ f => .frame T (fun y => ExpectedSpace.ofDenot (f y))

/-- `SoundOfDenot E d` — the denotation `d : BasisDenot` is sound at
    the expected `E : ExpectedSpace`. -/
def SoundOfDenot : ExpectedSpace → BasisDenot → Prop
  | .vecs V, .vecs V' vs =>
      -- Require HSpace equality (not merely carrier) so the predicate
      -- pins down the inner-product structure too; this matches
      -- `EnvWF`'s deep `matchesShape`.
      ∃ h : V' = V, IsListBasis V (h ▸ vs)
  | .frame T E_fib, .frame T' _ f =>
      -- The fiber-type T must match; then every fiber is sound at the
      -- pinned-down per-fiber expected space. (The frame's domain basis
      -- `domB` is not constrained by `SoundOfDenot`; its soundness is a
      -- separate fact established at the frame's introduction.)
      ∃ h : T' = T, ∀ y : T', SoundOfDenot (E_fib (h ▸ y)) (f y)
  -- Shape mismatch between expected and produced denotation: not sound.
  | .vecs _, .frame _ _ _ => False
  | .frame _ _, .vecs _ _ => False

/-- A sound denotation remains sound when its expectation is normalized to the complete
recursive shape carried by the denotation itself. In the frame case this is the pure pointwise
observational extension: normalize and recurse independently at every fiber. -/
theorem SoundOfDenot.to_ofDenot : ∀ (E : ExpectedSpace) (d : BasisDenot),
    SoundOfDenot E d → SoundOfDenot (ExpectedSpace.ofDenot d) d
  | .vecs V, .vecs V' vs, h => by
      obtain ⟨rfl, hb⟩ := h
      exact ⟨rfl, hb⟩
  | .frame T E, .frame T' dom f, h => by
      obtain ⟨rfl, hf⟩ := h
      refine ⟨rfl, fun y => ?_⟩
      exact SoundOfDenot.to_ofDenot (E y) (f y) (hf y)
  | .vecs _, .frame _ _ _, h => False.elim h
  | .frame _ _, .vecs _ _, h => False.elim h

/-- `ExpectedSpace.ofBasis σ b` — the canonical expected-space shape
    for `denotBasis σ b`. Mirrors `denotBasis`'s case structure: for
    non-`.frame` bases it returns `.vecs (denotSpace σ (Basis.sof b))`;
    for `.frame x b₀ b₁` it returns the per-fiber family
    `fun y : T_outer.El => ExpectedSpace.ofBasis (σ.bind x (T_outer.embed y)) b₁`
    matching `denotBasis`'s `.frame` clause exactly. -/
noncomputable def ExpectedSpace.ofBasis (σ : DEnv) : Basis → ExpectedSpace
  | .empty => .vecs (denotSpace σ Basis.empty.sof)
  | .one   => .vecs (denotSpace σ Basis.one.sof)
  | .dual b => .vecs (denotSpace σ (Basis.dual b).sof)
  | .dsum b₀ b₁ => .vecs (denotSpace σ (Basis.dsum b₀ b₁).sof)
  | .tprod b₀ b₁ => .vecs (denotSpace σ (Basis.tprod b₀ b₁).sof)
  | .proj s b₀ b₁ => .vecs (denotSpace σ (Basis.proj s b₀ b₁).sof)
  | .image b => .vecs (denotSpace σ (Basis.image b).sof)
  | .terms s es b => .vecs (denotSpace σ (Basis.terms s es b).sof)
  | .frame b₀ b₁ =>
      let T_outer : HType := denotTy σ (Basis.tof b₀)
      let x : Name := Basis.freshFor b₁
      .frame T_outer.El (fun y : T_outer.El =>
        ExpectedSpace.ofDenot
          (denotBasis (σ.bind x (T_outer.embed y)) (Basis.openVar x b₁)))

/-- `ExpectedSpace.ofBasis σ b = .vecs (denotSpace σ (Basis.sof b))` for
    every *non-`.frame`* basis. Handy for the `.dsum`/`.tprod` IH
    rewrites and any caller that needs to know the IH lands on the
    `.vecs` shape. -/
theorem ExpectedSpace.ofBasis_vecs_of_not_frame {σ : DEnv} {b : Basis}
    (h : ∀ b₀ b₁, b ≠ .frame b₀ b₁) :
    ExpectedSpace.ofBasis σ b = .vecs (denotSpace σ (Basis.sof b)) := by
  cases b with
  | empty => simp [ExpectedSpace.ofBasis]
  | one => simp [ExpectedSpace.ofBasis]
  | dual b => simp [ExpectedSpace.ofBasis]
  | dsum b₀ b₁ => simp [ExpectedSpace.ofBasis]
  | tprod b₀ b₁ => simp [ExpectedSpace.ofBasis]
  | proj s b₀ b₁ => simp [ExpectedSpace.ofBasis]
  | image b => simp [ExpectedSpace.ofBasis]
  | terms s es b => simp [ExpectedSpace.ofBasis]
  | frame b₀ b₁ => exact absurd rfl (h b₀ b₁)

/-- Specialised equality for `.dsum`. Handy as a rewrite to bring the
    main theorem's goal into `.vecs`-on-LHS form. -/
@[simp] theorem ExpectedSpace.ofBasis_dsum (σ : DEnv) (b₀ b₁ : Basis) :
    ExpectedSpace.ofBasis σ (Basis.dsum b₀ b₁) =
      .vecs (denotSpace σ (Basis.sof (Basis.dsum b₀ b₁))) := by
  simp [ExpectedSpace.ofBasis]

/-- Specialised equality for `.tprod`. -/
@[simp] theorem ExpectedSpace.ofBasis_tprod (σ : DEnv) (b₀ b₁ : Basis) :
    ExpectedSpace.ofBasis σ (Basis.tprod b₀ b₁) =
      .vecs (denotSpace σ (Basis.sof (Basis.tprod b₀ b₁))) := by
  simp [ExpectedSpace.ofBasis]

/-- Specialised equality for `.empty`. -/
@[simp] theorem ExpectedSpace.ofBasis_empty (σ : DEnv) :
    ExpectedSpace.ofBasis σ Basis.empty =
      .vecs (denotSpace σ (Basis.sof Basis.empty)) := by
  simp [ExpectedSpace.ofBasis]

/-- Specialised equality for `.one`. -/
@[simp] theorem ExpectedSpace.ofBasis_one (σ : DEnv) :
    ExpectedSpace.ofBasis σ Basis.one =
      .vecs (denotSpace σ (Basis.sof Basis.one)) := by
  simp [ExpectedSpace.ofBasis]

/-- Specialised equality for `.frame` — useful for the main theorem's
    `.frame` case proof. -/
theorem ExpectedSpace.ofBasis_frame (σ : DEnv) (b₀ b₁ : Basis) :
    ExpectedSpace.ofBasis σ (Basis.frame b₀ b₁) =
      .frame (denotTy σ (Basis.tof b₀)).El
        (fun y => ExpectedSpace.ofDenot
          (denotBasis
            (σ.bind (Basis.freshFor b₁) ((denotTy σ (Basis.tof b₀)).embed y))
            (Basis.openVar (Basis.freshFor b₁) b₁))) := by
  simp [ExpectedSpace.ofBasis]

/-! ## B4 closure helpers: `atSpace_vecs_self` and `atSpace_vecs_eq`.

The `BasisDenot.atSpace` helper uses a `Classical.dec` carrier-equality
cast . For inputs of shape `.vecs V vs`
where `V` literally matches the expected space, the cast reduces to
the identity. These two lemmas package that reduction. -/

/-- `.frame`-branch reduction of `BasisDenot.atSpace`: a frame-shaped
    denotation always extracts as `[]` regardless of the expected space.
    Direct consequence of `BasisDenot.atSpace`'s `.frame` arm. -/
@[simp] theorem BasisDenot.atSpace_frame (V : HSpace) (T : Type) (domB : BasisDenot)
    (f : T → BasisDenot) :
    BasisDenot.atSpace V (.frame T domB f) = [] := rfl

/-- For any `.vecs`-branch denotation `denotBasis σ b = .vecs V' vs`
    whose recorded HSpace `V'` agrees (definitionally) with the
    expected `denotSpace σ (Basis.sof b)`, the `.atSpace` extraction
    is the identity on `vs`. -/
theorem BasisDenot.atSpace_vecs_self (V : HSpace) (vs : List V.carrier) :
    BasisDenot.atSpace V (.vecs V vs) = vs := by
  -- Unfold: the `if h : V.carrier = V.carrier` branch fires with h = rfl,
  -- and `(rfl ▸ ·)` is the identity on each element.
  unfold BasisDenot.atSpace
  simp only [↓reduceDIte]

  exact List.map_id vs

/-- Stronger form: if `denotBasis σ b = .vecs V' vs` and `V' = V`
    (the typed expectation), then `atSpace V (denotBasis σ b) = h ▸ vs`. -/
theorem BasisDenot.atSpace_vecs_eq {V V' : HSpace} (vs : List V'.carrier)
    (h : V' = V) :
    BasisDenot.atSpace V (.vecs V' vs) = h ▸ vs := by
  subst h
  exact BasisDenot.atSpace_vecs_self V' vs

/-! ## Recursive semantic orthonormality

Unlike an `atSpace` projection, this predicate follows the complete semantic
basis shape.  In particular, a frame is orthonormal only when its stored
domain basis and every one of its (possibly frame-valued) fibers are
orthonormal.  Thus a frame can never satisfy the definition vacuously merely
because `BasisDenot.atSpace` returns the empty list on frames. -/

/-- A semantic basis is recursively orthonormal.

At a vector leaf, the Gram matrix in the leaf's own stored `HSpace` is the
identity.  At a frame, both the stored domain basis and every semantic fiber
must recursively satisfy the same condition. -/
def BasisDenot.RecursiveOrthonormal : BasisDenot → Prop
  | .vecs V vs =>
      ∀ i j : Fin vs.length,
        V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0
  | .frame _ domB fb =>
      domB.RecursiveOrthonormal ∧ ∀ x, (fb x).RecursiveOrthonormal

/-! ## Σ-Basis ↔ `IsListBasis` bridge.

`Module.Basis ι ℝ V.carrier` is the Mathlib form (used by `Basis.prod`,
`Basis.tensorProduct`, `Basis.dualBasis`) — our `IsListBasis` is the
`List`-shaped form used by `denotBasis`. The two are interconvertible
when the index is `Fin vs.length`.

Used by the soundness theorem's `.dsum` / `.tprod` / `.dual` cases:
lift each IH to a `Module.Basis`, apply the Mathlib construction, then
descend back to an `IsListBasis` via a `Fin`-indexed reindexing. -/

/-- Auxiliary fact: `vs.get i = B (Fin.cast hlen i)` when `vs = (List.finRange n).map B`. -/
private theorem IsListBasis.finRange_map_get {V : Type*}
    [AddCommGroup V] [Module ℝ V] {n : ℕ} (B : Fin n → V)
    (i : Fin ((List.finRange n).map B).length) :
    ((List.finRange n).map B).get i = B (Fin.cast (by simp) i) := by
  simp [List.get_eq_getElem, List.getElem_map, List.getElem_finRange, Fin.cast]

/-- **Bridge (backward direction).** Given a `Module.Basis (Fin n) ℝ V.carrier`,
    the list `(List.finRange n).map B` realises an `IsListBasis`. -/
theorem IsListBasis.of_basis_fin {V : HSpace} {n : ℕ}
    (B : Module.Basis (Fin n) ℝ V.carrier) :
    IsListBasis V ((List.finRange n).map B) := by
  -- The list view of `B` reindexes via `Fin.cast hlen`.
  have hlen : ((List.finRange n).map B).length = n := by simp
  have heq : (fun i : Fin ((List.finRange n).map B).length =>
                ((List.finRange n).map B).get i) =
              B ∘ (fun i : Fin ((List.finRange n).map B).length =>
                    Fin.cast hlen i) := by
    funext i
    exact IsListBasis.finRange_map_get (V := V.carrier) (B : Fin n → V.carrier) i
  refine ⟨?_, ?_⟩
  · -- LI: reindex `B`'s LI through `Fin.cast`, which is injective.
    rw [heq]
    exact B.linearIndependent.comp _ (Fin.cast_injective hlen)
  · -- Span = ⊤: range is preserved since `Fin.cast` is a bijection.
    rw [heq]
    have h_range_eq :
        Set.range (B ∘ (fun i : Fin ((List.finRange n).map B).length =>
                          Fin.cast hlen i)) = Set.range B := by
      ext x
      simp only [Set.mem_range, Function.comp_apply]
      refine ⟨fun ⟨i, hi⟩ => ⟨Fin.cast hlen i, hi⟩, fun ⟨j, hj⟩ => ?_⟩
      exact ⟨Fin.cast hlen.symm j, by simp [hj]⟩
    rw [h_range_eq]
    exact B.span_eq

/-- Length of the dsum list. -/
@[simp] theorem HSpace.dsumOfLists_length {V₀ V₁ : HSpace}
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).length = vs₀.length + vs₁.length := by
  unfold HSpace.dsumOfLists
  simp

/-- `dsumOfLists` with empty LHS reduces to `vs₁.map inr`. -/
@[simp] theorem HSpace.dsumOfLists_nil_left (V₀ V₁ : HSpace)
    (vs₁ : List V₁.carrier) :
    HSpace.dsumOfLists V₀ V₁ [] vs₁ =
      vs₁.map (LinearMap.inr ℝ V₀.carrier V₁.carrier) := by
  unfold HSpace.dsumOfLists
  simp

/-- `dsumOfLists` with empty RHS reduces to `vs₀.map inl`. -/
@[simp] theorem HSpace.dsumOfLists_nil_right (V₀ V₁ : HSpace)
    (vs₀ : List V₀.carrier) :
    HSpace.dsumOfLists V₀ V₁ vs₀ [] =
      vs₀.map (LinearMap.inl ℝ V₀.carrier V₁.carrier) := by
  unfold HSpace.dsumOfLists
  simp

/-- `tprodOfLists` with empty LHS yields `[]`. -/
@[simp] theorem HSpace.tprodOfLists_nil_left (V₀ V₁ : HSpace)
    (vs₁ : List V₁.carrier) :
    HSpace.tprodOfLists V₀ V₁ [] vs₁ = [] := by
  unfold HSpace.tprodOfLists
  simp

/-- `tprodOfLists` with empty RHS yields `[]`. -/
@[simp] theorem HSpace.tprodOfLists_nil_right (V₀ V₁ : HSpace)
    (vs₀ : List V₀.carrier) :
    HSpace.tprodOfLists V₀ V₁ vs₀ [] = [] := by
  unfold HSpace.tprodOfLists
  simp

/-- `dualOfList` of the empty list yields `[]`. -/
@[simp] theorem HSpace.dualOfList_nil (V : HSpace) :
    HSpace.dualOfList V [] = [] := by
  unfold HSpace.dualOfList
  simp

/-- The empty list is a basis of `HSpace.dual HSpace.empty`. The carrier
    `PUnit →ₗ[ℝ] ℝ` is the zero module (every linear map from PUnit is the
    zero map), so the empty list spans it trivially. -/
theorem isListBasis_dual_empty : IsListBasis (HSpace.dual HSpace.empty) [] := by
  refine ⟨?_, ?_⟩
  · -- LinearIndependent over Fin 0: vacuous.
    have : IsEmpty (Fin ([] : List (HSpace.dual HSpace.empty).carrier).length) := by
      simp only [List.length_nil]; exact Fin.isEmpty'
    exact linearIndependent_empty_type
  · -- span ℝ ∅ = ⊥; need ⊥ = ⊤ in HSpace.dual HSpace.empty's carrier.
    apply Submodule.eq_top_iff'.mpr
    intro φ
    -- φ : PUnit →ₗ[ℝ] ℝ; show φ = 0.
    have hφ : φ = 0 := by
      ext x
      have hx : x = PUnit.unit := Subsingleton.elim x PUnit.unit
      rw [hx]
      show φ PUnit.unit = 0
      -- φ PUnit.unit = φ (0 : PUnit) = 0.
      have h0 : (PUnit.unit : PUnit) = 0 := rfl
      rw [h0]
      exact map_zero φ
    rw [hφ]
    exact Submodule.zero_mem _

/-- **dsum case.** Combining two `IsListBasis` witnesses via `dsumOfLists`
    yields an `IsListBasis` on `HSpace.dsum V₀ V₁`. Built via Mathlib's
    `Module.Basis.prod` (after lifting each side through `IsListBasis.toBasis`)
    composed with the `finSumFinEquiv` reindex back to a `Fin`-indexed
    list. -/
theorem IsListBasis.dsum {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (h₀ : IsListBasis V₀ vs₀) (h₁ : IsListBasis V₁ vs₁) :
    IsListBasis (HSpace.dsum V₀ V₁) (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁) := by
  -- Unfold `dsumOfLists` and rename for clarity.
  unfold HSpace.dsumOfLists
  set vs := vs₀.map (LinearMap.inl ℝ V₀.carrier V₁.carrier) ++
            vs₁.map (LinearMap.inr ℝ V₀.carrier V₁.carrier)
  -- The Sum-shaped family that lines up element-wise with `vs`.
  let g : Fin vs₀.length ⊕ Fin vs₁.length → V₀.carrier × V₁.carrier :=
    Sum.elim
      (fun i => (vs₀.get i, 0))
      (fun j => (0, vs₁.get j))
  -- `vs.get : Fin vs.length → V₀.carrier × V₁.carrier` reindexes `g`
  -- through `finSumFinEquiv.symm` and a length cast.
  have hlen : vs.length = vs₀.length + vs₁.length := by
    simp [vs]
  have h_get : ∀ i : Fin vs.length,
      vs.get i = g (finSumFinEquiv.symm (Fin.cast hlen i)) := by
    intro i
    -- Case-split on whether `i` lies in the left half (`vs₀` part) or the right half.
    rcases Nat.lt_or_ge i.1 vs₀.length with hi | hi
    · -- Left half: `vs.get i = (vs₀.map inl).get ⟨i, _⟩ = inl (vs₀.get _) = (vs₀.get _, 0)`.
      have hL : vs.get i =
          (vs₀.map (LinearMap.inl ℝ V₀.carrier V₁.carrier)).get
            ⟨i.1, by simp [hi]⟩ := by
        simp [vs, List.get_eq_getElem, List.getElem_append_left, hi]
      have hL2 : (vs₀.map (LinearMap.inl ℝ V₀.carrier V₁.carrier)).get
            ⟨i.1, by simp [hi]⟩ = (vs₀.get ⟨i.1, hi⟩, 0) := by
        simp [List.get_eq_getElem, List.getElem_map, LinearMap.inl_apply]
      rw [hL, hL2]
      -- And `finSumFinEquiv.symm (Fin.cast hlen i) = Sum.inl ⟨i.1, hi⟩` when `i.1 < vs₀.length`.
      have hsymm :
          finSumFinEquiv.symm (Fin.cast hlen i) = Sum.inl ⟨i.1, hi⟩ := by
        -- `Fin.cast hlen i : Fin (vs₀.length + vs₁.length)`. Since `i.1 < vs₀.length`,
        -- `Fin.castAdd vs₁.length ⟨i.1, hi⟩` equals `Fin.cast hlen i`.
        have : Fin.cast hlen i = Fin.castAdd vs₁.length ⟨i.1, hi⟩ := by
          apply Fin.ext; rfl
        rw [this, finSumFinEquiv_symm_apply_castAdd]
      rw [hsymm]
      rfl
    · -- Right half: `vs.get i = (vs₁.map inr).get ⟨i.1 - vs₀.length, _⟩`.
      have hi_total : i.1 < vs₀.length + vs₁.length := by
        rw [← hlen]; exact i.isLt
      have hi_sub : i.1 - vs₀.length < vs₁.length := by
        omega
      have hR : vs.get i =
          (vs₁.map (LinearMap.inr ℝ V₀.carrier V₁.carrier)).get
            ⟨i.1 - vs₀.length, by simp [hi_sub]⟩ := by
        simp [vs, List.get_eq_getElem,
              List.getElem_append_right (show vs₀.length ≤ i.1 from hi),
              List.length_map, hi]
      have hR2 : (vs₁.map (LinearMap.inr ℝ V₀.carrier V₁.carrier)).get
            ⟨i.1 - vs₀.length, by simp [hi_sub]⟩ =
            (0, vs₁.get ⟨i.1 - vs₀.length, hi_sub⟩) := by
        simp [List.get_eq_getElem, List.getElem_map, LinearMap.inr_apply]
      rw [hR, hR2]
      -- And `finSumFinEquiv.symm (Fin.cast hlen i) = Sum.inr ⟨i.1 - vs₀.length, hi_sub⟩`.
      have hsymm :
          finSumFinEquiv.symm (Fin.cast hlen i) =
            Sum.inr ⟨i.1 - vs₀.length, hi_sub⟩ := by
        have : Fin.cast hlen i =
                Fin.natAdd vs₀.length ⟨i.1 - vs₀.length, hi_sub⟩ := by
          apply Fin.ext
          show i.1 = vs₀.length + (i.1 - vs₀.length)
          omega
        rw [this, finSumFinEquiv_symm_apply_natAdd]
      rw [hsymm]
      rfl
  refine ⟨?_, ?_⟩
  · -- LinearIndependent. `fun i => vs.get i = g ∘ finSumFinEquiv.symm ∘ Fin.cast hlen`.
    have h_lin_g : LinearIndependent ℝ g := by
      apply LinearIndependent.sum_type
      · -- LI of `i ↦ (vs₀.get i, 0)`. Push through the embedding inl.
        have : (fun i : Fin vs₀.length => (vs₀.get i, (0 : V₁.carrier))) =
                (LinearMap.inl ℝ V₀.carrier V₁.carrier) ∘ (fun i => vs₀.get i) := by
          funext i; rfl
        rw [this]
        exact (LinearMap.linearIndependent_iff (LinearMap.inl ℝ V₀.carrier V₁.carrier)
                Submodule.ker_inl).mpr h₀.1
      · -- LI of `j ↦ (0, vs₁.get j)`.
        have : (fun j : Fin vs₁.length => ((0 : V₀.carrier), vs₁.get j)) =
                (LinearMap.inr ℝ V₀.carrier V₁.carrier) ∘ (fun j => vs₁.get j) := by
          funext j; rfl
        rw [this]
        exact (LinearMap.linearIndependent_iff (LinearMap.inr ℝ V₀.carrier V₁.carrier)
                Submodule.ker_inr).mpr h₁.1
      · -- Disjoint spans: span of inl-image and span of inr-image are disjoint.
        -- `span (range (fun i => (vs₀.get i, 0))) ≤ V₀.carrier × {0}` and
        -- `span (range (fun j => (0, vs₁.get j))) ≤ {0} × V₁.carrier`; these are
        -- complementary (`isCompl_range_inl_range_inr`).
        have hL : Submodule.span ℝ
            (Set.range (g ∘ Sum.inl : Fin vs₀.length → V₀.carrier × V₁.carrier)) ≤
            LinearMap.range (LinearMap.inl ℝ V₀.carrier V₁.carrier) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨i, rfl⟩
          show (vs₀.get i, (0 : V₁.carrier)) ∈ LinearMap.range _
          exact ⟨vs₀.get i, rfl⟩
        have hR : Submodule.span ℝ
            (Set.range (g ∘ Sum.inr : Fin vs₁.length → V₀.carrier × V₁.carrier)) ≤
            LinearMap.range (LinearMap.inr ℝ V₀.carrier V₁.carrier) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨j, rfl⟩
          show ((0 : V₀.carrier), vs₁.get j) ∈ LinearMap.range _
          exact ⟨vs₁.get j, rfl⟩
        exact (LinearMap.isCompl_range_inl_inr (R := ℝ)
                  (M := V₀.carrier) (M₂ := V₁.carrier)).disjoint.mono hL hR

    have h_reindex : LinearIndependent ℝ
        (g ∘ (fun i : Fin vs.length => finSumFinEquiv.symm (Fin.cast hlen i))) :=
      h_lin_g.comp _ (Function.Injective.comp finSumFinEquiv.symm.injective
                       (Fin.cast_injective hlen))
    -- Compose with `h_get`.
    have h_eq : (fun i : Fin vs.length => vs.get i) =
                g ∘ (fun i : Fin vs.length => finSumFinEquiv.symm (Fin.cast hlen i)) := by
      funext i; exact h_get i
    rw [h_eq]; exact h_reindex
  · -- Span = ⊤. Set.range of the list-indexed family = Set.range g (via the bijection).
    have h_eq : (fun i : Fin vs.length => vs.get i) =
                g ∘ (fun i : Fin vs.length => finSumFinEquiv.symm (Fin.cast hlen i)) := by
      funext i; exact h_get i
    rw [h_eq]
    -- The composition's range equals `Set.range g` because the inner map is a bijection.
    have h_range :
        Set.range (g ∘ (fun i : Fin vs.length =>
                         finSumFinEquiv.symm (Fin.cast hlen i))) = Set.range g := by
      ext x
      simp only [Set.mem_range, Function.comp_apply]
      refine ⟨fun ⟨i, hi⟩ => ⟨_, hi⟩, fun ⟨s, hs⟩ => ?_⟩
      refine ⟨Fin.cast hlen.symm (finSumFinEquiv s), ?_⟩
      have : finSumFinEquiv.symm (Fin.cast hlen (Fin.cast hlen.symm (finSumFinEquiv s))) = s := by
        simp [Fin.cast_trans]
      rw [this]; exact hs
    rw [h_range]
    -- `Set.range g` spans the whole `V₀ × V₁` because `g`'s range covers
    -- `inl(vs₀) ∪ inr(vs₁)`, whose span is `(span vs₀) × (span vs₁) = ⊤ × ⊤ = ⊤`.
    have h_range_g : Set.range g =
        (LinearMap.inl ℝ V₀.carrier V₁.carrier) '' (Set.range (fun i => vs₀.get i)) ∪
        (LinearMap.inr ℝ V₀.carrier V₁.carrier) '' (Set.range (fun j => vs₁.get j)) := by
      ext x
      constructor
      · rintro ⟨s, hs⟩
        rcases s with i | j
        · left
          refine ⟨vs₀.get i, ⟨i, rfl⟩, ?_⟩
          show LinearMap.inl ℝ V₀.carrier V₁.carrier (vs₀.get i) = x
          rw [LinearMap.inl_apply]; exact hs
        · right
          refine ⟨vs₁.get j, ⟨j, rfl⟩, ?_⟩
          show LinearMap.inr ℝ V₀.carrier V₁.carrier (vs₁.get j) = x
          rw [LinearMap.inr_apply]; exact hs
      · rintro (⟨v, ⟨i, rfl⟩, rfl⟩ | ⟨w, ⟨j, rfl⟩, rfl⟩)
        · exact ⟨Sum.inl i, rfl⟩
        · exact ⟨Sum.inr j, rfl⟩
    rw [h_range_g, LinearMap.span_inl_union_inr, h₀.2, h₁.2]
    -- `(⊤ : Submodule ℝ V₀.carrier).prod (⊤ : Submodule ℝ V₁.carrier) = ⊤`.
    exact Submodule.prod_top

/-- Length of the tprod list. -/
@[simp] theorem HSpace.tprodOfLists_length {V₀ V₁ : HSpace}
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).length = vs₀.length * vs₁.length := by
  unfold HSpace.tprodOfLists
  -- `vs₀.flatMap (fun v => vs₁.map (mk v))`'s length is `vs₀.length * vs₁.length`.
  induction vs₀ with
  | nil => simp
  | cons v vs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, ih,
                 List.length_cons]
      ring

/-- `tprodOfLists.get` factors through the product-Fin equivalence:
    `(tprodOfLists vs₀ vs₁).get k = vs₀.get (k / n₁) ⊗ vs₁.get (k % n₁)`. -/
theorem HSpace.tprodOfLists_getElem {V₀ V₁ : HSpace}
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier)
    (k : ℕ) (hk : k < vs₀.length * vs₁.length)
    (hv₁_pos : 0 < vs₁.length) :
    have hi : k / vs₁.length < vs₀.length :=
      Nat.div_lt_iff_lt_mul hv₁_pos |>.mpr hk
    have hj : k % vs₁.length < vs₁.length := Nat.mod_lt _ hv₁_pos
    (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁)[k]'(by
      rw [HSpace.tprodOfLists_length]; exact hk) =
      vs₀[k / vs₁.length]'hi ⊗ₜ[ℝ] vs₁[k % vs₁.length]'hj := by
  induction vs₀ generalizing k with
  | nil => simp at hk
  | cons v vs ih =>
      unfold HSpace.tprodOfLists at *
      simp only [List.flatMap_cons]
      rcases Nat.lt_or_ge k vs₁.length with hk_small | hk_big
      · -- First block: k < vs₁.length.
        have h_in_left : k < (vs₁.map (fun w => v ⊗ₜ[ℝ] w)).length := by simpa
        rw [List.getElem_append_left h_in_left]
        simp only [List.getElem_map]
        -- k / vs₁.length = 0, k % vs₁.length = k.
        have h_div : k / vs₁.length = 0 := Nat.div_eq_of_lt hk_small
        have h_mod : k % vs₁.length = k := Nat.mod_eq_of_lt hk_small
        -- (v :: vs)[0] = v, vs₁[k] = vs₁[k % vs₁.length].
        congr 1
        · -- v = (v :: vs)[k / vs₁.length]
          simp [h_div]
        · -- vs₁[k] = vs₁[k % vs₁.length]
          congr 1
          exact h_mod.symm
      · -- Second block.
        have hk_sub : k - vs₁.length < vs.length * vs₁.length := by
          have : (v :: vs).length * vs₁.length = vs₁.length + vs.length * vs₁.length := by
            simp [List.length_cons]; ring
          omega
        have hk_ge : (vs₁.map (fun w => v ⊗ₜ[ℝ] w)).length ≤ k := by simpa
        rw [List.getElem_append_right hk_ge]

        have ih_eq := ih (k - vs₁.length) hk_sub
        unfold HSpace.tprodOfLists at ih_eq
        simp only [List.length_map]
        rw [ih_eq]
        -- Reduce indices.
        have h_div_eq : k / vs₁.length = (k - vs₁.length) / vs₁.length + 1 := by
          have hkrew : k = (k - vs₁.length) + vs₁.length := by omega
          conv_lhs => rw [hkrew]
          rw [Nat.add_div_right _ hv₁_pos]
        have h_mod_eq : k % vs₁.length = (k - vs₁.length) % vs₁.length := by
          have hkrew : k = (k - vs₁.length) + vs₁.length := by omega
          conv_lhs => rw [hkrew]
          rw [Nat.add_mod_right]

        congr 1
        · -- vs[(k - vs₁.length) / vs₁.length] = (v :: vs)[k / vs₁.length]
          -- Since k / vs₁.length = (k - vs₁.length) / vs₁.length + 1 and (v :: vs)[i+1] = vs[i].
          have : (v :: vs)[k / vs₁.length]'(by
                    rw [h_div_eq]; simpa [List.length_cons] using
                      Nat.succ_lt_succ
                        (Nat.div_lt_iff_lt_mul hv₁_pos |>.mpr hk_sub)) =
                  vs[(k - vs₁.length) / vs₁.length]'(
                    Nat.div_lt_iff_lt_mul hv₁_pos |>.mpr hk_sub) := by
            simp [h_div_eq, List.getElem_cons_succ]
          exact this.symm
        · -- vs₁[(k - vs₁.length) % vs₁.length] = vs₁[k % vs₁.length].
          congr 1
          exact h_mod_eq.symm

/-- **tprod case.** Combining two `IsListBasis` witnesses via `tprodOfLists`
    yields an `IsListBasis` on `HSpace.tprod V₀ V₁`. Built via Mathlib's
    `Module.Basis.tensorProduct` (after lifting each side through
    `IsListBasis.toBasis`) composed with the `finProdFinEquiv` reindex
    back to a `Fin`-indexed list. -/
theorem IsListBasis.tprod {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (h₀ : IsListBasis V₀ vs₀) (h₁ : IsListBasis V₁ vs₁) :
    IsListBasis (HSpace.tprod V₀ V₁) (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁) := by
  -- Lift IHs to Mathlib `Basis` form, take the tensor product, and reindex.
  let B₀ := h₀.toBasis
  let B₁ := h₁.toBasis
  -- B_tp : Basis (Fin vs₀.length × Fin vs₁.length) ℝ (V₀.carrier ⊗ V₁.carrier).
  let B_tp : Module.Basis (Fin vs₀.length × Fin vs₁.length) ℝ
                (V₀.carrier ⊗[ℝ] V₁.carrier) :=
    Module.Basis.tensorProduct B₀ B₁

  have hlen : (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).length =
              vs₀.length * vs₁.length :=
    HSpace.tprodOfLists_length vs₀ vs₁
  -- `g : Fin vs₀.length × Fin vs₁.length → V₀.carrier ⊗ V₁.carrier`.
  -- Define `g (i, j) = vs₀.get i ⊗ vs₁.get j`.
  let g : Fin vs₀.length × Fin vs₁.length → V₀.carrier ⊗[ℝ] V₁.carrier :=
    fun p => vs₀.get p.1 ⊗ₜ[ℝ] vs₁.get p.2
  -- B_tp equals `g` because `B₀ i = vs₀.get i`, `B₁ j = vs₁.get j`,
  -- and `Basis.tensorProduct_apply`.
  have h_Btp_eq : ⇑B_tp = g := by
    funext p
    show (B₀.tensorProduct B₁) p = g p
    rw [Module.Basis.tensorProduct_apply']
    show B₀ p.1 ⊗ₜ[ℝ] B₁ p.2 = g p
    simp [B₀, B₁, g, IsListBasis.toBasis_apply]
  -- Show the list-indexed family equals `g ∘ finProdFinEquiv.symm ∘ Fin.cast hlen`.
  have h_get : ∀ k : Fin (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).length,
      (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).get k =
        g (finProdFinEquiv.symm (Fin.cast hlen k)) := by
    intro k
    -- Establish vs₁.length > 0 (otherwise the list is empty).
    have hk_total : k.1 < vs₀.length * vs₁.length := hlen ▸ k.isLt
    have hv₁_pos : 0 < vs₁.length := by
      by_contra h0
      push_neg at h0
      have : vs₁.length = 0 := Nat.eq_zero_of_le_zero h0
      rw [this, Nat.mul_zero] at hk_total
      exact Nat.not_lt_zero _ hk_total
    have h_eq := HSpace.tprodOfLists_getElem vs₀ vs₁ k.1 hk_total hv₁_pos
    -- Rewrite the goal's LHS via h_eq.
    rw [List.get_eq_getElem, h_eq]
    -- After rw: LHS is `vs₀[k.1 / vs₁.length] ⊗ vs₁[k.1 % vs₁.length]`.
    -- RHS: g (finProdFinEquiv.symm (Fin.cast hlen k))
    --    = g (Fin.cast hlen k).divNat, (Fin.cast hlen k).modNat)
    --    = vs₀.get (.divNat) ⊗ vs₁.get (.modNat).
    -- `Fin.divNat k.1 = ⟨k.1 / vs₁.length, _⟩` etc. So the two sides match definitionally
    -- up to `vs₀[i] = vs₀.get i`.
    show _ = vs₀.get _ ⊗ₜ[ℝ] vs₁.get _
    simp only [List.get_eq_getElem]
    rfl
  -- LI and span follow.
  refine ⟨?_, ?_⟩
  · -- LinearIndependent of the list-indexed family.
    have h_lin_g : LinearIndependent ℝ g := by
      rw [← h_Btp_eq]; exact B_tp.linearIndependent
    have : (fun k : Fin (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).length =>
              (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).get k) =
           g ∘ (fun k => finProdFinEquiv.symm (Fin.cast hlen k)) := by
      funext k; exact h_get k
    rw [this]
    exact h_lin_g.comp _
      (Function.Injective.comp finProdFinEquiv.symm.injective (Fin.cast_injective hlen))
  · -- Span = ⊤.
    have h_span_g : Submodule.span ℝ (Set.range g) = ⊤ := by
      rw [← h_Btp_eq]; exact B_tp.span_eq
    have heq : (fun k : Fin (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).length =>
                  (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).get k) =
               g ∘ (fun k => finProdFinEquiv.symm (Fin.cast hlen k)) := by
      funext k; exact h_get k
    rw [heq]
    have h_range_eq :
        Set.range (g ∘ (fun k : Fin (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).length =>
                          finProdFinEquiv.symm (Fin.cast hlen k))) = Set.range g := by
      ext x
      simp only [Set.mem_range, Function.comp_apply]
      refine ⟨fun ⟨k, hk⟩ => ⟨_, hk⟩, fun ⟨p, hp⟩ => ?_⟩
      refine ⟨Fin.cast hlen.symm (finProdFinEquiv p), ?_⟩
      have : finProdFinEquiv.symm (Fin.cast hlen (Fin.cast hlen.symm (finProdFinEquiv p))) = p := by
        simp
      rw [this]; exact hp
    rw [h_range_eq]; exact h_span_g

open scoped Matrix

/-- **Gram isUnit**: invertibility follows from PD. -/
theorem IsListBasis.gram_isUnit {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) : IsUnit (IsListBasis.gram V vs) :=
  (IsListBasis.gram_posDef h).isUnit

/-- The list `dualOfList V vs` has length `vs.length`. -/
@[simp] theorem HSpace.dualOfList_length (V : HSpace) (vs : List V.carrier) :
    (V.dualOfList vs).length = vs.length := by
  simp [HSpace.dualOfList]

/-- **Dual basis (index-natural form)**: the `i`-th entry of `dualOfList V vs`,
    accessed by a `Fin vs.length` index (not `Fin (dualOfList).length`) to
    avoid cast clutter. -/
noncomputable def HSpace.dualVec (V : HSpace) (vs : List V.carrier)
    (i : Fin vs.length) : V.carrier →ₗ[ℝ] ℝ :=
  ∑ k : Fin vs.length, ((IsListBasis.gram V vs)⁻¹ i k) •
    V.innerProduct (vs.get k)

theorem HSpace.dualOfList_eq_finRange_map (V : HSpace) (vs : List V.carrier) :
    V.dualOfList vs = (List.finRange vs.length).map (HSpace.dualVec V vs) := by
  rfl

/-- **δ identity**: `(dualVec V vs i) (vs.get j) = δᵢⱼ` when `vs` is a basis. -/
theorem IsListBasis.dual_delta {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) (i j : Fin vs.length) :
    (V.dualVec vs i) (vs.get j) = if i = j then 1 else 0 := by
  unfold HSpace.dualVec
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  have h_isUnit := IsListBasis.gram_isUnit h
  have h_isUnit_det : IsUnit (IsListBasis.gram V vs).det := by
    rwa [Matrix.isUnit_iff_isUnit_det] at h_isUnit
  have h_inv_mul : (IsListBasis.gram V vs)⁻¹ * IsListBasis.gram V vs = 1 :=
    Matrix.nonsing_inv_mul _ h_isUnit_det
  have h_sum_eq : ∑ k : Fin vs.length,
        (IsListBasis.gram V vs)⁻¹ i k * V.innerProduct (vs.get k) (vs.get j) =
      ((IsListBasis.gram V vs)⁻¹ * IsListBasis.gram V vs) i j := by
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rfl
  rw [h_sum_eq, h_inv_mul]

  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hij]
    simp [hij]

/-- `eval_same` field of `Module.DualBases` for our dual: `wᵢ(vᵢ) = 1`. -/
theorem IsListBasis.dual_eval_same {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) (i : Fin vs.length) :
    (V.dualVec vs i) (vs.get i) = 1 := by
  rw [IsListBasis.dual_delta h i i]
  simp

/-- `eval_of_ne` field of `Module.DualBases` for our dual: `wᵢ(vⱼ) = 0` for `i ≠ j`. -/
theorem IsListBasis.dual_eval_of_ne {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) :
    Pairwise fun i j : Fin vs.length => (V.dualVec vs i) (vs.get j) = 0 := by
  intro i j hij
  rw [IsListBasis.dual_delta h i j]
  simp [hij]

/-- `total` field of `Module.DualBases` for our dual: `wᵢ` separate points.
    If two vectors agree on every `wᵢ`, they agree. -/
theorem IsListBasis.dual_total {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) :
    ∀ {m₁ m₂ : V.carrier}, (∀ i, V.dualVec vs i m₁ = V.dualVec vs i m₂) → m₁ = m₂ := by
  intro m₁ m₂ heq
  -- By linearity, reduce to showing (∀ i, w_i x = 0) → x = 0 where x = m₁ - m₂.
  rw [← sub_eq_zero]
  set x := m₁ - m₂
  -- We have `∀ i, w_i m₁ = w_i m₂`, i.e. `∀ i, w_i x = 0` by linearity.
  have h_wx_zero : ∀ i, V.dualVec vs i x = 0 := by
    intro i
    show V.dualVec vs i (m₁ - m₂) = 0
    rw [LinearMap.map_sub]
    rw [heq i, sub_self]
  -- Span: x = Σ_j c_j vs.get j for some coefficients c_j.
  have hspan := h.2
  -- Use the bridge: from IsListBasis, we get a Module.Basis.
  let b := h.toBasis
  -- Apply b.linearCombination_repr to express x.
  have h_repr_x : x = ∑ j, b.repr x j • vs.get j := by
    -- b.repr x is the representation in basis b; b j = vs.get j.
    -- b.repr_total: x = ∑_j (b.repr x j) • b j = ∑_j (b.repr x j) • vs.get j.
    conv_lhs => rw [← Module.Basis.linearCombination_repr b x]
    rw [Finsupp.linearCombination_apply]
    -- ∑ j ∈ (b.repr x).support, (b.repr x j) • b j
    rw [Finsupp.sum_fintype]
    · apply Finset.sum_congr rfl
      intro j _
      rw [IsListBasis.toBasis_apply]
    · intro j; rw [zero_smul]

  have h_coeff_zero : ∀ i, b.repr x i = 0 := by
    intro i
    have h_apply : V.dualVec vs i x = b.repr x i := by
      conv_lhs => rw [h_repr_x]
      rw [map_sum]
      -- ∑ j, V.dualVec vs i (b.repr x j • vs.get j)
      -- = ∑ j, b.repr x j * V.dualVec vs i (vs.get j)
      -- = ∑ j, b.repr x j * δᵢⱼ
      -- = b.repr x i.
      have h_term : ∀ j : Fin vs.length,
          V.dualVec vs i (b.repr x j • vs.get j) =
            (b.repr x j) * (if i = j then 1 else 0) := by
        intro j
        rw [LinearMap.map_smul, smul_eq_mul, IsListBasis.dual_delta h i j]
      rw [Finset.sum_congr rfl (fun j _ => h_term j)]
      -- ∑ j, b.repr x j * (if i = j then 1 else 0) = b.repr x i.
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [Ne.symm hji]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [← h_apply, h_wx_zero]

  rw [h_repr_x]
  apply Finset.sum_eq_zero
  intro j _
  rw [h_coeff_zero, zero_smul]

/-- Pointwise reconstruction in a list basis using its Gram-corrected dual family.  This is the
coordinate-free finite expansion used by linear-lambda assembly: evaluating the source map on
each basis vector determines the whole map. -/
theorem IsListBasis.sum_dual_smul {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) (x : V.carrier) :
    x = ∑ i : Fin vs.length, (V.dualVec vs i x) • vs.get i := by
  apply h.dual_total
  intro j
  rw [map_sum]
  simp_rw [LinearMap.map_smul, IsListBasis.dual_delta h]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Ne.symm hij]
  · exact fun hmem => absurd (Finset.mem_univ j) hmem

/-- A linear map is the finite sum of its values on a list basis, weighted pointwise by the dual
coordinates.  This is the semantic column-expansion equation behind both `llam_assemble` rules. -/
theorem IsListBasis.map_eq_sum_dual_smul {V W : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) (φ : V.carrier →ₗ[ℝ] W.carrier) (x : V.carrier) :
    φ x = ∑ i : Fin vs.length, (V.dualVec vs i x) • φ (vs.get i) := by
  conv_lhs => rw [h.sum_dual_smul x]
  rw [map_sum]
  simp only [LinearMap.map_smul]

/-- Tensor form of `map_eq_sum_dual_smul`: the tensor encoding of a linear map is the sum of
dual basis covectors tensored with its columns. -/
theorem IsListBasis.dualTensorHomEquiv_symm_eq_sum
    {V W : HSpace} {vs : List V.carrier} (h : IsListBasis V vs)
    (φ : V.carrier →ₗ[ℝ] W.carrier) :
    (dualTensorHomEquiv ℝ V.carrier W.carrier).symm φ =
      ∑ i : Fin vs.length, V.dualVec vs i ⊗ₜ[ℝ] φ (vs.get i) := by
  apply (dualTensorHomEquiv ℝ V.carrier W.carrier).injective
  rw [LinearEquiv.apply_symm_apply]
  ext x
  rw [map_sum]
  simp only [dualTensorHomEquiv, dualTensorHomEquivOfBasis_apply]
  rw [LinearMap.sum_apply]
  simp only [dualTensorHom_apply]
  exact h.map_eq_sum_dual_smul φ x

/-- Coefficient form of the tensor column expansion.  If each observed column is expressed in a
codomain basis, these are exactly the row-major coefficients emitted by linear assembly. -/
theorem IsListBasis.dualTensorHomEquiv_symm_eq_sum₂
    {V W : HSpace} {vs : List V.carrier} {ws : List W.carrier}
    (h : IsListBasis V vs) (φ : V.carrier →ₗ[ℝ] W.carrier)
    (a : Fin vs.length → Fin ws.length → ℝ)
    (hcol : ∀ i, φ (vs.get i) = ∑ j, a i j • ws.get j) :
    (dualTensorHomEquiv ℝ V.carrier W.carrier).symm φ =
      ∑ i, ∑ j, a i j • (V.dualVec vs i ⊗ₜ[ℝ] ws.get j) := by
  rw [h.dualTensorHomEquiv_symm_eq_sum φ]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcol i, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [TensorProduct.tmul_smul]

/-- Construct a `Module.DualBases` instance for `(vs.get, V.dualVec vs)`. -/
noncomputable def IsListBasis.dualBases {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) :
    Module.DualBases (fun i : Fin vs.length => vs.get i) (V.dualVec vs) where
  eval_same := IsListBasis.dual_eval_same h
  eval_of_ne := IsListBasis.dual_eval_of_ne h
  total := fun {_ _} => IsListBasis.dual_total h

/-- **Main lemma — `IsListBasis.dual`**: the Gram-corrected dual of a
    list basis is a list basis of the dual space.

    Closure path:
      Module.DualBases.basis → b.dualBasis → IsListBasis.of_basis_fin. -/
theorem IsListBasis.dual {V : HSpace} {vs : List V.carrier}
    (h : IsListBasis V vs) :
    IsListBasis (HSpace.dual V) (V.dualOfList vs) := by
  -- Bridge through Mathlib's DualBases machinery.
  let dB := IsListBasis.dualBases h
  -- dB.basis : Module.Basis (Fin vs.length) ℝ V.carrier with coe = vs.get.
  -- dB.basis.dualBasis : Module.Basis (Fin vs.length) ℝ (V →ₗ ℝ)
  --   with coe = V.dualVec vs (by `coe_dualBasis`).
  -- Apply IsListBasis.of_basis_fin on dB.basis.dualBasis to get
  -- IsListBasis (HSpace.dual V) ((List.finRange vs.length).map dB.basis.dualBasis).
  have h_lb := IsListBasis.of_basis_fin (V := HSpace.dual V)
                  (n := vs.length) dB.basis.dualBasis
  -- Show (List.finRange vs.length).map dB.basis.dualBasis = V.dualOfList vs.
  have h_eq : (List.finRange vs.length).map dB.basis.dualBasis =
              V.dualOfList vs := by
    rw [HSpace.dualOfList_eq_finRange_map]
    congr 1
    funext i
    rw [Module.DualBases.coe_dualBasis dB]
  rw [h_eq] at h_lb
  exact h_lb

/-! Direct sums of orthonormal basis lists are orthonormal for the direct-sum inner product. -/

namespace HSpace

/-- The inner product of an `HSpace` defines a Mathlib `InnerProductSpace` instance. -/
@[reducible] noncomputable def toNormedAddCommGroup (V : HSpace) :
    NormedAddCommGroup V.carrier :=
  letI core : InnerProductSpace.Core ℝ V.carrier :=
    IsInnerProduct.toIPSCore V.innerIsIP
  InnerProductSpace.Core.toNormedAddCommGroup (cd := core)

@[reducible] noncomputable def toInnerProductSpace (V : HSpace) :
    @InnerProductSpace ℝ V.carrier _ V.toNormedAddCommGroup.toSeminormedAddCommGroup :=
  letI nag : NormedAddCommGroup V.carrier := V.toNormedAddCommGroup
  InnerProductSpace.ofCore _

end HSpace

/-- `dsum`'s inner product as a function on coordinates. Unfolds the
    `LinearMap.mk₂` definition for use inside element-level reasoning. -/
@[simp] theorem HSpace.dsum_innerProduct_apply (V₀ V₁ : HSpace)
    (p q : (HSpace.dsum V₀ V₁).carrier) :
    (HSpace.dsum V₀ V₁).innerProduct p q =
      V₀.innerProduct p.1 q.1 + V₁.innerProduct p.2 q.2 := by
  rfl

/-- For any `V` and `v : V.carrier`, `V.innerProduct 0 v = 0`. Bilinearity
    of `V.innerProduct` (left zero). -/
private theorem HSpace.innerProduct_zero_left (V : HSpace) (v : V.carrier) :
    V.innerProduct 0 v = 0 := by simp

/-- For any `V` and `v : V.carrier`, `V.innerProduct v 0 = 0`. Bilinearity
    of `V.innerProduct` (right zero). -/
private theorem HSpace.innerProduct_zero_right (V : HSpace) (v : V.carrier) :
    V.innerProduct v 0 = 0 := by simp

theorem IsListBasis.dsum_orthonormal {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (h₀ : ∀ i j : Fin vs₀.length,
            V₀.innerProduct (vs₀.get i) (vs₀.get j) = if i = j then 1 else 0)
    (h₁ : ∀ i j : Fin vs₁.length,
            V₁.innerProduct (vs₁.get i) (vs₁.get j) = if i = j then 1 else 0)
    (i j : Fin (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).length) :
    (HSpace.dsum V₀ V₁).innerProduct
        ((HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).get i)
        ((HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).get j) =
      if i = j then 1 else 0 := by
  -- Length of the combined list.
  have hlen : (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).length = vs₀.length + vs₁.length :=
    HSpace.dsumOfLists_length vs₀ vs₁
  -- `get` on the left half: returns `(vs₀.get k', 0)`.
  have h_get_left :
      ∀ (k : Fin (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).length) (hk : k.1 < vs₀.length),
        (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).get k =
          (vs₀.get ⟨k.1, hk⟩, (0 : V₁.carrier)) := by
    intro k hk
    have h_in_left : k.1 < (vs₀.map (LinearMap.inl ℝ V₀.carrier V₁.carrier)).length := by
      simp [hk]
    have step1 :
        (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).get k =
          (vs₀.map (LinearMap.inl ℝ V₀.carrier V₁.carrier)).get
            ⟨k.1, h_in_left⟩ := by
      simp [HSpace.dsumOfLists, List.get_eq_getElem,
            List.getElem_append_left, hk]
    rw [step1]
    simp [List.get_eq_getElem, List.getElem_map, LinearMap.inl_apply]
  -- `get` on the right half: returns `(0, vs₁.get k')`.
  have h_get_right :
      ∀ (k : Fin (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).length) (hk : vs₀.length ≤ k.1),
        ∀ (hk_sub : k.1 - vs₀.length < vs₁.length),
          (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).get k =
            ((0 : V₀.carrier), vs₁.get ⟨k.1 - vs₀.length, hk_sub⟩) := by
    intro k hk hk_sub
    have step1 :
        (HSpace.dsumOfLists V₀ V₁ vs₀ vs₁).get k =
          (vs₁.map (LinearMap.inr ℝ V₀.carrier V₁.carrier)).get
            ⟨k.1 - vs₀.length, by simp [hk_sub]⟩ := by
      simp [HSpace.dsumOfLists, List.get_eq_getElem,
            List.getElem_append_right (show vs₀.length ≤ k.1 from hk),
            List.length_map, hk]
    rw [step1]
    simp [List.get_eq_getElem, List.getElem_map, LinearMap.inr_apply]
  -- Case-split on which half `i` and `j` belong to.
  rcases Nat.lt_or_ge i.1 vs₀.length with hi | hi
  · rcases Nat.lt_or_ge j.1 vs₀.length with hj | hj
    · -- Both in left half: reduces to `V₀.innerProduct (vs₀.get _) (vs₀.get _)`.
      rw [h_get_left i hi, h_get_left j hj, HSpace.dsum_innerProduct_apply]
      have h_zero : V₁.innerProduct 0 0 = 0 :=
        HSpace.innerProduct_zero_left V₁ 0
      rw [h_zero, add_zero]
      set hi' : Fin vs₀.length := ⟨i.1, hi⟩ with hi'_def
      set hj' : Fin vs₀.length := ⟨j.1, hj⟩ with hj'_def
      have h_ip : V₀.innerProduct (vs₀.get hi') (vs₀.get hj') =
                    if hi' = hj' then 1 else 0 := h₀ hi' hj'
      -- Bridge `i = j` (in Fin (dsum.length)) to `hi' = hj'` (in Fin vs₀.length).
      have h_iff : (i = j) ↔ (hi' = hj') := by
        constructor
        · intro h
          have : i.1 = j.1 := congrArg Fin.val h
          exact Fin.ext this
        · intro h
          have : hi'.1 = hj'.1 := congrArg Fin.val h
          show i = j
          exact Fin.ext this
      by_cases h_eq : i = j
      · rw [if_pos h_eq, if_pos (h_iff.mp h_eq)] at *
        exact h_ip
      · rw [if_neg h_eq, if_neg (fun heq => h_eq (h_iff.mpr heq))] at *
        exact h_ip
    · -- i in left, j in right: mixed product.
      rw [h_get_left i hi, HSpace.dsum_innerProduct_apply]
      have hj_sub : j.1 - vs₀.length < vs₁.length := by
        have hj_total : j.1 < vs₀.length + vs₁.length := by
          rw [← hlen]; exact j.isLt
        omega
      rw [h_get_right j hj hj_sub]
      rw [HSpace.innerProduct_zero_right V₀ _, HSpace.innerProduct_zero_left V₁ _,
          add_zero]
      have h_neq : i ≠ j := by
        intro heq
        have : i.1 = j.1 := Fin.val_eq_of_eq heq
        omega
      rw [if_neg h_neq]
  · -- i in right half.
    have hi_sub : i.1 - vs₀.length < vs₁.length := by
      have hi_total : i.1 < vs₀.length + vs₁.length := by
        rw [← hlen]; exact i.isLt
      omega
    rcases Nat.lt_or_ge j.1 vs₀.length with hj | hj
    · -- i in right, j in left: mixed product.
      rw [h_get_right i hi hi_sub, h_get_left j hj, HSpace.dsum_innerProduct_apply]
      rw [HSpace.innerProduct_zero_left V₀ _, HSpace.innerProduct_zero_right V₁ _,
          add_zero]
      have h_neq : i ≠ j := by
        intro heq
        have : i.1 = j.1 := Fin.val_eq_of_eq heq
        omega
      rw [if_neg h_neq]
    · -- Both in right half.
      have hj_sub : j.1 - vs₀.length < vs₁.length := by
        have hj_total : j.1 < vs₀.length + vs₁.length := by
          rw [← hlen]; exact j.isLt
        omega
      rw [h_get_right i hi hi_sub, h_get_right j hj hj_sub,
          HSpace.dsum_innerProduct_apply]
      have h_zero : V₀.innerProduct 0 0 = 0 :=
        HSpace.innerProduct_zero_left V₀ 0
      rw [h_zero, zero_add]
      set hi' : Fin vs₁.length := ⟨i.1 - vs₀.length, hi_sub⟩ with hi'_def
      set hj' : Fin vs₁.length := ⟨j.1 - vs₀.length, hj_sub⟩ with hj'_def
      have h_ip : V₁.innerProduct (vs₁.get hi') (vs₁.get hj') =
                    if hi' = hj' then 1 else 0 := h₁ hi' hj'
      have h_iff : (i = j) ↔ (hi' = hj') := by
        constructor
        · intro h
          have : i.1 = j.1 := congrArg Fin.val h
          apply Fin.ext
          show i.1 - vs₀.length = j.1 - vs₀.length
          omega
        · intro h
          have : hi'.1 = hj'.1 := congrArg Fin.val h
          show i = j
          apply Fin.ext
          have : i.1 - vs₀.length = j.1 - vs₀.length := this
          omega
      by_cases h_eq : i = j
      · rw [if_pos h_eq, if_pos (h_iff.mp h_eq)] at *
        exact h_ip
      · rw [if_neg h_eq, if_neg (fun heq => h_eq (h_iff.mpr heq))] at *
        exact h_ip

namespace HSpace

variable {V₀ V₁ : HSpace} (f : V₀.carrier →ₗ[ℝ] V₁.carrier)

/-- **Fact (a) (injectivity).** `f` restricted to the subtype of
    `orthRel V₀.IP (ker f)` is injective.

    Proof: `inj` ↔ `ker = ⊥`. An element `w` of the restricted subtype
    with `f w.val = 0` satisfies `w.val ∈ orthRel V₀.IP (ker f)` (by
    `w.property`) AND `w.val ∈ ker f` (since `f w.val = 0`). By
    `orthRel_inf_eq_bot`, `w.val = 0`, hence `w = 0`. -/
theorem f_inj_on_kerOrth :
    Function.Injective (f ∘ₗ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)).subtype) := by
  rw [← LinearMap.ker_eq_bot]
  rw [eq_bot_iff]
  intro w hw
  -- hw : w ∈ ker (f ∘ₗ K.subtype), i.e. f (w.val) = 0.
  have hw_val_in_ker : (w : V₀.carrier) ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    have h_eq : (f ∘ₗ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)).subtype) w
              = f (w : V₀.carrier) := by
      simp [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [← h_eq]
    exact LinearMap.mem_ker.mp hw
  have hw_val_in_orth : (w : V₀.carrier) ∈ Submodule.orthRel V₀.innerProduct (LinearMap.ker f) :=
    w.property

  have h_val_zero : (w : V₀.carrier) = 0 := by
    have h_inf : (w : V₀.carrier) ∈
        Submodule.orthRel V₀.innerProduct (LinearMap.ker f) ⊓ LinearMap.ker f := by
      rw [Submodule.mem_inf]
      exact ⟨hw_val_in_orth, hw_val_in_ker⟩
    rw [orthRel_inf_eq_bot V₀ (LinearMap.ker f), Submodule.mem_bot] at h_inf
    exact h_inf
  apply Subtype.ext
  exact h_val_zero

/-- **Fact (b) (surjectivity).** Every `y ∈ range f` lifts to some
    `w ∈ orthRel V₀.IP (ker f)` with `f w = y`.

    Proof: lift `y` to `x ∈ V₀` with `f x = y`. Decompose `x = a + b`
    via Mathlib's `K ⊕ Kᗮ = ⊤` decomposition for `K := ker f` under the
    IPS instance derived from `V₀.innerIsIP`. Then `f a = 0` and
    `f b = y`. `b ∈ Kᗮ_Mathlib`; the OrthRelBridge says this means
    `b ∈ orthRel V₀.IP (ker f)`. -/
theorem f_surj_on_kerOrth :
    ∀ y : LinearMap.range f, ∃ w : Submodule.orthRel V₀.innerProduct (LinearMap.ker f),
      f (w : V₀.carrier) = (y : V₁.carrier) := by
  intro y
  obtain ⟨x, hxy⟩ := y.property
  -- Open IPS instance on V₀.carrier for Mathlib's K ⊕ Kᗮ decomposition.
  letI core₀ : InnerProductSpace.Core ℝ V₀.carrier := V₀.innerIsIP.toIPSCore
  letI nag₀ : NormedAddCommGroup V₀.carrier :=
    InnerProductSpace.Core.toNormedAddCommGroup (cd := core₀)
  letI ips₀ : InnerProductSpace ℝ V₀.carrier := InnerProductSpace.ofCore inferInstance
  -- Decompose x = a + b with a ∈ ker f, b ∈ (ker f)ᗮ_Mathlib.
  have hsup : LinearMap.ker f ⊔ (LinearMap.ker f)ᗮ = ⊤ :=
    Submodule.sup_orthogonal_of_hasOrthogonalProjection
  have hxmem : x ∈ LinearMap.ker f ⊔ (LinearMap.ker f)ᗮ := by
    rw [hsup]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxmem
  -- b ∈ Kᗮ_Mathlib ↔ b ∈ orthRel V₀.IP (ker f) (via the bridge).
  have hb_in_orth : b ∈ Submodule.orthRel V₀.innerProduct (LinearMap.ker f) := by
    rw [HSpace.mem_orthRel_innerProduct_iff]
    intro u hu
    -- u ∈ ker f, b ∈ Kᗮ_Mathlib. Need V₀.innerProduct u b = 0.
    -- Under the IPS instance, @inner ℝ _ _ u b = V₀.innerProduct u b
    -- definitionally (since core₀.inner := V₀.innerProduct).
    have h_inner : @inner ℝ V₀.carrier _ u b = 0 :=
      Submodule.inner_right_of_mem_orthogonal hu hb
    exact h_inner
  refine ⟨⟨b, hb_in_orth⟩, ?_⟩
  -- f b = y: from f a = 0 and f (a + b) = f x = y.
  have hfa : f a = 0 := LinearMap.mem_ker.mp ha
  have hfb : f b = (y : V₁.carrier) := by
    have h_sum : f a + f b = f x := by
      rw [← LinearMap.map_add, hab]
    rw [hfa, zero_add] at h_sum
    rw [h_sum]
    exact hxy
  exact hfb

/-- **Bijection on the restricted spaces.** Bundle `f_inj_on_kerOrth` and
    `f_surj_on_kerOrth` into a linear equivalence
    `(orthRel V₀.IP (ker f)) ≃ₗ[ℝ] range f`. -/
noncomputable def f_kerOrth_equiv_range :
    (Submodule.orthRel V₀.innerProduct (LinearMap.ker f) : Submodule ℝ V₀.carrier) ≃ₗ[ℝ]
      (LinearMap.range f : Submodule ℝ V₁.carrier) :=
  let f_restr : (Submodule.orthRel V₀.innerProduct (LinearMap.ker f) : Submodule ℝ V₀.carrier)
                  →ₗ[ℝ] (LinearMap.range f : Submodule ℝ V₁.carrier) :=
    LinearMap.codRestrict (LinearMap.range f)
      (f ∘ₗ (Submodule.orthRel V₀.innerProduct (LinearMap.ker f)).subtype)
      (fun ⟨x, _⟩ => ⟨x, rfl⟩)
  have inj : Function.Injective f_restr := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ heq
    apply Subtype.ext
    have hfeq : f x = f y := by
      have := congrArg Subtype.val heq
      simpa [f_restr] using this
    -- We need to show x = y, knowing f x = f y and both x, y ∈ orthRel(ker f).
    -- Equivalently, x - y ∈ orthRel(ker f) ∩ ker f = {0}.
    have hsub_in_ker : x - y ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, hfeq, sub_self]
    have hsub_in_orth : x - y ∈ Submodule.orthRel V₀.innerProduct (LinearMap.ker f) :=
      sub_mem hx hy
    have h_inf : x - y ∈
        Submodule.orthRel V₀.innerProduct (LinearMap.ker f) ⊓ LinearMap.ker f := by
      rw [Submodule.mem_inf]; exact ⟨hsub_in_orth, hsub_in_ker⟩
    rw [orthRel_inf_eq_bot V₀ (LinearMap.ker f), Submodule.mem_bot] at h_inf
    exact sub_eq_zero.mp h_inf
  have surj : Function.Surjective f_restr := by
    intro y
    obtain ⟨w, hw⟩ := f_surj_on_kerOrth f y
    refine ⟨w, ?_⟩
    apply Subtype.ext
    simpa [f_restr] using hw
  LinearEquiv.ofBijective f_restr ⟨inj, surj⟩

@[simp] theorem f_kerOrth_equiv_range_apply
    (w : Submodule.orthRel V₀.innerProduct (LinearMap.ker f)) :
    ((f_kerOrth_equiv_range f w : LinearMap.range f) : V₁.carrier) = f (w : V₀.carrier) := by
  rfl

end HSpace

/-! ## Image-list helper: `IsListBasis.image_of_inj_surj`.

Given an `IsListBasis (ofSubmodule V₀ K) vs` where `K = orthRel V₀.IP (ker f)`,
the image list under `f` is an `IsListBasis (ofSubmodule V₁ (range f))`. -/

/-- **Image-of-basis lemma (transported).** Maps an `IsListBasis (ofSubmodule V₀ K) vs`
    to an `IsListBasis (ofSubmodule V₁ (range f)) (vs.map (lift via f))` when `f`
    restricted to `K` is bijective onto `range f`. Realised via the
    `LinearEquiv (ofSubmodule V₀ K).carrier ≃ₗ (range f)` and
    `Module.Basis.map`. -/
theorem IsListBasis.image_of_inj_surj
    {V₀ V₁ : HSpace} (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    {vs : List (HSpace.ofSubmodule V₀
                  (Submodule.orthRel V₀.innerProduct (LinearMap.ker f))).carrier}
    (h_basis : IsListBasis (HSpace.ofSubmodule V₀
                  (Submodule.orthRel V₀.innerProduct (LinearMap.ker f))) vs) :
    IsListBasis (HSpace.ofSubmodule V₁ (LinearMap.range f))
      (vs.map fun w =>
        ⟨f (Subtype.val w), LinearMap.mem_range_self f _⟩) := by
  -- Strategy: rewrite the mapped list as `(List.finRange vs.length).map B_R`
  -- where `B_R := (h_basis.toBasis).map equiv` and `equiv` is the linear
  -- equivalence `(orthRel V₀.IP (ker f)) ≃ₗ range f`. Then `IsListBasis.of_basis_fin`
  -- discharges.
  -- The `LinearEquiv (orthRel V₀.IP (ker f)) ≃ₗ range f` underlies the construction.
  let equiv := HSpace.f_kerOrth_equiv_range f
  -- Mathlib basis on (ofSubmodule V₀ (orthRel V₀.IP (ker f))).carrier via the IH.
  let B_K : Module.Basis (Fin vs.length) ℝ
              (HSpace.ofSubmodule V₀
                (Submodule.orthRel V₀.innerProduct (LinearMap.ker f))).carrier :=
    h_basis.toBasis
  -- Push it through `equiv` to a basis on `(ofSubmodule V₁ (range f)).carrier`.
  -- Note: `(ofSubmodule V₀ K).carrier` is definitionally `K`'s subtype, same for V₁.
  let B_R : Module.Basis (Fin vs.length) ℝ
              (HSpace.ofSubmodule V₁ (LinearMap.range f)).carrier :=
    B_K.map equiv
  -- Show the image-list equals `(List.finRange vs.length).map B_R`.
  have h_target_eq : (vs.map fun w =>
                        (⟨f (Subtype.val w), LinearMap.mem_range_self f _⟩ :
                          (HSpace.ofSubmodule V₁ (LinearMap.range f)).carrier)) =
                     (List.finRange vs.length).map B_R := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      -- LHS: (vs.map _)[i] = ⟨f (vs[i]).val, _⟩
      -- RHS: ((List.finRange n).map B_R)[i] = B_R ⟨i, _⟩
      have hi_vs : i < vs.length := by simpa using hi1
      simp only [List.getElem_map, List.getElem_finRange]
      -- B_R ⟨i, _⟩ = equiv (B_K ⟨i, _⟩) (by Module.Basis.map_apply)
      --           = equiv (vs.get ⟨i, _⟩) (by IsListBasis.toBasis_apply)
      have h_BK : B_K ⟨i, hi_vs⟩ = vs.get ⟨i, hi_vs⟩ :=
        IsListBasis.toBasis_apply h_basis ⟨i, hi_vs⟩
      have h_BR : B_R ⟨i, hi_vs⟩ = equiv (B_K ⟨i, hi_vs⟩) :=
        Module.Basis.map_apply B_K equiv ⟨i, hi_vs⟩
      -- Make the RHS index match definitionally
      show (⟨f (vs[i]'hi_vs).val, _⟩ : (HSpace.ofSubmodule V₁ (LinearMap.range f)).carrier)
            = B_R ⟨i, hi_vs⟩
      rw [h_BR, h_BK]

      apply Subtype.ext
      -- After Subtype.ext: f (vs[i]).val = (equiv (vs.get ⟨i, hi_vs⟩)).val
      show f (vs[i]'hi_vs).val = (equiv (vs.get ⟨i, hi_vs⟩) : V₁.carrier)
      rw [HSpace.f_kerOrth_equiv_range_apply f]
      -- Goal: f (vs[i]).val = f (vs.get ⟨i, hi_vs⟩).val.
      -- vs[i] = vs.get ⟨i, hi_vs⟩ by List.get_eq_getElem (rfl).
      rfl
  rw [h_target_eq]
  -- Apply `IsListBasis.of_basis_fin B_R` to get the final basis.
  exact IsListBasis.of_basis_fin (V := HSpace.ofSubmodule V₁ (LinearMap.range f)) B_R

/-! ### `liftToSubmodule` reduction when all elements lie in `K`

When every element of `vs` lies in `K`, `HSpace.liftToSubmodule K vs`
is `vs` paired with the membership proofs (a `pmap`-style packing).
Concretely, length is preserved and `get i = ⟨vs.get i', h_subset _⟩`
for the index aligned via the length equation. We package this as
a *length equality* and a *pointwise equation*; together they let
us transport LI/span between the lifted and unlifted versions. -/

/-- Internal helper: `liftToSubmodule K (v :: vs')` reduces to
    `⟨v, hv⟩ :: liftToSubmodule K vs'` when `v ∈ K`. -/
private theorem HSpace.liftToSubmodule_cons_of_mem
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Submodule ℝ V) (v : V) (vs' : List V) (hv : v ∈ K) :
    HSpace.liftToSubmodule K (v :: vs') =
      ⟨v, hv⟩ :: HSpace.liftToSubmodule K vs' := by
  unfold HSpace.liftToSubmodule
  simp only [List.filterMap_cons]
  -- The `if-then-else` packed in a Classical.dec evaluates to `some ⟨v,hv⟩`.
  have h_branch : (haveI := Classical.dec (v ∈ K)
                   if h : v ∈ K then some (⟨v, h⟩ : K) else none) =
                  some ⟨v, hv⟩ := by
    haveI := Classical.dec (v ∈ K)
    simp [hv]
  rw [h_branch]

/-- The lifted list has the same length as the original (no drops). -/
theorem HSpace.liftToSubmodule_length_of_subset
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Submodule ℝ V) (vs : List V) (h_sub : ∀ v ∈ vs, v ∈ K) :
    (HSpace.liftToSubmodule K vs).length = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs' ih =>
      have hv : v ∈ K := h_sub v List.mem_cons_self
      have h_sub' : ∀ w ∈ vs', w ∈ K :=
        fun w hw => h_sub w (List.mem_cons_of_mem v hw)
      rw [HSpace.liftToSubmodule_cons_of_mem K v vs' hv]
      simp [ih h_sub']

/-- The lifted list equals `vs.pmap (fun v h => ⟨v, h⟩)` when all
    elements are in `K`. We state it as a list equality (which then
    gives length + pointwise equality "for free"). -/
theorem HSpace.liftToSubmodule_eq_pmap_of_subset
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Submodule ℝ V) (vs : List V) (h_sub : ∀ v ∈ vs, v ∈ K) :
    HSpace.liftToSubmodule K vs =
      vs.pmap (fun v h => (⟨v, h⟩ : K)) h_sub := by
  induction vs with
  | nil =>
      simp [HSpace.liftToSubmodule]
  | cons v vs' ih =>
      have hv : v ∈ K := h_sub v List.mem_cons_self
      have h_sub' : ∀ w ∈ vs', w ∈ K :=
        fun w hw => h_sub w (List.mem_cons_of_mem v hw)
      rw [HSpace.liftToSubmodule_cons_of_mem K v vs' hv]
      rw [ih h_sub']
      simp [List.pmap]

/-- The lifted list's underlying values match `vs` pointwise. -/
theorem HSpace.liftToSubmodule_get_val_of_subset
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Submodule ℝ V) (vs : List V) (h_sub : ∀ v ∈ vs, v ∈ K)
    (i : Fin (HSpace.liftToSubmodule K vs).length) :
    ((HSpace.liftToSubmodule K vs).get i : V) =
      vs.get ⟨i.1, by
        have := HSpace.liftToSubmodule_length_of_subset K vs h_sub
        omega⟩ := by
  -- Use the pmap form: get on pmap is ⟨get i, h_subset⟩.
  have h_eq := HSpace.liftToSubmodule_eq_pmap_of_subset K vs h_sub
  -- Bypass the motive-not-type-correct issue by using getElem? values.
  have hlen : (HSpace.liftToSubmodule K vs).length = vs.length :=
    HSpace.liftToSubmodule_length_of_subset K vs h_sub
  -- Extract the index range constraint on `vs` via hlen.
  have hi : i.1 < vs.length := hlen ▸ i.isLt
  -- Take `get` of LHS using the explicit list-equation `h_eq` reduced to getElem.
  show ((HSpace.liftToSubmodule K vs).get i : V) = vs.get ⟨i.1, hi⟩
  rw [List.get_eq_getElem, List.get_eq_getElem]
  show ((HSpace.liftToSubmodule K vs)[i.1]'i.isLt : V) = vs[i.1]'hi
  -- Substitute the LHS via h_eq using HEq logic.
  congr 1
  -- Use Subtype.ext: ↑(pmap.getElem) = vs.getElem.
  -- We need to evaluate `(HSpace.liftToSubmodule K vs)[i.1]` via h_eq.
  have h_get_val :
      ((HSpace.liftToSubmodule K vs)[i.1]'i.isLt : V) = vs[i.1]'hi := by
    have : (HSpace.liftToSubmodule K vs)[i.1]'i.isLt =
           (vs.pmap (fun v h => (⟨v, h⟩ : K)) h_sub)[i.1]'(by
             rw [List.length_pmap]; exact hi) := by
      -- The two lists are equal, so getElem at the same index is equal.
      rw [List.getElem_of_eq h_eq]
    rw [this, List.getElem_pmap]

  exact h_get_val

/-! ### LI + length = finrank ⇒ `IsListBasis` -/

/-- **LI + length-equals-dim ⇒ basis.** If `V.carrier` is
    finite-dimensional, `vs : List V.carrier` is linearly independent
    (over ℝ) and its length equals the finite-rank of `V.carrier`,
    then `vs` is a basis of `V` (in our `IsListBasis` sense). We use
    Mathlib's `LinearIndependent.span_eq_top_of_card_eq_finrank'` to
    derive the span condition directly, avoiding the need to handle
    the empty / non-empty cases separately. -/
theorem IsListBasis.of_li_and_finrank (V : HSpace) (vs : List V.carrier)
    [FiniteDimensional ℝ V.carrier]
    (h_li : LinearIndependent ℝ (fun i : Fin vs.length => vs.get i))
    (h_dim : vs.length = Module.finrank ℝ V.carrier) :
    IsListBasis V vs := by
  refine ⟨h_li, ?_⟩
  -- LinearIndependent.span_eq_top_of_card_eq_finrank' works for any
  -- `Fintype ι` (no `Nonempty` hypothesis).
  have h_card_eq : Fintype.card (Fin vs.length) = Module.finrank ℝ V.carrier := by
    simp [h_dim]
  exact h_li.span_eq_top_of_card_eq_finrank' h_card_eq

/-- **Tensor-IP bridge.** The inner product on `HSpace.tprod V₀ V₁`
    (which is `LinearMap.BilinForm.tmul V₀.IP V₁.IP`) coincides on the
    tensor-product carrier with Mathlib's canonical tensor inner product
    (built from the IPS bridges on V₀ and V₁).

    Proof structure mirrors the `h_bridge` step in
    `HSpace.tprod`'s `innerIsIP` field: bilinearity reduces both sides
    to pure-tensor cases, where `BilinForm.tmul` equates to
    `V₀.IP a c * V₁.IP b d`, which is precisely Mathlib's `inner_tmul`. -/
theorem HSpace.tprod_inner_eq (V₀ V₁ : HSpace)
    (x y : V₀.carrier ⊗[ℝ] V₁.carrier) :
    letI _ := V₀.innerIsIP.toIPSCore
    letI _ := V₁.innerIsIP.toIPSCore
    letI _ : NormedAddCommGroup V₀.carrier :=
      (V₀.innerIsIP.toIPSCore).toNormedAddCommGroup
    letI _ : NormedAddCommGroup V₁.carrier :=
      (V₁.innerIsIP.toIPSCore).toNormedAddCommGroup
    letI _ : InnerProductSpace ℝ V₀.carrier :=
      InnerProductSpace.ofCore inferInstance
    letI _ : InnerProductSpace ℝ V₁.carrier :=
      InnerProductSpace.ofCore inferInstance
    (HSpace.tprod V₀ V₁).innerProduct x y =
      @inner ℝ (V₀.carrier ⊗[ℝ] V₁.carrier) _ x y := by
  letI _ := V₀.innerIsIP.toIPSCore
  letI _ := V₁.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V₀.carrier :=
    (V₀.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : NormedAddCommGroup V₁.carrier :=
    (V₁.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V₀.carrier :=
    InnerProductSpace.ofCore inferInstance
  letI _ : InnerProductSpace ℝ V₁.carrier :=
    InnerProductSpace.ofCore inferInstance
  show LinearMap.BilinForm.tmul V₀.innerProduct V₁.innerProduct x y = _
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      -- LHS via BilinForm.tmul: `V₁.IP b d * V₀.IP a c`.
      -- RHS via `inner_tmul` Mathlib lemma: `inner a c * inner b d`.
      -- `V₀.IP a c = @inner ℝ V₀.carrier _ a c` by rfl (the IPS bridge).
      show V₁.innerProduct b d * V₀.innerProduct a c =
        @inner ℝ (V₀.carrier ⊗[ℝ] V₁.carrier) _ (a ⊗ₜ b) (c ⊗ₜ d)
      rw [TensorProduct.inner_tmul]
      show V₁.innerProduct b d * V₀.innerProduct a c =
        V₀.innerProduct a c * V₁.innerProduct b d
      ring
    | add y₁ y₂ ih₁ ih₂ =>
      rw [map_add (LinearMap.BilinForm.tmul V₀.innerProduct V₁.innerProduct _),
          ih₁, ih₂, inner_add_right]
  | add x₁ x₂ ih₁ ih₂ =>
    rw [show ((LinearMap.BilinForm.tmul V₀.innerProduct V₁.innerProduct) (x₁ + x₂)) y
            = ((LinearMap.BilinForm.tmul V₀.innerProduct V₁.innerProduct) x₁) y
              + ((LinearMap.BilinForm.tmul V₀.innerProduct V₁.innerProduct) x₂) y from by
          rw [map_add (LinearMap.BilinForm.tmul V₀.innerProduct V₁.innerProduct) x₁ x₂,
              LinearMap.add_apply], ih₁, ih₂, inner_add_left]

/-- **Pure-tensor orthonormality (Mathlib-side).** If the families
    `vs₀.get` and `vs₁.get` are Mathlib-orthonormal under V₀'s and V₁'s
    IPS-bridge inners, then the family `(i, j) ↦ vs₀.get i ⊗ₜ vs₁.get j`
    is Mathlib-orthonormal under the tensor IPS inner. Direct from
    `Orthonormal.tmul`. -/
theorem HSpace.tprodOfLists_orthonormal_mathlib (V₀ V₁ : HSpace)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier)
    (h₀ : letI _ := V₀.innerIsIP.toIPSCore
          letI _ : NormedAddCommGroup V₀.carrier :=
            (V₀.innerIsIP.toIPSCore).toNormedAddCommGroup
          letI _ : InnerProductSpace ℝ V₀.carrier :=
            InnerProductSpace.ofCore inferInstance
          Orthonormal ℝ (fun i : Fin vs₀.length => vs₀.get i))
    (h₁ : letI _ := V₁.innerIsIP.toIPSCore
          letI _ : NormedAddCommGroup V₁.carrier :=
            (V₁.innerIsIP.toIPSCore).toNormedAddCommGroup
          letI _ : InnerProductSpace ℝ V₁.carrier :=
            InnerProductSpace.ofCore inferInstance
          Orthonormal ℝ (fun j : Fin vs₁.length => vs₁.get j)) :
    letI _ := V₀.innerIsIP.toIPSCore
    letI _ := V₁.innerIsIP.toIPSCore
    letI _ : NormedAddCommGroup V₀.carrier :=
      (V₀.innerIsIP.toIPSCore).toNormedAddCommGroup
    letI _ : NormedAddCommGroup V₁.carrier :=
      (V₁.innerIsIP.toIPSCore).toNormedAddCommGroup
    letI _ : InnerProductSpace ℝ V₀.carrier :=
      InnerProductSpace.ofCore inferInstance
    letI _ : InnerProductSpace ℝ V₁.carrier :=
      InnerProductSpace.ofCore inferInstance
    Orthonormal ℝ
      (fun p : Fin vs₀.length × Fin vs₁.length =>
        vs₀.get p.1 ⊗ₜ[ℝ] vs₁.get p.2) := by
  letI _ := V₀.innerIsIP.toIPSCore
  letI _ := V₁.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V₀.carrier :=
    (V₀.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : NormedAddCommGroup V₁.carrier :=
    (V₁.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V₀.carrier :=
    InnerProductSpace.ofCore inferInstance
  letI _ : InnerProductSpace ℝ V₁.carrier :=
    InnerProductSpace.ofCore inferInstance
  exact h₀.tmul h₁

/-- **Main per-case helper.** If both input lists are orthonormal in
    the `V.innerProduct = if i = j then 1 else 0` sense, then their
    tensor-product list `tprodOfLists` is orthonormal in the same sense
    under the canonical tensor IP `(HSpace.tprod V₀ V₁).innerProduct`. -/
theorem IsListBasis.tprod_orthonormal {V₀ V₁ : HSpace}
    {vs₀ : List V₀.carrier} {vs₁ : List V₁.carrier}
    (h₀ : ∀ i j : Fin vs₀.length,
      V₀.innerProduct (vs₀.get i) (vs₀.get j) = if i = j then 1 else 0)
    (h₁ : ∀ i j : Fin vs₁.length,
      V₁.innerProduct (vs₁.get i) (vs₁.get j) = if i = j then 1 else 0) :
    ∀ i j : Fin (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).length,
      (HSpace.tprod V₀ V₁).innerProduct
          ((HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).get i)
          ((HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).get j) = if i = j then 1 else 0 := by
  -- Lift hypotheses to Mathlib `Orthonormal`.
  letI _ := V₀.innerIsIP.toIPSCore
  letI _ := V₁.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V₀.carrier :=
    (V₀.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : NormedAddCommGroup V₁.carrier :=
    (V₁.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V₀.carrier :=
    InnerProductSpace.ofCore inferInstance
  letI _ : InnerProductSpace ℝ V₁.carrier :=
    InnerProductSpace.ofCore inferInstance
  have h₀_orth : Orthonormal ℝ (fun i : Fin vs₀.length => vs₀.get i) :=
    (V₀.orthonormal_iff_innerProduct (fun i => vs₀.get i)).mpr h₀
  have h₁_orth : Orthonormal ℝ (fun j : Fin vs₁.length => vs₁.get j) :=
    (V₁.orthonormal_iff_innerProduct (fun j => vs₁.get j)).mpr h₁
  -- Pure-tensor orthonormality on `Fin vs₀.length × Fin vs₁.length`.
  have h_tp_orth := HSpace.tprodOfLists_orthonormal_mathlib V₀ V₁ vs₀ vs₁ h₀_orth h₁_orth
  -- Bridge through the tprodOfLists reindex.
  -- Goal: `(HSpace.tprod V₀ V₁).innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0`.
  -- Step 1: rewrite indices via `tprodOfLists_getElem`.
  intro i j
  -- Length facts.
  have hlen : (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).length = vs₀.length * vs₁.length :=
    HSpace.tprodOfLists_length vs₀ vs₁
  -- Case on whether vs₁ is empty: if so, the goal is vacuous.
  by_cases hv₁_pos : 0 < vs₁.length
  · -- Express `vs.get i = vs₀.get _ ⊗ vs₁.get _` and ditto for j.
    have hi_total : i.1 < vs₀.length * vs₁.length := hlen ▸ i.isLt
    have hj_total : j.1 < vs₀.length * vs₁.length := hlen ▸ j.isLt
    have hi_eq := HSpace.tprodOfLists_getElem vs₀ vs₁ i.1 hi_total hv₁_pos
    have hj_eq := HSpace.tprodOfLists_getElem vs₀ vs₁ j.1 hj_total hv₁_pos
    -- Push goal into pure-tensor form.
    rw [List.get_eq_getElem, List.get_eq_getElem, hi_eq, hj_eq]

    rw [orthonormal_iff_ite] at h_tp_orth
    -- Specialise with the product indices.
    have hi_div : i.1 / vs₁.length < vs₀.length :=
      Nat.div_lt_iff_lt_mul hv₁_pos |>.mpr hi_total
    have hi_mod : i.1 % vs₁.length < vs₁.length := Nat.mod_lt _ hv₁_pos
    have hj_div : j.1 / vs₁.length < vs₀.length :=
      Nat.div_lt_iff_lt_mul hv₁_pos |>.mpr hj_total
    have hj_mod : j.1 % vs₁.length < vs₁.length := Nat.mod_lt _ hv₁_pos
    have h_inner := h_tp_orth
      (⟨i.1 / vs₁.length, hi_div⟩, ⟨i.1 % vs₁.length, hi_mod⟩)
      (⟨j.1 / vs₁.length, hj_div⟩, ⟨j.1 % vs₁.length, hj_mod⟩)
    -- LHS of h_inner is the Mathlib inner; bridge to tprod IP via `tprod_inner_eq`.
    -- `tprod_inner_eq` gives: `(tprod V₀ V₁).innerProduct x y = inner x y`.
    have h_lhs_eq :=
      HSpace.tprod_inner_eq V₀ V₁
        (vs₀.get ⟨i.1 / vs₁.length, hi_div⟩ ⊗ₜ[ℝ]
          vs₁.get ⟨i.1 % vs₁.length, hi_mod⟩)
        (vs₀.get ⟨j.1 / vs₁.length, hj_div⟩ ⊗ₜ[ℝ]
          vs₁.get ⟨j.1 % vs₁.length, hj_mod⟩)
    rw [← h_lhs_eq] at h_inner
    -- The product Fin pair equality decomposes into divmod equalities.
    -- Connect `(i_div, i_mod) = (j_div, j_mod)` to `i = j` (on Fin (n₀ * n₁)).
    have h_pair_iff :
        (⟨⟨i.1 / vs₁.length, hi_div⟩, ⟨i.1 % vs₁.length, hi_mod⟩⟩
            : Fin vs₀.length × Fin vs₁.length) =
          ⟨⟨j.1 / vs₁.length, hj_div⟩, ⟨j.1 % vs₁.length, hj_mod⟩⟩ ↔ i = j := by
      constructor
      · intro h
        apply Fin.ext
        have h₁₁ : i.1 / vs₁.length = j.1 / vs₁.length := by
          have := (Prod.mk.injEq _ _ _ _).mp h
          exact Fin.mk.inj this.1
        have h₂₂ : i.1 % vs₁.length = j.1 % vs₁.length := by
          have := (Prod.mk.injEq _ _ _ _).mp h
          exact Fin.mk.inj this.2
        -- Reconstruct i.1 = j.1 from div + mod equalities.
        have hi_decomp : i.1 = vs₁.length * (i.1 / vs₁.length) + i.1 % vs₁.length :=
          (Nat.div_add_mod i.1 vs₁.length).symm
        have hj_decomp : j.1 = vs₁.length * (j.1 / vs₁.length) + j.1 % vs₁.length :=
          (Nat.div_add_mod j.1 vs₁.length).symm
        rw [hi_decomp, hj_decomp, h₁₁, h₂₂]
      · intro h
        subst h
        rfl
    -- Massage h_inner's conditional via h_pair_iff. The if's `Decidable`
    -- instance depends on the LHS so `rw` fails motive-check; use `simp`
    -- with the iff explicitly (which handles the propositional rewrite).
    have h_inner' :
        (HSpace.tprod V₀ V₁).innerProduct
            (vs₀.get ⟨i.1 / vs₁.length, hi_div⟩ ⊗ₜ[ℝ]
              vs₁.get ⟨i.1 % vs₁.length, hi_mod⟩)
            (vs₀.get ⟨j.1 / vs₁.length, hj_div⟩ ⊗ₜ[ℝ]
              vs₁.get ⟨j.1 % vs₁.length, hj_mod⟩) =
          if i = j then (1 : ℝ) else 0 := by
      rw [h_inner]
      -- Both `if` conditions are propositionally equivalent by h_pair_iff.
      by_cases hij : i = j
      · -- Pair-equal direction.
        have hpair : (⟨⟨i.1 / vs₁.length, hi_div⟩,
                       ⟨i.1 % vs₁.length, hi_mod⟩⟩
                        : Fin vs₀.length × Fin vs₁.length) =
                     ⟨⟨j.1 / vs₁.length, hj_div⟩,
                       ⟨j.1 % vs₁.length, hj_mod⟩⟩ := h_pair_iff.mpr hij
        simp [hij, hpair]
      · -- Pair-unequal direction: if the pair were equal, then i = j.
        have hpair : (⟨⟨i.1 / vs₁.length, hi_div⟩,
                       ⟨i.1 % vs₁.length, hi_mod⟩⟩
                        : Fin vs₀.length × Fin vs₁.length) ≠
                     ⟨⟨j.1 / vs₁.length, hj_div⟩,
                       ⟨j.1 % vs₁.length, hj_mod⟩⟩ := fun h => hij (h_pair_iff.mp h)
        simp [hij, hpair]
    -- Push h_inner''s `.get` form into `getElem` form to match the goal.
    simp only [List.get_eq_getElem] at h_inner'
    exact h_inner'
  · -- vs₁.length = 0: `tprodOfLists vs₀ vs₁` has length `vs₀.length * 0 = 0`,
    -- so the goal is vacuous (no `i, j` exist).
    push_neg at hv₁_pos
    have hv₁ : vs₁.length = 0 := Nat.le_zero.mp hv₁_pos
    have hlen0 : (HSpace.tprodOfLists V₀ V₁ vs₀ vs₁).length = 0 := by
      rw [hlen, hv₁, Nat.mul_zero]
    -- `i : Fin 0` is empty.
    have : i.1 < 0 := hlen0 ▸ i.isLt
    exact absurd this (Nat.not_lt_zero _)

/-! ## FSV-contract consumers (agent: proj) — Part 2: LI helpers

The `BasisFSV.fsv*_linearly_independent` helpers below derive linear
independence of the FSV output from its orthonormality (the
`fsv*_orthonormal` axiom), using Mathlib's `Orthonormal.linearIndependent`
through the `HSpace.orthonormal_iff_innerProduct` bridge. They are
the only LI-producing consumers of the FSV contract — every
per-shape obligation downstream goes through them. -/

/-- **FSV LI derivation (Left).** Orthonormal ⇒ linearly independent
    on the ambient carrier `V₀.carrier`. -/
theorem BasisFSV.fsvLeft_linearly_independent
    (V₀ V₁ : HSpace) (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (pred : ℝ → Bool)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    LinearIndependent ℝ
      (fun i : Fin (BasisFSV.fsvLeft V₀ V₁ f pred vs₀ vs₁).length =>
        (BasisFSV.fsvLeft V₀ V₁ f pred vs₀ vs₁).get i) := by
  set us := BasisFSV.fsvLeft V₀ V₁ f pred vs₀ vs₁ with hus
  have h_orth := BasisFSV.fsvLeft_orthonormal V₀ V₁ f pred vs₀ vs₁
  -- Promote V₀ to a Mathlib InnerProductSpace inline.
  letI _ := V₀.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V₀.carrier :=
    (V₀.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V₀.carrier :=
    InnerProductSpace.ofCore inferInstance
  have h_iff := V₀.orthonormal_iff_innerProduct
                  (fun i : Fin us.length => us.get i)
  exact (h_iff.mpr h_orth).linearIndependent

/-- **FSV LI derivation (Right).** Orthonormal ⇒ linearly independent
    on the ambient carrier `V₁.carrier`. -/
theorem BasisFSV.fsvRight_linearly_independent
    (V₀ V₁ : HSpace) (f : V₀.carrier →ₗ[ℝ] V₁.carrier)
    (pred : ℝ → Bool)
    (vs₀ : List V₀.carrier) (vs₁ : List V₁.carrier) :
    LinearIndependent ℝ
      (fun i : Fin (BasisFSV.fsvRight V₀ V₁ f pred vs₀ vs₁).length =>
        (BasisFSV.fsvRight V₀ V₁ f pred vs₀ vs₁).get i) := by
  set us := BasisFSV.fsvRight V₀ V₁ f pred vs₀ vs₁ with hus
  have h_orth := BasisFSV.fsvRight_orthonormal V₀ V₁ f pred vs₀ vs₁
  letI _ := V₁.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V₁.carrier :=
    (V₁.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V₁.carrier :=
    InnerProductSpace.ofCore inferInstance
  have h_iff := V₁.orthonormal_iff_innerProduct
                  (fun i : Fin us.length => us.get i)
  exact (h_iff.mpr h_orth).linearIndependent

/-! ### Generic FSV → IsListBasis bridge.

The four `.proj` per-shape obligations all follow the same pattern:
the FSV output, lifted into the appropriate submodule via
`HSpace.liftToSubmodule`, forms a basis of `HSpace.ofSubmodule V K`.
The hypotheses are: subset (every output vector is in `K`), LI (in
the ambient carrier), and dim (output length equals finrank of `K`).
We package this once as a general helper. -/

/-- **Generic FSV → IsListBasis bridge.** Given a list `raw` of vectors
    in the ambient `V.carrier` that (a) all lie in the submodule `K`,
    (b) are linearly independent on `V.carrier`, and (c) have length
    equal to `finrank ℝ K`, the lifted list `HSpace.liftToSubmodule K raw`
    is a basis of `HSpace.ofSubmodule V K`. -/
theorem IsListBasis.of_fsv_contract (V : HSpace) (K : Submodule ℝ V.carrier)
    (raw : List V.carrier)
    (h_subset : ∀ v ∈ raw, v ∈ K)
    (h_li : LinearIndependent ℝ (fun i : Fin raw.length => raw.get i))
    (h_dim : raw.length = Module.finrank ℝ K) :
    IsListBasis (HSpace.ofSubmodule V K) (HSpace.liftToSubmodule K raw) := by
  -- (HSpace.ofSubmodule V K).carrier = K as a Submodule subtype; FD is
  -- inherited from V.carrier being FD.
  have hlen : (HSpace.liftToSubmodule K raw).length = raw.length :=
    HSpace.liftToSubmodule_length_of_subset K raw h_subset
  -- Step 1: build the LI proof on K via the subtype injection.
  -- The composition K.subtype ∘ (fun i => (liftToSubmodule K raw).get i)
  -- equals (fun i => raw.get (cast i)) after `liftToSubmodule_get_val_of_subset`.
  have h_li_lifted :
      LinearIndependent ℝ
        (fun i : Fin (HSpace.liftToSubmodule K raw).length =>
          (HSpace.liftToSubmodule K raw).get i) := by
    -- Re-index raw's LI through Fin.cast hlen to land at Fin (lifted).length.
    have h_li_cast :
        LinearIndependent ℝ
          (fun i : Fin (HSpace.liftToSubmodule K raw).length =>
            raw.get ⟨i.1, hlen ▸ i.isLt⟩) := by
      -- `fun i => raw.get ⟨i.1, _⟩ = (fun j : Fin raw.length => raw.get j) ∘ Fin.cast hlen`
      have h_fun_eq :
          (fun i : Fin (HSpace.liftToSubmodule K raw).length =>
            raw.get ⟨i.1, hlen ▸ i.isLt⟩) =
          (fun j : Fin raw.length => raw.get j) ∘ Fin.cast hlen := by
        funext i; simp [Function.comp, Fin.cast]
      rw [h_fun_eq]
      exact h_li.comp _ (Fin.cast_injective hlen)
    -- Lift through `K.subtype` (injective): if `K.subtype ∘ g` is LI, then `g` is LI.
    have h_li_via_subtype :
        LinearIndependent ℝ
          ((K.subtype : K →ₗ[ℝ] V.carrier) ∘
            (fun i : Fin (HSpace.liftToSubmodule K raw).length =>
              (HSpace.liftToSubmodule K raw).get i)) := by
      -- The composition equals `fun i => ((liftToSubmodule K raw).get i).val`,
      -- which by `liftToSubmodule_get_val_of_subset` equals
      -- `fun i => raw.get ⟨i.1, _⟩`.
      have h_comp_eq :
          ((K.subtype : K →ₗ[ℝ] V.carrier) ∘
            (fun i : Fin (HSpace.liftToSubmodule K raw).length =>
              (HSpace.liftToSubmodule K raw).get i)) =
          (fun i : Fin (HSpace.liftToSubmodule K raw).length =>
            raw.get ⟨i.1, hlen ▸ i.isLt⟩) := by
        funext i
        simp [Function.comp, Submodule.subtype_apply]
        exact HSpace.liftToSubmodule_get_val_of_subset K raw h_subset i
      rw [h_comp_eq]
      exact h_li_cast

    exact h_li_via_subtype.of_comp _
  -- Step 2: combine with dim.
  have h_dim_lifted :
      (HSpace.liftToSubmodule K raw).length =
        Module.finrank ℝ (HSpace.ofSubmodule V K).carrier := by
    -- (HSpace.ofSubmodule V K).carrier = K (subtype), finrank matches.
    show (HSpace.liftToSubmodule K raw).length = Module.finrank ℝ K
    rw [hlen]; exact h_dim
  -- FD inheriited: V.carrier is FD ⇒ K (its submodule) is FD.
  haveI : FiniteDimensional ℝ (HSpace.ofSubmodule V K).carrier := V.fd.finiteDimensional_submodule K
  exact IsListBasis.of_li_and_finrank (HSpace.ofSubmodule V K)
          (HSpace.liftToSubmodule K raw) h_li_lifted h_dim_lifted

/-! ## Riesz / orthonormal-collapse helpers for `.dual`-arm orthonormality.

These helpers support the `.dual` arm of `stdBasis_orthonormal_space` in
`BasisSoundnessTodo.lean` (see `stdBasis_orthonormal_dual_step`). They
formalise the orthonormality collapse documented in `Basis.lean`'s
`HSpace.dualOfList` docstring: for an orthonormal `vs`, the Gram matrix
is `1`, so `gram⁻¹ = 1`, so `dualVec V vs i = V.innerProduct (vs.get i)`
(the Riesz musical). Combined with `rieszInv_innerProduct`
(`rieszInv (V.IP v) = v`), this delivers the dual-IP orthonormality. -/

namespace IsInnerProduct

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
variable {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (h : IsInnerProduct B)

/-- **Riesz inverse cancels the IP**: `h.rieszInv (B v) = v`. Follows from
    `rieszInv = (linearEquivOfInjective B _ _).symm.toLinearMap` and
    `LinearEquiv.symm_apply_apply`. -/
theorem rieszInv_innerProduct (v : V) : h.rieszInv (B v) = v := by
  unfold IsInnerProduct.rieszInv
  -- Goal: (linearEquivOfInjective B _ _).symm.toLinearMap (B v) = v.
  -- LinearEquiv.symm_apply_apply: e.symm (e v) = v.
  exact (LinearMap.linearEquivOfInjective B _ _).symm_apply_apply v

end IsInnerProduct

namespace HSpace

/-- **Riesz inverse cancels `V.innerProduct`**: `V.innerIsIP.rieszInv (V.IP v) = v`.
    HSpace-level wrapper around `IsInnerProduct.rieszInv_innerProduct`. -/
theorem rieszInv_innerProduct (V : HSpace) (v : V.carrier) :
    V.innerIsIP.rieszInv (V.innerProduct v) = v :=
  V.innerIsIP.rieszInv_innerProduct v

end HSpace

/-- **Gram = 1 for orthonormal input.** When `vs` is orthonormal w.r.t.
    `V.innerProduct`, the Gram matrix coincides with the identity. -/
theorem IsListBasis.gram_eq_one_of_orthonormal (V : HSpace) (vs : List V.carrier)
    (h_orth : ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0) :
    IsListBasis.gram V vs = 1 := by
  -- Both sides are matrices Fin n × Fin n → ℝ; show pointwise equality.
  ext i j
  show V.innerProduct (vs.get i) (vs.get j) = (1 : Matrix _ _ ℝ) i j
  rw [h_orth i j]
  by_cases hij : i = j
  · subst hij; simp [Matrix.one_apply_eq]
  · rw [Matrix.one_apply_ne hij]; simp [hij]

/-- **dualVec collapses to Riesz for orthonormal input.** When `vs` is
    orthonormal w.r.t. `V.IP`, `V.dualVec vs i = V.innerProduct (vs.get i)`.
    The Gram matrix is `1`, hence `gram⁻¹ = 1`, and the sum collapses to
    the single `k = i` term. -/
theorem HSpace.dualVec_of_orthonormal (V : HSpace) (vs : List V.carrier)
    (h_orth : ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0)
    (i : Fin vs.length) :
    V.dualVec vs i = V.innerProduct (vs.get i) := by
  unfold HSpace.dualVec
  have h_gram_eq_one : IsListBasis.gram V vs = 1 :=
    IsListBasis.gram_eq_one_of_orthonormal V vs h_orth
  rw [h_gram_eq_one, inv_one]
  -- Goal: Σ k, (1 : Matrix _ _ ℝ) i k • V.IP (vs.get k) = V.IP (vs.get i).
  -- `(1 : Matrix) i k = if i = k then 1 else 0`; sum collapses.
  rw [Finset.sum_eq_single i]
  · simp [Matrix.one_apply_eq]
  · intro k _ hki
    rw [Matrix.one_apply_ne (Ne.symm hki), zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- **Metric tensor resolution in an orthonormal list basis.** The intrinsic inner-product
tensor is the diagonal sum of the Gram-corrected dual basis covectors. This is the
coordinate-free algebraic content of the operational `inner_std` identity matrix. -/
theorem IsListBasis.innerTensor_atSpace_eq_sum_dual_tmul
    {V : HSpace} {vs : List V.carrier} (h : IsListBasis V vs)
    (horth : ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0) :
    (V.innerTensor V.innerProduct).atSpace (HSpace.tprod (HSpace.dual V) (HSpace.dual V)) =
      ∑ i : Fin vs.length, V.dualVec vs i ⊗ₜ[ℝ] V.dualVec vs i := by
  let t := (dualTensorHomEquiv ℝ V.carrier (Module.Dual ℝ V.carrier)).symm V.innerProduct
  have hinner : V.innerTensor V.innerProduct =
      .hil ⟨HSpace.tprod (HSpace.dual V) (HSpace.dual V), t⟩ := rfl
  have hat : (DVal.hil ⟨HSpace.tprod (HSpace.dual V) (HSpace.dual V), t⟩).atSpace
      (HSpace.tprod (HSpace.dual V) (HSpace.dual V)) = t := by
    unfold DVal.atSpace DVal.asHil
    simp
  rw [hinner, hat]
  dsimp only [t]
  rw [IsListBasis.dualTensorHomEquiv_symm_eq_sum
    (V := V) (W := HSpace.dual V) h V.innerProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [HSpace.dualVec_of_orthonormal V vs horth]

/-- Lifting a list that lies in a submodule preserves its orthonormality.  The
indices are transported across the fact that `liftToSubmodule` drops no elements
under the subset hypothesis.  This is the common semantic bridge for all four
FSV-backed standard projection bases (`ker`, `coker`, `img`, and `coimg`). -/
theorem HSpace.liftToSubmodule_orthonormal_of_subset
    (V : HSpace) (K : Submodule ℝ V.carrier) (vs : List V.carrier)
    (hsub : ∀ v ∈ vs, v ∈ K)
    (horth : ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0) :
    ∀ i j : Fin (HSpace.liftToSubmodule K vs).length,
      (HSpace.ofSubmodule V K).innerProduct
        ((HSpace.liftToSubmodule K vs).get i)
        ((HSpace.liftToSubmodule K vs).get j) = if i = j then 1 else 0 := by
  intro i j
  have hlen : (HSpace.liftToSubmodule K vs).length = vs.length :=
    HSpace.liftToSubmodule_length_of_subset K vs hsub
  let i' : Fin vs.length := ⟨i.1, hlen ▸ i.isLt⟩
  let j' : Fin vs.length := ⟨j.1, hlen ▸ j.isLt⟩
  show V.innerProduct
      ((HSpace.liftToSubmodule K vs).get i : V.carrier)
      ((HSpace.liftToSubmodule K vs).get j : V.carrier) = if i = j then 1 else 0
  rw [HSpace.liftToSubmodule_get_val_of_subset K vs hsub i,
      HSpace.liftToSubmodule_get_val_of_subset K vs hsub j,
      horth i' j']
  have heq : i' = j' ↔ i = j := by
    constructor
    · intro hij
      apply Fin.ext
      exact Fin.mk.inj hij
    · intro hij
      subst hij
      rfl
  by_cases hij : i = j
  · simp [hij, heq.mpr hij]
  · simp [hij, heq]

/-- **Orthonormality of `dualOfList` for orthonormal input.** Under the
    Riesz-pullback inner product on `HSpace.dual V` (i.e.
    `(HSpace.dual V).IP φ ψ = V.IP (rieszInv φ) (rieszInv ψ)`),
    `dualOfList V vs` is orthonormal whenever `vs` is. The proof unfolds
    `dual_innerProduct_apply`, uses `dualVec_of_orthonormal` (so
    `dualVec vs i = V.IP (vs.get i)`), and `rieszInv_innerProduct`
    (so `rieszInv (V.IP v_i) = v_i`). -/
theorem HSpace.dualOfList_orthonormal_of_orthonormal (V : HSpace) (vs : List V.carrier)
    (h_orth : ∀ i j : Fin vs.length,
      V.innerProduct (vs.get i) (vs.get j) = if i = j then 1 else 0) :
    ∀ i j : Fin (V.dualOfList vs).length,
      (HSpace.dual V).innerProduct ((V.dualOfList vs).get i) ((V.dualOfList vs).get j) =
        if i = j then 1 else 0 := by
  intro i j
  -- `(V.dualOfList vs).length = vs.length`. Rewrite the indices to land
  -- in `Fin vs.length` using `Fin.cast` from `dualOfList_length`.
  have hlen : (V.dualOfList vs).length = vs.length := V.dualOfList_length vs
  let i' : Fin vs.length := Fin.cast hlen i
  let j' : Fin vs.length := Fin.cast hlen j
  -- (dualOfList V vs).get k unfolds to `dualVec V vs k'` for the cast index.
  have h_get : ∀ k : Fin (V.dualOfList vs).length,
      (V.dualOfList vs).get k = V.dualVec vs (Fin.cast hlen k) := by
    intro k
    -- `dualOfList = (finRange n).map (dualVec vs)`, then `getElem_map`+`getElem_finRange`.
    have heq := HSpace.dualOfList_eq_finRange_map V vs
    -- Convert get to a term that doesn't depend on the list (use heq for both sides).
    refine (List.get_of_eq heq k).trans ?_

    simp
    rfl
  have h_get_i := h_get i
  have h_get_j := h_get j
  rw [h_get_i, h_get_j]
  -- `(HSpace.dual V).IP = V.IP.compl₁₂ rieszInv rieszInv` by definition,
  -- so applied to two vectors it reduces to `V.IP (rieszInv ·) (rieszInv ·)`.
  show V.innerProduct (V.innerIsIP.rieszInv (V.dualVec vs i'))
        (V.innerIsIP.rieszInv (V.dualVec vs j')) = if i = j then 1 else 0
  rw [HSpace.dualVec_of_orthonormal V vs h_orth,
      HSpace.dualVec_of_orthonormal V vs h_orth,
      HSpace.rieszInv_innerProduct, HSpace.rieszInv_innerProduct]
  -- Goal: V.IP (vs.get i') (vs.get j') = if i = j then 1 else 0.
  rw [h_orth i' j']
  -- Goal: (if i' = j' then 1 else 0) = (if i = j then 1 else 0).
  -- `i = j ↔ i' = j'` since `Fin.cast` is an isomorphism.
  have h_iff : i' = j' ↔ i = j := by
    constructor
    · intro h
      apply Fin.ext
      show i.1 = j.1
      exact Fin.mk.inj h
    · intro h; subst h; rfl
  by_cases hij : i = j
  · simp [h_iff.mpr hij, hij]
  · simp [h_iff, hij]

end GLang
