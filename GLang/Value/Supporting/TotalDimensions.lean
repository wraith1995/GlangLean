/- Total shape and dimension queries and their substitution and opening laws. -/

import GLang.Value.Binding
import GLang.Proofs.Value.Binding.ValueLN
import GLang.Value.Supporting.StrictTyping
import GLang.Numerics.SVD.ValueSVD
import GLang.Numerics.RREF.ValueRREF
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GLang

/-- Abstract oracle for the four-fundamental-subspace dimension. Given
    a property tag, a parent space, and the embedded value expression,
    returns the dimension of the corresponding subspace. Concretely
    this is `shape(SVDUI(⟦e⟧ρ)).2` etc. per `fig:valSpaceSemantics`. -/
abbrev FFSOracle := ValFFSProp → ValSpace → ValExpr → Nat

def ValTy.spaceOf : ValTy → ValSpace
  | .space s  => s
  | .piTy _ _ => .empty

@[simp] theorem ValTy.spaceOf_space (s : ValSpace) :
    ValTy.spaceOf (.space s) = s := rfl

/-- `spaceOf` commutes with opening a bound index: `spaceOf (openRec k u τ) =
    openRec k u (spaceOf τ)`. (`.space s ↦ s`, both sides open `s`; `.piTy ↦
    .empty`, and `openRec` fixes `.empty`.) A building block for the
    locally-nameless soundness bridge — `inferSpace`/`inferType` read `spaceOf`
    off type annotations, and the bridge opens those annotations. -/
@[simp] theorem ValTy.spaceOf_openRec (k : Nat) (u : ValExpr) :
    ∀ (τ : ValTy), ValTy.spaceOf (ValTy.openRec k u τ) = ValSpace.openRec k u (ValTy.spaceOf τ)
  | .space _  => rfl
  | .piTy _ _ => rfl

/-- `spaceOf` commutes with de Bruijn raising. -/
@[simp] theorem ValTy.spaceOf_raise (n cutoff : Nat) :
    ∀ (τ : ValTy), ValTy.spaceOf (ValTy.raise n cutoff τ) =
      ValSpace.raise n cutoff (ValTy.spaceOf τ)
  | .space _  => rfl
  | .piTy _ _ => rfl

/-- Domain of a Π-type `ValTy`. On a `.space` (a non-arrow, hence applied
    at no argument site) we return the space itself as a harmless junk
    default — application sites only ever consult `.domain` on the type of
    a function subexpression `e₀ : (x:τ₀) → τ₁`, where it returns `τ₀`. -/
def ValTy.domain : ValTy → ValTy
  | .piTy τ₀ _ => τ₀
  | .space s   => .space s

@[simp] theorem ValTy.domain_piTy (τ₀ τ₁ : ValTy) :
    ValTy.domain (.piTy τ₀ τ₁) = τ₀ := rfl

/-- `domain` commutes with opening a bound index. (The bridge opens the function
    subexpression's inferred type, then reads its `.domain`.) -/
theorem ValTy.domain_openRec (k : Nat) (u : ValExpr) :
    ∀ (τ : ValTy), ValTy.domain (ValTy.openRec k u τ) = ValTy.openRec k u τ.domain
  | .piTy _ _ => rfl
  | .space _ => rfl

/-- `domain` commutes with de Bruijn raising. -/
@[simp] theorem ValTy.domain_raise (n cutoff : Nat) :
    ∀ (τ : ValTy), ValTy.domain (ValTy.raise n cutoff τ) =
      ValTy.raise n cutoff τ.domain
  | .piTy _ _ => rfl
  | .space _  => rfl

mutual

def ValSpace.shpOf (orc : FFSOracle) : ValSpace → List Nat
  | .empty         => [0]
  | .real          => [1]
  | .dsum s₀ s₁    =>

      [ValSpace.dof orc s₀ + ValSpace.dof orc s₁]
  | .tprod s₀ s₁   =>

      [ValSpace.dof orc s₀, ValSpace.dof orc s₁]
  | .ffs p s e     =>

      [orc p s e]

/-- Dimension `\dof{\lsv}{\rho}` — product of `shpOf`. -/
def ValSpace.dof (orc : FFSOracle) (s : ValSpace) : Nat :=
  (ValSpace.shpOf orc s).foldr (· * ·) 1
end

def ValSpace.rnk (orc : FFSOracle) (s : ValSpace) : Nat :=
  Nat.pred (ValSpace.shpOf orc s).length

/-- For the real line, the shape is `[1]`. -/
@[simp] theorem ValSpace.shpOf_real (orc : FFSOracle) :
    ValSpace.shpOf orc .real = [1] := by
  unfold ValSpace.shpOf; rfl

/-- For the empty space, the shape is `[0]`. -/
@[simp] theorem ValSpace.shpOf_empty (orc : FFSOracle) :
    ValSpace.shpOf orc .empty = [0] := by
  unfold ValSpace.shpOf; rfl

/-- For a tensor product, the shape is `[dof s₀, dof s₁]`. -/
@[simp] theorem ValSpace.shpOf_tprod (orc : FFSOracle) (s₀ s₁ : ValSpace) :
    ValSpace.shpOf orc (.tprod s₀ s₁)
      = [ValSpace.dof orc s₀, ValSpace.dof orc s₁] := by
  unfold ValSpace.shpOf; rfl

/-- For a direct sum, the shape is a length-1 tuple with summed dims. -/
@[simp] theorem ValSpace.shpOf_dsum (orc : FFSOracle) (s₀ s₁ : ValSpace) :
    ValSpace.shpOf orc (.dsum s₀ s₁)
      = [ValSpace.dof orc s₀ + ValSpace.dof orc s₁] := by
  unfold ValSpace.shpOf; rfl

/-- For an FFS subspace, the shape comes from the oracle. -/
@[simp] theorem ValSpace.shpOf_ffs (orc : FFSOracle) (p : ValFFSProp)
    (s : ValSpace) (e : ValExpr) :
    ValSpace.shpOf orc (.ffs p s e) = [orc p s e] := by
  unfold ValSpace.shpOf; rfl

/-- `dof` of `ℝ` is 1. -/
@[simp] theorem ValSpace.dof_real (orc : FFSOracle) :
    ValSpace.dof orc .real = 1 := by
  simp [ValSpace.dof]

/-- `dof` of the empty space is 0. -/
@[simp] theorem ValSpace.dof_empty (orc : FFSOracle) :
    ValSpace.dof orc .empty = 0 := by
  simp [ValSpace.dof]

/-- `dof` of a tensor product is the product of dimensions. -/
@[simp] theorem ValSpace.dof_tprod (orc : FFSOracle) (s₀ s₁ : ValSpace) :
    ValSpace.dof orc (.tprod s₀ s₁)
      = ValSpace.dof orc s₀ * ValSpace.dof orc s₁ := by
  simp [ValSpace.dof]

/-- `dof` of a direct sum is the sum of dimensions. -/
@[simp] theorem ValSpace.dof_dsum (orc : FFSOracle) (s₀ s₁ : ValSpace) :
    ValSpace.dof orc (.dsum s₀ s₁)
      = ValSpace.dof orc s₀ + ValSpace.dof orc s₁ := by
  simp [ValSpace.dof]

@[simp] theorem ValSpace.rnk_real (orc : FFSOracle) :
    ValSpace.rnk orc .real = 0 := by
  simp [ValSpace.rnk]

@[simp] theorem ValSpace.rnk_tprod (orc : FFSOracle) (s₀ s₁ : ValSpace) :
    ValSpace.rnk orc (.tprod s₀ s₁) = 1 := by
  simp [ValSpace.rnk]

@[simp] theorem ValSpace.rnk_dsum (orc : FFSOracle) (s₀ s₁ : ValSpace) :
    ValSpace.rnk orc (.dsum s₀ s₁) = 0 := by
  simp [ValSpace.rnk]

/-! Recursive shape bounds for flattened indices. Scalars admit index zero; empty
spaces admit none. Direct sums route indices to their summands. Tensor products
decode row and column indices and check both factors recursively. Fundamental
subspaces use the dimension supplied by the oracle. -/
def ValSpace.shapeInBounds (orc : FFSOracle) : ValSpace → Nat → Prop
  | .empty, _      => False
  | .real, i       => i = 0
  | .dsum s₀ s₁, i =>
      let d₀ := ValSpace.dof orc s₀
      if i < d₀ then ValSpace.shapeInBounds orc s₀ i
      else
        (i - d₀) < ValSpace.dof orc s₁ ∧
        ValSpace.shapeInBounds orc s₁ (i - d₀)
  | .tprod s₀ s₁, i =>
      let d₁ := ValSpace.dof orc s₁
      let a := i / d₁
      let b := i % d₁
      a < ValSpace.dof orc s₀ ∧
      ValSpace.shapeInBounds orc s₀ a ∧
      ValSpace.shapeInBounds orc s₁ b
  | .ffs p s e, i  =>
      -- FFS shape is opaque: a length-1 tuple of size `orc p s e =
      -- dof orc (.ffs p s e)`. Flat-OOB ≡ shape-OOB.
      i < orc p s e

/-- For `.real`, shape-in-bounds is exactly `i = 0`. -/
@[simp] theorem ValSpace.shapeInBounds_real (orc : FFSOracle) (i : Nat) :
    ValSpace.shapeInBounds orc .real i ↔ i = 0 := Iff.rfl

/-- For `.empty`, no flat index is shape-in-bounds. -/
@[simp] theorem ValSpace.shapeInBounds_empty (orc : FFSOracle) (i : Nat) :
    ¬ ValSpace.shapeInBounds orc .empty i := id

/-- For `.tprod`, unfold the conjunctive bound. -/
@[simp] theorem ValSpace.shapeInBounds_tprod (orc : FFSOracle)
    (s₀ s₁ : ValSpace) (i : Nat) :
    ValSpace.shapeInBounds orc (.tprod s₀ s₁) i ↔
      i / ValSpace.dof orc s₁ < ValSpace.dof orc s₀ ∧
      ValSpace.shapeInBounds orc s₀ (i / ValSpace.dof orc s₁) ∧
      ValSpace.shapeInBounds orc s₁ (i % ValSpace.dof orc s₁) := Iff.rfl

/-- For `.dsum`, split on the flat threshold `dof s₀`. -/
theorem ValSpace.shapeInBounds_dsum (orc : FFSOracle)
    (s₀ s₁ : ValSpace) (i : Nat) :
    ValSpace.shapeInBounds orc (.dsum s₀ s₁) i ↔
      (i < ValSpace.dof orc s₀ ∧ ValSpace.shapeInBounds orc s₀ i) ∨
      (¬ i < ValSpace.dof orc s₀ ∧
        (i - ValSpace.dof orc s₀) < ValSpace.dof orc s₁ ∧
        ValSpace.shapeInBounds orc s₁ (i - ValSpace.dof orc s₀)) := by
  show (if i < ValSpace.dof orc s₀ then ValSpace.shapeInBounds orc s₀ i
        else (i - ValSpace.dof orc s₀) < ValSpace.dof orc s₁ ∧
             ValSpace.shapeInBounds orc s₁ (i - ValSpace.dof orc s₀))
        ↔ _
  by_cases h : i < ValSpace.dof orc s₀
  · simp [h]
  · simp [h]

/-- For `.ffs`, shape-in-bounds is exactly the oracle's bound. -/
@[simp] theorem ValSpace.shapeInBounds_ffs (orc : FFSOracle)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr) (i : Nat) :
    ValSpace.shapeInBounds orc (.ffs p s e) i ↔ i < orc p s e := Iff.rfl

/-- Shape-in-bounds implies flat-in-bounds. The converse fails for
    `.tprod`-typed spaces where the shape is a length-2 tuple. -/
theorem ValSpace.shapeInBounds_imp_lt_dof (orc : FFSOracle) :
    ∀ (s : ValSpace) (i : Nat),
      ValSpace.shapeInBounds orc s i → i < ValSpace.dof orc s
  | .empty, i, h => by
      simp [ValSpace.shapeInBounds] at h
  | .real, i, h => by
      simp [ValSpace.shapeInBounds] at h
      subst h
      simp [ValSpace.dof_real]
  | .dsum s₀ s₁, i, h => by
      rw [ValSpace.dof_dsum]
      rw [ValSpace.shapeInBounds_dsum] at h
      rcases h with ⟨h₀, _⟩ | ⟨_, h_sub, _⟩
      · exact Nat.lt_of_lt_of_le h₀ (Nat.le_add_right _ _)
      · omega
  | .tprod s₀ s₁, i, h => by
      rw [ValSpace.dof_tprod]
      rw [ValSpace.shapeInBounds_tprod] at h
      obtain ⟨ha, _, hb⟩ := h
      have hb' : i % ValSpace.dof orc s₁ < ValSpace.dof orc s₁ :=
        ValSpace.shapeInBounds_imp_lt_dof orc s₁ _ hb
      have h_d₁_pos : 0 < ValSpace.dof orc s₁ :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) hb'
      have hrec : i = ValSpace.dof orc s₁ * (i / ValSpace.dof orc s₁)
                       + i % ValSpace.dof orc s₁ :=
        (Nat.div_add_mod i (ValSpace.dof orc s₁)).symm
      calc i = ValSpace.dof orc s₁ * (i / ValSpace.dof orc s₁)
                 + i % ValSpace.dof orc s₁ := hrec
        _ < ValSpace.dof orc s₁ * (i / ValSpace.dof orc s₁)
                 + ValSpace.dof orc s₁ := Nat.add_lt_add_left hb' _
        _ = ValSpace.dof orc s₁ * (i / ValSpace.dof orc s₁ + 1) := by ring
        _ ≤ ValSpace.dof orc s₁ * ValSpace.dof orc s₀ :=
            Nat.mul_le_mul_left _ ha
        _ = ValSpace.dof orc s₀ * ValSpace.dof orc s₁ := by ring
  | .ffs p s e, _, h => by
      simp [ValSpace.shapeInBounds] at h
      simp [ValSpace.dof]
      exact h

/-- Contrapositive: flat-out-of-bounds implies shape-out-of-bounds.
    The convenient direction for soundness proofs. -/
theorem ValSpace.not_shapeInBounds_of_ge_dof (orc : FFSOracle)
    (s : ValSpace) (i : Nat) (hi : i ≥ ValSpace.dof orc s) :
    ¬ ValSpace.shapeInBounds orc s i := by
  intro h
  exact absurd (ValSpace.shapeInBounds_imp_lt_dof orc s i h) (Nat.not_lt.mpr hi)

/-- Convenience: flat `i < dof s` is implied by shape-in-bounds. -/
theorem ValSpace.lt_dof_of_shapeInBounds (orc : FFSOracle) {s : ValSpace}
    {i : Nat} (h : ValSpace.shapeInBounds orc s i) : i < ValSpace.dof orc s :=
  ValSpace.shapeInBounds_imp_lt_dof orc s i h

/-- The shape predicate is equivalent to the flat predicate
    `i < dof orc s`: flat-in-bounds implies shape-in-bounds.
    Because `dof orc (tprod s₀ s₁) = dof s₀ * dof s₁` is a consistent
    product of dimensions and `shapeInBounds` recurses with consistent
    decoders, the recursive structure of `shapeInBounds` is just an
    *equivalent* re-expression of the flat predicate. The value of the
    recursive form is the *witness structure* it provides:
    decomposing `¬ shapeInBounds (tprod s₀ s₁) i` into
    `¬ shapeInBounds s₀ (i/d₁) ∨ ...` is the key step for tensor-
    routing soundness proofs. -/
theorem ValSpace.shapeInBounds_iff_lt_dof (orc : FFSOracle) :
    ∀ (s : ValSpace) (i : Nat),
      ValSpace.shapeInBounds orc s i ↔ i < ValSpace.dof orc s
  | .empty, i => by
      simp [ValSpace.shapeInBounds, ValSpace.dof_empty]
  | .real, i => by
      rw [ValSpace.shapeInBounds_real, ValSpace.dof_real]
      omega
  | .dsum s₀ s₁, i => by
      constructor
      · exact ValSpace.shapeInBounds_imp_lt_dof orc _ i
      · intro hflat
        rw [ValSpace.dof_dsum] at hflat
        rw [ValSpace.shapeInBounds_dsum]
        by_cases h_lt : i < ValSpace.dof orc s₀
        · left
          refine ⟨h_lt, ?_⟩
          exact (ValSpace.shapeInBounds_iff_lt_dof orc s₀ i).mpr h_lt
        · right
          refine ⟨h_lt, ?_, ?_⟩
          · omega
          · apply (ValSpace.shapeInBounds_iff_lt_dof orc s₁ _).mpr
            omega
  | .tprod s₀ s₁, i => by
      constructor
      · exact ValSpace.shapeInBounds_imp_lt_dof orc _ i
      · intro hflat
        rw [ValSpace.dof_tprod] at hflat
        rw [ValSpace.shapeInBounds_tprod]
        -- d₁ > 0 since `i < d₀ * d₁` and `i ≥ 0`.
        by_cases hd₁ : ValSpace.dof orc s₁ = 0
        · -- d₁ = 0 ⇒ dof = 0 ⇒ hflat is `i < 0`, contradiction.
          rw [hd₁, Nat.mul_zero] at hflat
          exact absurd hflat (Nat.not_lt_zero i)
        · have h_d₁_pos : 0 < ValSpace.dof orc s₁ := Nat.pos_of_ne_zero hd₁
          have ha : i / ValSpace.dof orc s₁ < ValSpace.dof orc s₀ := by
            rw [Nat.div_lt_iff_lt_mul h_d₁_pos]
            linarith [Nat.mul_comm (ValSpace.dof orc s₀) (ValSpace.dof orc s₁)]
          have hb : i % ValSpace.dof orc s₁ < ValSpace.dof orc s₁ :=
            Nat.mod_lt i h_d₁_pos
          refine ⟨ha, ?_, ?_⟩
          · exact (ValSpace.shapeInBounds_iff_lt_dof orc s₀ _).mpr ha
          · exact (ValSpace.shapeInBounds_iff_lt_dof orc s₁ _).mpr hb
  | .ffs p s e, i => by
      simp [ValSpace.shapeInBounds, ValSpace.dof]

/-- Convenience: `i < dof orc s → shapeInBounds orc s i`. -/
theorem ValSpace.shapeInBounds_of_lt_dof (orc : FFSOracle) (s : ValSpace)
    (i : Nat) (h : i < ValSpace.dof orc s) : ValSpace.shapeInBounds orc s i :=
  (ValSpace.shapeInBounds_iff_lt_dof orc s i).mpr h

/-- The syntax-transport laws needed before `ValSpace.SDEq` is available. -/
class FFSOracle.SubstOpenLaws (orc : FFSOracle) : Prop where
  substRespect : ∀ (x : VName) (e₁ : ValExpr) (p : ValFFSProp)
      (s : ValSpace) (e : ValExpr),
    orc p (ValSpace.subst x e₁ s) (ValExpr.subst x e₁ e) = orc p s e
  openRecRespect : ∀ (k : Nat) (u : ValExpr) (p : ValFFSProp)
      (s : ValSpace) (e : ValExpr),
    orc p (ValSpace.openRec k u s) (ValExpr.openRec k u e) = orc p s e

/-- Substitution coherence projected from an explicit oracle-law bundle. -/
theorem FFSOracle.subst_respect (orc : FFSOracle)
    [laws : FFSOracle.SubstOpenLaws orc]
    (x : VName) (e₁ : ValExpr)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr) :
    orc p (ValSpace.subst x e₁ s) (ValExpr.subst x e₁ e) = orc p s e :=
  laws.substRespect x e₁ p s e

/-- **Propagation of `dof` through type-substitution.** The
    dimension of a `ValSpace` is invariant under capture-naive
    substitution: the non-`ffs` cases recurse structurally; the
    `ffs` case appeals to `FFSOracle.subst_respect`. -/
@[simp] theorem ValSpace.dof_subst (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc]
    (x : VName) (e₁ : ValExpr) :
    ∀ (s : ValSpace),
      ValSpace.dof orc (ValSpace.subst x e₁ s) = ValSpace.dof orc s
  | .empty => by simp [ValSpace.subst]
  | .real  => by simp [ValSpace.subst]
  | .dsum s₀ s₁ => by
      simp [ValSpace.subst, ValSpace.dof_dsum,
        ValSpace.dof_subst orc x e₁ s₀, ValSpace.dof_subst orc x e₁ s₁]
  | .tprod s₀ s₁ => by
      simp [ValSpace.subst, ValSpace.dof_tprod,
        ValSpace.dof_subst orc x e₁ s₀, ValSpace.dof_subst orc x e₁ s₁]
  | .ffs p s e => by
      -- dof orc (.ffs p s e) = orc p s e (length-1 shape product).
      have hsubst := FFSOracle.subst_respect orc x e₁ p s e
      simp [ValSpace.subst, ValSpace.dof, ValSpace.shpOf, hsubst]

/-- **Propagation of `shapeInBounds` through type-substitution.**
    The bounding-box predicate is invariant under capture-naive
    substitution: the non-`ffs` cases recurse structurally
    (using `dof_subst` to align the inner thresholds); the
    `ffs` case appeals to `FFSOracle.subst_respect`. -/
theorem ValSpace.shapeInBounds_subst (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc]
    (x : VName) (e₁ : ValExpr) :
    ∀ (s : ValSpace) (i : Nat),
      ValSpace.shapeInBounds orc (ValSpace.subst x e₁ s) i ↔
      ValSpace.shapeInBounds orc s i
  | .empty, i => by
      simp [ValSpace.subst, ValSpace.shapeInBounds]
  | .real, i => by
      simp [ValSpace.subst, ValSpace.shapeInBounds]
  | .dsum s₀ s₁, i => by
      -- Both sides decode via `shapeInBounds_dsum`. The split
      -- threshold `dof orc s₀` is invariant by `dof_subst`.
      rw [ValSpace.subst]
      rw [ValSpace.shapeInBounds_dsum, ValSpace.shapeInBounds_dsum]
      rw [ValSpace.dof_subst orc x e₁ s₀, ValSpace.dof_subst orc x e₁ s₁]
      constructor
      · rintro (⟨h, hsb⟩ | ⟨h, hlt, hsb⟩)
        · left
          exact ⟨h, (ValSpace.shapeInBounds_subst orc x e₁ s₀ i).mp hsb⟩
        · right
          exact ⟨h, hlt,
            (ValSpace.shapeInBounds_subst orc x e₁ s₁ _).mp hsb⟩
      · rintro (⟨h, hsb⟩ | ⟨h, hlt, hsb⟩)
        · left
          exact ⟨h, (ValSpace.shapeInBounds_subst orc x e₁ s₀ i).mpr hsb⟩
        · right
          exact ⟨h, hlt,
            (ValSpace.shapeInBounds_subst orc x e₁ s₁ _).mpr hsb⟩
  | .tprod s₀ s₁, i => by
      -- Both sides decode via `shapeInBounds_tprod`. The split
      -- threshold `dof orc s₁` is invariant by `dof_subst`.
      rw [ValSpace.subst]
      rw [ValSpace.shapeInBounds_tprod, ValSpace.shapeInBounds_tprod]
      rw [ValSpace.dof_subst orc x e₁ s₀, ValSpace.dof_subst orc x e₁ s₁]
      constructor
      · rintro ⟨h_lt, h₀, h₁⟩
        exact ⟨h_lt,
          (ValSpace.shapeInBounds_subst orc x e₁ s₀ _).mp h₀,
          (ValSpace.shapeInBounds_subst orc x e₁ s₁ _).mp h₁⟩
      · rintro ⟨h_lt, h₀, h₁⟩
        exact ⟨h_lt,
          (ValSpace.shapeInBounds_subst orc x e₁ s₀ _).mpr h₀,
          (ValSpace.shapeInBounds_subst orc x e₁ s₁ _).mpr h₁⟩
  | .ffs p s e, i => by
      -- shapeInBounds orc (.ffs p s e) i ↔ i < orc p s e.
      rw [ValSpace.subst]
      rw [ValSpace.shapeInBounds_ffs, ValSpace.shapeInBounds_ffs]
      rw [FFSOracle.subst_respect orc x e₁ p s e]

/-- Opening coherence projected from an explicit oracle-law bundle. -/
theorem FFSOracle.openRec_respect (orc : FFSOracle)
    [laws : FFSOracle.SubstOpenLaws orc]
    (k : Nat) (u : ValExpr)
    (p : ValFFSProp) (s : ValSpace) (e : ValExpr) :
    orc p (ValSpace.openRec k u s) (ValExpr.openRec k u e) = orc p s e :=
  laws.openRecRespect k u p s e

/-- **Propagation of `dof` through opening.** Mirrors `dof_subst`. -/
@[simp] theorem ValSpace.dof_openRec (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] (k : Nat) (u : ValExpr) :
    ∀ (s : ValSpace),
      ValSpace.dof orc (ValSpace.openRec k u s) = ValSpace.dof orc s
  | .empty => by simp [ValSpace.openRec]
  | .real  => by simp [ValSpace.openRec]
  | .dsum s₀ s₁ => by
      simp [ValSpace.openRec, ValSpace.dof_dsum,
        ValSpace.dof_openRec orc k u s₀, ValSpace.dof_openRec orc k u s₁]
  | .tprod s₀ s₁ => by
      simp [ValSpace.openRec, ValSpace.dof_tprod,
        ValSpace.dof_openRec orc k u s₀, ValSpace.dof_openRec orc k u s₁]
  | .ffs p s e => by
      have hopen := FFSOracle.openRec_respect orc k u p s e
      simp [ValSpace.openRec, ValSpace.dof, ValSpace.shpOf, hopen]

/-- **Propagation of `shapeInBounds` through opening.** Mirrors
    `shapeInBounds_subst`. -/
theorem ValSpace.shapeInBounds_openRec (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] (k : Nat) (u : ValExpr) :
    ∀ (s : ValSpace) (i : Nat),
      ValSpace.shapeInBounds orc (ValSpace.openRec k u s) i ↔
      ValSpace.shapeInBounds orc s i
  | .empty, i => by simp [ValSpace.openRec, ValSpace.shapeInBounds]
  | .real, i => by simp [ValSpace.openRec, ValSpace.shapeInBounds]
  | .dsum s₀ s₁, i => by
      rw [ValSpace.openRec]
      rw [ValSpace.shapeInBounds_dsum, ValSpace.shapeInBounds_dsum]
      rw [ValSpace.dof_openRec orc k u s₀, ValSpace.dof_openRec orc k u s₁]
      constructor
      · rintro (⟨h, hsb⟩ | ⟨h, hlt, hsb⟩)
        · exact Or.inl ⟨h, (ValSpace.shapeInBounds_openRec orc k u s₀ i).mp hsb⟩
        · exact Or.inr ⟨h, hlt,
            (ValSpace.shapeInBounds_openRec orc k u s₁ _).mp hsb⟩
      · rintro (⟨h, hsb⟩ | ⟨h, hlt, hsb⟩)
        · exact Or.inl ⟨h, (ValSpace.shapeInBounds_openRec orc k u s₀ i).mpr hsb⟩
        · exact Or.inr ⟨h, hlt,
            (ValSpace.shapeInBounds_openRec orc k u s₁ _).mpr hsb⟩
  | .tprod s₀ s₁, i => by
      rw [ValSpace.openRec]
      rw [ValSpace.shapeInBounds_tprod, ValSpace.shapeInBounds_tprod]
      rw [ValSpace.dof_openRec orc k u s₀, ValSpace.dof_openRec orc k u s₁]
      constructor
      · rintro ⟨h_lt, h₀, h₁⟩
        exact ⟨h_lt,
          (ValSpace.shapeInBounds_openRec orc k u s₀ _).mp h₀,
          (ValSpace.shapeInBounds_openRec orc k u s₁ _).mp h₁⟩
      · rintro ⟨h_lt, h₀, h₁⟩
        exact ⟨h_lt,
          (ValSpace.shapeInBounds_openRec orc k u s₀ _).mpr h₀,
          (ValSpace.shapeInBounds_openRec orc k u s₁ _).mpr h₁⟩
  | .ffs p s e, i => by
      rw [ValSpace.openRec]
      rw [ValSpace.shapeInBounds_ffs, ValSpace.shapeInBounds_ffs]
      rw [FFSOracle.openRec_respect orc k u p s e]

inductive ValSpace.Skel : Type
  | leaf  : Nat → ValSpace.Skel
  | tprod : ValSpace.Skel → ValSpace.Skel → ValSpace.Skel
  | dsum  : ValSpace.Skel → ValSpace.Skel → ValSpace.Skel
  deriving DecidableEq, Repr

/-- The `.tprod`/`.dsum` skeleton of a value space, with `dof` at the leaves. -/
def ValSpace.skel (orc : FFSOracle) : ValSpace → ValSpace.Skel
  | .tprod a b => .tprod (ValSpace.skel orc a) (ValSpace.skel orc b)
  | .dsum a b  => .dsum (ValSpace.skel orc a) (ValSpace.skel orc b)
  | s          => .leaf (ValSpace.dof orc s)

/-- `dof` read off the skeleton. -/
def ValSpace.Skel.dof : ValSpace.Skel → Nat
  | .leaf n    => n
  | .tprod a b => a.dof * b.dof
  | .dsum a b  => a.dof + b.dof

/-- Shape-and-`dof` equivalence: equal skeletons. -/
abbrev ValSpace.SDEq (orc : FFSOracle) (s s' : ValSpace) : Prop :=
  ValSpace.skel orc s = ValSpace.skel orc s'

@[refl] theorem ValSpace.SDEq.refl (orc : FFSOracle) (s : ValSpace) :
    ValSpace.SDEq orc s s := rfl

theorem ValSpace.SDEq.symm (orc : FFSOracle) {s s' : ValSpace}
    (h : ValSpace.SDEq orc s s') : ValSpace.SDEq orc s' s := Eq.symm h

theorem ValSpace.SDEq.trans (orc : FFSOracle) {s₁ s₂ s₃ : ValSpace}
    (h : ValSpace.SDEq orc s₁ s₂) (h' : ValSpace.SDEq orc s₂ s₃) :
    ValSpace.SDEq orc s₁ s₃ := Eq.trans h h'

/-- `dof` equals the skeleton's `dof`. -/
theorem ValSpace.dof_eq_skel_dof (orc : FFSOracle) :
    ∀ s : ValSpace, ValSpace.dof orc s = (ValSpace.skel orc s).dof
  | .tprod a b => by
      rw [ValSpace.dof_tprod, ValSpace.dof_eq_skel_dof orc a,
          ValSpace.dof_eq_skel_dof orc b]; rfl
  | .dsum a b => by
      rw [ValSpace.dof_dsum, ValSpace.dof_eq_skel_dof orc a,
          ValSpace.dof_eq_skel_dof orc b]; rfl
  | .real => rfl
  | .empty => rfl
  | .ffs _ _ _ => rfl

/-- `SDEq`-related spaces have equal `dof`. -/
theorem ValSpace.SDEq.dof_eq (orc : FFSOracle) {s s' : ValSpace}
    (h : ValSpace.SDEq orc s s') : ValSpace.dof orc s = ValSpace.dof orc s' := by
  rw [ValSpace.dof_eq_skel_dof orc s, ValSpace.dof_eq_skel_dof orc s', h]

/-- The skeleton is invariant under opening (structure unchanged, `dof`
    invariant by `dof_openRec`). -/
theorem ValSpace.skel_openRec (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] (k : Nat) (u : ValExpr) :
    ∀ s : ValSpace, ValSpace.skel orc (ValSpace.openRec k u s) = ValSpace.skel orc s
  | .tprod a b => by
      rw [ValSpace.openRec]; show ValSpace.Skel.tprod _ _ = ValSpace.Skel.tprod _ _
      rw [skel_openRec orc k u a, skel_openRec orc k u b]
  | .dsum a b => by
      rw [ValSpace.openRec]; show ValSpace.Skel.dsum _ _ = ValSpace.Skel.dsum _ _
      rw [skel_openRec orc k u a, skel_openRec orc k u b]
  | .real => rfl
  | .empty => rfl
  | .ffs p s e => by
      show ValSpace.Skel.leaf (ValSpace.dof orc (ValSpace.openRec k u (.ffs p s e)))
          = ValSpace.Skel.leaf (ValSpace.dof orc (.ffs p s e))
      rw [ValSpace.dof_openRec]

/-- Opening a bound index keeps a space `SDEq` to itself. -/
theorem ValSpace.SDEq_openRec (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] (k : Nat) (u : ValExpr)
    (s : ValSpace) : ValSpace.SDEq orc s (ValSpace.openRec k u s) :=
  (ValSpace.skel_openRec orc k u s).symm

/-- A space whose skeleton is a `.tprod` is itself a `.tprod`. -/
theorem ValSpace.eq_tprod_of_skel (orc : FFSOracle) :
    ∀ {s : ValSpace} {a b : ValSpace.Skel}, ValSpace.skel orc s = .tprod a b →
      ∃ s0 s1, s = .tprod s0 s1
  | .tprod s0 s1, _, _, _ => ⟨s0, s1, rfl⟩
  | .dsum _ _, _, _, h => by simp [ValSpace.skel] at h
  | .real, _, _, h => by simp [ValSpace.skel] at h
  | .empty, _, _, h => by simp [ValSpace.skel] at h
  | .ffs _ _ _, _, _, h => by simp [ValSpace.skel] at h

/-- A space whose skeleton is a `.dsum` is itself a `.dsum`. -/
theorem ValSpace.eq_dsum_of_skel (orc : FFSOracle) :
    ∀ {s : ValSpace} {a b : ValSpace.Skel}, ValSpace.skel orc s = .dsum a b →
      ∃ s0 s1, s = .dsum s0 s1
  | .dsum s0 s1, _, _, _ => ⟨s0, s1, rfl⟩
  | .tprod _ _, _, _, h => by simp [ValSpace.skel] at h
  | .real, _, _, h => by simp [ValSpace.skel] at h
  | .empty, _, _, h => by simp [ValSpace.skel] at h
  | .ffs _ _ _, _, _, h => by simp [ValSpace.skel] at h

/-- Complete syntactic coherence contract for a frozen FFS oracle.  The final
field says that the FFS dimension depends on its ambient space only through
the `SDEq` skeleton. -/
class FFSOracle.Laws (orc : FFSOracle) : Prop extends FFSOracle.SubstOpenLaws orc where
  sdeqRespect : ∀ (p : ValFFSProp) {s₁ s₂ : ValSpace} (e : ValExpr),
    ValSpace.SDEq orc s₁ s₂ → orc p s₁ e = orc p s₂ e

/-- Shape-equivalence coherence projected from an explicit oracle-law bundle. -/
theorem FFSOracle.sdeq_respect (orc : FFSOracle) [laws : FFSOracle.Laws orc]
    (p : ValFFSProp)
    {s₁ s₂ : ValSpace} (e : ValExpr) :
    ValSpace.SDEq orc s₁ s₂ → orc p s₁ e = orc p s₂ e :=
  laws.sdeqRespect p e

end GLang
