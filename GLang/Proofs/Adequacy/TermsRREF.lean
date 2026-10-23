import GLang.Value.Supporting.TotalDimensionSemantics
import GLang.Numerics.RREF.BasisLexInd
import GLang.Numerics.Spectral.BasisFSVGSVD
import GLang.Proofs.Basis.BasisSoundness
import GLang.Proofs.Progress.Supporting.ProgressStdBasis
import GLang.Numerics.SVD.ValueSVD
import Mathlib.Data.List.GetD

/-!
# Matrix semantics for `S.Cob.terms_rref`

This module proves the matrix and coordinate facts used by the live
`ValExpr.rrefRep` implementation in the `terms_rref` operational arm.

If there are `K` terms in an `N`-dimensional basis `b'`, the direct-sum value
is laid out as `K` consecutive rows of `b'` coordinates.  The matrix row
reduction must instead see candidates as columns, so `termsCandidateMatrix`
forms

```
  A = [ termCoordinates.transpose | I_N ] : N x (K + N).
```

Let `C : N x N` be the existing COB from source `b` to `b'`; row `j` of `C`
contains the `b'` coordinates of source vector `b_j`.  In a full-rank RREF
decomposition `A = E * R`, the pivot columns of `A` are the columns of `E`.
Consequently the required COB from `b` to the pivot/`LexInd` basis is

```
  C * E_inv.transpose.
```

The theorem `termsRREFRepMatrix_row_expansion` proves this orientation from
the decomposition fields. `RawTermsRREFLexInd` proves the exact ordered
connection with source `HSpace.lexInd`; `RREFCanonicalRep` proves that the
observable representation is independent of the decomposition witness.
-/

namespace GLang

open scoped BigOperators
open Matrix

/-! ## LexInd transport through coordinates -/

/-- The concrete coordinate HSpace used to compare RREF columns with an
arbitrary semantic basis. -/
noncomputable def finRealHSpace (N : Nat) : HSpace where
  carrier := Fin N -> Real
  innerProduct := basisStandardIP (Pi.basisFun Real (Fin N))
  innerIsIP := basisStandardIP_isInnerProduct (Pi.basisFun Real (Fin N))

/-- The greedy `lexInd` scan commutes with an injective linear map. -/
theorem HSpace.lexIndAux_map_injective
    (V W : HSpace) (f : V.carrier →ₗ[Real] W.carrier)
    (hf : Function.Injective f) :
    forall (acc vs : List V.carrier),
      W.lexIndAux (acc.map f) (vs.map f) =
        (V.lexIndAux acc vs).map f := by
  intro acc vs
  induction vs generalizing acc with
  | nil => simp [HSpace.lexIndAux]
  | cons v vs ih =>
      have hset : {w | w ∈ acc.map f} = f '' {w | w ∈ acc} := by
        ext w
        simp
      have hmem :
          f v ∈ Submodule.span Real {w | w ∈ acc.map f} ↔
            v ∈ Submodule.span Real {w | w ∈ acc} := by
        rw [hset]
        exact Submodule.apply_mem_span_image_iff_mem_span hf
      by_cases hv : v ∈ Submodule.span Real {w | w ∈ acc}
      · have hvf := hmem.mpr hv
        simp only [List.map_cons, HSpace.lexIndAux]
        rw [if_pos hv, if_pos hvf]
        exact ih acc
      · have hvf : f v ∉ Submodule.span Real {w | w ∈ acc.map f} :=
          fun h => hv (hmem.mp h)
        simp only [List.map_cons, HSpace.lexIndAux]
        rw [if_neg hv, if_neg hvf]
        simpa using ih (acc ++ [v])

/-- Public form of the coordinate-transport lemma. -/
theorem HSpace.lexInd_map_injective
    (V W : HSpace) (f : V.carrier →ₗ[Real] W.carrier)
    (hf : Function.Injective f) (vs : List V.carrier) :
    W.lexInd (vs.map f) = (V.lexInd vs).map f := by
  unfold HSpace.lexInd
  simpa using HSpace.lexIndAux_map_injective V W f hf [] vs

/-! ## A generic greedy-scan characterization -/

/-- The vectors among positions `< n` marked by `keep`, in their original
left-to-right order.  This is the accumulator that the greedy `lexInd` scan
must have after processing the first `n` vectors. -/
def HSpace.keptPrefix {V : HSpace} (x : Nat -> V.carrier)
    (keep : Nat -> Bool) (n : Nat) : List V.carrier :=
  ((List.range n).filter keep).map x

/-- Scanning an append is the same as scanning its left half and continuing
from the resulting accumulator. -/
theorem HSpace.lexIndAux_append {V : HSpace}
    (acc xs ys : List V.carrier) :
    V.lexIndAux acc (xs ++ ys) =
      V.lexIndAux (V.lexIndAux acc xs) ys := by
  induction xs generalizing acc with
  | nil => simp [HSpace.lexIndAux]
  | cons x xs ih =>
      simp only [List.cons_append, HSpace.lexIndAux]
      split_ifs <;> exact ih _

/-- A reusable specification theorem for the greedy scan.  If `keep j` is
true exactly when vector `j` is outside the span of the earlier kept vectors,
then `lexInd` returns precisely those marked vectors. -/
theorem HSpace.lexInd_range_eq_keptPrefix
    (V : HSpace) (x : Nat -> V.carrier) (keep : Nat -> Bool) (n : Nat)
    (hspan : forall j, j < n -> (
      (x j ∈ Submodule.span Real {w | w ∈ HSpace.keptPrefix x keep j}) ↔
        keep j = false)) :
    V.lexInd ((List.range n).map x) = HSpace.keptPrefix x keep n := by
  unfold HSpace.lexInd
  induction n with
  | zero => simp [HSpace.keptPrefix, HSpace.lexIndAux]
  | succ n ih =>
      have ih' := ih (fun j hj => hspan j (Nat.lt.step hj))
      rw [List.range_succ, List.map_append,
        HSpace.lexIndAux_append, ih']
      simp only [List.map_singleton]
      by_cases hk : keep n = true
      · have hnmem :
            x n ∉ Submodule.span Real
              {w | w ∈ HSpace.keptPrefix x keep n} := by
          intro hm
          have hf := (hspan n (Nat.lt_succ_self n)).mp hm
          rw [hk] at hf
          contradiction
        simp only [HSpace.lexIndAux, hnmem, ↓reduceIte]
        simp [HSpace.keptPrefix, List.range_succ, List.filter_append, hk]
      · have hkfalse : keep n = false := Bool.eq_false_of_not_eq_true hk
        have hmem :
            x n ∈ Submodule.span Real
              {w | w ∈ HSpace.keptPrefix x keep n} :=
          (hspan n (Nat.lt_succ_self n)).mpr hkfalse
        simp only [HSpace.lexIndAux, hmem, ↓reduceIte]
        simp [HSpace.keptPrefix, List.range_succ, List.filter_append, hkfalse]

@[simp] theorem termsRREFRepDenot_entry
    {N K : Nat} (termCoords oldCob : Nat -> Real)
    (j i : Fin N) :
    termsRREFRepDenot N K termCoords oldCob (j.val * N + i.val) =
      termsRREFRepMatrix N K termCoords oldCob j i := by
  have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
  have hdiv : (j.val * N + i.val) / N = j.val := by
    rw [Nat.mul_comm j.val N, Nat.mul_add_div hN,
      Nat.div_eq_of_lt i.isLt, Nat.add_zero]
  have hmod : (j.val * N + i.val) % N = i.val := by
    rw [Nat.mul_comm j.val N, Nat.mul_add_mod,
      Nat.mod_eq_of_lt i.isLt]
  simp [termsRREFRepDenot, matrixAsDenot, Nat.ne_of_gt hN,
    hdiv, hmod, j.isLt, i.isLt]

/-! ## Repeated-direct-sum coordinate bookkeeping -/

/-- The left-associated direct sum of `n + 1` copies of `V`. -/
@[reducible] noncomputable def HSpace.dsumPow (V : HSpace) : Nat -> HSpace
  | 0 => V
  | n + 1 => HSpace.dsum (V.dsumPow n) V

/-- The corresponding concatenated basis list. -/
@[reducible] noncomputable def HSpace.dsumPowBasis (V : HSpace) (B : List V.carrier) :
    (n : Nat) -> List (V.dsumPow n).carrier
  | 0 => B
  | n + 1 => HSpace.dsumOfLists (V.dsumPow n) V
      (V.dsumPowBasis B n) B

/-- Package `n + 1` vectors into the left-associated direct sum. -/
@[reducible] noncomputable def HSpace.dsumPowVector (V : HSpace) :
    (n : Nat) -> (Fin (n + 1) -> V.carrier) -> (V.dsumPow n).carrier
  | 0, x => x 0
  | n + 1, x =>
      (V.dsumPowVector n (fun i => x i.castSucc), x (Fin.last (n + 1)))

@[simp] theorem HSpace.dsumPowBasis_length (V : HSpace)
    (B : List V.carrier) (n : Nat) :
    (V.dsumPowBasis B n).length = (n + 1) * B.length := by
  induction n with
  | zero =>
      simp only [HSpace.dsumPowBasis, Nat.zero_add, Nat.one_mul]
  | succ n ih =>
      change (HSpace.dsumOfLists (V.dsumPow n) V
        (V.dsumPowBasis B n) B).length = _
      rw [HSpace.dsumOfLists_length (V.dsumPowBasis B n) B, ih]
      simp only [Nat.add_mul, Nat.one_mul]

private theorem termsRREF_sum_prod_left
    {iota A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset iota) (g : iota -> A) :
    (∑ i ∈ s, (g i, (0 : B))) = (∑ i ∈ s, g i, 0) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem termsRREF_sum_prod_right
    {iota A B : Type} [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset iota) (g : iota -> B) :
    (∑ i ∈ s, ((0 : A), g i)) = (0, ∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => apply Prod.ext <;> simp
  | insert a s ha ih => apply Prod.ext <;> simp [ha, ih]

private theorem termsRREF_dsum_getD_left
    (V0 V1 : HSpace) (B0 : List V0.carrier) (B1 : List V1.carrier)
    (i : Nat) (hi : i < B0.length) :
    (HSpace.dsumOfLists V0 V1 B0 B1).getD i 0 = (B0.getD i 0, 0) := by
  unfold HSpace.dsumOfLists
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  change (B0.map (fun x => (x, 0))).getD i ((0, 0)) = _
  rw [show ((0, 0) : V0.carrier × V1.carrier) =
      (fun x => (x, 0)) 0 by rfl, List.getD_map]

private theorem termsRREF_dsum_getD_right
    (V0 V1 : HSpace) (B0 : List V0.carrier) (B1 : List V1.carrier)
    (i : Nat) (hi : i < B1.length) :
    (HSpace.dsumOfLists V0 V1 B0 B1).getD (B0.length + i) 0 =
      (0, B1.getD i 0) := by
  unfold HSpace.dsumOfLists
  have hmaplen :
      (B0.map (LinearMap.inl Real V0.carrier V1.carrier)).length = B0.length :=
    List.length_map _
  rw [← hmaplen, List.getD_append_right _ _ _ _ (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]
  change (B1.map (fun x => (0, x))).getD i ((0, 0)) = _
  rw [show ((0, 0) : V0.carrier × V1.carrier) =
      (fun x => (0, x)) 0 by rfl, List.getD_map]

private theorem termsRREF_sum_cast_of_eq {M : Type*} [AddCommMonoid M]
    {n m : Nat} (h : n = m) (f : Fin n -> M) :
    (∑ i, f i) = ∑ i : Fin m, f (Fin.cast h.symm i) := by
  subst m
  rfl

/-- Split a coefficient expansion in a direct-sum basis into its two
component expansions. -/
theorem termsRREF_dsum_coeff_sum
    (V0 V1 : HSpace) (B0 : List V0.carrier) (B1 : List V1.carrier)
    (c : Nat -> Real) :
    (∑ i : Fin (HSpace.dsumOfLists V0 V1 B0 B1).length,
        c i.val • (HSpace.dsumOfLists V0 V1 B0 B1).getD i.val 0) =
      (∑ i : Fin B0.length, c i.val • B0.getD i.val 0,
       ∑ i : Fin B1.length, c (B0.length + i.val) • B1.getD i.val 0) := by
  rw [termsRREF_sum_cast_of_eq
    (HSpace.dsumOfLists_length B0 B1)]
  rw [Fin.sum_univ_add]
  have h0 : (∑ i : Fin B0.length,
      c i.val •
        (HSpace.dsumOfLists V0 V1 B0 B1).getD i.val 0) =
      (∑ i : Fin B0.length,
        c i.val • B0.getD i.val 0, 0) := by
    rw [← termsRREF_sum_prod_left]
    apply Finset.sum_congr rfl
    intro i _
    rw [termsRREF_dsum_getD_left _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  have h1 : (∑ i : Fin B1.length,
      c (B0.length + i.val) •
        (HSpace.dsumOfLists V0 V1 B0 B1).getD
          (B0.length + i.val) 0) =
      (0, ∑ i : Fin B1.length,
        c (B0.length + i.val) • B1.getD i.val 0) := by
    rw [← termsRREF_sum_prod_right]
    apply Finset.sum_congr rfl
    intro i _
    rw [termsRREF_dsum_getD_right _ _ _ _ _ i.isLt]
    apply Prod.ext <;> simp
  simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
  rw [h0, h1]
  ext <;> simp

/-- Reading a coefficient vector in the repeated direct-sum basis row by row
recovers the coordinate row of each component vector. -/
theorem HSpace.dsumPow_coordinates (V : HSpace) (B : List V.carrier) :
    forall (n : Nat) (x : Fin (n + 1) -> V.carrier) (c : Nat -> Real),
      V.dsumPowVector n x =
        (∑ q : Fin (V.dsumPowBasis B n).length,
          c q.val • (V.dsumPowBasis B n).getD q.val 0) ->
      forall j : Fin (n + 1),
        x j = ∑ i : Fin B.length,
          c (j.val * B.length + i.val) • B.getD i.val 0
  | 0, x, c, h => by
      intro j
      have hj : j = 0 := Fin.eq_zero j
      subst j
      simpa [HSpace.dsumPowVector, HSpace.dsumPowBasis] using h
  | n + 1, x, c, h => by
      simp only [HSpace.dsumPowVector, HSpace.dsumPowBasis] at h
      have h' := h.trans (termsRREF_dsum_coeff_sum
        (V.dsumPow n) V (V.dsumPowBasis B n) B c)
      have hleft := congrArg Prod.fst h'
      have hright := congrArg Prod.snd h'
      simp only [Prod.fst, Prod.snd] at hleft hright
      intro j
      by_cases hj : j.val < n + 1
      · let j' : Fin (n + 1) := ⟨j.val, hj⟩
        have hx : x j = x j'.castSucc := by
          congr 1
        rw [hx]
        have hi := HSpace.dsumPow_coordinates V B n
          (fun i => x i.castSucc) c hleft j'
        simpa only [j'] using hi
      · have hjlast : j = Fin.last (n + 1) := by
          apply Fin.ext
          simp only [Fin.last]
          omega
        subst j
        rw [hright]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        rw [HSpace.dsumPowBasis_length]
        simp only [Fin.last, Nat.add_mul, Nat.one_mul]

theorem Term.dsumChain_append_singleton (e a : Term) (es : List Term) :
    Term.dsumChain e (es ++ [a]) = .dsumE (Term.dsumChain e es) a := by
  unfold Term.dsumChain
  rw [List.foldl_append]
  rfl

@[simp] theorem denotSpace_dsumChain (sigma : DEnv) (s : Space) :
    forall n : Nat,
      denotSpace sigma (Space.dsumChain s n) =
        (denotSpace sigma s).dsumPow n
  | 0 => rfl
  | n + 1 => by
      simp only [Space.dsumChain, denotSpace, denotSpaceAux,
        HSpace.dsumPow, denotSpace_dsumChain sigma s n]

@[simp] theorem denotBasis_dsumChain_at_dsumPow
    (sigma : DEnv) (b : Basis) : forall n : Nat,
      (denotBasis sigma (Basis.dsumChain b n)).atSpace
          ((denotSpace sigma (Basis.sof b)).dsumPow n) =
        (denotSpace sigma (Basis.sof b)).dsumPowBasis
          ((denotBasis sigma b).atSpace
            (denotSpace sigma (Basis.sof b))) n
  | 0 => rfl
  | n + 1 => by
      simp only [Basis.dsumChain, denotBasis, Basis.sof,
        HSpace.dsumPow, HSpace.dsumPowBasis]
      rw [Basis.sof_dsumChain, denotSpace_dsumChain]
      rw [BasisDenot.atSpace_vecs_self]
      rw [denotBasis_dsumChain_at_dsumPow sigma b n]

/-- The closed denotation of the syntactic left-associated sum chain is the
corresponding repeated semantic direct-sum vector, provided each component
has the advertised common HSpace. -/
theorem denotTerm_dsumChain_eq_hil_dsumPow
    (sigma : DEnv) (V : HSpace) (e : Term) :
    forall (es : List Term) (x : Nat -> V.carrier),
      (forall j : Fin (es.length + 1),
        denotTerm sigma ((e :: es).getD j.val default) =
          .hil ⟨V, x j.val⟩) ->
      denotTerm sigma (Term.dsumChain e es) =
        .hil ⟨V.dsumPow es.length,
          V.dsumPowVector es.length (fun j => x j.val)⟩ := by
  intro es
  induction es using List.reverseRecOn with
  | nil =>
      intro x h
      have h0 := h (0 : Fin 1)
      simpa [Term.dsumChain, HSpace.dsumPow, HSpace.dsumPowVector] using h0
  | append_singleton es a ih =>
      intro x h
      have hprefix : forall j : Fin (es.length + 1),
          denotTerm sigma ((e :: es).getD j.val default) =
            .hil ⟨V, x j.val⟩ := by
        intro j
        have hj := h (Fin.cast (by simp) j.castSucc)
        simp only [Fin.val_cast, Fin.val_castSucc] at hj
        rw [show e :: (es ++ [a]) = (e :: es) ++ [a] by simp] at hj
        rw [List.getD_append _ _ _ _ (by simpa using j.isLt)] at hj
        exact hj
      let jl : Fin ((es ++ [a]).length + 1) :=
        Fin.cast (by simp) (Fin.last (es.length + 1))
      have ha : denotTerm sigma a = .hil ⟨V, x (es.length + 1)⟩ := by
        have hj := h jl
        simp only [jl, Fin.val_cast, Fin.last] at hj
        rw [show e :: (es ++ [a]) = (e :: es) ++ [a] by simp] at hj
        rw [List.getD_append_right _ _ _ _ (by simp)] at hj
        simpa [List.length_cons] using hj
      rw [Term.dsumChain_append_singleton]
      have hi := ih x hprefix
      change denotTermAux sigma [] (Term.dsumChain e es) = _ at hi
      change denotTermAux sigma [] a = _ at ha
      simp only [denotTerm, denotTermAux]
      rw [hi, ha]
      simp only [DVal.asHil]
      have hlen : (es ++ [a]).length = es.length + 1 := by simp
      rw [hlen]
      rfl

/-- The precise RREF/LexInd interface required by `terms_rref`. -/
def CoordinateRREFLexIndContract : Prop :=
  forall (V : HSpace) (B : List V.carrier) (n : Nat) (xs : List V.carrier),
    IsListBasis V B ->
    forall (hlen : n = xs.length)
      (A : Matrix (Fin B.length) (Fin n) Real),
      (forall j : Fin n,
        xs.get (Fin.cast hlen j) = ∑ i : Fin B.length, A i j • B.get i) ->
      let g := matrixRREF A
      (List.finRange g.rank).map
          (fun k => xs.get (Fin.cast hlen (g.pivots k))) =
        V.lexInd xs

/-- Column list in the canonical coordinate HSpace. -/
def matrixColumnList {m n : Nat} (A : Matrix (Fin m) (Fin n) Real) :
    List (finRealHSpace m).carrier :=
  List.ofFn fun j => fun i => A i j

/-- The original columns selected by an RREF decomposition, in pivot order. -/
noncomputable def matrixPivotColumnList {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) :
    List (finRealHSpace m).carrier :=
  let g := matrixRREF A
  (List.finRange g.rank).map fun k => fun i => A i (g.pivots k)

/-- The coordinate RREF/LexInd correspondence, proved by
`standardRREFLexInd_proved` in `RawTermsRREFLexInd`. It fixes the ordinary
pointwise module structure on coordinate columns. -/
def StandardRREFLexIndContract : Prop :=
  forall {m n : Nat} (A : Matrix (Fin m) (Fin n) Real),
    matrixPivotColumnList A =
      (finRealHSpace m).lexInd (matrixColumnList A)

/-- Discarding a zero tail identifies a sum over `Fin m` with the same
sum over the initial `Fin r`. -/
theorem sum_fin_eq_sum_castLE_of_zero {M : Type*} [AddCommMonoid M]
    {r m : Nat} (h : r <= m) (f : Fin m -> M)
    (hz : forall i : Fin m, r <= i.val -> f i = 0) :
    (∑ i : Fin m, f i) =
      ∑ q : Fin r, f (Fin.castLE h q) := by
  let F : Nat -> M := fun i => if hi : i < m then f ⟨i, hi⟩ else 0
  calc
    (∑ i : Fin m, f i) = ∑ i : Fin m, F i.val := by
      apply Finset.sum_congr rfl
      intro i _
      simp [F, i.isLt]
    _ = ∑ i ∈ Finset.range m, F i := Fin.sum_univ_eq_sum_range F m
    _ = ∑ i ∈ Finset.range r, F i := by
      symm
      apply Finset.sum_subset (Finset.range_mono h)
      intro i him hir
      have him' : i < m := Finset.mem_range.mp him
      have hir' : r <= i :=
        Nat.le_of_not_gt (fun hi => hir (Finset.mem_range.mpr hi))
      simp only [F, him', ↓reduceDIte]
      exact hz ⟨i, him'⟩ hir'
    _ = ∑ q : Fin r, F q.val := (Fin.sum_univ_eq_sum_range F r).symm
    _ = ∑ q : Fin r, f (Fin.castLE h q) := by
      apply Finset.sum_congr rfl
      intro q _
      simp [F, Nat.lt_of_lt_of_le q.isLt h, Fin.castLE]

/-- Every recorded pivot column of the original matrix is the corresponding
column of the inverse row-operation matrix `E`.  This does not require full
row rank. -/
theorem matrixRREF_pivot_column_eq_E_general {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real)
    (r : Fin m) (q : Fin (matrixRREF A).rank) :
    A r ((matrixRREF A).pivots q) =
      (matrixRREF A).E r (Fin.castLE (matrixRREF A).rank_le_m q) := by
  let g := matrixRREF A
  let qr : Fin m := Fin.castLE g.rank_le_m q
  have hfactor := congrFun (congrFun (matrixRREF_factor A) r) (g.pivots q)
  rw [hfactor]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single qr]
  · have hpivot := g.pivot_entries_one q
    simpa only [qr, Fin.castLE, mul_one] using congrArg (g.E r qr * .) hpivot
  · intro k _ hk
    have hkval : k.val ≠ q.val := by
      intro h
      apply hk
      apply Fin.ext
      exact h
    rw [g.pivot_columns_zero q k hkval, mul_zero]
  · intro hqr
    exact (hqr (Finset.mem_univ qr)).elim

/-- Each original column is a linear combination of the original pivot
columns, with coefficients read from the corresponding RREF column. -/
theorem matrixRREF_column_eq_sum_pivots {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (j : Fin n) :
    (fun i : Fin m => A i j) =
      ∑ q : Fin (matrixRREF A).rank,
        (matrixRREF A).R (Fin.castLE (matrixRREF A).rank_le_m q) j •
          (fun i : Fin m => A i ((matrixRREF A).pivots q)) := by
  let g := matrixRREF A
  funext i
  have hfactor := congrFun (congrFun (matrixRREF_factor A) i) j
  rw [hfactor]
  simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [matrixRREF_pivot_column_eq_E_general A]
  rw [sum_fin_eq_sum_castLE_of_zero g.rank_le_m]
  · apply Finset.sum_congr rfl
    intro q _
    ring
  · intro k hk
    rw [g.zero_rows_below k hk, mul_zero]

/-- A total natural-number view of the columns of a finite matrix. -/
noncomputable def matrixColumnNat {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (j : Nat) : Fin m -> Real :=
  if hj : j < n then fun i => A i ⟨j, hj⟩ else 0

/-- Boolean marker for the pivot positions recorded by `matrixRREF`. -/
noncomputable def matrixRREFKeep {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (j : Nat) : Bool :=
  decide (exists q : Fin (matrixRREF A).rank,
    ((matrixRREF A).pivots q).val = j)

/-- The natural-number column enumeration agrees with `matrixColumnList`. -/
theorem matrixColumnList_eq_range {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) :
    matrixColumnList A = (List.range n).map (matrixColumnNat A) := by
  have hl : (matrixColumnList A).length = n := by
    simp [matrixColumnList]
  have hr : ((List.range n).map (matrixColumnNat A)).length = n :=
    (List.length_map (matrixColumnNat A)).trans List.length_range
  apply List.ext_getElem (hl.trans hr.symm)
  intro j hj0 hj1
  have hj : j < n := by
    exact hr ▸ hj1
  change (List.ofFn (fun k : Fin n => fun i : Fin m => A i k))[j] =
    ((List.range n).map (matrixColumnNat A))[j]
  rw [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  simp [matrixColumnNat, hj]

/-- Membership in the greedy accumulator has the expected pivot-prefix
description. -/
theorem mem_rref_keptPrefix_iff {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (bound : Nat)
    (w : Fin m -> Real) :
    w ∈ @HSpace.keptPrefix (finRealHSpace m)
        (matrixColumnNat A) (matrixRREFKeep A) bound ↔
      exists q : Fin (matrixRREF A).rank,
        ((matrixRREF A).pivots q).val < bound /\
        w = fun i => A i ((matrixRREF A).pivots q) := by
  classical
  change w ∈ (((List.range bound).filter (matrixRREFKeep A)).map
      (matrixColumnNat A)) ↔ _
  constructor
  · intro hw
    rw [List.mem_map] at hw
    obtain ⟨j, hjf, hjw⟩ := hw
    rw [List.mem_filter] at hjf
    have hj : j < bound := List.mem_range.mp hjf.1
    have hp : exists q : Fin (matrixRREF A).rank,
        ((matrixRREF A).pivots q).val = j := by
      simpa [matrixRREFKeep] using hjf.2
    obtain ⟨q, hq⟩ := hp
    refine ⟨q, hq.symm ▸ hj, ?_⟩
    rw [← hjw]
    have hjn : j < n := hq ▸ ((matrixRREF A).pivots q).isLt
    simp only [matrixColumnNat, dif_pos hjn]
    funext i
    apply congrArg (fun col : Fin n => A i col)
    exact Fin.ext hq.symm
  · rintro ⟨q, hq, rfl⟩
    rw [List.mem_map]
    refine ⟨((matrixRREF A).pivots q).val, ?_, ?_⟩
    · rw [List.mem_filter]
      refine ⟨List.mem_range.mpr hq, ?_⟩
      simp [matrixRREFKeep]
    · simp [matrixColumnNat, (matrixRREF A).pivots q |>.isLt]

/-- Applying the recorded inverse row operation to an original pivot column
produces the corresponding standard coordinate vector. -/
theorem matrixRREF_reduce_pivot_column {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real)
    (q : Fin (matrixRREF A).rank) :
    (matrixRREF A).E_inv.mulVecLin
        (fun i : Fin m => A i ((matrixRREF A).pivots q)) =
      Pi.single (Fin.castLE (matrixRREF A).rank_le_m q) (1 : Real) := by
  let g := matrixRREF A
  have hreduce : g.E_inv * A = g.R := by
    calc
      g.E_inv * A = g.E_inv * (g.E * g.R) := by
        rw [← matrixRREF_factor A]
      _ = (g.E_inv * g.E) * g.R := by rw [Matrix.mul_assoc]
      _ = (1 : Matrix (Fin m) (Fin m) Real) * g.R := by
        rw [g.E_left_inv, Matrix.diagonal_one]
      _ = g.R := Matrix.one_mul _
  funext k
  have hentry := congrFun (congrFun hreduce k) (g.pivots q)
  simp only [Matrix.mul_apply] at hentry
  rw [Matrix.mulVecLin_apply]
  change (∑ r : Fin m, g.E_inv k r * A r (g.pivots q)) = _
  rw [hentry]
  by_cases hk : k.val = q.val
  · have hk' : k = Fin.castLE g.rank_le_m q := by
      apply Fin.ext
      exact hk
    subst k
    have hrow : Fin.castLE g.rank_le_m q =
        ⟨q.val, Nat.lt_of_lt_of_le q.isLt g.rank_le_m⟩ := by
      apply Fin.ext
      rfl
    rw [hrow, g.pivot_entries_one q]
    simp
  · have hk' : k ≠ Fin.castLE g.rank_le_m q := by
      intro h
      apply hk
      exact congrArg Fin.val h
    rw [g.pivot_columns_zero q k hk]
    simp [Pi.single_apply, hk']

/-- The pivot columns are linearly independent, directly from the RREF
shape fields and the recorded inverse row operation. -/
theorem matrixRREF_pivot_columns_linearIndependent {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) :
    LinearIndependent Real (fun q : Fin (matrixRREF A).rank =>
      fun i : Fin m => A i ((matrixRREF A).pivots q)) := by
  let g := matrixRREF A
  let inc : Fin g.rank -> Fin m := Fin.castLE g.rank_le_m
  have hinc : Function.Injective inc := by
    intro i j hij
    apply Fin.ext
    exact Fin.mk.inj_iff.mp hij
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hc' := congrArg (fun v => g.E_inv.mulVecLin v) hc
  simp only [map_sum, map_smul, map_zero] at hc'
  dsimp only [g] at hc'
  simp_rw [matrixRREF_reduce_pivot_column A] at hc'
  have hp := congrFun hc' (inc p)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    Pi.single_apply, mul_ite, mul_one, mul_zero] at hp
  change (∑ q, if inc p = inc q then c q else 0) = 0 at hp
  simpa [hinc.eq_iff] using hp

/-- Once the coordinate-only RREF contract is available, transport through
the actual list-basis coordinate equivalence proves the fully semantic
contract. -/
theorem standardRREFLexInd_implies_coordinate
    (hstd : StandardRREFLexIndContract) :
    CoordinateRREFLexIndContract := by
  intro V B n xs hB hlen
  subst n
  intro A hcols
  let Q := finRealHSpace B.length
  let e : Q.carrier ≃ₗ[Real] V.carrier := hB.toBasis.equivFun.symm
  let f : Q.carrier →ₗ[Real] V.carrier := e.toLinearMap
  let cols : List Q.carrier := matrixColumnList A
  have hf : Function.Injective f := e.injective
  have hfcol : forall j : Fin xs.length,
      f (fun i : Fin B.length => A i j) = xs.get j := by
    intro j
    change hB.toBasis.equivFun.symm (fun i : Fin B.length => A i j) = _
    rw [Module.Basis.equivFun_symm_apply]
    simp only [IsListBasis.toBasis_apply]
    exact (hcols j).symm
  have hmap : cols.map f = xs := by
    calc
      cols.map f = List.ofFn
          (f ∘ fun j : Fin xs.length => fun i : Fin B.length => A i j) := by
        simp [cols, matrixColumnList, List.map_ofFn]
      _ = List.ofFn xs.get := by
        congr 1
        funext j
        exact hfcol j
      _ = xs := List.ofFn_get xs
  have hlex := HSpace.lexInd_map_injective Q V f hf cols
  have hpiv := hstd A
  calc
    (List.finRange (matrixRREF A).rank).map
        (fun k => xs.get ((matrixRREF A).pivots k)) =
        (matrixPivotColumnList A).map f := by
      unfold matrixPivotColumnList
      simp only [List.map_map]
      apply List.map_congr_left
      intro k _
      exact (hfcol ((matrixRREF A).pivots k)).symm
    _ = ((Q.lexInd cols).map f) := by
      exact congrArg (List.map f) hpiv
    _ = V.lexInd (cols.map f) := hlex.symm
    _ = V.lexInd xs := congrArg (V.lexInd) hmap

@[simp] theorem termsCandidateMatrix_term_column
    {N K : Nat} (termCoords : Nat -> Real) (i : Fin N) (j : Fin K) :
    termsCandidateMatrix N K termCoords i (Fin.castAdd N j) =
      termCoords (j.val * N + i.val) := by
  simp [termsCandidateMatrix]

@[simp] theorem termsCandidateMatrix_basis_column
    {N K : Nat} (termCoords : Nat -> Real) (i j : Fin N) :
    termsCandidateMatrix N K termCoords i (Fin.natAdd K j) =
      if i = j then 1 else 0 := by
  simp [termsCandidateMatrix, Fin.ext_iff]

/-- Appending the full identity family forces the chosen RREF decomposition
to have full row rank.  This is derivable from the current factorization,
zero-row, and inverse fields; it does not need the RREF/LexInd axiom. -/
theorem termsCandidateMatrix_rref_rank
    {N K : Nat} (termCoords : Nat -> Real) :
    (matrixRREF (termsCandidateMatrix N K termCoords)).rank = N := by
  classical
  let A := termsCandidateMatrix N K termCoords
  let g := matrixRREF A
  apply Nat.le_antisymm g.rank_le_m
  by_contra hle
  have hlt : g.rank < N := Nat.lt_of_not_ge hle
  let k : Fin N := ⟨g.rank, hlt⟩
  have hreduce : g.E_inv * A = g.R := by
    calc
      g.E_inv * A = g.E_inv * (g.E * g.R) := by
        rw [← matrixRREF_factor A]
      _ = (g.E_inv * g.E) * g.R := by rw [Matrix.mul_assoc]
      _ = (1 : Matrix (Fin N) (Fin N) Real) * g.R := by
        rw [g.E_left_inv, Matrix.diagonal_one]
      _ = g.R := Matrix.one_mul _
  have hzero : forall r : Fin N, g.E_inv k r = 0 := by
    intro r
    have hentry := congrFun (congrFun hreduce k) (Fin.natAdd K r)
    have hRzero : g.R k (Fin.natAdd K r) = 0 :=
      g.zero_rows_below k (by simp [k]) (Fin.natAdd K r)
    rw [Matrix.mul_apply, hRzero] at hentry
    have hnot : ¬ K + r.val < K :=
      Nat.not_lt_of_ge (Nat.le_add_right K r.val)
    have hentry' : g.E_inv k r = 0 := by
      simpa [A, termsCandidateMatrix, hnot, mul_ite] using hentry
    exact hentry'
  have hone := congrFun (congrFun g.E_left_inv k) k
  simp [Matrix.mul_apply, hzero] at hone

/-- A square RREF transformation's recorded left inverse is also a right
inverse.  This is the only inverse fact needed by the output orientation. -/
theorem matrixRREF_E_mul_E_inv {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) :
    (matrixRREF A).E * (matrixRREF A).E_inv = 1 := by
  apply (mul_eq_one_comm.mp ?_)
  simpa only [Matrix.diagonal_one] using (matrixRREF A).E_left_inv

/-- At full row rank, pivot column `i` of the original candidate matrix is
column `i` of `rref.E`. -/
theorem matrixRREF_pivot_column_eq_E {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real)
    (hRank : (matrixRREF A).rank = m) (r i : Fin m) :
    A r ((matrixRREF A).pivots (Fin.cast hRank.symm i)) =
      (matrixRREF A).E r i := by
  let g := matrixRREF A
  let q : Fin g.rank := Fin.cast hRank.symm i
  have hfactor := congrFun (congrFun (matrixRREF_factor A) r) (g.pivots q)
  rw [hfactor]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · have hpivot := g.pivot_entries_one q
    have hrow : (⟨q.val, Nat.lt_of_lt_of_le q.isLt g.rank_le_m⟩ : Fin m) = i := by
      apply Fin.ext
      exact rfl
    rw [← hrow, hpivot, mul_one]
  · intro k _ hki
    have hkval : k.val ≠ q.val := by
      intro h
      apply hki
      apply Fin.ext
      exact h
    rw [g.pivot_columns_zero q k hkval, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Matrix-level soundness and orientation of the candidate implementation. -/
theorem termsRREFRepMatrix_row_expansion
    {V : Type*} [AddCommGroup V] [Module Real V]
    {N K : Nat} (termCoords oldCob : Nat -> Real)
    (B S T : Fin N -> V)
    (hRank : (matrixRREF (termsCandidateMatrix N K termCoords)).rank = N)
    (hSource : forall j : Fin N,
      S j = ∑ r : Fin N, denotAsMatrix N N oldCob j r • B r)
    (hTarget : forall i : Fin N,
      T i = ∑ r : Fin N,
        termsCandidateMatrix N K termCoords r
          ((matrixRREF (termsCandidateMatrix N K termCoords)).pivots
            (Fin.cast hRank.symm i)) • B r) :
    forall j : Fin N, S j = ∑ i : Fin N,
      termsRREFRepMatrix N K termCoords oldCob j i • T i := by
  let A := termsCandidateMatrix N K termCoords
  let C := denotAsMatrix N N oldCob
  let g := matrixRREF A
  have hright : g.E * g.E_inv = 1 := matrixRREF_E_mul_E_inv A
  have hpivot : forall r i : Fin N,
      A r (g.pivots (Fin.cast hRank.symm i)) = g.E r i := by
    exact matrixRREF_pivot_column_eq_E A hRank
  have hTarget' : forall i : Fin N,
      T i = ∑ r : Fin N,
        A r (g.pivots (Fin.cast hRank.symm i)) • B r := by
    intro i
    simpa only [A, g] using hTarget i
  have hB : forall r : Fin N,
      B r = ∑ i : Fin N, g.E_inv i r • T i := by
    intro r
    conv_rhs =>
      enter [2, i]
      rw [hTarget' i]
    simp_rw [hpivot]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    conv_rhs =>
      enter [2, k]
      rw [← Finset.sum_smul]
    have hentry : forall k : Fin N,
        (∑ i : Fin N, g.E_inv i r * g.E k i) =
          if k = r then 1 else 0 := by
      intro k
      have h := congrFun (congrFun hright k) r
      simpa only [Matrix.mul_apply, Matrix.one_apply, mul_comm] using h
    simp_rw [hentry]
    simp
  intro j
  rw [hSource]
  simp_rw [hB]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_smul]
  congr 1

theorem termsRREFRepMatrix_row_expansion_full
    {V : Type*} [AddCommGroup V] [Module Real V]
    {N K : Nat} (termCoords oldCob : Nat -> Real)
    (B S T : Fin N -> V)
    (hSource : forall j : Fin N,
      S j = ∑ r : Fin N, denotAsMatrix N N oldCob j r • B r)
    (hTarget : forall i : Fin N,
      T i = ∑ r : Fin N,
        termsCandidateMatrix N K termCoords r
          ((matrixRREF (termsCandidateMatrix N K termCoords)).pivots
            (Fin.cast (termsCandidateMatrix_rref_rank termCoords).symm i)) • B r) :
    forall j : Fin N, S j = ∑ i : Fin N,
      termsRREFRepMatrix N K termCoords oldCob j i • T i := by
  exact termsRREFRepMatrix_row_expansion termCoords oldCob B S T
    (termsCandidateMatrix_rref_rank termCoords) hSource hTarget

theorem termsRREFRepMatrix_cob_of_coordinates
    (hcoord : CoordinateRREFLexIndContract)
    (V : HSpace) (B S xs : List V.carrier)
    (hB : IsListBasis V B)
    (termCoords oldCob : Nat -> Real)
    (hSource : forall j : Fin B.length,
      S.getD j.val 0 =
        ∑ r : Fin B.length,
          denotAsMatrix B.length B.length oldCob j r • B.getD r.val 0)
    (hTerms : forall j : Fin xs.length,
      xs.get j =
        ∑ i : Fin B.length,
          termCoords (j.val * B.length + i.val) • B.get i) :
    let T := V.lexInd (xs ++ B)
    T.length = B.length /\
      forall j : Fin B.length,
        S.getD j.val 0 = ∑ i : Fin B.length,
          termsRREFRepMatrix B.length xs.length termCoords oldCob j i •
            T.getD i.val 0 := by
  classical
  let A := termsCandidateMatrix B.length xs.length termCoords
  let g := matrixRREF A
  let T := V.lexInd (xs ++ B)
  have hcols : forall j : Fin (xs.length + B.length),
      (xs ++ B).get (Fin.cast (by simp) j) =
        ∑ i : Fin B.length, A i j • B.get i := by
    intro j
    change (xs ++ B)[j.val] = _
    by_cases hj : j.val < xs.length
    · let jx : Fin xs.length := ⟨j.val, hj⟩
      have hjx : jx.val = j.val := by simp [jx]
      rw [List.getElem_append_left hj]
      trans ∑ i : Fin B.length,
        termCoords (jx.val * B.length + i.val) • B.get i
      · simpa only [List.get_eq_getElem, hjx] using hTerms jx
      apply Finset.sum_congr rfl
      intro i _
      simp [A, termsCandidateMatrix, hj, hjx]
    · have hjle : xs.length ≤ j.val := Nat.le_of_not_gt hj
      have hjB : j.val - xs.length < B.length := by
        have := j.isLt
        omega
      let jb : Fin B.length := ⟨j.val - xs.length, hjB⟩
      rw [List.getElem_append_right hjle]
      change B.get jb = _
      have hentry : forall i : Fin B.length,
          A i j = if i = jb then 1 else 0 := by
        intro i
        simp [A, termsCandidateMatrix, hj, jb, Fin.ext_iff]
      simp_rw [hentry]
      simp
  have hpiv' := hcoord V B (xs.length + B.length) (xs ++ B) hB
    (by simp) A hcols
  have hpiv :
      (List.finRange g.rank).map
          (fun k => (xs ++ B).get (Fin.cast (by simp) (g.pivots k))) = T := by
    simpa only [A, g, T, List.length_append] using hpiv'
  have hrank : g.rank = B.length := by
    simpa only [g, A] using
      termsCandidateMatrix_rref_rank termCoords
  have hTlen : T.length = B.length := by
    rw [← hpiv]
    simp [hrank]
  refine ⟨hTlen, ?_⟩
  have hTarget : forall i : Fin B.length,
      T.getD i.val 0 = ∑ r : Fin B.length,
        A r (g.pivots (Fin.cast hrank.symm i)) • B.getD r.val 0 := by
    intro i
    let q : Fin g.rank := Fin.cast hrank.symm i
    have hiT : i.val < T.length := by simpa only [hTlen] using i.isLt
    have hTget : T.getD i.val 0 =
        (xs ++ B).get (Fin.cast (by simp) (g.pivots q)) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiT]
      simp only [Option.getD_some]
      have himap : i.val <
          ((List.finRange g.rank).map
            (fun k => (xs ++ B).get (Fin.cast (by simp) (g.pivots k)))).length := by
        simp [hrank, i.isLt]
      have hq := List.getElem_of_eq hpiv himap
      rw [← hq]
      simp [q]
      congr 2
    rw [hTget]
    have hcolq := hcols (g.pivots q)
    rw [hcolq]
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    simp [q]
  exact termsRREFRepMatrix_row_expansion_full termCoords oldCob
    (fun i => B.getD i.val 0) (fun j => S.getD j.val 0)
    (fun i => T.getD i.val 0) hSource (by
      intro i
      simpa only [A, g] using hTarget i)

/-- Evaluator read-off for the checked `terms_rref` expression in positive
ambient dimension. -/
theorem denotValB_semS_termsRREFRep_ok
    (orc : FFSOracleSem) (rho : ValEnvSem)
    {env0 env1 : ValExpr} {sv : ValSpace}
    {a0 a1 : FlatArray} {N K : Nat}
    (h0 : denotValB_semS orc rho [] [] env0 = .ok (.array a0))
    (h1 : denotValB_semS orc rho [] [] env1 = .ok (.array a1))
    (hsv : ValSpace.dof (orc rho [] []) sv = N)
    (ha0 : a0.length = K * N)
    (ha1 : a1.length = N * N)
    (hN : 0 < N) :
    denotValB_semS orc rho [] []
        (ValExpr.reshapBase
          (.rrefRep env0
            (ValExpr.reshapBase env1 (.tprod sv sv)))
          (.tprod sv sv)) =
      .ok (.array (FlatArray.ofFn (N * N)
        (termsRREFRepDenot N K a0.get a1.get))) := by
  have hdim : ValSpace.dof (orc rho [] []) (.tprod sv sv) = N * N := by
    simp only [ValSpace.dof_tprod, hsv]
  have hinner : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env1 (.tprod sv sv)) = .ok (.array a1) := by
    apply denotValB_semS_reshap_space_ok
    · exact h1
    · exact ha1.trans hdim.symm
  have hK' : a0.length / N = K := by
    rw [ha0]
    exact Nat.mul_div_cancel K hN
  have hrref : denotValB_semS orc rho [] []
      (.rrefRep env0 (ValExpr.reshapBase env1 (.tprod sv sv))) =
      .ok (.array (FlatArray.ofFn (N * N)
        (termsRREFRepDenot N K a0.get a1.get))) := by
    rw [denotValB_semS, h0, hinner]
    simp only [ValValSem.bindArrays, ValValSem.bindArray,
      ValExpr.reshapBase, ValExpr.inferSpaceCtx, ValTy.spaceOf_space,
      ValSpace.dof_tprod, hsv, ValValSem.arrayOf]
    rw [hK']
    simp only [ha0, ha1, and_self, if_true]
  apply denotValB_semS_reshap_space_ok
  · exact hrref
  · simp only [FlatArray.length_ofFn, hdim]

end GLang
