import GLang.Numerics.SVD.PairedSVDCoordinates
import GLang.Numerics.SVD.ValueNumericalInputs
import GLang.Value.Binding

/-! Checked selection of the paired canonical GSVD blocks.

Domain blocks project the ordered coordinate axes and apply lexInd and
normalized Gram–Schmidt. Positive codomain columns are normalized images of
the paired domain columns; the zero codomain block is projected independently.
The coordinate-chart theorems identify these exact lists with source FSV.
Input arrays store the map domain first; output columns use C-order.
-/
noncomputable section
namespace GLang.ValueCanonicalFSV
open BasisSpectral

/-- An exact matrix shape, retained before flattening. -/
structure ResultMatrix where
  rows : ℕ
  cols : ℕ
  data : Matrix (Fin rows) (Fin cols) ℝ

/-- Store the entire matrix, including literal zero dimensions. -/
def ResultMatrix.flatten (r : ResultMatrix) : FlatArray :=
  FlatArray.ofFn (r.rows * r.cols) (matrixAsDenot r.data)

/-- Exact C-order indexing, without transposing the selected columns. -/
theorem ResultMatrix.flatten_get (r : ResultMatrix) (i : Fin r.rows) (j : Fin r.cols) :
    r.flatten.get (r.cols * i.val + j.val) = r.data i j := by
  have hn : r.cols ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)
  have hidx : r.cols * i.val + j.val < r.rows * r.cols := by
    nlinarith [i.isLt, j.isLt]
  rw [ResultMatrix.flatten, FlatArray.get_ofFn_lt _ _ _ hidx]
  simp [matrixAsDenot, hn, Nat.mul_add_div (Nat.pos_of_ne_zero hn),
    Nat.div_eq_of_lt j.isLt, Nat.mod_eq_of_lt j.isLt, i.isLt]

/-- Select a block of the single paired, canonical GSVD. -/
def select {m n : ℕ} (which : ValFFSProp) (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) : ResultMatrix :=
  let g := ValuePairedSVD.decomposition A G H hG hH
  match which with
  | .kernel => ⟨m, m - A.rank, g.UI⟩
  | .cokernel => ⟨m, A.rank, g.U⟩
  | .image => ⟨n, A.rank, g.V⟩
  | .coimage => ⟨n, n - A.rank, g.VI⟩

abbrev selectGSVD := @select

theorem selectGSVD_eq_select {m n : ℕ} (which : ValFFSProp)
    (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    selectGSVD which A G H hG hH = select which A G H hG hH := rfl

/-- Reject malformed flat shapes and non-positive-definite metric inputs. -/
def eval (which : ValFFSProp) (m n : ℕ) (a g h : FlatArray) : Except DimError ResultMatrix := by
  classical
  exact if GSVDInputsShape m n a g h then
    let A := (denotAsMatrix m n a.get).transpose
    let G := denotAsMatrix m m g.get
    let H := denotAsMatrix n n h.get
    if hG : G.PosDef then
      if hH : H.PosDef then .ok (selectGSVD which A G H hG hH)
      else .error .mismatch
    else .error .mismatch
  else .error .mismatch

/-- The exact success equation needed by each operational embedding arm. -/
theorem eval_ok (which : ValFFSProp) (m n : ℕ) (a g h : FlatArray)
    (hs : GSVDInputsShape m n a g h)
    (hg : (denotAsMatrix m m g.get).PosDef)
    (hh : (denotAsMatrix n n h.get).PosDef) :
    eval which m n a g h = .ok (select which
      (denotAsMatrix m n a.get).transpose
      (denotAsMatrix m m g.get) (denotAsMatrix n n h.get) hg hh) := by
  simp only [eval, hs, if_true, dif_pos hg, dif_pos hh, selectGSVD_eq_select]

theorem eval_shape_mismatch (which : ValFFSProp) (m n : ℕ) (a g h : FlatArray)
    (hs : ¬ GSVDInputsShape m n a g h) :
    eval which m n a g h = .error .mismatch := by
  simp only [eval, hs, if_false]

theorem eval_metric_mismatch (which : ValFFSProp) (m n : ℕ) (a g h : FlatArray)
    (hg : ¬ (denotAsMatrix m m g.get).PosDef ∨ ¬ (denotAsMatrix n n h.get).PosDef) :
    eval which m n a g h = .error .mismatch := by
  classical
  rcases hg with hg | hh
  · simp [eval, hg]
  · simp [eval, hh]

/-- Runtime success certifies both input shapes and genuine metric validity. -/
theorem eval_success_valid (which : ValFFSProp) (m n : ℕ) (a g h : FlatArray)
    (r : ResultMatrix) (hr : eval which m n a g h = .ok r) :
    GSVDInputsShape m n a g h ∧ (denotAsMatrix m m g.get).PosDef ∧
      (denotAsMatrix n n h.get).PosDef := by
  classical
  unfold eval at hr
  split at hr
  · rename_i hs
    dsimp only at hr
    split at hr
    · rename_i hg
      split at hr
      · rename_i hh
        exact ⟨hs, hg, hh⟩
      · contradiction
    · contradiction
  · contradiction
/-- Reject malformed flat shapes and non-positive-definite metric inputs. -/
def evalSigma (m n : ℕ) (a g h : FlatArray) : Except DimError ResultMatrix := by
  classical
  exact if GSVDInputsShape m n a g h then
    let A := (denotAsMatrix m n a.get).transpose
    let G := denotAsMatrix m m g.get
    let H := denotAsMatrix n n h.get
    if hG : G.PosDef then
      if hH : H.PosDef then .ok (⟨A.rank, A.rank, (ValuePairedSVD.decomposition A G H hG hH).sMat⟩)
      else .error .mismatch
    else .error .mismatch
  else .error .mismatch

theorem evalSigma_shape_mismatch (m n : ℕ) (a g h : FlatArray)
    (hs : ¬ GSVDInputsShape m n a g h) :
    evalSigma m n a g h = .error .mismatch := by
  simp only [evalSigma, hs, if_false]

/-- Identity-metric specialization of the same paired decomposition. -/
def standard {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : GSVDecomposition m n :=
  ValuePairedSVD.decomposition A 1 1 Matrix.PosDef.one Matrix.PosDef.one

end GLang.ValueCanonicalFSV
