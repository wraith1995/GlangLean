import GLang.Value.Supporting.TotalDimensionSemantics
import Lean

/-! The live canonical-FSV leaf must use GSVD, with exact agreement and no
additional assumptions. This gate is included in the maintenance suite. -/
open GLang Lean Elab Command

/-- Successes and failures agree with the paired canonical specification for
all arrays, including malformed shapes and non-positive-definite metrics. -/
example (which : ValFFSProp) (m n : ℕ) (a g h : FlatArray) :
    ValueCanonicalFSV.eval which m n a g h = (by
      classical
      exact if GSVDInputsShape m n a g h then
        let A := (denotAsMatrix m n a.get).transpose
        let G := denotAsMatrix m m g.get
        let H := denotAsMatrix n n h.get
        if hG : G.PosDef then
          if hH : H.PosDef then .ok (ValueCanonicalFSV.select which A G H hG hH)
          else .error .mismatch
        else .error .mismatch
      else .error .mismatch) := by
  classical
  simp only [ValueCanonicalFSV.eval, ValueCanonicalFSV.selectGSVD_eq_select]

elab "check_canonical_gsvd_bridge" : command => do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ValuePairedSVD.factorization,
      ``ValuePairedSVD.image_coordinates,
      ``ValuePairedSVD.U_ofCoords, ``ValuePairedSVD.UI_ofCoords,
      ``ValuePairedSVD.V_ofCoords, ``ValuePairedSVD.VI_ofCoords,
      ``ValueCanonicalFSV.selectGSVD_eq_select, ``ValueCanonicalFSV.eval_ok] do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless standard.contains ax do
        throwError "Unexpected assumption in {n}: {ax}"
  -- Check the actual evaluator's definition path, not just available lemmas.
  for (src, dst) in [(``ValueCanonicalFSV.eval, ``ValueCanonicalFSV.selectGSVD),
      (``ValueCanonicalFSV.selectGSVD, ``ValueCanonicalFSV.select),
      (``ValueCanonicalFSV.select, ``ValuePairedSVD.decomposition),
      (``ValuePairedSVD.decomposition, ``ValuePairedSVD.u),
      (``ValuePairedSVD.decomposition, ``ValuePairedSVD.v)] do
    let some body := (← getConstInfo src).value? |
      throwError "Missing implementation: {src}"
    unless body.getUsedConstants.contains dst do
      throwError "Live GSVD path disconnected: {src} does not use {dst}"
  logInfo "Live paired GSVD equals source FSV, with unchanged errors and only standard foundations."

check_canonical_gsvd_bridge
#print axioms GLang.ValueCanonicalFSV.selectGSVD_eq_select

/-- The value language contains no separate FSV primitive. All five selectors
have live checked equations using the single paired numerical package. -/
elab "check_svd_selector_surface" : command => do
  let .inductInfo info ← getConstInfo ``ValExpr | throwError "Expected ValExpr syntax"
  if info.ctors.contains ``ValExpr.canonicalFSV then
    throwError "FSV remains a primitive value constructor"
  let .defnInfo _ ← getConstInfo ``ValExpr.canonicalFSV |
    throwError "Uniform block selection must be a derived definition"
  for (eqn, leaf) in [(``denotValB_semS.eq_19, ``ValueCanonicalFSV.evalSigma),
      (``denotValB_semS.eq_20, ``ValueCanonicalFSV.eval),
      (``denotValB_semS.eq_21, ``ValueCanonicalFSV.eval),
      (``denotValB_semS.eq_22, ``ValueCanonicalFSV.eval),
      (``denotValB_semS.eq_23, ``ValueCanonicalFSV.eval)] do
    let info ← getConstInfo eqn
    unless info.type.getUsedConstants.contains leaf do
      throwError "Selector equation {eqn} is disconnected from {leaf}"
  for src in [``ValueCanonicalFSV.evalSigma, ``ValueCanonicalFSV.standard] do
    let some body := (← getConstInfo src).value? | throwError "Missing selector body"
    unless body.getUsedConstants.contains ``ValuePairedSVD.decomposition do
      throwError "Selector {src} is disconnected from the paired decomposition"
  logInfo "No FSV value constructor; all SVD selectors use the paired convention."

check_svd_selector_surface

example (m n : ℕ) (a g h : FlatArray)
    (hs : ¬ GSVDInputsShape m n a g h) :
    ValueCanonicalFSV.evalSigma m n a g h = .error .mismatch :=
  ValueCanonicalFSV.evalSigma_shape_mismatch m n a g h hs

example (m n : ℕ) (a g h : FlatArray)
    (hg : ¬ (denotAsMatrix m m g.get).PosDef) :
    ValueCanonicalFSV.evalSigma m n a g h = .error .mismatch := by
  classical
  simp [ValueCanonicalFSV.evalSigma, hg]
