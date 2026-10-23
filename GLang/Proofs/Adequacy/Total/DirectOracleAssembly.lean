import GLang.Proofs.Adequacy.Total.DirectOracleFv
import GLang.Proofs.Adequacy.Total.DirectOracleEval
import GLang.Proofs.Adequacy.Raw.RawOracleTransport

/-!
# Direct-oracle open/push assembly

The direct fixed point needs prefix-general evaluator transport internally.
`DirectOracleEval` derives that transport from the one-leaf oracle law; this
file uses it in the paired well-founded induction that constructs
`RawValueOpenPushOracleCoherent` for the direct oracle.
-/

namespace GLang.DirectOracleAssembly

open DirectOracleWF
open DirectOracleFv
open DirectOracleEval

private theorem derivedDirectQuery_openPush_of_evalPrefix
    (hEval : EvalPrefixFromLeaf)
    (rho : ValEnvSem) (y : VName) (sigmaV : ValTy) (w : ValValSem)
    (G : List ValTy) (D : List ValValSem) (property : ValFFSProp)
    (parent : ValSpace) (witness : ValExpr)
    (hlen : G.length = D.length)
    (hlcSigma : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    (hyParent : y ∉ ValSpace.fv parent)
    (hyWitness : y ∉ ValExpr.fv witness) :
    derivedDirectQuery
        ⟨rho.update y w, ValTy.closePrefix (.var y sigmaV) G, D,
          property, ValSpace.openRec G.length (.var y sigmaV) parent,
          ValExpr.openRec G.length (.var y sigmaV) witness⟩ =
      derivedDirectQuery
        ⟨rho, G ++ [sigmaV], D ++ [w], property, parent, witness⟩ := by
  let namedRoot : Query :=
    ⟨rho.update y w, ValTy.closePrefix (.var y sigmaV) G, D,
      property, ValSpace.openRec G.length (.var y sigmaV) parent,
      ValExpr.openRec G.length (.var y sigmaV) witness⟩
  let pushedRoot : Query :=
    ⟨rho, G ++ [sigmaV], D ++ [w], property, parent, witness⟩
  have hrootMeasure : Query.derivedMeasure namedRoot =
      Query.derivedMeasure pushedRoot := by
    exact Query.derivedMeasure_open_push_prefix rho y sigmaV w G D property
      parent witness hlen hlcSigma hySigma hyG hyParent hyWitness
  generalize hn : Query.derivedMeasure pushedRoot = n
  induction n using Nat.strong_induction_on generalizing
      rho y sigmaV w G D property parent witness with
  | h n ih =>
      let guarded : FFSOracleSem :=
        smallerDerivedOracle pushedRoot
          (fun query _ => derivedDirectQuery query)
      have guarded_openPush : RawValueOpenPushOracleCoherent guarded := by
        intro rho' y' sigmaV' w' G' D' property' parent' witness'
          hlen' hlcSigma' hySigma' hyG' hyParent' hyWitness'
        let named : Query :=
          ⟨rho'.update y' w',
            ValTy.closePrefix (.var y' sigmaV') G', D', property',
            ValSpace.openRec G'.length (.var y' sigmaV') parent',
            ValExpr.openRec G'.length (.var y' sigmaV') witness'⟩
        let pushed : Query :=
          ⟨rho', G' ++ [sigmaV'], D' ++ [w'], property', parent', witness'⟩
        have hmeasure : Query.derivedMeasure named =
            Query.derivedMeasure pushed := by
          exact Query.derivedMeasure_open_push_prefix rho' y' sigmaV' w'
            G' D' property' parent' witness' hlen' hlcSigma' hySigma'
            hyG' hyParent' hyWitness'
        change
          (if _ : Query.derivedMeasure named <
                Query.derivedMeasure pushedRoot then
              derivedDirectQuery named
            else 0) =
          (if _ : Query.derivedMeasure pushed <
                Query.derivedMeasure pushedRoot then
              derivedDirectQuery pushed
            else 0)
        by_cases hlt : Query.derivedMeasure pushed <
            Query.derivedMeasure pushedRoot
        · have hlt' : Query.derivedMeasure named <
              Query.derivedMeasure pushedRoot := by
            simpa only [hmeasure] using hlt
          rw [dif_pos hlt, dif_pos hlt']
          exact ih (Query.derivedMeasure pushed)
            (by simpa only [hn] using hlt)
            rho' y' sigmaV' w' G' D' property' parent' witness'
            hlen' hlcSigma' hySigma' hyG' hyParent' hyWitness'
            hmeasure rfl
        · have hlt' : ¬ Query.derivedMeasure named <
              Query.derivedMeasure pushedRoot := by
            simpa only [hmeasure] using hlt
          rw [dif_neg hlt, dif_neg hlt']
      have hguardedRoots :
          smallerDerivedOracle namedRoot
              (fun query _ => derivedDirectQuery query) = guarded := by
        funext rho' G' D' property' parent' witness'
        simp only [guarded, smallerDerivedOracle]
        rw [hrootMeasure]
      have hshape := rawShpOf_valueOpenPush guarded_openPush
        (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
        (G := G) (D := D) hlen hlcSigma hySigma hyG parent hyParent
      have heval := hEval guarded guarded_openPush
        (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
        (G := G) (D := D) (e := witness)
        hlen hlcSigma hySigma hyG hyWitness
      change derivedDirectQuery namedRoot = derivedDirectQuery pushedRoot
      rw [derivedDirectQuery_eq namedRoot, derivedDirectQuery_eq pushedRoot]
      simp only [derivedStep,hrootMeasure]
      split
      · rfl
      rw [hguardedRoots, hshape]
      unfold ffsOperandRank
      rw [hshape, heval]

/-- The direct well-founded oracle satisfies the primitive leafwise
fresh-name/de-Bruijn law once corrected inference supplies structural
prefix-general evaluator transport. -/
theorem derivedDirectOracle_valueOpenPush
    (hEval : EvalPrefixFromLeaf) :
    RawValueOpenPushOracleCoherent derivedDirectOracle := by
  intro rho y sigmaV w G D property parent witness
    hlen hlcSigma hySigma hyG hyParent hyWitness
  exact derivedDirectQuery_openPush_of_evalPrefix hEval
    rho y sigmaV w G D property parent witness hlen hlcSigma
    hySigma hyG hyParent hyWitness

theorem derivedDirectOracle_rawAdequacySpec_of_prefix
    (hPrefix : EvalPrefixFromLeaf) :
    RawAdequacyOracleSpec derivedDirectOracle := by
  have hleaf : RawValueOpenPushOracleCoherent derivedDirectOracle :=
    derivedDirectOracle_valueOpenPush hPrefix
  exact
    { toOracleSpec := derivedDirectOracle_spec
      valueOpenPushOracleCoherent := hleaf }

/-- End-to-end constructive oracle package consumed by raw adequacy. -/
theorem derivedDirectOracle_rawAdequacySpec :
    RawAdequacyOracleSpec derivedDirectOracle :=
  derivedDirectOracle_rawAdequacySpec_of_prefix evalPrefixFromLeaf

end GLang.DirectOracleAssembly
