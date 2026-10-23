import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectEval
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectFv
import GLang.Proofs.Adequacy.Foundations.QueryStateOpening

/-! Constructive binder transport for the complete partial oracle. -/
namespace GLang.PartialDirectOpenPush
open DirectOracleWF PartialValueTransport

private theorem query_openPush
    (rho : ValEnvSem) (y : VName) (sigmaV : ValTy) (w : ValValSem)
    (G : List ValTy) (D : List ValValSem) (property : ValFFSProp)
    (parent : ValSpace) (witness : ValExpr)
    (hlen : G.length = D.length)
    (hlcSigma : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    (hyParent : y ∉ ValSpace.fv parent)
    (hyWitness : y ∉ ValExpr.fv witness) :
    PartialDirectOracle.query
        ⟨rho.update y w, ValTy.closePrefix (.var y sigmaV) G, D,
          property, ValSpace.openRec G.length (.var y sigmaV) parent,
          ValExpr.openRec G.length (.var y sigmaV) witness⟩ =
      PartialDirectOracle.query
        ⟨rho, G ++ [sigmaV], D ++ [w], property, parent, witness⟩ := by
  let namedRoot : Query :=
    ⟨rho.update y w, ValTy.closePrefix (.var y sigmaV) G, D,
      property, ValSpace.openRec G.length (.var y sigmaV) parent,
      ValExpr.openRec G.length (.var y sigmaV) witness⟩
  let pushedRoot : Query :=
    ⟨rho, G ++ [sigmaV], D ++ [w], property, parent, witness⟩
  have hrootMeasure : Query.certifiedMeasure namedRoot =
      Query.certifiedMeasure pushedRoot := by
    exact Query.certifiedMeasure_open_push_prefix rho y sigmaV w G D property
      parent witness hlen hlcSigma hySigma hyG hyParent hyWitness
  generalize hn : Query.certifiedMeasure pushedRoot = n
  induction n using Nat.strong_induction_on generalizing
      rho y sigmaV w G D property parent witness with
  | h n ih =>
      let guarded : PartialFFSOracleSem :=
        PartialDirectOracle.smallerOracle pushedRoot
          (fun query _ => PartialDirectOracle.query query)
      have guarded_openPush : OracleOpenPush guarded := by
        intro rho' y' sigmaV' w' G' D' property' parent' witness'
          hlen' hlcSigma' hySigma' hyG' hyParent' hyWitness'
        let named : Query :=
          ⟨rho'.update y' w',
            ValTy.closePrefix (.var y' sigmaV') G', D', property',
            ValSpace.openRec G'.length (.var y' sigmaV') parent',
            ValExpr.openRec G'.length (.var y' sigmaV') witness'⟩
        let pushed : Query :=
          ⟨rho', G' ++ [sigmaV'], D' ++ [w'], property', parent', witness'⟩
        have hmeasure : Query.certifiedMeasure named =
            Query.certifiedMeasure pushed := by
          exact Query.certifiedMeasure_open_push_prefix rho' y' sigmaV' w'
            G' D' property' parent' witness' hlen' hlcSigma' hySigma'
            hyG' hyParent' hyWitness'
        change
          (if _ : Query.certifiedMeasure named <
                Query.certifiedMeasure pushedRoot then
              PartialDirectOracle.query named
            else .error .mismatch) =
          (if _ : Query.certifiedMeasure pushed <
                Query.certifiedMeasure pushedRoot then
              PartialDirectOracle.query pushed
            else .error .mismatch)
        by_cases hlt : Query.certifiedMeasure pushed <
            Query.certifiedMeasure pushedRoot
        · have hlt' : Query.certifiedMeasure named <
              Query.certifiedMeasure pushedRoot := by
            simpa only [hmeasure] using hlt
          rw [dif_pos hlt, dif_pos hlt']
          exact ih (Query.certifiedMeasure pushed)
            (by simpa only [hn] using hlt)
            rho' y' sigmaV' w' G' D' property' parent' witness'
            hlen' hlcSigma' hySigma' hyG' hyParent' hyWitness'
            hmeasure rfl
        · have hlt' : ¬ Query.certifiedMeasure named <
              Query.certifiedMeasure pushedRoot := by
            simpa only [hmeasure] using hlt
          rw [dif_neg hlt, dif_neg hlt']
      have hguardedRoots :
          PartialDirectOracle.smallerOracle namedRoot
              (fun query _ => PartialDirectOracle.query query) = guarded := by
        funext rho' G' D' property' parent' witness'
        simp only [guarded, PartialDirectOracle.smallerOracle]
        rw [hrootMeasure]
      let W : World guarded := ⟨rho, y, sigmaV, w, G, D, hlen, hlcSigma, hySigma, hyG⟩
      have hshape := (observations guarded_openPush W parent hyParent).2
      have heval := eval_open guarded guarded_openPush rho y sigmaV w G D witness
        hlen hlcSigma hySigma hyG hyWitness
      change PartialDirectOracle.query namedRoot = PartialDirectOracle.query pushedRoot
      rw [PartialDirectOracle.query_eq namedRoot, PartialDirectOracle.query_eq pushedRoot]
      simp only [PartialDirectOracle.step, hrootMeasure]
      split
      · rfl
      rw [hguardedRoots]
      change ffsDimensionPartial property
        ((ValSpace.openRec G.length W.u parent).shpOfPartial (guarded W.namedRho W.namedG W.namedD))
        (denotValB_partial guarded W.namedRho W.namedG W.namedD
          (ValExpr.openRec G.length W.u witness)) = _
      change denotValB_partial guarded W.namedRho W.namedG W.namedD
        (ValExpr.openRec G.length W.u witness) =
        denotValB_partial guarded W.pushedRho W.pushedG W.pushedD witness at heval
      rw [hshape, heval]
      rfl

/-- The direct well-founded oracle satisfies the primitive leafwise
fresh-name/de-Bruijn law once corrected inference supplies structural
prefix-general evaluator transport. -/
theorem oracle_openPush :
    OracleOpenPush PartialDirectOracle.oracle := by
  intro rho y sigmaV w G D property parent witness
    hlen hlcSigma hySigma hyG hyParent hyWitness
  exact query_openPush
    rho y sigmaV w G D property parent witness hlen hlcSigma
    hySigma hyG hyParent hyWitness

/-- The connected evaluator's named-variable and bound-slot presentations agree
on the complete partial result. No oracle law remains as a caller premise. -/
theorem eval_openPush
    (rho : ValEnvSem) (y : VName) (sigmaV : ValTy) (w : ValValSem)
    (G : List ValTy) (D : List ValValSem) (e : ValExpr)
    (hlen : G.length = D.length) (hlc : sigmaV.lc) (hySigma : y ∉ sigmaV.fv)
    (hyG : ValTyCtxFresh y G) (hy : y ∉ e.fv) :
    Adequacy.Partial.evalVal (rho.update y w) (ValTy.closePrefix (.var y sigmaV) G) D
      (ValExpr.openRec G.length (.var y sigmaV) e) =
    Adequacy.Partial.evalVal rho (G ++ [sigmaV]) (D ++ [w]) e :=
  eval_open PartialDirectOracle.oracle oracle_openPush rho y sigmaV w G D e
    hlen hlc hySigma hyG hy

/-- Checking at a partially interpreted type commutes with the binder bridge. -/
theorem check_type_openPush (W : World PartialDirectOracle.oracle) (t : ValTy)
    (ht : W.y ∉ t.fv) (a : (ValTy.openRec W.G.length W.u t).carrierEl)
    (b : t.carrierEl) (hab : HEq a b) :
    HEq (checkValTyPartial PartialDirectOracle.oracle W.namedRho W.namedG W.namedD
        (ValTy.openRec W.G.length W.u t) a)
      (checkValTyPartial PartialDirectOracle.oracle W.pushedRho W.pushedG W.pushedD t b) := by
  have hs := ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u t
  have hT := type_heq oracle_openPush t W ht
  have hh := bind_heq (type_eq hs) (ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hs)
    _ _ hT
    (fun T => PartialValType.check (τ := ValTy.openRec W.G.length W.u t) T a)
    (fun T => PartialValType.check (τ := t) T b)
    (fun T T' hTT => check_heq hs T T' hTT a b hab)
  have equation (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
      (τ : ValTy) (v : τ.carrierEl) :
      checkValTyPartial PartialDirectOracle.oracle ρ Γ Δ τ v =
        (denotValTyPartial PartialDirectOracle.oracle ρ Γ Δ τ).bind
          (fun T => PartialValType.check (τ := τ) T v) := by
    unfold checkValTyPartial
    cases denotValTyPartial PartialDirectOracle.oracle ρ Γ Δ τ <;> rfl
  rw [equation, equation]
  exact hh

/-- The checked connected endpoint preserves the full partial result across
named/bound syntax, including checks in arbitrarily nested dependent fibers. -/
theorem checked_openPush (W : World PartialDirectOracle.oracle) (t : ValTy) (e : ValExpr)
    (ht : W.y ∉ t.fv) (he : W.y ∉ e.fv) :
    HEq (Adequacy.Partial.evalValCheckedAt W.namedRho W.namedG W.namedD
        (ValTy.openRec W.G.length W.u t) (ValExpr.openRec W.G.length W.u e))
      (Adequacy.Partial.evalValCheckedAt W.pushedRho W.pushedG W.pushedD t e) := by
  have hev := eval_openPush W.rho W.y W.sigmaV W.w W.G W.D e
    W.length_eq W.sigma_lc W.y_sigma W.y_G he
  have hs := ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u t
  have hc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hs
  simp only [Adequacy.Partial.evalValCheckedAt, denotValB_partialCheckedAt]
  have hev' : denotValB_partial PartialDirectOracle.oracle W.namedRho W.namedG W.namedD
      (ValExpr.openRec W.G.length W.u e) =
      denotValB_partial PartialDirectOracle.oracle W.pushedRho W.pushedG W.pushedD e := hev
  rw [hev']
  cases hv : denotValB_partial PartialDirectOracle.oracle W.pushedRho W.pushedG W.pushedD e with
  | error err => exact except_error_heq hc err
  | ok v =>
      simp only []
      have hd := carrierFromVal_SameShape _ _ hs v
      have hh := bind_heq hc hc _ _ hd
        (fun a => checkValTyPartial PartialDirectOracle.oracle W.namedRho W.namedG W.namedD
          (ValTy.openRec W.G.length W.u t) a)
        (fun b => checkValTyPartial PartialDirectOracle.oracle W.pushedRho W.pushedG W.pushedD t b)
        (fun a b hab => check_type_openPush W t ht a b hab)
      generalize hn : (ValTy.openRec W.G.length W.u t).carrierFromVal v = named at hh ⊢
      generalize hp : t.carrierFromVal v = pushed at hh ⊢
      cases named <;> cases pushed <;> simpa only [Except.bind] using hh

end GLang.PartialDirectOpenPush
