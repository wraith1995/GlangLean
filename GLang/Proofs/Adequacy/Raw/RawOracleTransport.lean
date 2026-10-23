import GLang.Proofs.Adequacy.Raw.RawAgreementTransport
import GLang.Proofs.Adequacy.Raw.RawNonBetaValueKernel
import GLang.Proofs.Adequacy.Total.DirectOracleEval

/-!
# Raw binder transport from value-language coherence

The public oracle boundary contains no adequacy judgment. This module derives
the fresh-name/de-Bruijn bridges used by the direct mutual proof from a single
FFS-leaf equation. Full evaluator coherence follows constructively from that
leaf equation; transport of the `RawAgree` payload is structural.
-/

namespace GLang

/-! ## Leaf-to-shape transport -/

/-- The one-leaf presentation equation propagates through a whole value-space
shape. The dependent prefix is kept explicit for use below Pi binders. -/
theorem rawShpOf_valueOpenPush
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (hlcSigma : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall (sv : ValSpace), y ∉ ValSpace.fv sv ->
      ValSpace.shpOf
          (orc (rho.update y w) (ValTy.closePrefix (.var y sigmaV) G) D)
          (ValSpace.openRec G.length (.var y sigmaV) sv) =
        ValSpace.shpOf (orc rho (G ++ [sigmaV]) (D ++ [w])) sv := by
  intro sv hySv
  generalize hn : ValSpace.size sv = n
  induction n using Nat.strong_induction_on generalizing sv with
  | h n ih =>
    cases sv with
    | empty => simp only [ValSpace.openRec, ValSpace.shpOf]
    | real => simp only [ValSpace.openRec, ValSpace.shpOf]
    | dsum sv0 sv1 =>
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hySv
      have hlt0 : ValSpace.size sv0 < n := by
        simp only [ValSpace.size] at hn
        omega
      have hlt1 : ValSpace.size sv1 < n := by
        simp only [ValSpace.size] at hn
        omega
      have ih0 := ih (ValSpace.size sv0) hlt0 sv0 hySv.1 rfl
      have ih1 := ih (ValSpace.size sv1) hlt1 sv1 hySv.2 rfl
      have hd0 := congrArg (fun xs => xs.foldr (fun a b => a * b) 1) ih0
      have hd1 := congrArg (fun xs => xs.foldr (fun a b => a * b) 1) ih1
      simp only [ValSpace.openRec, ValSpace.shpOf_dsum, ValSpace.dof,
        hd0, hd1]
    | tprod sv0 sv1 =>
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hySv
      have hlt0 : ValSpace.size sv0 < n := by
        simp only [ValSpace.size] at hn
        omega
      have hlt1 : ValSpace.size sv1 < n := by
        simp only [ValSpace.size] at hn
        omega
      have ih0 := ih (ValSpace.size sv0) hlt0 sv0 hySv.1 rfl
      have ih1 := ih (ValSpace.size sv1) hlt1 sv1 hySv.2 rfl
      have hd0 := congrArg (fun xs => xs.foldr (fun a b => a * b) 1) ih0
      have hd1 := congrArg (fun xs => xs.foldr (fun a b => a * b) 1) ih1
      simp only [ValSpace.openRec, ValSpace.shpOf_tprod, ValSpace.dof,
        hd0, hd1]
    | ffs p s e =>
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hySv
      simp only [ValSpace.openRec, ValSpace.shpOf_ffs]
      exact congrArg List.singleton
        (horacle hlen hlcSigma hySigma hyG hySv.1 hySv.2)

/-- Fresh-name/de-Bruijn transport for raw dimensions, derived from the
single-FFS-leaf equation. The recursion is generalized over the dependent
prefix introduced by enclosing Pi codomains. -/
theorem RawAgreeDimsAt.valueOpenPush
    {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlcSigma : ValTy.lc sigmaV) (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall {sigma : DEnv} {Ds : List DVal} {tau : Ty}
      {tauV : ValTy} {B : BasisDenot},
      G.length = D.length -> y ∉ ValTy.fv tauV ->
      RawAgreeDimsAt orc sigma (rho.update y w) Ds
        (ValTy.closePrefix (.var y sigmaV) G) D tau
        (ValTy.openRec G.length (.var y sigmaV) tauV) B ->
      RawAgreeDimsAt orc sigma rho Ds
        (G ++ [sigmaV]) (D ++ [w]) tau tauV B := by
  intro sigma Ds tau tauV B hlen hyTau hd
  generalize hn : Ty.size tau + ValTy.kindSize tauV = n
  induction n using Nat.strong_induction_on generalizing
      Ds G D tau tauV B with
  | h n ih =>
    cases tau with
    | space s =>
      cases tauV with
      | space sv =>
        simp only [ValTy.fv] at hyTau
        simp only [ValTy.openRec, RawAgreeDimsAt] at hd ⊢
        rw [← rawShpOf_valueOpenPush horacle hlen hlcSigma hySigma hyG sv hyTau]
        exact hd
      | piTy _ _ =>
        simp only [ValTy.openRec] at hd
        simpa only [RawAgreeDimsAt] using hd
    | piTy tau0 tau1 =>
      cases tauV with
      | space _ =>
        simp only [ValTy.openRec] at hd
        simpa only [RawAgreeDimsAt] using hd
      | piTy tauV0 tauV1 =>
        simp only [ValTy.fv, Finset.mem_union, not_or] at hyTau
        simp only [ValTy.openRec, RawAgreeDimsAt] at hd ⊢
        have hdomLt : Ty.size tau0 + ValTy.kindSize tauV0 < n := by
          simp only [Ty.size, ValTy.kindSize_piTy] at hn
          omega
        have hdomPushed : RawAgreeDimsAt orc sigma rho Ds
            (G ++ [sigmaV]) (D ++ [w]) tau0 tauV0 B.domainBasis :=
          ih (Ty.size tau0 + ValTy.kindSize tauV0) hdomLt
            hyG hlen hyTau.1 hd.1 rfl
        have hyPushed : ValTyCtxFresh y (G ++ [sigmaV]) := by
          intro tauV' htauV'
          rw [List.mem_append] at htauV'
          rcases htauV' with htauV' | htauV'
          · exact hyG tauV' htauV'
          · rw [List.mem_singleton] at htauV'
            subst tauV'
            exact hySigma
        refine ⟨hdomPushed, ?_⟩
        intro x' argVal argPushed htoPushed hargPushed
        have hdomPushedUpdate : RawAgreeDimsAt orc sigma (rho.update y w) Ds
            (G ++ [sigmaV]) (D ++ [w]) tau0 tauV0 B.domainBasis :=
          (RawAgreeDimsAt.update_of_not_mem_fv hirr sigma rho y w
            tau0 tauV0 Ds (G ++ [sigmaV]) (D ++ [w]) B.domainBasis
            hyPushed hyTau.1).mpr hdomPushed
        have hargPushedUpdate : RawAgree orc sigma (rho.update y w) Ds
            (G ++ [sigmaV]) (D ++ [w]) tau0 tauV0 B.domainBasis
            ((denotTyAux sigma Ds tau0).embed x') argVal :=
          (RawAgree.update_of_not_mem_fv hirr sigma rho y w
            tau0 tauV0 Ds (G ++ [sigmaV]) (D ++ [w]) B.domainBasis
            ((denotTyAux sigma Ds tau0).embed x') argVal
            hyPushed hyTau.1).mpr hargPushed
        have hsame : ValSoundOfDenot.ValTy.SameShape tauV0
            (ValTy.openRec G.length (.var y sigmaV) tauV0) :=
          (ValSoundOfDenot.ValTy.SameShape_openRec
            G.length (.var y sigmaV) tauV0).symm
        have hargNamed : RawAgree orc sigma (rho.update y w) Ds
            (ValTy.closePrefix (.var y sigmaV) G) D tau0
            (ValTy.openRec G.length (.var y sigmaV) tauV0) B.domainBasis
            ((denotTyAux sigma Ds tau0).embed x') argVal :=
          RawAgree.realize_transport orc sigma (rho.update y w) hsame
            hdomPushedUpdate hd.1 hargPushedUpdate
        obtain ⟨argNamed, htoNamed⟩ := hargNamed.toEl
        have hcodNamed := hd.2 x' argVal argNamed htoNamed hargNamed
        have hcodLt : Ty.size tau1 + ValTy.kindSize tauV1 < n := by
          simp only [Ty.size, ValTy.kindSize_piTy] at hn
          omega
        have hlen' : (tauV0 :: G).length = (argVal :: D).length := by
          simp only [List.length_cons, hlen]
        have hyG' : forall t, t ∈ tauV0 :: G -> y ∉ ValTy.fv t := by
          intro t ht
          simp only [List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact hyTau.1
          · exact hyG t ht
        have hcodPushed :=
          ih (Ty.size tau1 + ValTy.kindSize tauV1) hcodLt
            hyG' hlen' hyTau.2 hcodNamed rfl
        simpa only [ValTy.closePrefix, List.length_cons,
          Nat.succ_eq_add_one] using hcodPushed

/-- The leaf equation implies the exact dimension bridge consumed by the
direct mutual adequacy proof. -/
theorem RawAdequacyOracleSpec.rawBinderCoherent
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc) :
    RawAgreeDimsValueOpenPushAt orc := by
  intro sigma rho y tau tauV sigmaV d w B hlcSigma hySigma hyTau hdims
  simpa only [ValTy.closePrefix, List.nil_append, ValTy.openVar] using
    RawAgreeDimsAt.valueOpenPush hspec.toOracleSpec.fvIrrel
      hspec.valueOpenPushOracleCoherent (rho := rho) (y := y)
      (sigmaV := sigmaV) (w := w) (G := []) (D := [])
      hlcSigma hySigma (by simp) (sigma := sigma) (Ds := [d])
      (tau := tau) (tauV := tauV) (B := B) rfl hyTau hdims

/-- The evaluator equation follows from depth-aware lookup and the primitive leaf law. -/
theorem RawAdequacyOracleSpec.valueOpenPushEvalCoherent
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc) :
    RawValueOpenPushEvalCoherent orc :=
  DirectOracleEval.valueOpenPushEvalCoherent_from_leaf
    hspec.valueOpenPushOracleCoherent

/-- The primitive value-language equation derives the full evaluator result
bridge. The agreement payload is transported structurally from the named and
pushed dimension facts; it is not an oracle assumption. -/
theorem RawAdequacyOracleSpec.rawResultBinderCoherent
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc) :
    RawResultAgreeValueOpenPushAt orc := by
  intro sigma rho y tau tauV sigmaV d w B source e
    hlcSigma hlcOpen hySigma hyTau hyE hdims hresult
  have hpushedDims : RawAgreeDimsAt orc sigma rho [d] [sigmaV] [w]
      tau tauV B := hspec.rawBinderCoherent hlcSigma hySigma hyTau hdims
  have hpushedDimsUpdate : RawAgreeDimsAt orc sigma (rho.update y w)
      [d] [sigmaV] [w] tau tauV B :=
    (RawAgreeDimsAt.update_of_not_mem_fv hspec.toOracleSpec.fvIrrel
      sigma rho y w tau tauV [d] [sigmaV] [w] B
      (by simp [ValTyCtxFresh, hySigma]) hyTau).mpr hpushedDims
  obtain ⟨value, hnamedEval, hnamedAgree⟩ := hresult
  have hshape : ValSoundOfDenot.ValTy.SameShape
      (ValTy.openVar y sigmaV tauV) tauV :=
    ValSoundOfDenot.ValTy.SameShape_openRec 0 (.var y sigmaV) tauV
  have hpushedAgreeUpdate : RawAgree orc sigma (rho.update y w)
      [d] [sigmaV] [w] tau tauV B source value :=
    RawAgree.realize_transport orc sigma (rho.update y w) hshape
      hdims hpushedDimsUpdate hnamedAgree
  have hpushedAgree : RawAgree orc sigma rho [d] [sigmaV] [w]
      tau tauV B source value :=
    (RawAgree.update_of_not_mem_fv hspec.toOracleSpec.fvIrrel sigma rho y w
      tau tauV [d] [sigmaV] [w] B source value
      (by simp [ValTyCtxFresh, hySigma]) hyTau).mp hpushedAgreeUpdate
  have heval := hspec.valueOpenPushEvalCoherent
    (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
    (e := e) hlcSigma hlcOpen hySigma hyE
  refine ⟨value, ?_, hpushedAgree⟩
  exact heval.symm.trans hnamedEval

end GLang
