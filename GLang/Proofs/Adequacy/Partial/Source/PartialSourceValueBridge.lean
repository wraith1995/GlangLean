import GLang.Proofs.Adequacy.Partial.Source.PartialSourceRepresentation

namespace GLang.PartialAdequacy

theorem DimsAt.valueOpenPush
    {orc : PartialFFSOracleSem}
    (horacle : PartialDirectOpenPush.OracleOpenPush orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlcSigma : ValTy.lc sigmaV) (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall {sigma : DEnv} {Ds : List DVal} {tau : Ty}
      {tauV : ValTy} {B : BasisDenot},
      G.length = D.length -> y ∉ ValTy.fv tauV ->
      DimsAt orc sigma (rho.update y w) Ds
        (ValTy.closePrefix (.var y sigmaV) G) D tau
        (ValTy.openRec G.length (.var y sigmaV) tauV) B ->
      DimsAt orc sigma rho Ds
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
        simp only [ValTy.openRec, DimsAt] at hd ⊢
        have hb := (PartialDirectOpenPush.observations horacle
          ⟨rho,y,sigmaV,w,G,D,hlen,hlcSigma,hySigma,hyG⟩ sv hyTau).2
        change (ValSpace.openRec G.length (.var y sigmaV) sv).shpOfPartial
          (orc (rho.update y w) (ValTy.closePrefix (.var y sigmaV) G) D) =
          sv.shpOfPartial (orc rho (G ++ [sigmaV]) (D ++ [w])) at hb
        rw [← hb]
        exact hd
      | piTy _ _ =>
        simp only [ValTy.openRec] at hd
        simpa only [DimsAt] using hd
    | piTy tau0 tau1 =>
      cases tauV with
      | space _ =>
        simp only [ValTy.openRec] at hd
        simpa only [DimsAt] using hd
      | piTy tauV0 tauV1 =>
        simp only [ValTy.fv, Finset.mem_union, not_or] at hyTau
        simp only [ValTy.openRec, DimsAt] at hd ⊢
        have hdomLt : Ty.size tau0 + ValTy.kindSize tauV0 < n := by
          simp only [Ty.size, ValTy.kindSize_piTy] at hn
          omega
        have hdomPushed : DimsAt orc sigma rho Ds
            (G ++ [sigmaV]) (D ++ [w]) tau0 tauV0 B.domainBasis :=
          ih (Ty.size tau0 + ValTy.kindSize tauV0) hdomLt
            hyG hlen hyTau.1 hd.1 rfl
        refine ⟨hdomPushed, ?_⟩
        intro x' argVal argPushed htoPushed hargPushed
        have hsame : ValSoundOfDenot.ValTy.SameShape tauV0
            (ValTy.openRec G.length (.var y sigmaV) tauV0) :=
          (ValSoundOfDenot.ValTy.SameShape_openRec
            G.length (.var y sigmaV) tauV0).symm
        have hargNamed : Agree orc sigma (rho.update y w) Ds
            (ValTy.closePrefix (.var y sigmaV) G) D tau0
            (ValTy.openRec G.length (.var y sigmaV) tauV0) B.domainBasis
            ((denotTyAux sigma Ds tau0).embed x') argVal :=
          Agree.representation_transport sigma hsame
            hdomPushed hd.1 hargPushed
        obtain ⟨argNamed, htoNamed, _⟩ := hargNamed.decode
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

/-- Successful partial evaluation and source agreement commute with opening
at a fresh named binder, retaining the identical raw argument. -/
theorem ResultAgree.valueOpenPush
    {orc : PartialFFSOracleSem}
    (horacle : PartialDirectOpenPush.OracleOpenPush orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlcSigma : ValTy.lc sigmaV) (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    {sigma : DEnv} {Ds : List DVal} {tau : Ty}
    {tauV : ValTy} {B : BasisDenot} {source : DVal} {e : ValExpr}
    (hlen : G.length = D.length) (hyTau : y ∉ ValTy.fv tauV)
    (hyE : y ∉ ValExpr.fv e)
    (hd : DimsAt orc sigma (rho.update y w) Ds
      (ValTy.closePrefix (.var y sigmaV) G) D tau
      (ValTy.openRec G.length (.var y sigmaV) tauV) B)
    (hr : ResultAgree orc sigma (rho.update y w) Ds
      (ValTy.closePrefix (.var y sigmaV) G) D tau
      (ValTy.openRec G.length (.var y sigmaV) tauV) B source
      (denotValB_partial orc (rho.update y w)
        (ValTy.closePrefix (.var y sigmaV) G) D
        (ValExpr.openRec G.length (.var y sigmaV) e))) :
    ResultAgree orc sigma rho Ds (G ++ [sigmaV]) (D ++ [w]) tau tauV B source
      (denotValB_partial orc rho (G ++ [sigmaV]) (D ++ [w]) e) := by
  obtain ⟨out,hout,ha⟩ := hr
  have hdt := DimsAt.valueOpenPush horacle hlcSigma hySigma hyG hlen hyTau hd
  have he := PartialDirectOpenPush.eval_open orc horacle rho y sigmaV w G D e
    hlen hlcSigma hySigma hyG hyE
  refine ⟨out,he.symm.trans hout,?_⟩
  exact Agree.representation_transport sigma
    (ValSoundOfDenot.ValTy.SameShape_openRec G.length (.var y sigmaV) tauV)
    hd hdt ha

end GLang.PartialAdequacy
