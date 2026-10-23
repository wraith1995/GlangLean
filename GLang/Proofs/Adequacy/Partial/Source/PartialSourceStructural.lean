import GLang.Proofs.Adequacy.Partial.Source.PartialSourceReshape
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMotives

namespace GLang.PartialAdequacy
open Basis (BasisValid)

theorem arm_var_nlin
    {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {tauv : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (_hGamma : Gamma.lookup x = some (Basis.tof b))
    (_hbv : BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b tauv)
    (ihTy : MTyAtSubctx orc Gamma Psi b tauv) :
    MTermSubctx orc ∅ Gamma Psi (.var x) b v tauv := by
  intro Psi' hsub _hdisj rho Delta' Gamma' sigma GammaV hle hc
  have hlookup' : EvalCtx.lookup Psi' (x, b) = some v :=
    hsub (x, b) v hlookup
  obtain ⟨tauStored, xs, Gamma0, Psi0, _hsigma, hStoredTy,
      _hinferSpace, hresult, hdimsStored⟩ :=
    hc.history.lookup_current_result hirr hlookup'
  have hdimsTarget : DimsAt orc sigma rho [] [] []
      (Basis.tof b) tauv (denotBasis sigma b) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hshape : ValSoundOfDenot.ValTy.SameShape tauStored tauv :=
    evalT_sameShape hStoredTy (hTy.mono hsub).toEvalT
  obtain ⟨out, hout, hagree⟩ := hresult
  exact ⟨⟨out, hout,
    Agree.representation_transport sigma hshape hdimsStored hdimsTarget hagree⟩, hdimsTarget⟩

theorem arm_var_lin
    {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} {s : Space} {tauV : ValTy}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (_htof : Basis.tof b = .space s)
    (_hbv : BasisValid Gamma b)
    (hTy : S.TyAt Gamma Psi b tauV)
    (ihTy : MTyAtSubctx orc Gamma Psi b tauV) :
    MTermSubctx orc (Finmap.singleton x s) Gamma Psi
      (.var x) b v tauV := by
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have hlookup' : EvalCtx.lookup Psi' (x, b) = some v :=
    hsub (x, b) v hlookup
  obtain ⟨tauStored, xs, Gamma0, Psi0, _hsigma, hStoredTy,
      _hinferSpace, hresult, hdimsStored⟩ :=
    hc.history.lookup_current_result hirr hlookup'
  have hdimsTarget : DimsAt orc sigma rho [] [] []
      (Basis.tof b) tauV (denotBasis sigma b) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hshape : ValSoundOfDenot.ValTy.SameShape tauStored tauV :=
    evalT_sameShape hStoredTy (hTy.mono hsub).toEvalT
  obtain ⟨out, hout, hagree⟩ := hresult
  exact ⟨⟨out, hout,
    Agree.representation_transport sigma hshape hdimsStored hdimsTarget hagree⟩, hdimsTarget⟩

theorem arm_promote
    {orc : PartialFFSOracleSem}
    {Delta lin : LCtx} {Gamma Gamma'' : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (_hdDelta : Finmap.Disjoint lin Delta)
    (hdGamma : Finmap.Disjoint lin.toNL Gamma'')
    (_hfr : PromoteFresh lin Delta Gamma)
    (hleP : NLCtxIncl Gamma Gamma'')
    (_ht : Nonempty (HasType Delta (lin.toNL ∪ Gamma'') e (Basis.tof b)))
    (_hbv : BasisValid (lin.toNL ∪ Gamma'') b)
    (_hTy : S.TyAt (lin.toNL ∪ Gamma'') Psi b tauV)
    (_he : S.Term (lin ∪ Delta) Gamma Psi e b v tauV)
    (ih : MTermSubctx orc (lin ∪ Delta) Gamma Psi e b v tauV) :
    MTermSubctx orc Delta (lin.toNL ∪ Gamma'') Psi e b v tauV := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have hctxP : Graded.CtxDisj (lin ∪ Delta) Gamma := fun x hxD hxG =>
    Graded.CtxDisj.promote_inner hctx hdGamma x hxD (hleP.mem_of hxG)
  apply ih hsub hctxP rho Delta' Gamma' sigma GammaV ?_ hc
  refine ⟨?_, ?_⟩
  · intro x s hx
    by_cases hmem : x ∈ lin
    · rw [Finmap.lookup_union_left hmem] at hx
      have hnl : (lin.toNL ∪ Gamma'').lookup x = some (.space s) := by
        have hl := LCtx.toNL_lookup lin x s hx
        rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hl)]
        exact hl
      exact Or.inr (hle.2 x _ hnl)
    · rw [Finmap.lookup_union_right hmem] at hx
      exact hle.1 x s hx
  · intro x tau hx
    have hx'' : Gamma''.lookup x = some tau := hleP x tau hx
    have hnot : x ∉ lin.toNL := fun hm =>
      hdGamma x hm (Finmap.mem_of_lookup_eq_some hx'')
    apply hle.2 x tau
    rw [Finmap.lookup_union_right hnot]
    exact hx''

theorem arm_reshape
    {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauv tauv' : ValTy}
    (_ht : Nonempty (HasType Delta Gamma e (Basis.tof b)))
    (_hbv : BasisValid Gamma b)
    (_hTy : S.TyAt Gamma Psi b tauv')
    (_he : S.Term Delta Gamma Psi e b v tauv)
    (ihTy : MTyAtSubctx orc Gamma Psi b tauv')
    (ihE : MTermSubctx orc Delta Gamma Psi e b v tauv) :
    MTermSubctx orc Delta Gamma Psi e b
      (.reshap v tauv' tauv) tauv' := by
  intro Psi' hsub hdisj rho Delta' Gamma' sigma GammaV hle hc
  let child := ihE hsub hdisj rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : DimsAt orc sigma rho [] [] []
      (Basis.tof b) tauv' (denotBasis sigma b) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  exact reshape_compiled (_he.mono hsub) hc.history hirr targetDims child

end GLang.PartialAdequacy
