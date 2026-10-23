import GLang.Proofs.Adequacy.Partial.Source.PartialSourceLinearSums
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceWellFormed
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceFFS

namespace GLang.PartialAdequacy
open Basis (BasisValid)

theorem arm_inner_std
    {orc : PartialFFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 : Basis}
    {s : GLang.Space} {sv : ValSpace}
    (hb0 : Basis.isStd b0)
    (hsof : Basis.sof b0 = s)
    (_ht : Nonempty (HasType ∅ Gamma (.inner s)
      (Basis.tof (.tprod (.dual b0) (.dual b0)))))
    (hbv : BasisValid Gamma (.tprod (.dual b0) (.dual b0)))
    (_hTy : S.TyAt Gamma Psi (.tprod (.dual b0) (.dual b0))
      (.space (.tprod sv sv)))
    (_hsv : S.Space Gamma Psi s sv)
    (ihTy : MTyAtSubctx orc Gamma Psi
      (.tprod (.dual b0) (.dual b0)) (.space (.tprod sv sv)))
    (ihSpace : MSpaceSubctx orc Gamma Psi s sv) :
    MTermSubctx orc ∅ Gamma Psi (.inner s)
      (.tprod (.dual b0) (.dual b0)) (.idelta sv)
      (.space (.tprod sv sv)) := by
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims : DimsAt orc sigma rho [] [] []
      (Basis.tof (.tprod (.dual b0) (.dual b0)))
      (.space (.tprod sv sv))
      (denotBasis sigma (.tprod (.dual b0) (.dual b0))) :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hb0v : BasisValid Gamma b0 := by
    cases hbv with
    | tprod h _ _ _ =>
        cases h with
        | dual h _ => exact h
  obtain ⟨hlb, horth⟩ := denotBasis_std_orthonormal_core
    (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl hb0
  have hshape : ValSpace.shpOfPartial (orc rho [] []) sv =
      .ok (srcShp sigma [] s) :=
    ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  subst s
  have hr := inner (shape_dof hshape) hlb.finrank_eq.symm hlb horth
  refine ⟨?_,targetDims⟩
  simpa only [Basis.tof, Basis.sof, denotBasis, denotSpace, denotSpaceAux,
    denotTerm, denotTermAux, BasisDenot.atSpace_vecs_self] using hr

end GLang.PartialAdequacy
