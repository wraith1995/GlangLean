import GLang.Proofs.Adequacy.Raw.RawSpaceFFSAdequacy
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobAdequacyCore

namespace GLang

open Basis (BasisValid)

/-- The two concrete endpoints of `image_svds` are valid bases of the same
image space, hence have equal list lengths in every raw-consistent world. -/
theorem raw_denotBasis_image_svds_length
    {Gamma : NLCtx} {sigma : DEnv} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis}
    (hctx : CtxWF ∅ Gamma) (henv : EnvWF sigma ∅ Gamma)
    (hbSrc : BasisValid Gamma
      (.image (.proj (.coker s0 s1 e) b0 b1)))
    (hbTgt : BasisValid Gamma
      (.proj (.img s0 s1 e) b0 b1)) :
    ((denotBasis sigma
        (.image (.proj (.coker s0 s1 e) b0 b1))).atSpace
      (denotSpace sigma
        (Basis.sof (.image (.proj (.coker s0 s1 e) b0 b1))))).length =
      ((denotBasis sigma (.proj (.img s0 s1 e) b0 b1)).atSpace
        (denotSpace sigma
          (Basis.sof (.proj (.img s0 s1 e) b0 b1)))).length := by
  exact raw_denotBasis_length_eq_of_sof_eq hctx henv hbSrc hbTgt rfl

/-- Oracle-independent inference core for `image_svds`.  The only facts it
needs about the two FFS results are their ordinary space adequacy statements;
callers may obtain those either from `OracleSpec` or from certified eventual
queries in the direct mutual induction. -/
theorem raw_arm_cob_infer_image_svds_of_spaces
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {e : GLang.Term} {leev : ValExpr} {s0 s1 : GLang.Space}
    {svb : ValSpace}
    (hbSrc : BasisValid Gamma
      (.image (.proj (.coker s0 s1 e) b0 b1)))
    (hbTgt : BasisValid Gamma
      (.proj (.img s0 s1 e) b0 b1))
    (hcokerSpace : RawMSpaceSubctx orc Gamma Psi (.coker s0 s1 e)
      (.ffs .cokernel svb (ValExpr.reshapBase leev svb)))
    (himageSpace : RawMSpaceSubctx orc Gamma Psi (.img s0 s1 e)
      (.ffs .image svb (ValExpr.reshapBase leev svb))) :
    RawCobInferSubctx orc Gamma Psi
      (.reshap (.imageCoords svb leev)
        (.space (.tprod
          (.ffs .cokernel svb (ValExpr.reshapBase leev svb))
          (.ffs .image svb (ValExpr.reshapBase leev svb))))
        (.space (ValExpr.inferSpaceCtx [] (.imageCoords svb leev))))
      (.image (.proj (.coker s0 s1 e) b0 b1)) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hcokerDof := ValSpace.raw_dof_eq_finrank_of_shpOf
    (hcokerSpace hsub rho Delta' Gamma' sigma GammaV hle hc)
  have hsrcBasis := denotBasis_atSpace_isListBasis sigma Gamma'
    (.image (.proj (.coker s0 s1 e) b0 b1))
    (raw_basisValid_mono hbSrc hle) hc.ctxWF_nl hc.envWF_nl
  obtain ⟨_, himageLen⟩ := raw_cob_basis_length orc hbTgt
    himageSpace hsub hle hc
  refine ⟨.ffs .cokernel svb (ValExpr.reshapBase leev svb),
    .ffs .image svb (ValExpr.reshapBase leev svb), ?_, ?_, ?_⟩
  · simp [ValExpr.inferSpaceCtx]
  · exact hcokerDof.trans
      ((raw_finrank_denotSpace_coker_eq_img sigma s0 s1 e).trans
        hsrcBasis.finrank_eq)
  · exact himageLen.symm.trans
      (raw_denotBasis_image_svds_length hc.ctxWF_nl hc.envWF_nl
        (raw_basisValid_mono hbSrc hle)
        (raw_basisValid_mono hbTgt hle)).symm

/-- Raw inference companion for `S.Cob.image_svds`.

The first inferred factor is the strengthened cokernel realization and the
second is the strengthened image realization.  Both dimensions are measured
against the source concrete basis, as required by `RawCobInferSubctx`. -/
theorem raw_arm_cob_infer_image_svds
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {e : GLang.Term} {leev : ValExpr} {s0 s1 : GLang.Space}
    {svb : ValSpace}
    (hbSrc : BasisValid Gamma
      (.image (.proj (.coker s0 s1 e) b0 b1)))
    (hbTgt : BasisValid Gamma
      (.proj (.img s0 s1 e) b0 b1))
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (_hb0 : Basis.isStd b0) (_hb1 : Basis.isStd b1)
    (hsvb : S.Space Gamma Psi
      (Basis.sof (.tprod (.dual b0) b1)) svb)
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) leev
      (.space svb))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi
      (Basis.sof (.tprod (.dual b0) b1)) svb)
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) leev (.space svb)) :
    RawCobInferSubctx orc Gamma Psi
      (.reshap (.imageCoords svb leev)
        (.space (.tprod
          (.ffs .cokernel svb (ValExpr.reshapBase leev svb))
          (.ffs .image svb (ValExpr.reshapBase leev svb))))
        (.space (ValExpr.inferSpaceCtx [] (.imageCoords svb leev))))
      (.image (.proj (.coker s0 s1 e) b0 b1)) := by
  let w : ValExpr := ValExpr.reshapBase leev svb
  have hcokerSpace : RawMSpaceSubctx orc Gamma Psi (.coker s0 s1 e)
      (.ffs .cokernel svb w) :=
    raw_arm_space_coker hspec
      (Basis.BasisValid.sof_valid hbSrc.image_inv.1)
      (by simp only [Basis.sof, hs0, hs1])
      ⟨b0, b1, rfl⟩
      hsvb he ihSpace ihTerm
  have himageSpace : RawMSpaceSubctx orc Gamma Psi (.img s0 s1 e)
      (.ffs .image svb w) :=
    raw_arm_space_img hspec
      (Basis.BasisValid.sof_valid hbTgt)
      (by simp only [Basis.sof, hs0, hs1])
      ⟨b0, b1, rfl⟩
      hsvb he ihSpace ihTerm
  simp only [w] at hcokerSpace himageSpace
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  exact raw_arm_cob_infer_image_svds_of_spaces
    (orc := orc) (Gamma := Gamma) (Psi := Psi)
    hbSrc hbTgt hcokerSpace himageSpace hsub
      rho Delta' Gamma' sigma GammaV hle hc

end GLang
