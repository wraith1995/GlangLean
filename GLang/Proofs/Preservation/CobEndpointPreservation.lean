import GLang.Proofs.Adequacy.Total.DirectPublic
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobDirectMutualMaster
import GLang.Proofs.Preservation.ValuePreservationV2

/-!
# Endpoint-aware COB preservation

The syntax-only `CobShapeT` preservation result intentionally permits the two
matrix factors to realize different source spaces.  In particular, the SVD
image conversion carries cokernel and image factors, so equating either factor
space directly with the endpoint space is false.

This module adds the sound endpoint statement: each inferred matrix *axis
dimension* is the concrete coordinate length of its corresponding endpoint
basis.  It retains `CobShapeT` alongside those equations, so validity and
scope are not lost.  The generic theorem has an explicit oracle contract;
the public convenience theorem specializes it to the constructive oracle.
-/

namespace GLang
namespace Metatheory

open scoped BigOperators

/-- Oracle-polymorphic endpoint-aware change-of-basis preservation.
`CobShapeT` supplies the two genuine (and intentionally not necessarily
equal) source spaces carried by the matrix value.  The additional equations
identify the dynamic size of each inferred matrix axis with the concrete
coordinate length of the corresponding source/target basis. -/
theorem cobEndpointPreservationOfOracle
    (orc : FFSOracleSem) (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {bSrc bTgt : Basis} {env : ValExpr}
    (hstep : Operational.Cob Gamma Psi bSrc env bTgt)
    (hconsistent :
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho) :
    CobShapeT Psi env Psi.keyNames /\
      exists svSrc svTgt,
        ValExpr.inferSpaceCtx [] env = .tprod svSrc svTgt /\
        ValSpace.dof (orc rho [] []) svSrc =
          ((denotBasis sigma bSrc).atSpace
            (denotSpace sigma (Basis.sof bSrc))).length /\
        ValSpace.dof (orc rho [] []) svTgt =
          ((denotBasis sigma bTgt).atSpace
            (denotSpace sigma (Basis.sof bTgt))).length := by
  have hstrengthened := hstep.toStrengthened
  have hvalid := hconsistent.evalCtxValidPlus
  have hrho : V2.RhoValid Psi Psi.keyNames := hvalid.rhoValid_keyNames
  obtain ⟨hsource⟩ := hstrengthened.basisValid_src.sof_valid
  obtain ⟨hshape, hvalue, hfvs⟩ := V2.preservation_master.2.2.1
    (Operational.Cob.toUnchecked hstep) (∅ : LCtx) Gamma Psi.keyNames
    hvalid hrho (V2.keyScope_keyNames Psi) hsource
  have hpreserved : CobShapeT Psi env Psi.keyNames :=
    ⟨hshape, hvalue, hfvs⟩
  obtain ⟨svSrc, svTgt, hinfer, hsrc, htgtSrc⟩ :=
    (hstrengthened.rawDirectMutualMaster hspec).infer
      (EvalCtx.Subctx.refl Psi) rho Delta Gamma sigma GammaV
      (NLCtxIncl.refl Gamma) hconsistent
  have hlen :
      ((denotBasis sigma bSrc).atSpace
        (denotSpace sigma (Basis.sof bSrc))).length =
      ((denotBasis sigma bTgt).atSpace
        (denotSpace sigma (Basis.sof bTgt))).length :=
    raw_denotBasis_length_eq_of_sof_eq hconsistent.ctxWF_nl
      hconsistent.envWF_nl hstrengthened.basisValid_src
      hstrengthened.basisValid_tgt hstrengthened.sof_eq
  exact ⟨hpreserved, svSrc, svTgt, hinfer, hsrc, htgtSrc.trans hlen⟩

/-- Endpoint-aware change-of-basis preservation for the supplied constructive
oracle. -/
theorem cobEndpointPreservation
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {bSrc bTgt : Basis} {env : ValExpr}
    (hstep : Operational.Cob Gamma Psi bSrc env bTgt)
    (hconsistent :
      Adequacy.Direct.Consistent Delta Gamma Psi GammaV sigma rho) :
    CobShapeT Psi env Psi.keyNames /\
      exists svSrc svTgt,
        ValExpr.inferSpaceCtx [] env = .tprod svSrc svTgt /\
        ValSpace.dof (directOracle rho [] []) svSrc =
          ((denotBasis sigma bSrc).atSpace
            (denotSpace sigma (Basis.sof bSrc))).length /\
        ValSpace.dof (directOracle rho [] []) svTgt =
          ((denotBasis sigma bTgt).atSpace
            (denotSpace sigma (Basis.sof bTgt))).length :=
  cobEndpointPreservationOfOracle directOracle directApplicationOracle_spec
    hstep hconsistent.raw

theorem cobCommonDimensionAdequacyOfOracle
    (orc : FFSOracleSem) (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {bSrc bTgt : Basis} {env : ValExpr}
    (hstep : Operational.Cob Gamma Psi bSrc env bTgt)
    (hconsistent :
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho) :
    CobShapeT Psi env Psi.keyNames /\
      CobAgree orc sigma rho bSrc bTgt env /\
      exists (N : Nat) (svSrc svTgt : ValSpace),
        ValExpr.inferSpaceCtx [] env = .tprod svSrc svTgt /\
        N = ValSpace.dof (orc rho [] []) svSrc /\
        N = ValSpace.dof (orc rho [] []) svTgt /\
        N = ((denotBasis sigma bSrc).atSpace
          (denotSpace sigma (Basis.sof bSrc))).length /\
        N = ((denotBasis sigma bTgt).atSpace
          (denotSpace sigma (Basis.sof bTgt))).length := by
  obtain ⟨hshape, svSrc, svTgt, hinfer, hsrc, htgt⟩ :=
    cobEndpointPreservationOfOracle orc hspec hstep hconsistent
  have hagree : CobAgree orc sigma rho bSrc bTgt env :=
    (hstep.toStrengthened.rawDirectMutualMaster hspec).agree
      (EvalCtx.Subctx.refl Psi) rho Delta Gamma sigma GammaV
      (NLCtxIncl.refl Gamma) hconsistent
  have hstrengthened := hstep.toStrengthened
  have hlen :
      ((denotBasis sigma bSrc).atSpace
        (denotSpace sigma (Basis.sof bSrc))).length =
      ((denotBasis sigma bTgt).atSpace
        (denotSpace sigma (Basis.sof bTgt))).length :=
    raw_denotBasis_length_eq_of_sof_eq hconsistent.ctxWF_nl
      hconsistent.envWF_nl hstrengthened.basisValid_src
      hstrengthened.basisValid_tgt hstrengthened.sof_eq
  let N := ((denotBasis sigma bSrc).atSpace
    (denotSpace sigma (Basis.sof bSrc))).length
  exact ⟨hshape, hagree, N, svSrc, svTgt, hinfer,
    hsrc.symm, hlen.trans htgt.symm, rfl, hlen⟩

/-- Common-dimension change-of-basis adequacy for the supplied constructive
oracle. -/
theorem cobCommonDimensionAdequacy
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {bSrc bTgt : Basis} {env : ValExpr}
    (hstep : Operational.Cob Gamma Psi bSrc env bTgt)
    (hconsistent :
      Adequacy.Direct.Consistent Delta Gamma Psi GammaV sigma rho) :
    CobShapeT Psi env Psi.keyNames /\
      Adequacy.Direct.CobAgree sigma rho bSrc bTgt env /\
      exists (N : Nat) (svSrc svTgt : ValSpace),
        ValExpr.inferSpaceCtx [] env = .tprod svSrc svTgt /\
        N = ValSpace.dof (directOracle rho [] []) svSrc /\
        N = ValSpace.dof (directOracle rho [] []) svTgt /\
        N = ((denotBasis sigma bSrc).atSpace
          (denotSpace sigma (Basis.sof bSrc))).length /\
        N = ((denotBasis sigma bTgt).atSpace
          (denotSpace sigma (Basis.sof bTgt))).length :=
  cobCommonDimensionAdequacyOfOracle directOracle directApplicationOracle_spec
    hstep hconsistent.raw

/-! ## The coefficient matrix is an automorphism

`CobAgree` by itself only gives a square row expansion.  Bijectivity also
uses the operationally derived validity of both endpoints, whose denotations
are genuine bases of their common source space.  Thus this fact is valid at
the checked public boundary, but would be false for arbitrary lists merely
satisfying the bare shape equations.
-/

private theorem cobAgreeCoordinateMatrixBijective
    (orc : FFSOracleSem)
    {rho : ValEnvSem} {Gamma : NLCtx} {sigma : DEnv}
    {bSrc bTgt : Basis} {env : ValExpr}
    (hctx : CtxWF ∅ Gamma) (henv : EnvWF sigma ∅ Gamma)
    (hbSrc : Basis.BasisValid Gamma bSrc)
    (hbTgt : Basis.BasisValid Gamma bTgt)
    (hsof : Basis.sof bSrc = Basis.sof bTgt)
    (hagree : CobAgree orc sigma rho bSrc bTgt env) :
    let V := denotSpace sigma (Basis.sof bSrc)
    let S := (denotBasis sigma bSrc).atSpace V
    exists a : FlatArray,
      denotValB_semS orc rho [] [] env = .ok (.array a) /\
      a.length = S.length * S.length /\
      Function.Bijective
        (Matrix.toLin' (denotAsMatrix S.length S.length a.get)) := by
  let V := denotSpace sigma (Basis.sof bSrc)
  let S := (denotBasis sigma bSrc).atSpace V
  let T := (denotBasis sigma bTgt).atSpace V
  change T.length = S.length /\
    ∃ a : FlatArray,
      denotValB_semS orc rho [] [] env = .ok (.array a) /\
      a.length = S.length * S.length /\
      ∀ j : Fin S.length,
        S.getD j.val 0 =
          ∑ i : Fin S.length,
            a.get (j.val * S.length + i.val) • T.getD i.val 0 at hagree
  obtain ⟨hlen, a, ha, halen, hrows⟩ := hagree
  have hS : IsListBasis V S := by
    simpa [V, S] using
      denotBasis_atSpace_isListBasis sigma Gamma bSrc hbSrc hctx henv
  have hT : IsListBasis V T := by
    have h :=
      denotBasis_atSpace_isListBasis sigma Gamma bTgt hbTgt hctx henv
    rw [← hsof] at h
    simpa [V, T] using h
  let M : Matrix (Fin S.length) (Fin S.length) ℝ :=
    denotAsMatrix S.length S.length a.get
  let bT : Module.Basis (Fin S.length) ℝ V.carrier :=
    hT.toBasis.reindex (finCongr hlen)
  have hbT_apply (i : Fin S.length) : bT i = T.getD i.val 0 := by
    rw [List.getD_eq_getElem T 0 (hlen.symm ▸ i.isLt)]
    simp [bT, Module.Basis.reindex_apply, IsListBasis.toBasis_apply]
  have hbS_apply (i : Fin S.length) :
      hS.toBasis i = S.getD i.val 0 := by
    simp [IsListBasis.toBasis_apply]
  have hmrows : ∀ j, hS.toBasis j = ∑ i, M j i • bT i := by
    intro j
    rw [hbS_apply, hrows j]
    apply Finset.sum_congr rfl
    intro i _
    rw [hbT_apply]
    simp [M, denotAsMatrix, Nat.mul_comm S.length j.val]
  have hcoord : M.transpose =
      LinearMap.toMatrix hS.toBasis bT LinearMap.id := by
    ext j i
    rw [LinearMap.toMatrix_apply, LinearMap.id_apply, hmrows i]
    rw [bT.repr_sum_self]
    rfl
  have hbijTranspose : Function.Bijective (Matrix.toLin' M.transpose) := by
    rw [hcoord]
    exact Basis.raw_toMatrix_id_bijective hS.toBasis bT
  have hunitTranspose : IsUnit M.transpose :=
    Matrix.mulVec_injective_iff_isUnit.mp (by
      simpa only [Matrix.toLin'_apply] using hbijTranspose.1)
  have hunit : IsUnit M := by
    rwa [Matrix.isUnit_transpose] at hunitTranspose
  have hbij : Function.Bijective (Matrix.toLin' M) := by
    constructor
    · simpa only [Matrix.toLin'_apply] using
        Matrix.mulVec_injective_iff_isUnit.mpr hunit
    · simpa only [Matrix.toLin'_apply] using
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  exact ⟨a, ha, halen, hbij⟩

theorem cobCoordinateMatrixBijectiveOfOracle
    (orc : FFSOracleSem) (hspec : RawApplicationOracleSpec orc)
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {bSrc bTgt : Basis} {env : ValExpr}
    (hstep : Operational.Cob Gamma Psi bSrc env bTgt)
    (hconsistent :
      RawTypedConsistent orc Delta Gamma Psi GammaV sigma rho) :
    exists (N : Nat) (svSrc svTgt : ValSpace) (a : FlatArray),
      CobShapeT Psi env Psi.keyNames /\
      CobAgree orc sigma rho bSrc bTgt env /\
      ValExpr.inferSpaceCtx [] env = .tprod svSrc svTgt /\
      N = ValSpace.dof (orc rho [] []) svSrc /\
      N = ValSpace.dof (orc rho [] []) svTgt /\
      N = ((denotBasis sigma bSrc).atSpace
        (denotSpace sigma (Basis.sof bSrc))).length /\
      N = ((denotBasis sigma bTgt).atSpace
        (denotSpace sigma (Basis.sof bTgt))).length /\
      denotValB_semS orc rho [] [] env = .ok (.array a) /\
      a.length = N * N /\
      Function.Bijective
        (Matrix.toLin' (denotAsMatrix N N a.get)) := by
  obtain ⟨hshape, hagree, N, svSrc, svTgt, hinfer,
      hsrcDof, htgtDof, hsrcLen, htgtLen⟩ :=
    cobCommonDimensionAdequacyOfOracle orc hspec hstep hconsistent
  have hstrengthened := hstep.toStrengthened
  obtain ⟨a, ha, halen, hbij⟩ :=
    cobAgreeCoordinateMatrixBijective orc hconsistent.ctxWF_nl
      hconsistent.envWF_nl hstrengthened.basisValid_src
      hstrengthened.basisValid_tgt hstrengthened.sof_eq hagree
  rw [← hsrcLen] at halen hbij
  exact ⟨N, svSrc, svTgt, a, hshape, hagree, hinfer,
    hsrcDof, htgtDof, hsrcLen, htgtLen, ha, halen, hbij⟩

/-- Constructive-oracle specialization: every checked change of basis
evaluates to a square coordinate matrix that is a linear automorphism. -/
theorem cobCoordinateMatrixBijective
    {rho : ValEnvSem} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {bSrc bTgt : Basis} {env : ValExpr}
    (hstep : Operational.Cob Gamma Psi bSrc env bTgt)
    (hconsistent :
      Adequacy.Direct.Consistent Delta Gamma Psi GammaV sigma rho) :
    exists (N : Nat) (svSrc svTgt : ValSpace) (a : FlatArray),
      CobShapeT Psi env Psi.keyNames /\
      Adequacy.Direct.CobAgree sigma rho bSrc bTgt env /\
      ValExpr.inferSpaceCtx [] env = .tprod svSrc svTgt /\
      N = ValSpace.dof (directOracle rho [] []) svSrc /\
      N = ValSpace.dof (directOracle rho [] []) svTgt /\
      N = ((denotBasis sigma bSrc).atSpace
        (denotSpace sigma (Basis.sof bSrc))).length /\
      N = ((denotBasis sigma bTgt).atSpace
        (denotSpace sigma (Basis.sof bTgt))).length /\
      denotValB_semS directOracle rho [] [] env = .ok (.array a) /\
      a.length = N * N /\
      Function.Bijective
        (Matrix.toLin' (denotAsMatrix N N a.get)) :=
  cobCoordinateMatrixBijectiveOfOracle directOracle directApplicationOracle_spec
    hstep hconsistent.raw

end Metatheory
end GLang
