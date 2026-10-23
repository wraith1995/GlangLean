import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceEmbeddingShapes
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCanonicalBlocks
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMatrixReadback
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourcePinvConstructors

namespace GLang.PartialAdequacy
open scoped BigOperators
open Basis (BasisValid)

theorem arm_embed_kernel
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (_ht : Nonempty (HasType ∅ Gamma (.embed (.ker s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0))
    (_hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (_hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (ihI0 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    MTermSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.embed (.ker s0 s1 e))
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.vtrans (.gsvdUI v env0 env1))
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) := by
  subst s0
  subst s1
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma b0).atSpace V0
  let S1 := (denotBasis sigma b1).atSpace V1
  let f := (denotTerm sigma e).asLinMap V0 V1
  have hb0v : BasisValid Gamma b0 :=
    (S.Term.basisValid he).tprod_inv.1.dual_inv
  have hb1v : BasisValid Gamma b1 :=
    (S.Term.basisValid he).tprod_inv.2
  have hlb0 : IsListBasis V0 S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb1 : IsListBasis V1 S1 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b0)
    (raw_basisValid_mono (S.Term.basisValid he).tprod_inv.1 hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb1d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono
      (.dual hb1v ((by cases S.Term.basisValid he with | tprod _ _ _ htof => exact htof))) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have hshape : (.tprod sv0 sv1 : ValSpace).shpOfPartial
      (PartialDirectOracle.oracle rho [] []) =
      .ok [Module.finrank ℝ V0.carrier,Module.finrank ℝ V1.carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using trE.dims
  obtain ⟨hd0,hd1⟩ := tprod_shape_factors hshape
  rw [hlb0.finrank_eq] at hd0
  rw [hlb1.finrank_eq] at hd1
  have hi := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hs : (.tprod sv0 sv1 : ValSpace).shpOfPartial (PartialDirectOracle.oracle rho [] []) =
      .ok [S0.length,S1.length] := by
    simp [ValSpace.shpOfPartial,hd0,hd1,bind,Except.bind,pure,Except.pure]
  rw [hs] at hi
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hi
  obtain ⟨ae,heval,halen,hM⟩ := trace_witness_matrix hlb0 hlb1 trE
  obtain ⟨ag,hg,hgl,hG⟩ := trace_inner_matrix hlb0 hlb0d trI0
  obtain ⟨ah,hh,hhl,hH⟩ := trace_inner_matrix hlb1 hlb1d trI1
  have hgd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d := by
    have hi := ihI0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd0,bind,Except.bind,pure,Except.pure]
  have hhd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d := by
    have hi := ihI1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd1,bind,Except.bind,pure,Except.pure]
  obtain ⟨out,hout,hlen,hget⟩ := eval_vtrans_canonicalUI heval hg hh halen
    (by simpa only [pow_two] using hgl) (by simpa only [pow_two] using hhl)
    hinfer ha hb hM hG hH hlb0.gram_posDef hlb1.gram_posDef hgd hhd
    (hc.exprFinite (he.mono hsub).toOpStep)
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  let K : Submodule ℝ V0.carrier := LinearMap.ker f
  let raw : List V0.carrier := BasisFSV.fsvLeft V0 V1 f
    (fun mu => decide (mu = 0)) S0 S1
  have rawEq : raw = List.ofCoords S0 (hlb0.canonical hlb1 f).UI := by
    exact BasisFSV.fsvLeft_eq_canonicalUI hlb0 hlb1 f
  have rawSub : ∀ x ∈ raw, x ∈ K := by
    exact BasisFSV.fsvLeft_subset_ker V0 V1 f S0 S1
  have hlbProj := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)
    (raw_basisValid_mono hbv.tprod_inv.1.dual_inv hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlbProj' : IsListBasis (HSpace.ofSubmodule V0 K)
      (HSpace.liftToSubmodule K raw) := by
    simpa [V0, V1, S0, S1, f, K, raw, Basis.sof,
      denotSpace, denotSpaceAux, denotTerm, denotBasis,
      BasisDenot.atSpace_vecs_self] using hlbProj
  have projListEq :
      (denotBasis sigma
        (.proj (.ker (Basis.sof b0) (Basis.sof b1) e) b0 b1)).atSpace
          (HSpace.ofSubmodule V0 K) =
        HSpace.liftToSubmodule K raw := by
    simp [V0, V1, S0, S1, f, K, raw, denotSpace, denotTerm,
      denotBasis, BasisDenot.atSpace_vecs_self]
  have hlift : (HSpace.liftToSubmodule K raw).length =
      S0.length - (hlb0.canonical hlb1 f).r := by
    rw [HSpace.liftToSubmodule_length_of_subset K raw rawSub,rawEq,List.ofCoords_length]
  have htarget : ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] [])
      (.tprod (.ffs .kernel (.tprod sv0 sv1)
        (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) =
      .ok [Module.finrank ℝ (HSpace.ofSubmodule V0 K).carrier,Module.finrank ℝ V0.carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual,
      denotSpaceAux,denotSpace,V0,V1,K,f,denotTerm] using targetDims
  have hsubdim := (tprod_shape_factors htarget).1
  rw [hlbProj'.finrank_eq,hlift] at hsubdim
  have hres := embedding_of_columns (σ := sigma) (Ds := [])
    (sSub := .ker (Basis.sof b0) (Basis.sof b1) e) (sAmb := Basis.sof b0)
    K (by rfl) S0 (hlb0.canonical hlb1 f).UI raw rawEq rawSub hlbProj'
    hout hlen hget hsubdim hd0
  refine ⟨?_,targetDims⟩
  simpa [ResultAgree,Agree,Basis.tof,Basis.sof,denotBasis,denotSpace,denotSpaceAux,
    denotTerm,denotTermAux,V0,V1,S0,S1,K,f,raw,BasisDenot.atSpace_vecs_self]
    using hres

theorem arm_embed_cokernel
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (_ht : Nonempty (HasType ∅ Gamma (.embed (.coker s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0))
    (_hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (_hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (ihI0 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    MTermSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.embed (.coker s0 s1 e))
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.vtrans (.gsvdU v env0 env1))
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) := by
  subst s0
  subst s1
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma b0).atSpace V0
  let S1 := (denotBasis sigma b1).atSpace V1
  let f := (denotTerm sigma e).asLinMap V0 V1
  have hb0v : BasisValid Gamma b0 :=
    (S.Term.basisValid he).tprod_inv.1.dual_inv
  have hb1v : BasisValid Gamma b1 :=
    (S.Term.basisValid he).tprod_inv.2
  have hlb0 : IsListBasis V0 S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb1 : IsListBasis V1 S1 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b0)
    (raw_basisValid_mono (S.Term.basisValid he).tprod_inv.1 hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb1d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono
      (.dual hb1v ((by cases S.Term.basisValid he with | tprod _ _ _ htof => exact htof))) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have hshape : (.tprod sv0 sv1 : ValSpace).shpOfPartial
      (PartialDirectOracle.oracle rho [] []) =
      .ok [Module.finrank ℝ V0.carrier,Module.finrank ℝ V1.carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using trE.dims
  obtain ⟨hd0,hd1⟩ := tprod_shape_factors hshape
  rw [hlb0.finrank_eq] at hd0
  rw [hlb1.finrank_eq] at hd1
  have hi := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hs : (.tprod sv0 sv1 : ValSpace).shpOfPartial (PartialDirectOracle.oracle rho [] []) =
      .ok [S0.length,S1.length] := by
    simp [ValSpace.shpOfPartial,hd0,hd1,bind,Except.bind,pure,Except.pure]
  rw [hs] at hi
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hi
  obtain ⟨ae,heval,halen,hM⟩ := trace_witness_matrix hlb0 hlb1 trE
  obtain ⟨ag,hg,hgl,hG⟩ := trace_inner_matrix hlb0 hlb0d trI0
  obtain ⟨ah,hh,hhl,hH⟩ := trace_inner_matrix hlb1 hlb1d trI1
  have hgd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d := by
    have hi := ihI0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd0,bind,Except.bind,pure,Except.pure]
  have hhd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d := by
    have hi := ihI1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd1,bind,Except.bind,pure,Except.pure]
  obtain ⟨out,hout,hlen,hget⟩ := eval_vtrans_canonicalU heval hg hh halen
    (by simpa only [pow_two] using hgl) (by simpa only [pow_two] using hhl)
    hinfer ha hb hM hG hH hlb0.gram_posDef hlb1.gram_posDef hgd hhd
    (hc.exprFinite (he.mono hsub).toOpStep)
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  let K : Submodule ℝ V0.carrier :=
    Submodule.orthRel V0.innerProduct (LinearMap.ker f)
  let raw : List V0.carrier := BasisFSV.fsvLeft V0 V1 f
    (fun mu => decide (mu ≠ 0)) S0 S1
  have rawEq : raw = List.ofCoords S0 (hlb0.canonical hlb1 f).U := by
    exact BasisFSV.fsvLeft_eq_canonicalU hlb0 hlb1 f
  have rawSub : ∀ x ∈ raw, x ∈ K := by
    exact BasisFSV.fsvLeft_subset_coker V0 V1 f S0 S1
  have hlbProj := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)
    (raw_basisValid_mono hbv.tprod_inv.1.dual_inv hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlbProj' : IsListBasis (HSpace.ofSubmodule V0 K)
      (HSpace.liftToSubmodule K raw) := by
    simpa [V0, V1, S0, S1, f, K, raw, Basis.sof,
      denotSpace, denotSpaceAux, denotTerm, denotBasis,
      BasisDenot.atSpace_vecs_self] using hlbProj
  have projListEq :
      (denotBasis sigma
        (.proj (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)).atSpace
          (HSpace.ofSubmodule V0 K) =
        HSpace.liftToSubmodule K raw := by
    simp [V0, V1, S0, S1, f, K, raw, denotSpace, denotTerm,
      denotBasis, BasisDenot.atSpace_vecs_self]
  have hlift : (HSpace.liftToSubmodule K raw).length =
      (hlb0.canonical hlb1 f).r := by
    rw [HSpace.liftToSubmodule_length_of_subset K raw rawSub,rawEq,List.ofCoords_length]
  have htarget : ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] [])
      (.tprod (.ffs .cokernel (.tprod sv0 sv1)
        (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) =
      .ok [Module.finrank ℝ (HSpace.ofSubmodule V0 K).carrier,Module.finrank ℝ V0.carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual,
      denotSpaceAux,denotSpace,V0,V1,K,f,denotTerm] using targetDims
  have hsubdim := (tprod_shape_factors htarget).1
  rw [hlbProj'.finrank_eq,hlift] at hsubdim
  have hres := embedding_of_columns (σ := sigma) (Ds := [])
    (sSub := .coker (Basis.sof b0) (Basis.sof b1) e) (sAmb := Basis.sof b0)
    K (by rfl) S0 (hlb0.canonical hlb1 f).U raw rawEq rawSub hlbProj'
    hout hlen hget hsubdim hd0
  refine ⟨?_,targetDims⟩
  simpa [ResultAgree,Agree,Basis.tof,Basis.sof,denotBasis,denotSpace,denotSpaceAux,
    denotTerm,denotTermAux,V0,V1,S0,S1,K,f,raw,BasisDenot.atSpace_vecs_self]
    using hres

theorem arm_embed_image
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (_ht : Nonempty (HasType ∅ Gamma (.embed (.img s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1))
    (_hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (_hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (ihI0 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    MTermSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.embed (.img s0 s1 e))
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.vtrans (.gsvdV v env0 env1))
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) := by
  subst s0
  subst s1
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma b0).atSpace V0
  let S1 := (denotBasis sigma b1).atSpace V1
  let f := (denotTerm sigma e).asLinMap V0 V1
  have hb0v : BasisValid Gamma b0 :=
    (S.Term.basisValid he).tprod_inv.1.dual_inv
  have hb1v : BasisValid Gamma b1 :=
    (S.Term.basisValid he).tprod_inv.2
  have hlb0 : IsListBasis V0 S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb1 : IsListBasis V1 S1 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b0)
    (raw_basisValid_mono (S.Term.basisValid he).tprod_inv.1 hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb1d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono
      (.dual hb1v ((by cases S.Term.basisValid he with | tprod _ _ _ htof => exact htof))) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have hshape : (.tprod sv0 sv1 : ValSpace).shpOfPartial
      (PartialDirectOracle.oracle rho [] []) =
      .ok [Module.finrank ℝ V0.carrier,Module.finrank ℝ V1.carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using trE.dims
  obtain ⟨hd0,hd1⟩ := tprod_shape_factors hshape
  rw [hlb0.finrank_eq] at hd0
  rw [hlb1.finrank_eq] at hd1
  have hi := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hs : (.tprod sv0 sv1 : ValSpace).shpOfPartial (PartialDirectOracle.oracle rho [] []) =
      .ok [S0.length,S1.length] := by
    simp [ValSpace.shpOfPartial,hd0,hd1,bind,Except.bind,pure,Except.pure]
  rw [hs] at hi
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hi
  obtain ⟨ae,heval,halen,hM⟩ := trace_witness_matrix hlb0 hlb1 trE
  obtain ⟨ag,hg,hgl,hG⟩ := trace_inner_matrix hlb0 hlb0d trI0
  obtain ⟨ah,hh,hhl,hH⟩ := trace_inner_matrix hlb1 hlb1d trI1
  have hgd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d := by
    have hi := ihI0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd0,bind,Except.bind,pure,Except.pure]
  have hhd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d := by
    have hi := ihI1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd1,bind,Except.bind,pure,Except.pure]
  obtain ⟨out,hout,hlen,hget⟩ := eval_vtrans_canonicalV heval hg hh halen
    (by simpa only [pow_two] using hgl) (by simpa only [pow_two] using hhl)
    hinfer ha hb hM hG hH hlb0.gram_posDef hlb1.gram_posDef hgd hhd
    (hc.exprFinite (he.mono hsub).toOpStep)
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  let K : Submodule ℝ V1.carrier := LinearMap.range f
  let raw : List V1.carrier := BasisFSV.fsvRight V0 V1 f
    (fun mu => decide (mu ≠ 0)) S0 S1
  have rawEq : raw = List.ofCoords S1 (hlb0.canonical hlb1 f).V := by
    exact BasisFSV.fsvRight_eq_canonicalV hlb0 hlb1 f
  have rawSub : ∀ x ∈ raw, x ∈ K := by
    exact BasisFSV.fsvRight_subset_range V0 V1 f S0 S1
  have hlbProj := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)
    (raw_basisValid_mono hbv.tprod_inv.1.dual_inv hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlbProj' : IsListBasis (HSpace.ofSubmodule V1 K)
      (HSpace.liftToSubmodule K raw) := by
    simpa [V0, V1, S0, S1, f, K, raw, Basis.sof,
      denotSpace, denotSpaceAux, denotTerm, denotBasis,
      BasisDenot.atSpace_vecs_self] using hlbProj
  have projListEq :
      (denotBasis sigma
        (.proj (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)).atSpace
          (HSpace.ofSubmodule V1 K) =
        HSpace.liftToSubmodule K raw := by
    simp [V0, V1, S0, S1, f, K, raw, denotSpace, denotTerm,
      denotBasis, BasisDenot.atSpace_vecs_self]
  have hlift : (HSpace.liftToSubmodule K raw).length =
      (hlb0.canonical hlb1 f).r := by
    rw [HSpace.liftToSubmodule_length_of_subset K raw rawSub,rawEq,List.ofCoords_length]
  have htarget : ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] [])
      (.tprod (.ffs .image (.tprod sv0 sv1)
        (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) =
      .ok [Module.finrank ℝ (HSpace.ofSubmodule V1 K).carrier,Module.finrank ℝ V1.carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual,
      denotSpaceAux,denotSpace,V0,V1,K,f,denotTerm] using targetDims
  have hsubdim := (tprod_shape_factors htarget).1
  rw [hlbProj'.finrank_eq,hlift] at hsubdim
  have hres := embedding_of_columns (σ := sigma) (Ds := [])
    (sSub := .img (Basis.sof b0) (Basis.sof b1) e) (sAmb := Basis.sof b1)
    K (by rfl) S1 (hlb0.canonical hlb1 f).V raw rawEq rawSub hlbProj'
    hout hlen hget hsubdim hd1
  refine ⟨?_,targetDims⟩
  simpa [ResultAgree,Agree,Basis.tof,Basis.sof,denotBasis,denotSpace,denotSpaceAux,
    denotTerm,denotTermAux,V0,V1,S0,S1,K,f,raw,BasisDenot.atSpace_vecs_self]
    using hres

theorem arm_embed_coimage
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (_ht : Nonempty (HasType ∅ Gamma (.embed (.coimg s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1))
    (_hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (_hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (_hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (ihI0 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    MTermSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.embed (.coimg s0 s1 e))
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.vtrans (.gsvdVI v env0 env1))
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) := by
  subst s0
  subst s1
  intro Psi' hsub _hctx rho Delta' Gamma' sigma GammaV hle hc
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma b0).atSpace V0
  let S1 := (denotBasis sigma b1).atSpace V1
  let f := (denotTerm sigma e).asLinMap V0 V1
  have hb0v : BasisValid Gamma b0 :=
    (S.Term.basisValid he).tprod_inv.1.dual_inv
  have hb1v : BasisValid Gamma b1 :=
    (S.Term.basisValid he).tprod_inv.2
  have hlb0 : IsListBasis V0 S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb1 : IsListBasis V1 S1 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1v hle.2) hc.ctxWF_nl hc.envWF_nl
  have hlb0d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b0)
    (raw_basisValid_mono (S.Term.basisValid he).tprod_inv.1 hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlb1d := denotBasis_atSpace_isListBasis sigma Gamma' (.dual b1)
    (raw_basisValid_mono
      (.dual hb1v ((by cases S.Term.basisValid he with | tprod _ _ _ htof => exact htof))) hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have trE := ihE.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI0 := ihI0.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have trI1 := ihI1.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hle hc
  have hshape : (.tprod sv0 sv1 : ValSpace).shpOfPartial
      (PartialDirectOracle.oracle rho [] []) =
      .ok [Module.finrank ℝ V0.carrier,Module.finrank ℝ V1.carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual] using trE.dims
  obtain ⟨hd0,hd1⟩ := tprod_shape_factors hshape
  rw [hlb0.finrank_eq] at hd0
  rw [hlb1.finrank_eq] at hd1
  have hi := ihE.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hs : (.tprod sv0 sv1 : ValSpace).shpOfPartial (PartialDirectOracle.oracle rho [] []) =
      .ok [S0.length,S1.length] := by
    simp [ValSpace.shpOfPartial,hd0,hd1,bind,Except.bind,pure,Except.pure]
  rw [hs] at hi
  obtain ⟨sa,sb,hinfer,ha,hb⟩ := infer_tprod_of_partial_shape hi
  obtain ⟨ae,heval,halen,hM⟩ := trace_witness_matrix hlb0 hlb1 trE
  obtain ⟨ag,hg,hgl,hG⟩ := trace_inner_matrix hlb0 hlb0d trI0
  obtain ⟨ah,hh,hhl,hH⟩ := trace_inner_matrix hlb1 hlb1d trI1
  have hgd : ∃ d, (ValExpr.inferSpaceCtx [] env0).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d := by
    have hi := ihI0.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd0,bind,Except.bind,pure,Except.pure]
  have hhd : ∃ d, (ValExpr.inferSpaceCtx [] env1).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok d := by
    have hi := ihI1.dof rfl hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    unfold ValSpace.dofPartial
    rw [hi]
    simp [ValSpace.shpOfPartial,hd1,bind,Except.bind,pure,Except.pure]
  obtain ⟨out,hout,hlen,hget⟩ := eval_vtrans_canonicalVI heval hg hh halen
    (by simpa only [pow_two] using hgl) (by simpa only [pow_two] using hhl)
    hinfer ha hb hM hG hH hlb0.gram_posDef hlb1.gram_posDef hgd hhd
    (hc.exprFinite (he.mono hsub).toOpStep)
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  let K : Submodule ℝ V1.carrier :=
    Submodule.orthRel V1.innerProduct (LinearMap.range f)
  let raw : List V1.carrier := BasisFSV.fsvRight V0 V1 f
    (fun mu => decide (mu = 0)) S0 S1
  have rawEq : raw = List.ofCoords S1 (hlb0.canonical hlb1 f).VI := by
    exact BasisFSV.fsvRight_eq_canonicalVI hlb0 hlb1 f
  have rawSub : ∀ x ∈ raw, x ∈ K := by
    exact BasisFSV.fsvRight_subset_coimg V0 V1 f S0 S1
  have hlbProj := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)
    (raw_basisValid_mono hbv.tprod_inv.1.dual_inv hle.2)
      hc.ctxWF_nl hc.envWF_nl
  have hlbProj' : IsListBasis (HSpace.ofSubmodule V1 K)
      (HSpace.liftToSubmodule K raw) := by
    simpa [V0, V1, S0, S1, f, K, raw, Basis.sof,
      denotSpace, denotSpaceAux, denotTerm, denotBasis,
      BasisDenot.atSpace_vecs_self] using hlbProj
  have projListEq :
      (denotBasis sigma
        (.proj (.coimg (Basis.sof b0) (Basis.sof b1) e) b0 b1)).atSpace
          (HSpace.ofSubmodule V1 K) =
        HSpace.liftToSubmodule K raw := by
    simp [V0, V1, S0, S1, f, K, raw, denotSpace, denotTerm,
      denotBasis, BasisDenot.atSpace_vecs_self]
  have hlift : (HSpace.liftToSubmodule K raw).length =
      S1.length - (hlb0.canonical hlb1 f).r := by
    rw [HSpace.liftToSubmodule_length_of_subset K raw rawSub,rawEq,List.ofCoords_length]
  have htarget : ValSpace.shpOfPartial (PartialDirectOracle.oracle rho [] [])
      (.tprod (.ffs .coimage (.tprod sv0 sv1)
        (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) =
      .ok [Module.finrank ℝ (HSpace.ofSubmodule V1 K).carrier,Module.finrank ℝ V1.carrier] := by
    simpa only [Basis.tof,Basis.sof,DimsAt,RawSpaceFFS.srcShp_tprod_dual,
      denotSpaceAux,denotSpace,V0,V1,K,f,denotTerm] using targetDims
  have hsubdim := (tprod_shape_factors htarget).1
  rw [hlbProj'.finrank_eq,hlift] at hsubdim
  have hres := embedding_of_columns (σ := sigma) (Ds := [])
    (sSub := .coimg (Basis.sof b0) (Basis.sof b1) e) (sAmb := Basis.sof b1)
    K (by rfl) S1 (hlb0.canonical hlb1 f).VI raw rawEq rawSub hlbProj'
    hout hlen hget hsubdim hd1
  refine ⟨?_,targetDims⟩
  simpa [ResultAgree,Agree,Basis.tof,Basis.sof,denotBasis,denotSpace,denotSpaceAux,
    denotTerm,denotTermAux,V0,V1,S0,S1,K,f,raw,BasisDenot.atSpace_vecs_self]
    using hres

theorem arm_embed_kernel_facts
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (ht : Nonempty (HasType ∅ Gamma (.embed (.ker s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0))
    (hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (ihI0 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.embed (.ker s0 s1 e))
      (.tprod (.dual (.proj (.ker s0 s1 e) b0 b1)) b0)
      (.vtrans (.gsvdUI v env0 env1))
      (.space (.tprod
        (.ffs .kernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) :=
  ⟨arm_embed_kernel hs0 hs1 ht hbv hTy hi0 hi1 he ihTy ihI0 ihI1 ihE,
    embedding_dof .kernel he ihE⟩

theorem arm_embed_cokernel_facts
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (ht : Nonempty (HasType ∅ Gamma (.embed (.coker s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0))
    (hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)))
    (ihI0 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.embed (.coker s0 s1 e))
      (.tprod (.dual (.proj (.coker s0 s1 e) b0 b1)) b0)
      (.vtrans (.gsvdU v env0 env1))
      (.space (.tprod
        (.ffs .cokernel (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0)) :=
  ⟨arm_embed_cokernel hs0 hs1 ht hbv hTy hi0 hi1 he ihTy ihI0 ihI1 ihE,
    embedding_dof .cokernel he ihE⟩

theorem arm_embed_image_facts
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (ht : Nonempty (HasType ∅ Gamma (.embed (.img s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1))
    (hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (ihI0 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.embed (.img s0 s1 e))
      (.tprod (.dual (.proj (.img s0 s1 e) b0 b1)) b1)
      (.vtrans (.gsvdV v env0 env1))
      (.space (.tprod
        (.ffs .image (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) :=
  ⟨arm_embed_image hs0 hs1 ht hbv hTy hi0 hi1 he ihTy ihI0 ihI1 ihE,
    embedding_dof .image he ihE⟩

theorem arm_embed_coimage_facts
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b0 b1 : Basis} {e : Term} {v env0 env1 : ValExpr}
    {s0 s1 : Space} {sv0 sv1 : ValSpace}
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (ht : Nonempty (HasType ∅ Gamma (.embed (.coimg s0 s1 e))
      (Basis.tof (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1))))
    (hbv : BasisValid Gamma
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1))
    (hTy : S.TyAt Gamma Psi
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (hi0 : S.Term ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (hi1 : S.Term ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space (.tprod sv0 sv1)))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)))
    (ihI0 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s0)
      (.tprod (.dual b0) (.dual b0)) env0
      (.space (.tprod sv0 sv0)))
    (ihI1 : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.inner s1)
      (.tprod (.dual b1) (.dual b1)) env1
      (.space (.tprod sv1 sv1)))
    (ihE : TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space (.tprod sv0 sv1))) :
    TermFactsSubctx PartialDirectOracle.oracle ∅ Gamma Psi (.embed (.coimg s0 s1 e))
      (.tprod (.dual (.proj (.coimg s0 s1 e) b0 b1)) b1)
      (.vtrans (.gsvdVI v env0 env1))
      (.space (.tprod
        (.ffs .coimage (.tprod sv0 sv1)
          (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1)) :=
  ⟨arm_embed_coimage hs0 hs1 ht hbv hTy hi0 hi1 he ihTy ihI0 ihI1 ihE,
    embedding_dof .coimage he ihE⟩

end GLang.PartialAdequacy
