import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceProjectionCore

namespace GLang.PartialAdequacy
open scoped BigOperators
open Basis (BasisValid)

theorem arm_cob_proj_ker_coker
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 b0' : Basis} {env1 env2 env3 : ValExpr}
    {sv0 sv1 sv sv' sv0' : ValSpace}
    (hbSrc : BasisValid Gamma (.proj s b0 b1))
    (hbTgt : BasisValid Gamma (.proj s b0' b1))
    (hs : s = .ker s0 s1 e ∨ s = .coker s0 s1 e)
    (hsofb0 : Basis.sof b0 = s0)
    (_hsofb1 : Basis.sof b1 = s1)
    (_hsv0 : S.Space Gamma Psi (Basis.sof b0) sv0)
    (_hsv1 : S.Space Gamma Psi (Basis.sof b1) sv1)
    (_hsv : S.Space Gamma Psi s sv)
    (_hsv' : S.Space Gamma Psi s sv')
    (_hsv0' : S.Space Gamma Psi (Basis.sof b0') sv0')
    (hcob : S.Cob Gamma Psi b0 env2 b0')
    (_hembd : S.Term ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (_hproj : S.Term ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0'))
      (.tprod (.dual b0') (.proj s b0' b1)) env1
      (.space (.tprod sv0' sv')))
    (ihSv0 : MSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (ihSv : MSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : MSpaceSubctx orc Gamma Psi s sv')
    (ihSv0' : MSpaceSubctx orc Gamma Psi (Basis.sof b0') sv0')
    (ihCob : MCobSubctx orc Gamma Psi b0 env2 b0')
    (ihEmbd : MTermSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (ihProj : MTermSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0'))
      (.tprod (.dual b0') (.proj s b0' b1)) env1
      (.space (.tprod sv0' sv'))) :
    MCobSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv0' sv0'
        (ValExpr.reshapBase env1 (.tprod sv0' sv'))
        (.mtm 0 0 sv0 sv0
          (ValExpr.reshapBase env2 (.tprod sv0 sv0'))
          (ValExpr.reshapBase env3 (.tprod sv sv0))))
      (.proj s b0' b1) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hctx : RawCtxIncl ∅ Gamma Delta' Gamma' := by
    refine ⟨?_, hle⟩
    intro x sx hx
    simp at hx
  have trEmbd := ihEmbd hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc
  have trProj := ihProj hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc
  have cobAgree := ihCob hsub rho Delta' Gamma' sigma GammaV hle hc
  have hsofAmbient : Basis.sof b0 = Basis.sof b0' := S.Cob.sof_eq hcob

  have hb0v := (raw_proj_basisValid_components hbSrc).1
  have hb0'v := (raw_proj_basisValid_components hbTgt).1
  have hBS := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj s b0 b1) (raw_basisValid_mono hbSrc hle)
    hc.ctxWF_nl hc.envWF_nl
  have hBT := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj s b0' b1) (raw_basisValid_mono hbTgt hle)
    hc.ctxWF_nl hc.envWF_nl
  have hBA := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono hb0v hle) hc.ctxWF_nl hc.envWF_nl
  have hBA' := denotBasis_atSpace_isListBasis sigma Gamma' b0'
    (raw_basisValid_mono hb0'v hle) hc.ctxWF_nl hc.envWF_nl

  obtain ⟨a3, ha3, ha3len, hrow3⟩ :=
    trace_linear_map_rows hBS hBA trEmbd
  obtain ⟨a1, ha1, ha1len, hrow1⟩ :=
    trace_linear_map_rows hBA' hBT trProj

  let V := denotSpace sigma s
  let W := denotSpace sigma (Basis.sof b0)
  let S0 := (denotBasis sigma (.proj s b0 b1)).atSpace V
  let S1 := (denotBasis sigma (.proj s b0' b1)).atSpace V
  let A0 := (denotBasis sigma b0).atSpace W
  let A1 := (denotBasis sigma b0').atSpace W
  let emb := (denotTerm sigma (Term.lembd s)).asLinMap V W
  let proj := (denotTerm sigma (Term.lproj s (Basis.sof b0))).asLinMap W V

  have hrow1' : forall j : Fin A1.length,
      proj (A1.get j) = ∑ i : Fin S1.length,
        a1.get (j.val * S1.length + i.val) • S1.get i := by
    have h := hrow1
    rw [← hsofAmbient] at h
    simpa only [proj, A1, S1, W, V] using h

  simp only [CobAgree,CobResult,CobRows] at cobAgree
  obtain ⟨a2, ha2, hA1len, ha2len, hrow2⟩ := cobAgree
  have hrow2' : forall j : Fin A0.length,
      A0.get j = ∑ i : Fin A1.length,
        a2.get (j.val * A0.length + i.val) • A1.get i := by
    intro j
    calc
      A0.get j = A0.getD j.val 0 :=
        (List.getD_eq_getElem A0 0 j.isLt).symm
      _ = ∑ i : Fin A0.length,
          a2.get (j.val * A0.length + i.val) • A1.getD i.val 0 :=
        hrow2 j
      _ = ∑ i : Fin A1.length,
          a2.get (j.val * A0.length + i.val) • A1.get i := by
        rw [Fin.raw_sum_cast_of_eq hA1len.symm]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.val_cast]
        rw [List.getD_eq_getElem A1 0 i.isLt]
        rw [List.get_eq_getElem]

  have hSdim := basis_dimension hbSrc ihSv hsub hle hc
  have hTdim := basis_dimension hbTgt ihSv' hsub hle hc
  have hA0dim := basis_dimension hb0v ihSv0 hsub hle hc
  have hA1dim0 := basis_dimension hb0'v ihSv0' hsub hle hc
  have hA1dim : sv0'.dofPartial (orc rho [] []) = .ok A1.length := by
    rw [← hsofAmbient] at hA1dim0
    exact hA1dim0
  have ha3Len : a3.length = S0.length*A0.length := ha3len
  have ha2Len : a2.length = A0.length*A1.length := by
    change a2.length = A0.length*A0.length at ha2len
    change A1.length = A0.length at hA1len
    rw [hA1len]
    exact ha2len
  have ha1Len : a1.length = A1.length*S1.length := by
    rw [← hsofAmbient] at ha1len
    exact ha1len
  have hr3 := reshape_array ha3 (dof_tprod_ok hSdim hA0dim) ha3Len
  have hr2 := reshape_array ha2 (dof_tprod_ok hA0dim hA1dim) ha2Len
  have hr1 := reshape_array ha1 (dof_tprod_ok hA1dim hTdim) ha1Len
  obtain ⟨a23,ha23,ha23len,hget23⟩ := mtm_rectangular orc rho (sAux := sv0)
    (left := ValExpr.reshapBase env2 (.tprod sv0 sv0'))
    (right := ValExpr.reshapBase env3 (.tprod sv sv0))
    rfl rfl hr2 hr3 hSdim hA0dim hA1dim ha2Len ha3Len
  obtain ⟨a,ha,halen,hget⟩ := mtm_rectangular orc rho (sAux := sv0')
    (left := ValExpr.reshapBase env1 (.tprod sv0' sv'))
    (right := .mtm 0 0 sv0 sv0
      (ValExpr.reshapBase env2 (.tprod sv0 sv0'))
      (ValExpr.reshapBase env3 (.tprod sv sv0)))
    rfl rfl hr1 ha23 hSdim hA1dim hTdim ha1Len ha23len

  have hleft : forall j : Fin S0.length,
      proj (emb (S0.get j)) = S0.get j := by
    intro j
    change (denotTerm sigma (Term.lproj s (Basis.sof b0))).asLinMap
        (denotSpace sigma (Basis.sof b0)) (denotSpace sigma s)
        ((denotTerm sigma (Term.lembd s)).asLinMap
          (denotSpace sigma s) (denotSpace sigma (Basis.sof b0))
          (S0.get j)) = S0.get j
    rw [hsofb0]
    exact raw_lproj_lembd_ker_coker sigma hs (S0.get j)

  have hrow3' : forall j : Fin S0.length,
      emb (S0.get j) = ∑ i : Fin A0.length,
        a3.get (j.val * A0.length + i.val) • A0.get i := by
    simpa only [emb, S0, A0, V, W] using hrow3

  have hsum3 : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin A0.length,
        a3.get (j.val * A0.length + i.val) • proj (A0.get i) := by
    intro j
    rw [← hleft j, hrow3' j, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  have hsum2 : forall j : Fin A0.length,
      proj (A0.get j) = ∑ i : Fin A1.length,
        a2.get (j.val * A1.length + i.val) • proj (A1.get i) := by
    intro j
    rw [hrow2' j, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    have hidx : j.val * A0.length + i.val =
        j.val * A1.length + i.val :=
      congrArg (fun n => j.val * n + i.val) hA1len.symm
    rw [hidx]

  have hsum23 : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin A1.length,
        a23.get (j.val * A1.length + i.val) • proj (A1.get i) :=
    raw_rectangular_comp_family
      (source := fun j => S0.get j)
      (middle := fun i => proj (A0.get i))
      (target := fun i => proj (A1.get i))
      a23 a3 a2 hsum3 hsum2 (by
        intro j i hj hi
        simpa only [hA1len] using hget23 j i hj hi)
  have hsum : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin S1.length,
        a.get (j.val * S1.length + i.val) • S1.get i :=
    raw_rectangular_comp_family
      (source := fun j => S0.get j)
      (middle := fun i => proj (A1.get i))
      (target := fun i => S1.get i)
      a a23 a1 hsum23 hrow1' hget

  have hSTlen : S1.length = S0.length := by
    exact hBT.finrank_eq.symm.trans hBS.finrank_eq
  unfold CobAgree CobResult CobRows
  dsimp only
  refine ⟨a,ha,by simpa only [S0, S1] using hSTlen, ?_, ?_⟩
  · have halen' : a.length = S0.length * S0.length :=
      halen.trans (congrArg (fun n => S0.length * n) hSTlen)
    simpa only [S0] using halen'
  · intro j
    change S0.getD j.val 0 = ∑ i : Fin S0.length,
      a.get (j.val * S0.length + i.val) • S1.getD i.val 0
    calc
      S0.getD j.val 0 = S0.get j :=
        List.getD_eq_getElem S0 0 j.isLt
      _ = ∑ i : Fin S1.length,
          a.get (j.val * S1.length + i.val) • S1.get i := hsum j
      _ = ∑ i : Fin S0.length,
          a.get (j.val * S0.length + i.val) • S1.getD i.val 0 := by
        rw [Fin.raw_sum_cast_of_eq hSTlen]
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val < S1.length := by
          simpa only [hSTlen] using i.isLt
        simp only [Fin.val_cast, hSTlen]
        rw [List.getD_eq_getElem S1 0 hi]
        rfl

theorem arm_cob_proj_ker_coker_cod
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 b1' : Basis} {env1 env3 : ValExpr}
    {sv0 sv sv' : ValSpace}
    (hbSrc : BasisValid Gamma (.proj s b0 b1))
    (hbTgt : BasisValid Gamma (.proj s b0 b1'))
    (hs : s = .ker s0 s1 e ∨ s = .coker s0 s1 e)
    (hsofb0 : Basis.sof b0 = s0)
    (_hsofb1 : Basis.sof b1 = s1)
    (_hsofb1' : Basis.sof b1' = s1)
    (_hsv0 : S.Space Gamma Psi (Basis.sof b0) sv0)
    (_hsv : S.Space Gamma Psi s sv)
    (_hsv' : S.Space Gamma Psi s sv')
    (_hembd : S.Term ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (_hproj : S.Term ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0))
      (.tprod (.dual b0) (.proj s b0 b1')) env1
      (.space (.tprod sv0 sv')))
    (ihSv0 : MSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (ihSv : MSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : MSpaceSubctx orc Gamma Psi s sv')
    (ihEmbd : MTermSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (ihProj : MTermSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0))
      (.tprod (.dual b0) (.proj s b0 b1')) env1
      (.space (.tprod sv0 sv'))) :
    MCobSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv0 sv0
        (ValExpr.reshapBase env1 (.tprod sv0 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv0)))
      (.proj s b0 b1') := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hctx : RawCtxIncl ∅ Gamma Delta' Gamma' := by
    refine ⟨?_, hle⟩
    intro x sx hx
    simp at hx
  have trEmbd := ihEmbd hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc
  have trProj := ihProj hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc

  have hb0v := (raw_proj_basisValid_components hbSrc).1
  have hBS := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj s b0 b1) (raw_basisValid_mono hbSrc hle)
    hc.ctxWF_nl hc.envWF_nl
  have hBT := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj s b0 b1') (raw_basisValid_mono hbTgt hle)
    hc.ctxWF_nl hc.envWF_nl
  have hBA := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono hb0v hle) hc.ctxWF_nl hc.envWF_nl

  obtain ⟨a3, ha3, ha3len, hrow3⟩ :=
    trace_linear_map_rows hBS hBA trEmbd
  obtain ⟨a1, ha1, ha1len, hrow1⟩ :=
    trace_linear_map_rows hBA hBT trProj

  let V := denotSpace sigma s
  let W := denotSpace sigma (Basis.sof b0)
  let S0 := (denotBasis sigma (.proj s b0 b1)).atSpace V
  let S1 := (denotBasis sigma (.proj s b0 b1')).atSpace V
  let A := (denotBasis sigma b0).atSpace W
  let emb := (denotTerm sigma (Term.lembd s)).asLinMap V W
  let proj := (denotTerm sigma
    (Term.lproj s (Basis.sof b0))).asLinMap W V

  have hrow3' : forall j : Fin S0.length,
      emb (S0.get j) = ∑ i : Fin A.length,
        a3.get (j.val * A.length + i.val) • A.get i := by
    simpa only [emb, S0, A, V, W] using hrow3
  have hrow1' : forall j : Fin A.length,
      proj (A.get j) = ∑ i : Fin S1.length,
        a1.get (j.val * S1.length + i.val) • S1.get i := by
    simpa only [proj, A, S1, W, V] using hrow1

  have hSdim := basis_dimension hbSrc ihSv hsub hle hc
  have hTdim := basis_dimension hbTgt ihSv' hsub hle hc
  have hAdim := basis_dimension hb0v ihSv0 hsub hle hc
  have ha3Len : a3.length = S0.length*A.length := ha3len
  have ha1Len : a1.length = A.length*S1.length := ha1len
  have hr3 := reshape_array ha3 (dof_tprod_ok hSdim hAdim) ha3Len
  have hr1 := reshape_array ha1 (dof_tprod_ok hAdim hTdim) ha1Len
  obtain ⟨a,ha,halen,hget⟩ := mtm_rectangular orc rho (sAux := sv0)
    (left := ValExpr.reshapBase env1 (.tprod sv0 sv'))
    (right := ValExpr.reshapBase env3 (.tprod sv sv0))
    rfl rfl hr1 hr3 hSdim hAdim hTdim ha1Len ha3Len

  have hleft : forall j : Fin S0.length,
      proj (emb (S0.get j)) = S0.get j := by
    intro j
    change (denotTerm sigma
        (Term.lproj s (Basis.sof b0))).asLinMap
        (denotSpace sigma (Basis.sof b0)) (denotSpace sigma s)
        ((denotTerm sigma (Term.lembd s)).asLinMap
          (denotSpace sigma s) (denotSpace sigma (Basis.sof b0))
          (S0.get j)) = S0.get j
    rw [hsofb0]
    exact raw_lproj_lembd_ker_coker sigma hs (S0.get j)
  have hsum3 : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin A.length,
        a3.get (j.val * A.length + i.val) • proj (A.get i) := by
    intro j
    rw [← hleft j, hrow3' j, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  have hsum : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin S1.length,
        a.get (j.val * S1.length + i.val) • S1.get i :=
    raw_rectangular_comp_family
      (source := fun j => S0.get j)
      (middle := fun i => proj (A.get i))
      (target := fun i => S1.get i)
      a a3 a1 hsum3 hrow1' hget

  have hSTlen : S1.length = S0.length :=
    hBT.finrank_eq.symm.trans hBS.finrank_eq
  unfold CobAgree CobResult CobRows
  dsimp only
  refine ⟨a,ha,by simpa only [S0, S1] using hSTlen, ?_, ?_⟩
  · have halen' : a.length = S0.length * S0.length :=
      halen.trans (congrArg (fun n => S0.length * n) hSTlen)
    simpa only [S0] using halen'
  · intro j
    change S0.getD j.val 0 = ∑ i : Fin S0.length,
      a.get (j.val * S0.length + i.val) • S1.getD i.val 0
    calc
      S0.getD j.val 0 = S0.get j :=
        List.getD_eq_getElem S0 0 j.isLt
      _ = ∑ i : Fin S1.length,
          a.get (j.val * S1.length + i.val) • S1.get i := hsum j
      _ = ∑ i : Fin S0.length,
          a.get (j.val * S0.length + i.val) • S1.getD i.val 0 := by
        rw [Fin.raw_sum_cast_of_eq hSTlen]
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val < S1.length := by
          simpa only [hSTlen] using i.isLt
        simp only [Fin.val_cast, hSTlen]
        rw [List.getD_eq_getElem S1 0 hi]
        rfl

theorem arm_cob_proj_img_coimg_dom
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 b0' : Basis} {env1 env3 : ValExpr}
    {sv1 sv sv' : ValSpace}
    (hbSrc : BasisValid Gamma (.proj s b0 b1))
    (hbTgt : BasisValid Gamma (.proj s b0' b1))
    (hs : s = .img s0 s1 e ∨ s = .coimg s0 s1 e)
    (_hsofb0 : Basis.sof b0 = s0)
    (hsofb1 : Basis.sof b1 = s1)
    (_hsofb0' : Basis.sof b0' = s0)
    (_hsv1 : S.Space Gamma Psi (Basis.sof b1) sv1)
    (_hsv : S.Space Gamma Psi s sv)
    (_hsv' : S.Space Gamma Psi s sv')
    (_hembd : S.Term ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (_hproj : S.Term ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1))
      (.tprod (.dual b1) (.proj s b0' b1)) env1
      (.space (.tprod sv1 sv')))
    (ihSv1 : MSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : MSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : MSpaceSubctx orc Gamma Psi s sv')
    (ihEmbd : MTermSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (ihProj : MTermSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1))
      (.tprod (.dual b1) (.proj s b0' b1)) env1
      (.space (.tprod sv1 sv'))) :
    MCobSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv1 sv1
        (ValExpr.reshapBase env1 (.tprod sv1 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv1)))
      (.proj s b0' b1) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hctx : RawCtxIncl ∅ Gamma Delta' Gamma' := by
    refine ⟨?_, hle⟩
    intro x sx hx
    simp at hx
  have trEmbd := ihEmbd hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc
  have trProj := ihProj hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc

  have hb1v := (raw_proj_basisValid_components hbSrc).2
  have hBS := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj s b0 b1) (raw_basisValid_mono hbSrc hle)
    hc.ctxWF_nl hc.envWF_nl
  have hBT := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj s b0' b1) (raw_basisValid_mono hbTgt hle)
    hc.ctxWF_nl hc.envWF_nl
  have hBA := denotBasis_atSpace_isListBasis sigma Gamma' b1
    (raw_basisValid_mono hb1v hle) hc.ctxWF_nl hc.envWF_nl

  obtain ⟨a3, ha3, ha3len, hrow3⟩ :=
    trace_linear_map_rows hBS hBA trEmbd
  obtain ⟨a1, ha1, ha1len, hrow1⟩ :=
    trace_linear_map_rows hBA hBT trProj

  let V := denotSpace sigma s
  let W := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma (.proj s b0 b1)).atSpace V
  let S1 := (denotBasis sigma (.proj s b0' b1)).atSpace V
  let A := (denotBasis sigma b1).atSpace W
  let emb := (denotTerm sigma (Term.lembd s)).asLinMap V W
  let proj := (denotTerm sigma
    (Term.lproj s (Basis.sof b1))).asLinMap W V

  have hrow3' : forall j : Fin S0.length,
      emb (S0.get j) = ∑ i : Fin A.length,
        a3.get (j.val * A.length + i.val) • A.get i := by
    simpa only [emb, S0, A, V, W] using hrow3
  have hrow1' : forall j : Fin A.length,
      proj (A.get j) = ∑ i : Fin S1.length,
        a1.get (j.val * S1.length + i.val) • S1.get i := by
    simpa only [proj, A, S1, W, V] using hrow1

  have hSdim := basis_dimension hbSrc ihSv hsub hle hc
  have hTdim := basis_dimension hbTgt ihSv' hsub hle hc
  have hAdim := basis_dimension hb1v ihSv1 hsub hle hc
  have ha3Len : a3.length = S0.length*A.length := ha3len
  have ha1Len : a1.length = A.length*S1.length := ha1len
  have hr3 := reshape_array ha3 (dof_tprod_ok hSdim hAdim) ha3Len
  have hr1 := reshape_array ha1 (dof_tprod_ok hAdim hTdim) ha1Len
  obtain ⟨a,ha,halen,hget⟩ := mtm_rectangular orc rho (sAux := sv1)
    (left := ValExpr.reshapBase env1 (.tprod sv1 sv'))
    (right := ValExpr.reshapBase env3 (.tprod sv sv1))
    rfl rfl hr1 hr3 hSdim hAdim hTdim ha1Len ha3Len

  have hleft : forall j : Fin S0.length,
      proj (emb (S0.get j)) = S0.get j := by
    intro j
    change (denotTerm sigma
        (Term.lproj s (Basis.sof b1))).asLinMap
        (denotSpace sigma (Basis.sof b1)) (denotSpace sigma s)
        ((denotTerm sigma (Term.lembd s)).asLinMap
          (denotSpace sigma s) (denotSpace sigma (Basis.sof b1))
          (S0.get j)) = S0.get j
    rw [hsofb1]
    exact raw_lproj_lembd_img_coimg sigma hs (S0.get j)
  have hsum3 : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin A.length,
        a3.get (j.val * A.length + i.val) • proj (A.get i) := by
    intro j
    rw [← hleft j, hrow3' j, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  have hsum : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin S1.length,
        a.get (j.val * S1.length + i.val) • S1.get i :=
    raw_rectangular_comp_family
      (source := fun j => S0.get j)
      (middle := fun i => proj (A.get i))
      (target := fun i => S1.get i)
      a a3 a1 hsum3 hrow1' hget

  have hSTlen : S1.length = S0.length :=
    hBT.finrank_eq.symm.trans hBS.finrank_eq
  unfold CobAgree CobResult CobRows
  dsimp only
  refine ⟨a,ha,by simpa only [S0, S1] using hSTlen, ?_, ?_⟩
  · have halen' : a.length = S0.length * S0.length :=
      halen.trans (congrArg (fun n => S0.length * n) hSTlen)
    simpa only [S0] using halen'
  · intro j
    change S0.getD j.val 0 = ∑ i : Fin S0.length,
      a.get (j.val * S0.length + i.val) • S1.getD i.val 0
    calc
      S0.getD j.val 0 = S0.get j :=
        List.getD_eq_getElem S0 0 j.isLt
      _ = ∑ i : Fin S1.length,
          a.get (j.val * S1.length + i.val) • S1.get i := hsum j
      _ = ∑ i : Fin S0.length,
          a.get (j.val * S0.length + i.val) • S1.getD i.val 0 := by
        rw [Fin.raw_sum_cast_of_eq hSTlen]
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val < S1.length := by
          simpa only [hSTlen] using i.isLt
        simp only [Fin.val_cast, hSTlen]
        rw [List.getD_eq_getElem S1 0 hi]
        rfl

theorem arm_cob_proj_img_coimg
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 b1' : Basis} {env1 env2 env3 : ValExpr}
    {sv0 sv1 sv sv' sv1' : ValSpace}
    (hbSrc : BasisValid Gamma (.proj s b0 b1))
    (hbTgt : BasisValid Gamma (.proj s b0 b1'))
    (hs : s = .img s0 s1 e ∨ s = .coimg s0 s1 e)
    (_hsofb0 : Basis.sof b0 = s0)
    (hsofb1 : Basis.sof b1 = s1)
    (_hsv0 : S.Space Gamma Psi (Basis.sof b0) sv0)
    (_hsv1 : S.Space Gamma Psi (Basis.sof b1) sv1)
    (_hsv : S.Space Gamma Psi s sv)
    (_hsv' : S.Space Gamma Psi s sv')
    (_hsv1' : S.Space Gamma Psi (Basis.sof b1') sv1')
    (hcob : S.Cob Gamma Psi b1 env2 b1')
    (_hembd : S.Term ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (_hproj : S.Term ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1'))
      (.tprod (.dual b1') (.proj s b0 b1')) env1
      (.space (.tprod sv1' sv')))
    (ihSv1 : MSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : MSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : MSpaceSubctx orc Gamma Psi s sv')
    (ihSv1' : MSpaceSubctx orc Gamma Psi (Basis.sof b1') sv1')
    (ihCob : MCobSubctx orc Gamma Psi b1 env2 b1')
    (ihEmbd : MTermSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (ihProj : MTermSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1'))
      (.tprod (.dual b1') (.proj s b0 b1')) env1
      (.space (.tprod sv1' sv'))) :
    MCobSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv1' sv1'
        (ValExpr.reshapBase env1 (.tprod sv1' sv'))
        (.mtm 0 0 sv1 sv1
          (ValExpr.reshapBase env2 (.tprod sv1 sv1'))
          (ValExpr.reshapBase env3 (.tprod sv sv1))))
      (.proj s b0 b1') := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hctx : RawCtxIncl ∅ Gamma Delta' Gamma' := by
    refine ⟨?_, hle⟩
    intro x sx hx
    simp at hx
  have trEmbd := ihEmbd hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc
  have trProj := ihProj hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc
  have cobAgree := ihCob hsub rho Delta' Gamma' sigma GammaV hle hc
  have hsofAmbient : Basis.sof b1 = Basis.sof b1' := S.Cob.sof_eq hcob

  have hb1v := (raw_proj_basisValid_components hbSrc).2
  have hb1'v := (raw_proj_basisValid_components hbTgt).2
  have hBS := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj s b0 b1) (raw_basisValid_mono hbSrc hle)
    hc.ctxWF_nl hc.envWF_nl
  have hBT := denotBasis_atSpace_isListBasis sigma Gamma'
    (.proj s b0 b1') (raw_basisValid_mono hbTgt hle)
    hc.ctxWF_nl hc.envWF_nl
  have hBA := denotBasis_atSpace_isListBasis sigma Gamma' b1
    (raw_basisValid_mono hb1v hle) hc.ctxWF_nl hc.envWF_nl
  have hBA' := denotBasis_atSpace_isListBasis sigma Gamma' b1'
    (raw_basisValid_mono hb1'v hle) hc.ctxWF_nl hc.envWF_nl

  obtain ⟨a3, ha3, ha3len, hrow3⟩ :=
    trace_linear_map_rows hBS hBA trEmbd
  obtain ⟨a1, ha1, ha1len, hrow1⟩ :=
    trace_linear_map_rows hBA' hBT trProj

  let V := denotSpace sigma s
  let W := denotSpace sigma (Basis.sof b1)
  let S0 := (denotBasis sigma (.proj s b0 b1)).atSpace V
  let S1 := (denotBasis sigma (.proj s b0 b1')).atSpace V
  let A0 := (denotBasis sigma b1).atSpace W
  let A1 := (denotBasis sigma b1').atSpace W
  let emb := (denotTerm sigma (Term.lembd s)).asLinMap V W
  let proj := (denotTerm sigma
    (Term.lproj s (Basis.sof b1))).asLinMap W V

  have hrow1' : forall j : Fin A1.length,
      proj (A1.get j) = ∑ i : Fin S1.length,
        a1.get (j.val * S1.length + i.val) • S1.get i := by
    have h := hrow1
    rw [← hsofAmbient] at h
    simpa only [proj, A1, S1, W, V] using h

  simp only [CobAgree,CobResult,CobRows] at cobAgree
  obtain ⟨a2, ha2, hA1len, ha2len, hrow2⟩ := cobAgree
  have hrow2' : forall j : Fin A0.length,
      A0.get j = ∑ i : Fin A1.length,
        a2.get (j.val * A0.length + i.val) • A1.get i := by
    intro j
    calc
      A0.get j = A0.getD j.val 0 :=
        (List.getD_eq_getElem A0 0 j.isLt).symm
      _ = ∑ i : Fin A0.length,
          a2.get (j.val * A0.length + i.val) • A1.getD i.val 0 :=
        hrow2 j
      _ = ∑ i : Fin A1.length,
          a2.get (j.val * A0.length + i.val) • A1.get i := by
        rw [Fin.raw_sum_cast_of_eq hA1len.symm]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.val_cast]
        rw [List.getD_eq_getElem A1 0 i.isLt]
        rw [List.get_eq_getElem]

  have hSdim := basis_dimension hbSrc ihSv hsub hle hc
  have hTdim := basis_dimension hbTgt ihSv' hsub hle hc
  have hA0dim := basis_dimension hb1v ihSv1 hsub hle hc
  have hA1dim0 := basis_dimension hb1'v ihSv1' hsub hle hc
  have hA1dim : sv1'.dofPartial (orc rho [] []) = .ok A1.length := by
    rw [← hsofAmbient] at hA1dim0
    exact hA1dim0
  have ha3Len : a3.length = S0.length*A0.length := ha3len
  have ha2Len : a2.length = A0.length*A1.length := by
    change a2.length = A0.length*A0.length at ha2len
    change A1.length = A0.length at hA1len
    rw [hA1len]
    exact ha2len
  have ha1Len : a1.length = A1.length*S1.length := by
    rw [← hsofAmbient] at ha1len
    exact ha1len
  have hr3 := reshape_array ha3 (dof_tprod_ok hSdim hA0dim) ha3Len
  have hr2 := reshape_array ha2 (dof_tprod_ok hA0dim hA1dim) ha2Len
  have hr1 := reshape_array ha1 (dof_tprod_ok hA1dim hTdim) ha1Len
  obtain ⟨a23,ha23,ha23len,hget23⟩ := mtm_rectangular orc rho (sAux := sv1)
    (left := ValExpr.reshapBase env2 (.tprod sv1 sv1'))
    (right := ValExpr.reshapBase env3 (.tprod sv sv1))
    rfl rfl hr2 hr3 hSdim hA0dim hA1dim ha2Len ha3Len
  obtain ⟨a,ha,halen,hget⟩ := mtm_rectangular orc rho (sAux := sv1')
    (left := ValExpr.reshapBase env1 (.tprod sv1' sv'))
    (right := .mtm 0 0 sv1 sv1
      (ValExpr.reshapBase env2 (.tprod sv1 sv1'))
      (ValExpr.reshapBase env3 (.tprod sv sv1)))
    rfl rfl hr1 ha23 hSdim hA1dim hTdim ha1Len ha23len

  have hleft : forall j : Fin S0.length,
      proj (emb (S0.get j)) = S0.get j := by
    intro j
    change (denotTerm sigma
        (Term.lproj s (Basis.sof b1))).asLinMap
        (denotSpace sigma (Basis.sof b1)) (denotSpace sigma s)
        ((denotTerm sigma (Term.lembd s)).asLinMap
          (denotSpace sigma s) (denotSpace sigma (Basis.sof b1))
          (S0.get j)) = S0.get j
    rw [hsofb1]
    exact raw_lproj_lembd_img_coimg sigma hs (S0.get j)
  have hrow3' : forall j : Fin S0.length,
      emb (S0.get j) = ∑ i : Fin A0.length,
        a3.get (j.val * A0.length + i.val) • A0.get i := by
    simpa only [emb, S0, A0, V, W] using hrow3
  have hsum3 : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin A0.length,
        a3.get (j.val * A0.length + i.val) • proj (A0.get i) := by
    intro j
    rw [← hleft j, hrow3' j, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
  have hsum2 : forall j : Fin A0.length,
      proj (A0.get j) = ∑ i : Fin A1.length,
        a2.get (j.val * A1.length + i.val) • proj (A1.get i) := by
    intro j
    rw [hrow2' j, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    have hidx : j.val * A0.length + i.val =
        j.val * A1.length + i.val :=
      congrArg (fun n => j.val * n + i.val) hA1len.symm
    rw [hidx]
  have hsum23 : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin A1.length,
        a23.get (j.val * A1.length + i.val) • proj (A1.get i) :=
    raw_rectangular_comp_family
      (source := fun j => S0.get j)
      (middle := fun i => proj (A0.get i))
      (target := fun i => proj (A1.get i))
      a23 a3 a2 hsum3 hsum2 (by
        intro j i hj hi
        simpa only [hA1len] using hget23 j i hj hi)
  have hsum : forall j : Fin S0.length,
      S0.get j = ∑ i : Fin S1.length,
        a.get (j.val * S1.length + i.val) • S1.get i :=
    raw_rectangular_comp_family
      (source := fun j => S0.get j)
      (middle := fun i => proj (A1.get i))
      (target := fun i => S1.get i)
      a a23 a1 hsum23 hrow1' hget

  have hSTlen : S1.length = S0.length :=
    hBT.finrank_eq.symm.trans hBS.finrank_eq
  unfold CobAgree CobResult CobRows
  dsimp only
  refine ⟨a,ha,by simpa only [S0, S1] using hSTlen, ?_, ?_⟩
  · have halen' : a.length = S0.length * S0.length :=
      halen.trans (congrArg (fun n => S0.length * n) hSTlen)
    simpa only [S0] using halen'
  · intro j
    change S0.getD j.val 0 = ∑ i : Fin S0.length,
      a.get (j.val * S0.length + i.val) • S1.getD i.val 0
    calc
      S0.getD j.val 0 = S0.get j :=
        List.getD_eq_getElem S0 0 j.isLt
      _ = ∑ i : Fin S1.length,
          a.get (j.val * S1.length + i.val) • S1.get i := hsum j
      _ = ∑ i : Fin S0.length,
          a.get (j.val * S0.length + i.val) • S1.getD i.val 0 := by
        rw [Fin.raw_sum_cast_of_eq hSTlen]
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val < S1.length := by
          simpa only [hSTlen] using i.isLt
        simp only [Fin.val_cast, hSTlen]
        rw [List.getD_eq_getElem S1 0 hi]
        rfl

private theorem infer_space_pair
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {b : Basis} {env : ValExpr} {sv0 sv1 : ValSpace}
    (hb : BasisValid Gamma b)
    (hshape : ValExpr.inferSpaceCtx [] env = .tprod sv0 sv1)
    (ih0 : MSpaceSubctx orc Gamma Psi (Basis.sof b) sv0)
    (ih1 : MSpaceSubctx orc Gamma Psi (Basis.sof b) sv1) :
    CobInferSubctx orc Gamma Psi env b := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  exact ⟨sv0,sv1,hshape,basis_dimension hb ih0 hsub hle hc,
    basis_dimension hb ih1 hsub hle hc⟩

theorem arm_cob_infer_proj_ker_coker
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {b0 b1 : Basis} {env1 env2 env3 : ValExpr}
    {sv0 sv sv' sv0' : ValSpace}
    (hbSrc : Basis.BasisValid Gamma (.proj s b0 b1))
    (ihSpace : MSpaceSubctx orc Gamma Psi s sv)
    (ihSpace' : MSpaceSubctx orc Gamma Psi s sv') :
    CobInferSubctx orc Gamma Psi
      (.mtm 0 0 sv0' sv0'
        (ValExpr.reshapBase env1 (.tprod sv0' sv'))
        (.mtm 0 0 sv0 sv0
          (ValExpr.reshapBase env2 (.tprod sv0 sv0'))
          (ValExpr.reshapBase env3 (.tprod sv sv0))))
      (.proj s b0 b1) := by
  exact infer_space_pair
    (env := .mtm 0 0 sv0' sv0'
      (ValExpr.reshapBase env1 (.tprod sv0' sv'))
      (.mtm 0 0 sv0 sv0
        (ValExpr.reshapBase env2 (.tprod sv0 sv0'))
        (ValExpr.reshapBase env3 (.tprod sv sv0))))
    (sv0 := sv) (sv1 := sv') hbSrc rfl ihSpace ihSpace'

theorem arm_cob_facts_proj_ker_coker
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 b0' : Basis} {env1 env2 env3 : ValExpr}
    {sv0 sv1 sv sv' sv0' : ValSpace}
    (hbSrc : BasisValid Gamma (.proj s b0 b1))
    (hbTgt : BasisValid Gamma (.proj s b0' b1))
    (hs : s = .ker s0 s1 e ∨ s = .coker s0 s1 e)
    (hsofb0 : Basis.sof b0 = s0)
    (hsofb1 : Basis.sof b1 = s1)
    (hsv0 : S.Space Gamma Psi (Basis.sof b0) sv0)
    (hsv1 : S.Space Gamma Psi (Basis.sof b1) sv1)
    (hsv : S.Space Gamma Psi s sv)
    (hsv' : S.Space Gamma Psi s sv')
    (hsv0' : S.Space Gamma Psi (Basis.sof b0') sv0')
    (hcob : S.Cob Gamma Psi b0 env2 b0')
    (hembd : S.Term ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (hproj : S.Term ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0'))
      (.tprod (.dual b0') (.proj s b0' b1)) env1
      (.space (.tprod sv0' sv')))
    (ihSv0 : MSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (_ihSv1 : MSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : MSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : MSpaceSubctx orc Gamma Psi s sv')
    (ihSv0' : MSpaceSubctx orc Gamma Psi (Basis.sof b0') sv0')
    (ihCob : CobFactsSubctx orc Gamma Psi b0 env2 b0')
    (ihEmbd : TermFactsSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (ihProj : TermFactsSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0'))
      (.tprod (.dual b0') (.proj s b0' b1)) env1
      (.space (.tprod sv0' sv'))) :
    CobFactsSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv0' sv0'
        (ValExpr.reshapBase env1 (.tprod sv0' sv'))
        (.mtm 0 0 sv0 sv0
          (ValExpr.reshapBase env2 (.tprod sv0 sv0'))
          (ValExpr.reshapBase env3 (.tprod sv sv0))))
      (.proj s b0' b1) := by
  exact ⟨arm_cob_proj_ker_coker hbSrc hbTgt hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv0' hcob hembd hproj
      ihSv0 ihSv ihSv' ihSv0' ihCob.agree ihEmbd.trace ihProj.trace,
    arm_cob_infer_proj_ker_coker hbSrc ihSv ihSv'⟩

theorem arm_cob_infer_proj_ker_coker_cod
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {b0 b1 : Basis} {env1 env3 : ValExpr}
    {sv0 sv sv' : ValSpace}
    (hbSrc : Basis.BasisValid Gamma (.proj s b0 b1))
    (ihSpace : MSpaceSubctx orc Gamma Psi s sv)
    (ihSpace' : MSpaceSubctx orc Gamma Psi s sv') :
    CobInferSubctx orc Gamma Psi
      (.mtm 0 0 sv0 sv0
        (ValExpr.reshapBase env1 (.tprod sv0 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv0)))
      (.proj s b0 b1) := by
  exact infer_space_pair
    (env := .mtm 0 0 sv0 sv0
      (ValExpr.reshapBase env1 (.tprod sv0 sv'))
      (ValExpr.reshapBase env3 (.tprod sv sv0)))
    (sv0 := sv) (sv1 := sv') hbSrc rfl ihSpace ihSpace'

theorem arm_cob_facts_proj_ker_coker_cod
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 b1' : Basis} {env1 env3 : ValExpr}
    {sv0 sv sv' : ValSpace}
    (hbSrc : BasisValid Gamma (.proj s b0 b1))
    (hbTgt : BasisValid Gamma (.proj s b0 b1'))
    (hs : s = .ker s0 s1 e ∨ s = .coker s0 s1 e)
    (hsofb0 : Basis.sof b0 = s0)
    (hsofb1 : Basis.sof b1 = s1)
    (hsofb1' : Basis.sof b1' = s1)
    (hsv0 : S.Space Gamma Psi (Basis.sof b0) sv0)
    (hsv : S.Space Gamma Psi s sv)
    (hsv' : S.Space Gamma Psi s sv')
    (hembd : S.Term ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (hproj : S.Term ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0))
      (.tprod (.dual b0) (.proj s b0 b1')) env1
      (.space (.tprod sv0 sv')))
    (ihSv0 : MSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (ihSv : MSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : MSpaceSubctx orc Gamma Psi s sv')
    (ihEmbd : TermFactsSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (ihProj : TermFactsSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0))
      (.tprod (.dual b0) (.proj s b0 b1')) env1
      (.space (.tprod sv0 sv'))) :
    CobFactsSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv0 sv0
        (ValExpr.reshapBase env1 (.tprod sv0 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv0)))
      (.proj s b0 b1') := by
  exact ⟨arm_cob_proj_ker_coker_cod hbSrc hbTgt hs hsofb0
      hsofb1 hsofb1' hsv0 hsv hsv' hembd hproj
      ihSv0 ihSv ihSv' ihEmbd.trace ihProj.trace,
    arm_cob_infer_proj_ker_coker_cod hbSrc ihSv ihSv'⟩

theorem arm_cob_infer_proj_img_coimg_dom
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {b0 b1 : Basis} {env1 env3 : ValExpr}
    {sv1 sv sv' : ValSpace}
    (hbSrc : Basis.BasisValid Gamma (.proj s b0 b1))
    (ihSpace : MSpaceSubctx orc Gamma Psi s sv)
    (ihSpace' : MSpaceSubctx orc Gamma Psi s sv') :
    CobInferSubctx orc Gamma Psi
      (.mtm 0 0 sv1 sv1
        (ValExpr.reshapBase env1 (.tprod sv1 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv1)))
      (.proj s b0 b1) := by
  exact infer_space_pair
    (env := .mtm 0 0 sv1 sv1
      (ValExpr.reshapBase env1 (.tprod sv1 sv'))
      (ValExpr.reshapBase env3 (.tprod sv sv1)))
    (sv0 := sv) (sv1 := sv') hbSrc rfl ihSpace ihSpace'

theorem arm_cob_facts_proj_img_coimg_dom
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 b0' : Basis} {env1 env3 : ValExpr}
    {sv1 sv sv' : ValSpace}
    (hbSrc : BasisValid Gamma (.proj s b0 b1))
    (hbTgt : BasisValid Gamma (.proj s b0' b1))
    (hs : s = .img s0 s1 e ∨ s = .coimg s0 s1 e)
    (hsofb0 : Basis.sof b0 = s0)
    (hsofb1 : Basis.sof b1 = s1)
    (hsofb0' : Basis.sof b0' = s0)
    (hsv1 : S.Space Gamma Psi (Basis.sof b1) sv1)
    (hsv : S.Space Gamma Psi s sv)
    (hsv' : S.Space Gamma Psi s sv')
    (hembd : S.Term ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (hproj : S.Term ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1))
      (.tprod (.dual b1) (.proj s b0' b1)) env1
      (.space (.tprod sv1 sv')))
    (ihSv1 : MSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : MSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : MSpaceSubctx orc Gamma Psi s sv')
    (ihEmbd : TermFactsSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (ihProj : TermFactsSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1))
      (.tprod (.dual b1) (.proj s b0' b1)) env1
      (.space (.tprod sv1 sv'))) :
    CobFactsSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv1 sv1
        (ValExpr.reshapBase env1 (.tprod sv1 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv1)))
      (.proj s b0' b1) := by
  exact ⟨arm_cob_proj_img_coimg_dom hbSrc hbTgt hs hsofb0
      hsofb1 hsofb0' hsv1 hsv hsv' hembd hproj
      ihSv1 ihSv ihSv' ihEmbd.trace ihProj.trace,
    arm_cob_infer_proj_img_coimg_dom hbSrc ihSv ihSv'⟩

theorem arm_cob_infer_proj_img_coimg
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s : Space} {b0 b1 : Basis} {env1 env2 env3 : ValExpr}
    {sv1 sv sv' sv1' : ValSpace}
    (hbSrc : Basis.BasisValid Gamma (.proj s b0 b1))
    (ihSpace : MSpaceSubctx orc Gamma Psi s sv)
    (ihSpace' : MSpaceSubctx orc Gamma Psi s sv') :
    CobInferSubctx orc Gamma Psi
      (.mtm 0 0 sv1' sv1'
        (ValExpr.reshapBase env1 (.tprod sv1' sv'))
        (.mtm 0 0 sv1 sv1
          (ValExpr.reshapBase env2 (.tprod sv1 sv1'))
          (ValExpr.reshapBase env3 (.tprod sv sv1))))
      (.proj s b0 b1) := by
  exact infer_space_pair
    (env := .mtm 0 0 sv1' sv1'
      (ValExpr.reshapBase env1 (.tprod sv1' sv'))
      (.mtm 0 0 sv1 sv1
        (ValExpr.reshapBase env2 (.tprod sv1 sv1'))
        (ValExpr.reshapBase env3 (.tprod sv sv1))))
    (sv0 := sv) (sv1 := sv') hbSrc rfl ihSpace ihSpace'

theorem arm_cob_facts_proj_img_coimg
    {orc : PartialFFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
    {s0 s1 : Space} {e : Term} {s : Space}
    {b0 b1 b1' : Basis} {env1 env2 env3 : ValExpr}
    {sv0 sv1 sv sv' sv1' : ValSpace}
    (hbSrc : BasisValid Gamma (.proj s b0 b1))
    (hbTgt : BasisValid Gamma (.proj s b0 b1'))
    (hs : s = .img s0 s1 e ∨ s = .coimg s0 s1 e)
    (hsofb0 : Basis.sof b0 = s0)
    (hsofb1 : Basis.sof b1 = s1)
    (hsv0 : S.Space Gamma Psi (Basis.sof b0) sv0)
    (hsv1 : S.Space Gamma Psi (Basis.sof b1) sv1)
    (hsv : S.Space Gamma Psi s sv)
    (hsv' : S.Space Gamma Psi s sv')
    (hsv1' : S.Space Gamma Psi (Basis.sof b1') sv1')
    (hcob : S.Cob Gamma Psi b1 env2 b1')
    (hembd : S.Term ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (hproj : S.Term ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1'))
      (.tprod (.dual b1') (.proj s b0 b1')) env1
      (.space (.tprod sv1' sv')))
    (_ihSv0 : MSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (ihSv1 : MSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : MSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : MSpaceSubctx orc Gamma Psi s sv')
    (ihSv1' : MSpaceSubctx orc Gamma Psi (Basis.sof b1') sv1')
    (ihCob : CobFactsSubctx orc Gamma Psi b1 env2 b1')
    (ihEmbd : TermFactsSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (ihProj : TermFactsSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1'))
      (.tprod (.dual b1') (.proj s b0 b1')) env1
      (.space (.tprod sv1' sv'))) :
    CobFactsSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv1' sv1'
        (ValExpr.reshapBase env1 (.tprod sv1' sv'))
        (.mtm 0 0 sv1 sv1
          (ValExpr.reshapBase env2 (.tprod sv1 sv1'))
          (ValExpr.reshapBase env3 (.tprod sv sv1))))
      (.proj s b0 b1') := by
  exact ⟨arm_cob_proj_img_coimg hbSrc hbTgt hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv1' hcob hembd hproj
      ihSv1 ihSv ihSv' ihSv1' ihCob.agree ihEmbd.trace ihProj.trace,
    arm_cob_infer_proj_img_coimg hbSrc ihSv ihSv'⟩

end GLang.PartialAdequacy
