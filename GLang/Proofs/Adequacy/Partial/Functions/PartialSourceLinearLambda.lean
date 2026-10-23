import GLang.Proofs.Adequacy.Partial.Source.PartialSourceLinearHistory
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceLinearSums
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceBounds
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCob

namespace GLang.PartialAdequacy
open scoped BigOperators TensorProduct
open Basis (BasisValid)
open PartialValueEval

private theorem raw_llam_rawAgree_space_array
    {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {s : GLang.Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : Agree orc sigma rho Ds Gv Dv
      (.space s) (.space sv) B x y) : exists a, y = .array a := by
  cases y with
  | array a => exact ⟨a, rfl⟩
  | fn T f => simpa only [Agree] using h

/-- A child compiled at a space value type cannot be observed through a
source frame basis.  Consequently its successful raw agreement both exposes
the source basis as an ordinary space basis and exposes an array result. -/
private theorem raw_llam_rawAgree_basis_space_array
    {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {b : Basis} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : Agree orc sigma rho Ds Gv Dv
      (Basis.tof b) (.space sv) B x y) :
    Basis.tof b = .space (Basis.sof b) ∧ exists a, y = .array a := by
  cases b <;> cases y <;>
    simp only [Basis.tof, Agree, reduceCtorEq] at h ⊢ <;>
    first | contradiction | exact ⟨True.intro, ⟨_, rfl⟩⟩

private theorem agree_one_real
    {orc : PartialFFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {x : DVal} {a : FlatArray}
    (h : Agree orc sigma rho [] [] [] (.space .real) (.space .real)
      (denotBasis sigma .one) x (.array a)) :
    x.atSpace HSpace.real = a.get 0 := by
  rw [agree_space_iff (by simp [ValSpace.dofPartial, ValSpace.shpOfPartial, bind, Except.bind, pure, Except.pure] : ValSpace.real.dofPartial (orc rho [] []) = .ok 1)] at h
  have hc := h.2.2
  simp only [denotBasis, denotSpaceAux, BasisDenot.atSpace_vecs_self, Fin.sum_univ_one, Fin.val_zero, List.getD_cons_zero] at hc
  change x.atSpace HSpace.real = (a.get 0 : ℝ) * 1 at hc
  simpa using hc

theorem arm_llam_assemble_real
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b' : Basis} {e : Term} {sv' : ValSpace}
    {env : Fin (ValSpace.dofUB sv') → ValExpr}
    (htof' : Basis.tof b' = .space (Basis.sof b'))
    (ht : Nonempty (HasType Delta Gamma
      (.llam (Basis.sof b') .real e) (Basis.tof (.dual b'))))
    (hbv : BasisValid Gamma (.dual b'))
    (_hTy : S.TyAt Gamma Psi (.dual b') (.space sv'))
    (_hsv' : S.Space Gamma Psi (Basis.sof b') sv')
    (L : Finset Name)
    (hfam : forall y, y ∉ L → forall i : Fin (ValSpace.dofUB sv'),
      S.Term (Finmap.insert y (Basis.sof b') Delta) Gamma
        (Psi.extend y b' (.delta i.val sv'))
        (Term.openVar y e) .one (env i) (.space .real))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi (.dual b') (.space sv'))
    (ihSpace : MSpaceSubctx PartialDirectOracle.oracle Gamma Psi (Basis.sof b') sv')
    (ihfam : forall y, y ∉ L → forall i : Fin (ValSpace.dofUB sv'),
      TermFactsSubctx PartialDirectOracle.oracle
        (Finmap.insert y (Basis.sof b') Delta) Gamma
        (Psi.extend y b' (.delta i.val sv'))
        (Term.openVar y e) .one (env i) (.space .real)) :
    MTermSubctx PartialDirectOracle.oracle Delta Gamma Psi
      (.llam (Basis.sof b') .real e) (.dual b')
      (ValExpr.sumAt sv' (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
          .scale (ValExpr.reshapBase (env i) .real)
            (.delta i.val sv')) sv') (.space sv') := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hbdom : BasisValid Gamma b' := hbv.dual_inv
  have hB := denotBasis_atSpace_isListBasis sigma Gamma' b'
    (raw_basisValid_mono hbdom hle.2) hc.ctxWF_nl hc.envWF_nl
  have hdim := shape_dof (ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hdn := dof_numbers _ _ _ hdim
  have hlen : ((denotBasis sigma b').atSpace (denotSpace sigma (Basis.sof b'))).length =
      ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv' := hB.finrank_eq.symm.trans hdn.symm
  have hNle : ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv' ≤ ValSpace.dofUB sv' := by
    rw [hdn]
    exact dof_success_le rho [] [] sv' _ hdim
  have hdimN : sv'.dofPartial (PartialDirectOracle.oracle rho [] []) =
      .ok (ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv') := by rw [hdn]; exact hdim
  obtain ⟨Delta1, hDelta1, hsourceTyping⟩ :=
    raw_hasType_ctxIncl hc.ctxWF_raw ht hctx hle
  have hlinear := denot_llam_real_body_isLinear hsourceTyping.some
    (hc.ctxWF_raw.of_sub_Δ hDelta1) (hc.envWF_raw.of_sub_Δ hDelta1)
  have hfvsv' : ValSpace.fv sv' ⊆ Psi'.keyNames :=
    (_hsv'.mono hsub).fv_subset_keyNames hc.evalCtxScoped
  have hfvenv : forall i : Fin (ValSpace.dofUB sv'),
      ValExpr.fv (env i) ⊆ Psi'.keyNames :=
    EvalCtxScoped.drop_family
      (fun z hz i hsc => by
        have hterm := (hfam z hz i).mono
          (EvalCtx.Subctx.extend hsub z b' (.delta i.val sv'))
        exact hterm.fv_subset_keyNames hsc)
      hc.evalCtxScoped hfvsv'
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (L ∪ Delta'.keys ∪ Gamma'.keys ∪ Psi'.keyNames ∪ Term.fv e)
  simp only [Finset.mem_union, not_or] at hy
  obtain ⟨⟨⟨⟨hyL, hyDeltaK⟩, hyGammaK⟩, hyPsi⟩, hyE⟩ := hy
  have hyDelta : y ∉ Delta' := fun hm =>
    hyDeltaK (Finmap.mem_keys.mpr hm)
  have hyGamma : y ∉ Gamma' := fun hm =>
    hyGammaK (Finmap.mem_keys.mpr hm)
  have hyEval : forall b, (y, b) ∉ Psi' := by
    intro b hm
    exact hyPsi (EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hm⟩)
  let N := ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv'
  let V := denotSpace sigma (Basis.sof b')
  let vs := (denotBasis sigma b').atSpace V
  let ruleIndex : Fin N → Fin (ValSpace.dofUB sv') :=
    Fin.castLE hNle
  let sourceAt (i : Fin N) : DVal :=
    .hil ⟨V, vs.getD i.val 0⟩
  have hcol (i : Fin N) : exists a : FlatArray,
      denotValB_partial PartialDirectOracle.oracle rho [] [] (env (ruleIndex i)) =
          .ok (.array a) ∧
      a.length = 1 ∧
      (denotTermAux sigma [sourceAt i] e).atSpace HSpace.real = a.get 0 := by
    have hdimsSpace : DimsAt PartialDirectOracle.oracle sigma rho [] [] []
        (Basis.tof b') (.space sv') (denotBasis sigma b') := by
      rw [htof']
      simp only [DimsAt]
      exact ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    obtain ⟨yv, hdelta, hcExt⟩ := hc.extend_binder_lin_delta
      ⟨hyDelta, hyGamma, hyEval⟩ hle.2 htof' hbdom
      (show Basis.IsTyBasis b' from
        (show Basis.IsSpaceBasis b' from _hTy.isTyBasis).toIsTyBasis)
      (_hsv'.mono hsub) hdimN i hdimsSpace
    have hctxExt : Graded.CtxDisj
        (Finmap.insert y (Basis.sof b') Delta) Gamma :=
      Graded.CtxDisj.insert' hctx (by
        intro hm
        obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp hm
        exact hyGamma (Finmap.mem_of_lookup_eq_some (hle.2 y tau htau)))
    have child := (ihfam y hyL (ruleIndex i)).trace
      (EvalCtx.Subctx.extend hsub y b' (.delta (ruleIndex i).val sv'))
      hctxExt (rho.update y yv)
      (Finmap.insert y (Basis.sof b') Delta') Gamma'
      (sigma.bind y (sourceAt i))
      (Finmap.insert y (.space sv') GammaV)
      (hle.insert_lin y (Basis.sof b')) (by
        simpa only [ruleIndex, Fin.castLE, sourceAt, V, vs]
          using hcExt)
    obtain ⟨out, hout, hagree⟩ := child.result
    obtain ⟨a, rfl⟩ := raw_llam_rawAgree_space_array hagree
    have hsrc : denotTerm (sigma.bind y (sourceAt i))
        (Term.openVar y e) = denotTermAux sigma [sourceAt i] e :=
      denotTerm_openVar_bind (hfam y hyL (ruleIndex i)).hasType.some.lc hyE
    rw [hsrc] at hagree
    have hagree' : Agree PartialDirectOracle.oracle (sigma.bind y (sourceAt i))
        (rho.update y yv) [] [] [] (.space .real) (.space .real)
        (denotBasis (sigma.bind y (sourceAt i)) .one)
        (denotTermAux sigma [sourceAt i] e) (.array a) := by
      simpa only [Basis.tof, Basis.sof, Agree] using hagree
    have hscalar := agree_one_real hagree'
    have haLen : a.length = 1 := by
      rw [agree_space_iff (by simp [ValSpace.dofPartial, ValSpace.shpOfPartial, bind, Except.bind, pure, Except.pure] : ValSpace.real.dofPartial (PartialDirectOracle.oracle (rho.update y yv) [] []) = .ok 1)] at hagree'
      exact hagree'.2.1
    have houtRoot : denotValB_partial PartialDirectOracle.oracle rho [] [] (env (ruleIndex i)) =
        .ok (.array a) := by
      have hfresh := PartialDirectFv.eval_fresh rho y yv (env (ruleIndex i)) [] []
        (fun hm => hyPsi (hfvenv (ruleIndex i) hm)) (by intro tau hm; cases hm)
      change denotValB_partial PartialDirectOracle.oracle (rho.update y yv) [] [] (env (ruleIndex i)) =
        denotValB_partial PartialDirectOracle.oracle rho [] [] (env (ruleIndex i)) at hfresh
      exact hfresh.symm.trans hout
    exact ⟨a, houtRoot, haLen, hscalar⟩
  choose columns hcolumnsDen hcolumnsLen hcolumnsSource using hcol
  let summand : Fin (ValSpace.dofUB sv') → ValExpr := fun i =>
    .scale (ValExpr.reshapBase (env i) .real) (.delta i.val sv')
  let row : Fin N → FlatArray := fun i =>
    FlatArray.ofFn N (fun j =>
      (columns i).get 0 * if j = i.val then 1 else 0)
  have hsummandInfer (i : Fin (ValSpace.dofUB sv')) :
      ValExpr.inferSpaceCtx [] (summand i) = sv' := by
    rfl
  have hsummand (i : Fin N) :
      denotValB_partial PartialDirectOracle.oracle rho [] []
          (summand (Fin.castLE hNle i)) = .ok (.array (row i)) := by
    have hreshape := reshapeBase_ok (hcolumnsDen i) (by
      rw [hcolumnsLen i]; simp [ValSpace.dofPartial, ValSpace.shpOfPartial, bind, Except.bind, pure, Except.pure] : ValSpace.real.dofPartial (PartialDirectOracle.oracle rho [] []) = .ok (columns i).length)
    have hcast : Fin.castLE hNle i = ruleIndex i := by
      apply Fin.ext
      rfl
    rw [hcast]
    simp only [summand, ValExpr.reshapBase]
    rw [denotValB_partial]
    have hg : dimensions (PartialDirectOracle.oracle rho [] []) [sv'] = .ok () := by
      simp [dimensions, hdimN, bind, Except.bind]
    simp only [ValExpr.inferSpaceCtx]
    rw [withDimensions, hg]
    dsimp only
    simp only [ValExpr.reshapBase] at hreshape
    rw [hreshape, delta_ok hdimN]
    simp only [ValValSem.bindArrays, ValValSem.bindArray,
      ValValSem.arrayOf]
    rw [if_pos (by
      simp only [ValueShape.scale, ValExpr.inferSpaceCtx, FlatArray.length_ofFn,
        hcolumnsLen i, and_self])]
    congr 2
    apply FlatArray.ofFn_congr
    · rfl
    · intro j
      simp only [ruleIndex, Fin.castLE,
        ValExpr.inferSpaceCtx]
      by_cases hjN : j < N
      · rw [FlatArray.get_ofFn_lt _ _ _ hjN]
        by_cases hji : j = i.val
        · simp [hji, show i.val < ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv' from i.isLt, row]
        · simp [hji, row]
      · rw [FlatArray.get_ofFn_ge _ _ _ (Nat.not_lt.mp hjN)]
        have hji : j ≠ i.val := fun h => hjN (h ▸ i.isLt)
        simp [hji, row]
  have hvsum := vsum_rows_ok hdimN hNle summand row hsummand
    (vsum_same_infer hNle hdimN summand hsummandInfer)
    (fun _ => rfl)
  let out : FlatArray := FlatArray.ofFn N
    (fun j => ∑ i : Fin N, (row i).get j)
  have hvsum' : denotValB_partial PartialDirectOracle.oracle rho [] []
      (.vsum sv' (List.ofFn summand)) = .ok (.array out) := by
    simpa only [out, N] using hvsum
  have hout : denotValB_partial PartialDirectOracle.oracle rho [] []
      (ValExpr.sumAt sv' (List.ofFn summand) sv') =
        .ok (.array out) := by
    rw [denotValB_partial_sumAt]
    exact reshapeBase_ok hvsum' (by simpa only [out, FlatArray.length_ofFn, N] using hdimN)
  have houtCoord (i : Fin N) : out.get i.val = (columns i).get 0 := by
    rw [show out.get i.val = ∑ j : Fin N, (row j).get i.val by
      simp only [out, FlatArray.get_ofFn_lt _ _ _ i.isLt]]
    rw [Finset.sum_eq_single i]
    · simp [row, i.isLt]
    · intro j hj hji
      have hval : i.val ≠ j.val := fun hij => hji (Fin.ext hij.symm)
      simp only [row, FlatArray.get_ofFn_lt _ _ _ i.isLt, if_neg hval,
        mul_zero]
    · exact fun hmem => absurd (Finset.mem_univ i) hmem
  let phi : V.carrier →ₗ[ℝ] ℝ := LinearMap.ofFun fun x =>
    (denotTermAux sigma [.hil ⟨V, x⟩] e).atSpace HSpace.real
  have hphi (x : V.carrier) :
      phi x = (denotTermAux sigma [.hil ⟨V, x⟩] e).atSpace HSpace.real :=
    LinearMap.ofFun_apply_of_isLinearMap hlinear x
  have hsource :
      (denotTerm sigma (.llam (Basis.sof b') .real e)).atSpace
        (HSpace.dual V) = phi := by
    rw [denotTerm_llam_real, atSpace_llamRealDVal]
  have hbasisDual :
      (denotBasis sigma (.dual b')).atSpace (HSpace.dual V) =
        V.dualOfList vs := by
    rw [denotBasis.eq_def]
    simp only [Basis.sof, denotSpace, denotSpaceAux, V, vs]
    rw [BasisDenot.atSpace_vecs_self]
  have hphiColumns : phi = ∑ i : Fin N,
      (columns i).get 0 • (V.dualOfList vs).getD i.val 0 := by
    apply raw_llam_linearFunctional_dual_sum V vs hlen hB phi
      (fun i => (columns i).get 0)
    intro i
    rw [hphi]
    exact hcolumnsSource i
  refine ⟨?_, targetDims⟩
  refine ⟨.array out, ?_, ?_⟩
  · simpa only [summand] using hout
  · simp only [Basis.tof, Basis.sof]
    rw [agree_space_iff hdimN]
    refine ⟨?_, ?_, ?_⟩
    · change ((denotBasis sigma (.dual b')).atSpace
          (HSpace.dual V)).length = ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv'
      rw [hbasisDual, HSpace.dualOfList_length, hlen]
    · simp only [out, FlatArray.length_ofFn, N]
    · change (denotTerm sigma (.llam (Basis.sof b') .real e)).atSpace
          (HSpace.dual V) =
        ∑ i : Fin (ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv'),
          out.get i.val •
            ((denotBasis sigma (.dual b')).atSpace
              (HSpace.dual V)).getD i.val 0
      rw [hsource, hbasisDual, hphiColumns]
      apply Finset.sum_congr rfl
      intro i hi
      rw [houtCoord]

theorem arm_llam_assemble
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {b' b : Basis} {e : Term} {sv' sv : ValSpace}
    {env : Fin (ValSpace.dofUB sv') → ValExpr}
    (htof' : Basis.tof b' = .space (Basis.sof b'))
    (ht : Nonempty (HasType Delta Gamma
      (.llam (Basis.sof b') (Basis.sof b) e)
      (Basis.tof (.tprod (.dual b') b))))
    (hbv : BasisValid Gamma (.tprod (.dual b') b))
    (_hTy : S.TyAt Gamma Psi (.tprod (.dual b') b)
      (.space (.tprod sv' sv)))
    (_hsv' : S.Space Gamma Psi (Basis.sof b') sv')
    (_hsv : S.Space Gamma Psi (Basis.sof b) sv)
    (L : Finset Name)
    (hfam : forall y, y ∉ L → forall i : Fin (ValSpace.dofUB sv'),
      S.Term (Finmap.insert y (Basis.sof b') Delta) Gamma
        (Psi.extend y b' (.delta i.val sv'))
        (Term.openVar y e) b (env i) (.space sv))
    (ihTy : MTyAtSubctx PartialDirectOracle.oracle Gamma Psi (.tprod (.dual b') b)
      (.space (.tprod sv' sv)))
    (ihSpaceDom : MSpaceSubctx PartialDirectOracle.oracle Gamma Psi (Basis.sof b') sv')
    (ihSpaceCod : MSpaceSubctx PartialDirectOracle.oracle Gamma Psi (Basis.sof b) sv)
    (ihfam : forall y, y ∉ L → forall i : Fin (ValSpace.dofUB sv'),
      TermFactsSubctx PartialDirectOracle.oracle
        (Finmap.insert y (Basis.sof b') Delta) Gamma
        (Psi.extend y b' (.delta i.val sv'))
        (Term.openVar y e) b (env i) (.space sv)) :
    MTermSubctx PartialDirectOracle.oracle Delta Gamma Psi
      (.llam (Basis.sof b') (Basis.sof b) e)
      (.tprod (.dual b') b)
      (ValExpr.sumAt sv' (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
          .tprodE (.delta i.val sv')
            (ValExpr.reshapBase (env i) sv))
        (.tprod sv' sv)) (.space (.tprod sv' sv)) := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims := ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  obtain ⟨hbdomDual, hbcod⟩ := hbv.tprod_inv
  have hbdom : BasisValid Gamma b' := hbdomDual.dual_inv
  have hBdom := denotBasis_atSpace_isListBasis sigma Gamma' b'
    (raw_basisValid_mono hbdom hle.2) hc.ctxWF_nl hc.envWF_nl
  have hBcod := denotBasis_atSpace_isListBasis sigma Gamma' b
    (raw_basisValid_mono hbcod hle.2) hc.ctxWF_nl hc.envWF_nl
  have hdimDom := shape_dof (ihSpaceDom hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hdimCod := shape_dof (ihSpaceCod hsub rho Delta' Gamma' sigma GammaV hle.2 hc)
  have hdDom := dof_numbers _ _ _ hdimDom
  have hdCod := dof_numbers _ _ _ hdimCod
  have hlenDom : ((denotBasis sigma b').atSpace (denotSpace sigma (Basis.sof b'))).length =
      ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv' := hBdom.finrank_eq.symm.trans hdDom.symm
  have hlenCod : ((denotBasis sigma b).atSpace (denotSpace sigma (Basis.sof b))).length =
      ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv := hBcod.finrank_eq.symm.trans hdCod.symm
  have hNle : ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv' ≤ ValSpace.dofUB sv' := by
    rw [hdDom]
    exact dof_success_le rho [] [] sv' _ hdimDom
  have hdimN : sv'.dofPartial (PartialDirectOracle.oracle rho [] []) = .ok (ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv') := by
    rw [hdDom]; exact hdimDom
  have hdimM : sv.dofPartial (PartialDirectOracle.oracle rho [] []) = .ok (ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv) := by
    rw [hdCod]; exact hdimCod
  obtain ⟨Delta1, hDelta1, hsourceTyping⟩ :=
    raw_hasType_ctxIncl hc.ctxWF_raw ht hctx hle
  have hlinear := denot_llam_tensor_body_isLinear hsourceTyping.some
    (hc.ctxWF_raw.of_sub_Δ hDelta1) (hc.envWF_raw.of_sub_Δ hDelta1)
  have hne : Basis.sof b ≠ .real :=
    hsourceTyping.some.llam_tensor_codomain_ne_real
  have hfvsv' : ValSpace.fv sv' ⊆ Psi'.keyNames :=
    (_hsv'.mono hsub).fv_subset_keyNames hc.evalCtxScoped
  have hfvsv : ValSpace.fv sv ⊆ Psi'.keyNames :=
    (_hsv.mono hsub).fv_subset_keyNames hc.evalCtxScoped
  have hfvenv : forall i : Fin (ValSpace.dofUB sv'),
      ValExpr.fv (env i) ⊆ Psi'.keyNames :=
    EvalCtxScoped.drop_family
      (fun z hz i hsc => by
        have hterm := (hfam z hz i).mono
          (EvalCtx.Subctx.extend hsub z b' (.delta i.val sv'))
        exact hterm.fv_subset_keyNames hsc)
      hc.evalCtxScoped hfvsv'
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    (L ∪ Delta'.keys ∪ Gamma'.keys ∪ Psi'.keyNames ∪
      Term.fv e ∪ Basis.fv b)
  simp only [Finset.mem_union, not_or] at hy
  obtain ⟨⟨⟨⟨⟨hyL, hyDeltaK⟩, hyGammaK⟩, hyPsi⟩, hyE⟩, hyB⟩ := hy
  have hyDelta : y ∉ Delta' := fun hm =>
    hyDeltaK (Finmap.mem_keys.mpr hm)
  have hyGamma : y ∉ Gamma' := fun hm =>
    hyGammaK (Finmap.mem_keys.mpr hm)
  have hyEval : forall b0, (y, b0) ∉ Psi' := by
    intro b0 hm
    exact hyPsi (EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b0, hm⟩)
  have hySv : y ∉ ValSpace.fv sv := fun hm => hyPsi (hfvsv hm)
  have hySofB : y ∉ Space.fv (Basis.sof b) := fun hm =>
    hyB (Basis.fv_sof_subset b hm)
  let N := ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv'
  let M := ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv
  let V := denotSpace sigma (Basis.sof b')
  let W := denotSpace sigma (Basis.sof b)
  let vs := (denotBasis sigma b').atSpace V
  let ws := (denotBasis sigma b).atSpace W
  have hvsLen : vs.length = N := by
    simpa only [vs, V, N] using hlenDom
  have hwsLen : ws.length = M := by
    simpa only [ws, W, M] using hlenCod
  let ruleIndex : Fin N → Fin (ValSpace.dofUB sv') :=
    Fin.castLE hNle
  let sourceAt (i : Fin N) : DVal :=
    .hil ⟨V, vs.getD i.val 0⟩
  have hcol (i : Fin N) : exists a : FlatArray,
      denotValB_partial PartialDirectOracle.oracle rho [] [] (env (ruleIndex i)) =
          .ok (.array a) ∧
      a.length = M ∧
      (denotTermAux sigma [sourceAt i] e).atSpace W =
        ∑ j : Fin M, a.get j.val • ws.getD j.val 0 := by
    have hdimsSpace : DimsAt PartialDirectOracle.oracle sigma rho [] [] []
        (Basis.tof b') (.space sv') (denotBasis sigma b') := by
      rw [htof']
      simp only [DimsAt]
      exact ihSpaceDom hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    obtain ⟨yv, hdelta, hcExt⟩ := hc.extend_binder_lin_delta
      ⟨hyDelta, hyGamma, hyEval⟩ hle.2 htof' hbdom
      (show Basis.IsTyBasis b' from
        (show Basis.IsSpaceBasis b' from _hTy.isTyBasis.1).toIsTyBasis)
      (_hsv'.mono hsub) hdimN i hdimsSpace
    have hctxExt : Graded.CtxDisj
        (Finmap.insert y (Basis.sof b') Delta) Gamma :=
      Graded.CtxDisj.insert' hctx (by
        intro hm
        obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp hm
        exact hyGamma (Finmap.mem_of_lookup_eq_some (hle.2 y tau htau)))
    have child := (ihfam y hyL (ruleIndex i)).trace
      (EvalCtx.Subctx.extend hsub y b' (.delta (ruleIndex i).val sv'))
      hctxExt (rho.update y yv)
      (Finmap.insert y (Basis.sof b') Delta') Gamma'
      (sigma.bind y (sourceAt i))
      (Finmap.insert y (.space sv') GammaV)
      (hle.insert_lin y (Basis.sof b')) (by
        simpa only [ruleIndex, Fin.castLE, sourceAt, V, vs]
          using hcExt)
    obtain ⟨out, hout, hagree⟩ := child.result
    obtain ⟨htofb, a, rfl⟩ := raw_llam_rawAgree_basis_space_array hagree
    rw [htofb] at hagree
    have hsrc : denotTerm (sigma.bind y (sourceAt i))
        (Term.openVar y e) = denotTermAux sigma [sourceAt i] e :=
      denotTerm_openVar_bind (hfam y hyL (ruleIndex i)).hasType.some.lc hyE
    rw [hsrc] at hagree
    have hagree' : Agree PartialDirectOracle.oracle (sigma.bind y (sourceAt i))
        (rho.update y yv) [] [] [] (.space (Basis.sof b)) (.space sv)
        (denotBasis (sigma.bind y (sourceAt i)) b)
        (denotTermAux sigma [sourceAt i] e) (.array a) := by
      simpa only [Agree] using hagree
    have hWbind : denotSpace (sigma.bind y (sourceAt i))
        (Basis.sof b) = W := by
      exact denotSpace_agree _
        (DEnv.AgreeOn.bind_left_of_not_mem hySofB)
    have hBbind : denotBasis (sigma.bind y (sourceAt i)) b =
        denotBasis sigma b :=
      denotBasis_agree b (DEnv.AgreeOn.bind_left_of_not_mem hyB)
    have hWbindAux : denotSpaceAux (sigma.bind y (sourceAt i)) []
        (Basis.sof b) = W := by
      simpa only [denotSpace] using hWbind
    have hdFresh : sv.dofPartial (PartialDirectOracle.oracle (rho.update y yv) [] []) = .ok M :=
      ((PartialDirectFv.observations PartialDirectFv.oracle_fresh rho y yv [] []
        (by intro tau hm; cases hm) sv hySv).1).trans hdimM
    rw [agree_space_iff hdFresh] at hagree'
    have hcoords := hagree'.2.2
    have haLen := hagree'.2.1
    rw [hWbindAux, hBbind] at hcoords
    have houtRoot : denotValB_partial PartialDirectOracle.oracle rho [] [] (env (ruleIndex i)) = .ok (.array a) := by
      have hfresh := PartialDirectFv.eval_fresh rho y yv (env (ruleIndex i)) [] []
        (fun hm => hyPsi (hfvenv (ruleIndex i) hm)) (by intro tau hm; cases hm)
      change denotValB_partial PartialDirectOracle.oracle (rho.update y yv) [] [] (env (ruleIndex i)) =
        denotValB_partial PartialDirectOracle.oracle rho [] [] (env (ruleIndex i)) at hfresh
      exact hfresh.symm.trans hout
    refine ⟨a, houtRoot, ?_, ?_⟩
    · simpa only [M] using haLen
    · simpa only [M, W, ws] using hcoords
  choose columns hcolumnsDen hcolumnsLen hcolumnsSource using hcol
  let summand : Fin (ValSpace.dofUB sv') → ValExpr := fun i =>
    .tprodE (.delta i.val sv') (ValExpr.reshapBase (env i) sv)
  let deltaRow : Fin N → FlatArray := fun i =>
    FlatArray.ofFn N (fun j => if j = i.val then 1 else 0)
  let row : Fin N → FlatArray := fun i =>
    FlatArray.ofFn (N * M) (fun k =>
      (deltaRow i).get (k / M) * (columns i).get (k % M))
  have hsummandInfer (i : Fin (ValSpace.dofUB sv')) :
      ValExpr.inferSpaceCtx [] (summand i) = .tprod sv' sv := by
    rfl
  have hsummand (i : Fin N) :
      denotValB_partial PartialDirectOracle.oracle rho [] []
          (summand (Fin.castLE hNle i)) = .ok (.array (row i)) := by
    have hreshape := reshapeBase_ok (hcolumnsDen i) (by rw [hcolumnsLen i]; exact hdimM)
    have hcast : Fin.castLE hNle i = ruleIndex i := by
      apply Fin.ext
      rfl
    rw [hcast]
    simp only [summand, ValExpr.reshapBase]
    rw [denotValB_partial]
    have hg : dimensions (PartialDirectOracle.oracle rho [] []) [sv', sv] = .ok () := by
      simp [dimensions, hdimN, hdimM, bind, Except.bind]
    simp only [ValExpr.inferSpaceCtx, ValTy.spaceOf]
    rw [withDimensions, hg]
    dsimp only
    simp only [ValExpr.reshapBase] at hreshape
    rw [delta_ok hdimN, hreshape]
    simp only [ValValSem.bindArrays, ValValSem.bindArray,
      ValValSem.arrayOf]
    rw [if_pos (by
      simp only [ValueShape.pair, ValExpr.inferSpaceCtx, ValTy.spaceOf,
        FlatArray.length_ofFn, hcolumnsLen i, M, and_self])]
    congr 2
    apply FlatArray.ofFn_congr
    · simp only [ValExpr.inferSpaceCtx, ValTy.spaceOf,
        ValSpace.dof_tprod, N, M]
    · intro k
      simp only [ruleIndex, Fin.castLE,
        ValExpr.inferSpaceCtx, N, M]
      congr 1
      simp only [deltaRow]
      rw [FlatArray.get_ofFn]
      by_cases hkN : k / ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv <
          ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) sv'
      · simp [N, hkN, i.isLt]
      · simp [N, hkN]
  have hvsumInfer : (ValExpr.inferSpaceCtx [] (.vsum sv' (List.ofFn summand))).dofPartial
      (PartialDirectOracle.oracle rho [] []) = .ok (N * M) := by
    cases hlist : List.ofFn summand with
    | nil =>
        have hUBzero : ValSpace.dofUB sv' = 0 := by
          have hlen := congrArg List.length hlist
          simpa using hlen
        have hNzero : N = 0 := Nat.eq_zero_of_le_zero (by
          simpa only [hUBzero] using hNle)
        simp [hlist, ValExpr.inferSpaceCtx, ValExpr.inferSpace,
          ValSpace.dofPartial, ValSpace.shpOfPartial, hNzero, bind, Except.bind, pure, Except.pure]
    | cons a as =>
        have hUBpos : 0 < ValSpace.dofUB sv' := by
          by_contra hnot
          have hUBzero : ValSpace.dofUB sv' = 0 := Nat.eq_zero_of_not_pos hnot
          have hlen := congrArg List.length hlist
          simp [hUBzero] at hlen
        let i0 : Fin (ValSpace.dofUB sv') := ⟨0, hUBpos⟩
        have hget : (List.ofFn summand)[0]? = some (summand i0) := by
          simp [i0, hUBpos]
        rw [hlist] at hget
        have ha : a = summand i0 := Option.some.inj hget
        simp only [hlist, ValExpr.inferSpaceCtx, ha, hsummandInfer]
        exact dof_tprod_ok hdimN hdimM
  have hvsum := vsum_rows_ok hdimN hNle summand row hsummand
    hvsumInfer (fun _ => rfl)
  let out : FlatArray := FlatArray.ofFn (N * M)
    (fun k => ∑ i : Fin N, (row i).get k)
  have hvsum' : denotValB_partial PartialDirectOracle.oracle rho [] []
      (.vsum sv' (List.ofFn summand)) = .ok (.array out) := by
    simpa only [out, N, M, ValSpace.dof_tprod] using hvsum
  have hout : denotValB_partial PartialDirectOracle.oracle rho [] []
      (ValExpr.sumAt sv' (List.ofFn summand)
        (.tprod sv' sv)) = .ok (.array out) := by
    rw [denotValB_partial_sumAt]
    exact reshapeBase_ok hvsum' (by
      simpa only [out, FlatArray.length_ofFn, N, M] using dof_tprod_ok hdimN hdimM)
  let phi : V.carrier →ₗ[ℝ] W.carrier := LinearMap.ofFun fun x =>
    (denotTermAux sigma [.hil ⟨V, x⟩] e).atSpace W
  have hphi (x : V.carrier) :
      phi x = (denotTermAux sigma [.hil ⟨V, x⟩] e).atSpace W :=
    LinearMap.ofFun_apply_of_isLinearMap hlinear x
  have hsource :
      (denotTerm sigma
        (.llam (Basis.sof b') (Basis.sof b) e)).atSpace
          (HSpace.tprod (HSpace.dual V) W) =
        (dualTensorHomEquiv ℝ V.carrier W.carrier).symm phi := by
    rw [denotTerm_llam_non_real hne]
    simp only [llamTensorDVal, DVal.atSpace_hil_self, phi, V, W]
  have hbasisTensor :
      (denotBasis sigma (.tprod (.dual b') b)).atSpace
          (HSpace.tprod (HSpace.dual V) W) =
        HSpace.tprodOfLists (HSpace.dual V) W
          (V.dualOfList vs) ws := by
    rw [denotBasis, denotBasis]
    simp only [Basis.sof, denotSpace, denotSpaceAux, V, W, vs, ws]
    rw [BasisDenot.atSpace_vecs_self, BasisDenot.atSpace_vecs_self]
  let coeff (i j : Nat) : ℝ :=
    if hi : i < N then (columns ⟨i, hi⟩).get j else 0
  have hrows : ∀ i, i < vs.length →
      phi (vs.getD i 0) = ∑ j ∈ Finset.range ws.length,
        coeff i j • ws.getD j 0 := by
    intro i hi
    have hiN : i < N := by rw [← hvsLen]; exact hi
    rw [hphi]
    have hc := hcolumnsSource ⟨i, hiN⟩
    rw [Fin.sum_univ_eq_sum_range
      (fun j => (columns ⟨i, hiN⟩).get j • ws.getD j 0)] at hc
    rw [hwsLen]
    simpa only [sourceAt, V, vs, W, ws, M, coeff,
      dif_pos hiN] using hc
  have hsourceExpansion := raw_llam_linearMap_tensor_coeff_sum
    V W vs ws hBdom phi coeff hrows
  refine ⟨?_, targetDims⟩
  refine ⟨.array out, ?_, ?_⟩
  · simpa only [summand] using hout
  · simp only [Basis.tof]
    have hdTotal : (ValSpace.tprod sv' sv).dofPartial (PartialDirectOracle.oracle rho [] []) =
        .ok (ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) (.tprod sv' sv)) := by
      rw [ValSpace.dof_tprod]
      exact dof_tprod_ok hdimN hdimM
    rw [agree_space_iff hdTotal]
    refine ⟨?_, ?_, ?_⟩
    · change ((denotBasis sigma (.tprod (.dual b') b)).atSpace
          (HSpace.tprod (HSpace.dual V) W)).length =
        ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) (.tprod sv' sv)
      rw [hbasisTensor, HSpace.tprodOfLists_length,
        HSpace.dualOfList_length, hlenDom, hlenCod,
        ValSpace.dof_tprod]
    · simp only [out, FlatArray.length_ofFn, ValSpace.dof_tprod, N, M]
    · change (denotTerm sigma
          (.llam (Basis.sof b') (Basis.sof b) e)).atSpace
            (HSpace.tprod (HSpace.dual V) W) =
        ∑ k : Fin (ValSpace.dof (numbers (PartialDirectOracle.oracle rho [] [])) (.tprod sv' sv)),
          out.get k.val •
            ((denotBasis sigma (.tprod (.dual b') b)).atSpace
              (HSpace.tprod (HSpace.dual V) W)).getD k.val 0
      rw [hsource, hbasisTensor, hsourceExpansion,
        Fin.sum_univ_eq_sum_range (fun k => out.get k •
          (HSpace.tprodOfLists (HSpace.dual V) W
            (V.dualOfList vs) ws).getD k 0)]
      apply Finset.sum_congr
      · rw [HSpace.tprodOfLists_length, HSpace.dualOfList_length,
          hlenDom, hlenCod, ValSpace.dof_tprod]
      · intro k hk
        congr 1
        have hkNM : k < N * M := by
          simpa only [ValSpace.dof_tprod, N, M] using
            Finset.mem_range.mp hk
        have hMpos : 0 < M := by
          by_contra hz
          have hMzero : M = 0 := Nat.eq_zero_of_not_pos hz
          simp [hMzero] at hkNM
        have hiN : k / M < N :=
          (Nat.div_lt_iff_lt_mul hMpos).2 hkNM
        let i : Fin N := ⟨k / M, hiN⟩
        rw [show out.get k = ∑ q : Fin N, (row q).get k by
          simp only [out, FlatArray.get_ofFn_lt _ _ _ hkNM]]
        rw [Finset.sum_eq_single i]
        · simp only [row, FlatArray.get_ofFn_lt _ _ _ hkNM,
            deltaRow]
          rw [FlatArray.get_ofFn_lt _ _ _ hiN]
          rw [hwsLen]
          simp [i, coeff, hiN]
        · intro q hq hqi
          have hneq : k / M ≠ q.val := fun heq =>
            hqi (Fin.ext heq.symm)
          simp only [row, FlatArray.get_ofFn_lt _ _ _ hkNM,
            deltaRow, FlatArray.get_ofFn_lt _ _ _ hiN,
            if_neg hneq, zero_mul]
        · exact fun hmem => absurd (Finset.mem_univ i) hmem

end GLang.PartialAdequacy
