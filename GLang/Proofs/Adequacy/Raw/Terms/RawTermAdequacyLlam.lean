import GLang.Proofs.Value.Soundness.ValueSumAtSemantics
import GLang.Proofs.Adequacy.Raw.RawLlamInfrastructure
import GLang.Proofs.Adequacy.Raw.RawLlamSource
import GLang.Proofs.Adequacy.Raw.RawSpaceFFSAdequacy
import Mathlib.Data.Fin.Tuple.Take

/-!
# Raw linear-lambda assembly

The strengthened assembly rules compile a linear lambda by evaluating its
body at every concrete basis coordinate and summing the resulting columns.
This module proves the two ordinary exact-basis trace arms directly over the
raw telescope.
-/

namespace GLang

open scoped BigOperators TensorProduct
open Basis (BasisValid)

private theorem raw_llam_rawAgree_space_array
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {s : GLang.Space} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : RawAgree orc sigma rho Ds Gv Dv
      (.space s) (.space sv) B x y) : exists a, y = .array a := by
  cases y with
  | array a => exact ⟨a, rfl⟩
  | fn T f => simpa only [RawAgree] using h

/-- A child compiled at a space value type cannot be observed through a
source frame basis.  Consequently its successful raw agreement both exposes
the source basis as an ordinary space basis and exposes an array result. -/
private theorem raw_llam_rawAgree_basis_space_array
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {b : Basis} {sv : ValSpace} {B : BasisDenot}
    {x : DVal} {y : ValValSem}
    (h : RawAgree orc sigma rho Ds Gv Dv
      (Basis.tof b) (.space sv) B x y) :
    Basis.tof b = .space (Basis.sof b) ∧ exists a, y = .array a := by
  cases b <;> cases y <;>
    simp only [Basis.tof, RawAgree, reduceCtorEq] at h ⊢ <;>
    first | contradiction | exact ⟨True.intro, ⟨_, rfl⟩⟩

private theorem raw_llam_fin_sum_of_eq_one
    {M : Type} [AddCommMonoid M] (h : n = 1) (f : Fin n → M) :
    (∑ i, f i) = f ⟨0, h.symm ▸ Nat.zero_lt_one⟩ := by
  subst n
  simp

private theorem raw_llam_agree_one_real
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {x : DVal} {a : FlatArray}
    (h : LegacyAgree orc sigma rho [] [] [] (.space .real) (.space .real)
      (denotBasis sigma .one) x (.array a)) :
    x.atSpace HSpace.real = a.get 0 := by
  have hc := LegacyAgree.coords h
  simp only [denotSpaceAux] at hc
  rw [raw_llam_fin_sum_of_eq_one (ValSpace.dof_real _)] at hc
  simp only [denotBasis, BasisDenot.atSpace_vecs_self] at hc
  simp at hc
  rw [hc]
  simpa only [smul_eq_mul] using (mul_one (a.get 0 : ℝ))

private theorem raw_llam_sequenceArrays_ok
    (as : List FlatArray) :
    ValValSem.sequenceArrays (as.map (fun a =>
      (Except.ok (.array a) : Except DimError ValValSem))) = .ok as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, ValValSem.sequenceArrays, ih]

private theorem raw_llam_vsum_infer_dof
    {orc : FFSOracleSem} {rho : ValEnvSem} {sv : ValSpace}
    {n : Nat} (hn : ValSpace.dof (orc rho [] []) sv ≤ n)
    (summand : Fin n → ValExpr)
    (hinfer : forall i, ValExpr.inferSpaceCtx [] (summand i) = sv) :
    ValSpace.dof (orc rho [] [])
        (ValExpr.inferSpaceCtx [] (.vsum sv (List.ofFn summand))) =
      ValSpace.dof (orc rho [] []) sv := by
  cases n with
  | zero =>
      have hz : ValSpace.dof (orc rho [] []) sv = 0 := Nat.eq_zero_of_le_zero hn
      simpa only [List.ofFn_zero, ValExpr.inferSpaceCtx, ValExpr.inferSpace,
        ValSpace.dof_empty] using hz.symm
  | succ n =>
      simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, List.ofFn_succ,
        hinfer]

private theorem raw_llam_vsum_ok
    {orc : FFSOracleSem} {rho : ValEnvSem} {sv : ValSpace}
    {n : Nat} (hn : ValSpace.dof (orc rho [] []) sv ≤ n)
    (summand : Fin n → ValExpr)
    (rows : Fin (ValSpace.dof (orc rho [] []) sv) → FlatArray)
    (heval : forall i,
      denotValB_semS orc rho [] [] (summand (Fin.castLE hn i)) =
        .ok (.array (rows i)))
    (hinfer : forall i, ValExpr.inferSpaceCtx [] (summand i) = sv)
    (hrows : ∀ i, (rows i).length = ValSpace.dof (orc rho [] []) sv) :
    denotValB_semS orc rho [] []
        (.vsum sv (List.ofFn summand)) =
      .ok (.array (FlatArray.ofFn (ValSpace.dof (orc rho [] []) sv)
        (fun j => ∑ i : Fin (ValSpace.dof (orc rho [] []) sv),
          (rows i).get j))) := by
  rw [denotValB_semS.eq_16]
  simp only [List.length_ofFn, if_pos hn]
  rw [← Fin.ofFn_take_eq_take_ofFn hn]
  simp only [List.attach_map_val, List.map_ofFn, Fin.take_apply,
    Function.comp_apply]
  rw [show
      List.ofFn (denotValB_semS orc rho [] [] ∘
        Fin.take (ValSpace.dof (orc rho [] []) sv) hn summand) =
          List.ofFn (fun i =>
            (Except.ok (.array (rows i)) : Except DimError ValValSem)) by
        apply congrArg List.ofFn
        funext i
        exact heval i]
  have hseq : ValValSem.sequenceArrays
      (List.ofFn fun i =>
        (Except.ok (.array (rows i)) : Except DimError ValValSem)) =
      .ok (List.ofFn rows) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      raw_llam_sequenceArrays_ok (List.ofFn rows)
  rw [hseq]
  simp only
  have hfamily : ValueShape.family (ValSpace.dof (orc rho [] []) sv)
      (ValSpace.dof (orc rho [] []) (ValExpr.inferSpaceCtx [] (.vsum sv (List.ofFn summand))))
      (List.ofFn rows) := by
    constructor
    · simp
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact (hrows i).trans (raw_llam_vsum_infer_dof hn summand hinfer).symm
  rw [if_pos hfamily]
  congr 2
  · exact raw_llam_vsum_infer_dof hn summand hinfer
  · funext j
    let f : Nat → ℝ := fun i => match (List.ofFn rows)[i]? with
      | some a => a.get j
      | none => 0
    calc
      (∑ i ∈ Finset.range (ValSpace.dof (orc rho [] []) sv),
          match (List.ofFn rows)[i]? with
          | some a => a.get j
          | none => 0) =
          ∑ i : Fin (ValSpace.dof (orc rho [] []) sv), f i.val := by
            exact (Fin.sum_univ_eq_sum_range f _).symm
      _ = ∑ i : Fin (ValSpace.dof (orc rho [] []) sv),
          (rows i).get j := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [f, List.getElem?_ofFn, i.isLt, ↓reduceDIte]

/-- The same finite-family evaluator when the index space and result space
are different.  The caller supplies the (constructor-specific) inferred
result dimension; this is the form used by tensor-codomain assembly. -/
private theorem raw_llam_vsum_rows_ok
    {orc : FFSOracleSem} {rho : ValEnvSem} {sIndex : ValSpace}
    {n outN : Nat} (hn : ValSpace.dof (orc rho [] []) sIndex ≤ n)
    (summand : Fin n → ValExpr)
    (rows : Fin (ValSpace.dof (orc rho [] []) sIndex) → FlatArray)
    (heval : forall i,
      denotValB_semS orc rho [] [] (summand (Fin.castLE hn i)) =
        .ok (.array (rows i)))
    (hinfer : ValSpace.dof (orc rho [] [])
        (ValExpr.inferSpaceCtx [] (.vsum sIndex (List.ofFn summand))) = outN)
    (hrows : ∀ i, (rows i).length = outN) :
    denotValB_semS orc rho [] []
        (.vsum sIndex (List.ofFn summand)) =
      .ok (.array (FlatArray.ofFn outN
        (fun j => ∑ i : Fin (ValSpace.dof (orc rho [] []) sIndex),
          (rows i).get j))) := by
  rw [denotValB_semS.eq_16]
  simp only [List.length_ofFn, if_pos hn]
  rw [← Fin.ofFn_take_eq_take_ofFn hn]
  simp only [List.attach_map_val, List.map_ofFn, Fin.take_apply,
    Function.comp_apply]
  rw [show
      List.ofFn (denotValB_semS orc rho [] [] ∘
        Fin.take (ValSpace.dof (orc rho [] []) sIndex) hn summand) =
          List.ofFn (fun i =>
            (Except.ok (.array (rows i)) : Except DimError ValValSem)) by
        apply congrArg List.ofFn
        funext i
        exact heval i]
  have hseq : ValValSem.sequenceArrays
      (List.ofFn fun i =>
        (Except.ok (.array (rows i)) : Except DimError ValValSem)) =
      .ok (List.ofFn rows) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      raw_llam_sequenceArrays_ok (List.ofFn rows)
  rw [hseq]
  simp only
  rw [hinfer]
  have hfamily : ValueShape.family (ValSpace.dof (orc rho [] []) sIndex) outN
      (List.ofFn rows) := by
    constructor
    · simp
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hrows i
  rw [if_pos hfamily]
  congr 2
  funext j
  let f : Nat → ℝ := fun i => match (List.ofFn rows)[i]? with
    | some a => a.get j
    | none => 0
  calc
    (∑ i ∈ Finset.range (ValSpace.dof (orc rho [] []) sIndex),
        match (List.ofFn rows)[i]? with
        | some a => a.get j
        | none => 0) =
        ∑ i : Fin (ValSpace.dof (orc rho [] []) sIndex), f i.val := by
          exact (Fin.sum_univ_eq_sum_range f _).symm
    _ = ∑ i : Fin (ValSpace.dof (orc rho [] []) sIndex),
        (rows i).get j := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [f, List.getElem?_ofFn, i.isLt, ↓reduceDIte]

/-- A real-valued linear functional is determined by its values on a finite
list basis, expressed in the corresponding dual list basis. -/
private theorem raw_llam_linearFunctional_dual_sum
    (V : HSpace) (vs : List V.carrier) {N : Nat}
    (hlen : vs.length = N) (hvs : IsListBasis V vs)
    (phi : V.carrier →ₗ[ℝ] ℝ) (coeff : Fin N → ℝ)
    (hcol : forall i : Fin N, phi (vs.getD i.val 0) = coeff i) :
    phi = ∑ i : Fin N, coeff i • (V.dualOfList vs).getD i.val 0 := by
  subst N
  apply LinearMap.ext
  intro x
  change phi x = _
  calc
    phi x = ∑ i : Fin vs.length,
        (V.dualVec vs i x) • phi (vs.get i) :=
      hvs.map_eq_sum_dual_smul (W := HSpace.real) phi x
    _ = _ := by
      rw [LinearMap.sum_apply]
      apply Fintype.sum_congr
      intro i
      have hiDual : i.val < (V.dualOfList vs).length := by
        rw [HSpace.dualOfList_length]
        exact i.isLt
      have hdual : (V.dualOfList vs).getD i.val 0 =
          V.dualVec vs i := by
        rw [List.getD_eq_getElem _ _ hiDual]
        refine (List.get_of_eq
          (HSpace.dualOfList_eq_finRange_map V vs) ⟨i.val, hiDual⟩).trans ?_
        simp
      have hc : phi (vs.get i) = coeff i := by
        simpa [List.getD_eq_getElem vs 0 i.isLt] using hcol i
      rw [hdual, LinearMap.smul_apply, hc]
      change (V.dualVec vs i x) * coeff i =
        coeff i * V.dualVec vs i x
      exact mul_comm _ _

private theorem raw_llam_sum_range_mul_div_mod
    {A : Type} [AddCommMonoid A]
    (m n : Nat) (g : Nat → Nat → A) :
    (∑ k ∈ Finset.range (m * n), g (k / n) (k % n)) =
      ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, g i j := by
  rw [← Fin.sum_univ_eq_sum_range, ← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro i
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro j
  have hnpos : 0 < n := Nat.zero_lt_of_lt j.isLt
  change g ((j.val + n * i.val) / n) ((j.val + n * i.val) % n) =
    g i.val j.val
  rw [Nat.add_mul_div_left _ _ hnpos, Nat.div_eq_of_lt j.isLt,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  simp

/-- Row-major coefficient form of the tensor that encodes a linear map. -/
private theorem raw_llam_linearMap_tensor_coeff_sum (V W : HSpace)
    (vs : List V.carrier) (ws : List W.carrier)
    (hvs : IsListBasis V vs) (f : V.carrier →ₗ[ℝ] W.carrier)
    (a : Nat → Nat → ℝ)
    (hrow : ∀ i < vs.length,
      f (vs.getD i 0) = ∑ j ∈ Finset.range ws.length,
        a i j • ws.getD j 0) :
    (dualTensorHomEquiv ℝ V.carrier W.carrier).symm f =
      ∑ k ∈ Finset.range
          (HSpace.tprodOfLists (HSpace.dual V) W
            (V.dualOfList vs) ws).length,
        a (k / ws.length) (k % ws.length) •
          (HSpace.tprodOfLists (HSpace.dual V) W
            (V.dualOfList vs) ws).getD k 0 := by
  rw [hvs.dualTensorHomEquiv_symm_eq_sum₂ (ws := ws) f
    (fun i j => a i.val j.val) (fun i => by
      have hc := hrow i.val i.isLt
      rw [← Fin.sum_univ_eq_sum_range] at hc
      simpa [List.getD_eq_getElem vs 0 i.isLt,
        List.getD_eq_getElem ws 0] using hc)]
  calc
    (∑ i : Fin vs.length, ∑ j : Fin ws.length,
        a i.val j.val • (V.dualVec vs i ⊗ₜ[ℝ] ws.get j)) =
        ∑ i ∈ Finset.range vs.length, ∑ j ∈ Finset.range ws.length,
          a i j • ((V.dualOfList vs).getD i 0 ⊗ₜ[ℝ] ws.getD j 0) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Fintype.sum_congr
      intro i
      rw [← Fin.sum_univ_eq_sum_range]
      apply Fintype.sum_congr
      intro j
      rw [RawSpaceFFS.dualOfList_getD_eq_dualVec V vs i.isLt,
        List.getD_eq_getElem ws 0 j.isLt]
      congr
    _ = ∑ k ∈ Finset.range (vs.length * ws.length),
        a (k / ws.length) (k % ws.length) •
          ((V.dualOfList vs).getD (k / ws.length) 0 ⊗ₜ[ℝ]
            ws.getD (k % ws.length) 0) := by
      exact (raw_llam_sum_range_mul_div_mod vs.length ws.length
        (fun i j => a i j •
          ((V.dualOfList vs).getD i 0 ⊗ₜ[ℝ] ws.getD j 0))).symm
    _ = ∑ k ∈ Finset.range
          (HSpace.tprodOfLists (HSpace.dual V) W
            (V.dualOfList vs) ws).length,
        a (k / ws.length) (k % ws.length) •
          (HSpace.tprodOfLists (HSpace.dual V) W
            (V.dualOfList vs) ws).getD k 0 := by
      rw [HSpace.tprodOfLists_length, HSpace.dualOfList_length]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k < vs.length * ws.length := Finset.mem_range.mp hk
      have hw : ws.length ≠ 0 := by
        intro hz
        simp [hz] at hk'
      rw [RawSpaceFFS.tprodOfLists_getD _ _ _ _ k
        (by rw [HSpace.dualOfList_length]; exact hk')
        (Nat.pos_of_ne_zero hw)]

/-! ## Real codomain -/

theorem arm_llam_assemble_real
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
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
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.dual b') (.space sv'))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b') sv')
    (ihfam : forall y, y ∉ L → forall i : Fin (ValSpace.dofUB sv'),
      RawTermDofFactsSubctx orc
        (Finmap.insert y (Basis.sof b') Delta) Gamma
        (Psi.extend y b' (.delta i.val sv'))
        (Term.openVar y e) .one (env i) (.space .real)) :
    RawMTermTraceSubctx orc Delta Gamma Psi
      (.llam (Basis.sof b') .real e) (.dual b')
      (ValExpr.sumAt sv' (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
          .scale (ValExpr.reshapBase (env i) .real)
            (.delta i.val sv')) sv') (.space sv') := by
  intro Psi' hsub hctx rho Delta' Gamma' sigma GammaV hle hc
  have targetDims :=
    ihTy hsub rho Delta' Gamma' sigma GammaV hle.2 hc
  have hbdom : BasisValid Gamma b' := hbv.dual_inv
  obtain ⟨hB, hlen⟩ :=
    raw_cob_basis_length orc hbdom ihSpace hsub hle.2 hc
  have hNle : ValSpace.dof (orc rho [] []) sv' ≤ ValSpace.dofUB sv' :=
    ValSpace.dof_le_dofUB hspec.toOracleSpec rho [] [] sv'
  obtain ⟨Delta1, hDelta1, hsourceTyping⟩ :=
    raw_hasType_ctxIncl hc.raw.ctxWF_raw ht hctx hle
  have hlinear := denot_llam_real_body_isLinear hsourceTyping.some
    (hc.raw.ctxWF_raw.of_sub_Δ hDelta1) (hc.raw.envWF_raw.of_sub_Δ hDelta1)
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
  let N := ValSpace.dof (orc rho [] []) sv'
  let V := denotSpace sigma (Basis.sof b')
  let vs := (denotBasis sigma b').atSpace V
  let ruleIndex : Fin N → Fin (ValSpace.dofUB sv') :=
    ValSpace.rawFinOfDofUB
      hspec.toOracleSpec rho
  let sourceAt (i : Fin N) : DVal :=
    .hil ⟨V, vs.getD i.val 0⟩
  have hcol (i : Fin N) : exists a : FlatArray,
      denotValB_semS orc rho [] [] (env (ruleIndex i)) =
          .ok (.array a) ∧
      a.length = 1 ∧
      (denotTermAux sigma [sourceAt i] e).atSpace HSpace.real = a.get 0 := by
    have hdimsSpace : RawAgreeDimsAt orc sigma rho [] [] []
        (Basis.tof b') (.space sv') (denotBasis sigma b') := by
      rw [htof']
      simp only [RawAgreeDimsAt]
      exact ihSpace hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    obtain ⟨yv, hdelta, hcExt⟩ := hc.extend_binder_lin_delta
      ⟨hyDelta, hyGamma, hyEval⟩ hle.2 htof' hbdom
      (show Basis.IsTyBasis b' from
        (show Basis.IsSpaceBasis b' from _hTy.isTyBasis).toIsTyBasis)
      (_hsv'.mono hsub) i hdimsSpace
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
        simpa only [ruleIndex, ValSpace.rawFinOfDofUB, sourceAt, V, vs]
          using hcExt)
    obtain ⟨out, hout, hagree⟩ := child.result
    obtain ⟨a, rfl⟩ := raw_llam_rawAgree_space_array hagree
    have hsrc : denotTerm (sigma.bind y (sourceAt i))
        (Term.openVar y e) = denotTermAux sigma [sourceAt i] e :=
      denotTerm_openVar_bind (hfam y hyL (ruleIndex i)).hasType.some.lc hyE
    rw [hsrc] at hagree
    have hagree' : LegacyAgree orc (sigma.bind y (sourceAt i))
        (rho.update y yv) [] [] [] (.space .real) (.space .real)
        (denotBasis (sigma.bind y (sourceAt i)) .one)
        (denotTermAux sigma [sourceAt i] e) (.array a) := by
      simpa only [Basis.tof, Basis.sof, RawAgree] using hagree
    have hscalar := raw_llam_agree_one_real hagree'
    have haLen := (LegacyAgree.length hagree').2
    have houtRoot : denotValB_semS orc rho [] [] (env (ruleIndex i)) =
        .ok (.array a) := by
      rw [← denotValB_semS_update_of_not_mem_fv
        hspec.toOracleSpec.fvIrrel rho y yv
        (env (ruleIndex i)) [] []
        (fun hm => hyPsi (hfvenv (ruleIndex i) hm)) (by simp)]
      exact hout
    refine ⟨a, houtRoot, ?_, hscalar⟩
    simpa only [ValSpace.dof_real] using haLen
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
      denotValB_semS orc rho [] []
          (summand (Fin.castLE hNle i)) = .ok (.array (row i)) := by
    have hreshape := denotValB_semS_reshap_space_ok orc rho [] []
      (env (ruleIndex i)) .real (columns i)
      (hcolumnsDen i) (by
        simpa only [ValSpace.dof_real] using hcolumnsLen i)
    have hcast : Fin.castLE hNle i = ruleIndex i := by
      apply Fin.ext
      rfl
    rw [hcast]
    simp only [summand, ValExpr.reshapBase]
    rw [denotValB_semS.eq_5, hreshape, denotValB_semS.eq_7]
    simp only [ValValSem.bindArrays, ValValSem.bindArray,
      ValValSem.arrayOf]
    rw [if_pos (by
      simp only [ValueShape.scale, ValExpr.inferSpaceCtx, FlatArray.length_ofFn,
        hcolumnsLen i, and_self])]
    congr 2
    apply FlatArray.ofFn_congr
    · rfl
    · intro j
      simp only [ruleIndex, ValSpace.rawFinOfDofUB,
        ValExpr.inferSpaceCtx]
      by_cases hjN : j < N
      · rw [FlatArray.get_ofFn_lt _ _ _ hjN]
        by_cases hji : j = i.val
        · simp [hji, i.isLt, row]
        · simp [hji, row]
      · rw [FlatArray.get_ofFn_ge _ _ _ (Nat.not_lt.mp hjN)]
        have hji : j ≠ i.val := fun h => hjN (h ▸ i.isLt)
        simp [hji, row]
  have hvsum := raw_llam_vsum_ok hNle summand row hsummand
    hsummandInfer (fun _ => rfl)
  let out : FlatArray := FlatArray.ofFn N
    (fun j => ∑ i : Fin N, (row i).get j)
  have hvsum' : denotValB_semS orc rho [] []
      (.vsum sv' (List.ofFn summand)) = .ok (.array out) := by
    simpa only [out, N] using hvsum
  have hout : denotValB_semS orc rho [] []
      (ValExpr.sumAt sv' (List.ofFn summand) sv') =
        .ok (.array out) := by
    rw [denotValB_semS_sumAt]
    exact denotValB_semS_reshap_space_ok orc rho [] []
      (.vsum sv' (List.ofFn summand)) sv' out hvsum'
      (by simp only [out, FlatArray.length_ofFn, N])
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
  · simp only [Basis.tof, Basis.sof, RawAgree]
    rw [LegacyAgree.space_iff]
    refine ⟨?_, ?_, ?_⟩
    · change ((denotBasis sigma (.dual b')).atSpace
          (HSpace.dual V)).length = ValSpace.dof (orc rho [] []) sv'
      rw [hbasisDual, HSpace.dualOfList_length, hlen]
    · simp only [out, FlatArray.length_ofFn, N]
    · change (denotTerm sigma (.llam (Basis.sof b') .real e)).atSpace
          (HSpace.dual V) =
        ∑ i : Fin (ValSpace.dof (orc rho [] []) sv'),
          out.get i.val •
            ((denotBasis sigma (.dual b')).atSpace
              (HSpace.dual V)).getD i.val 0
      rw [hsource, hbasisDual, hphiColumns]
      apply Finset.sum_congr rfl
      intro i hi
      rw [houtCoord]

/-! ## Tensor codomain -/

theorem arm_llam_assemble
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
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
    (ihTy : RawMTyAtSubctx orc Gamma Psi (.tprod (.dual b') b)
      (.space (.tprod sv' sv)))
    (ihSpaceDom : RawMSpaceSubctx orc Gamma Psi (Basis.sof b') sv')
    (ihSpaceCod : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) sv)
    (ihfam : forall y, y ∉ L → forall i : Fin (ValSpace.dofUB sv'),
      RawTermDofFactsSubctx orc
        (Finmap.insert y (Basis.sof b') Delta) Gamma
        (Psi.extend y b' (.delta i.val sv'))
        (Term.openVar y e) b (env i) (.space sv)) :
    RawMTermTraceSubctx orc Delta Gamma Psi
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
  obtain ⟨hBdom, hlenDom⟩ :=
    raw_cob_basis_length orc hbdom ihSpaceDom hsub hle.2 hc
  obtain ⟨hBcod, hlenCod⟩ :=
    raw_cob_basis_length orc hbcod ihSpaceCod hsub hle.2 hc
  have hNle : ValSpace.dof (orc rho [] []) sv' ≤ ValSpace.dofUB sv' :=
    ValSpace.dof_le_dofUB hspec.toOracleSpec rho [] [] sv'
  obtain ⟨Delta1, hDelta1, hsourceTyping⟩ :=
    raw_hasType_ctxIncl hc.raw.ctxWF_raw ht hctx hle
  have hlinear := denot_llam_tensor_body_isLinear hsourceTyping.some
    (hc.raw.ctxWF_raw.of_sub_Δ hDelta1) (hc.raw.envWF_raw.of_sub_Δ hDelta1)
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
  let N := ValSpace.dof (orc rho [] []) sv'
  let M := ValSpace.dof (orc rho [] []) sv
  let V := denotSpace sigma (Basis.sof b')
  let W := denotSpace sigma (Basis.sof b)
  let vs := (denotBasis sigma b').atSpace V
  let ws := (denotBasis sigma b).atSpace W
  have hvsLen : vs.length = N := by
    simpa only [vs, V, N] using hlenDom
  have hwsLen : ws.length = M := by
    simpa only [ws, W, M] using hlenCod
  let ruleIndex : Fin N → Fin (ValSpace.dofUB sv') :=
    ValSpace.rawFinOfDofUB
      hspec.toOracleSpec rho
  let sourceAt (i : Fin N) : DVal :=
    .hil ⟨V, vs.getD i.val 0⟩
  have hcol (i : Fin N) : exists a : FlatArray,
      denotValB_semS orc rho [] [] (env (ruleIndex i)) =
          .ok (.array a) ∧
      a.length = M ∧
      (denotTermAux sigma [sourceAt i] e).atSpace W =
        ∑ j : Fin M, a.get j.val • ws.getD j.val 0 := by
    have hdimsSpace : RawAgreeDimsAt orc sigma rho [] [] []
        (Basis.tof b') (.space sv') (denotBasis sigma b') := by
      rw [htof']
      simp only [RawAgreeDimsAt]
      exact ihSpaceDom hsub rho Delta' Gamma' sigma GammaV hle.2 hc
    obtain ⟨yv, hdelta, hcExt⟩ := hc.extend_binder_lin_delta
      ⟨hyDelta, hyGamma, hyEval⟩ hle.2 htof' hbdom
      (show Basis.IsTyBasis b' from
        (show Basis.IsSpaceBasis b' from _hTy.isTyBasis.1).toIsTyBasis)
      (_hsv'.mono hsub) i hdimsSpace
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
        simpa only [ruleIndex, ValSpace.rawFinOfDofUB, sourceAt, V, vs]
          using hcExt)
    obtain ⟨out, hout, hagree⟩ := child.result
    obtain ⟨htofb, a, rfl⟩ := raw_llam_rawAgree_basis_space_array hagree
    rw [htofb] at hagree
    have hsrc : denotTerm (sigma.bind y (sourceAt i))
        (Term.openVar y e) = denotTermAux sigma [sourceAt i] e :=
      denotTerm_openVar_bind (hfam y hyL (ruleIndex i)).hasType.some.lc hyE
    rw [hsrc] at hagree
    have hagree' : LegacyAgree orc (sigma.bind y (sourceAt i))
        (rho.update y yv) [] [] [] (.space (Basis.sof b)) (.space sv)
        (denotBasis (sigma.bind y (sourceAt i)) b)
        (denotTermAux sigma [sourceAt i] e) (.array a) := by
      simpa only [RawAgree] using hagree
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
    have hcoords := LegacyAgree.coords hagree'
    have haLen := (LegacyAgree.length hagree').2
    rw [hWbindAux, hBbind,
      ValSpace.dof_update_of_not_mem_fv
        hspec.toOracleSpec.fvIrrel rho y yv [] []
        (by simp [ValTyCtxFresh]) sv hySv]
      at hcoords
    rw [ValSpace.dof_update_of_not_mem_fv
      hspec.toOracleSpec.fvIrrel rho y yv [] []
      (by simp [ValTyCtxFresh]) sv hySv]
      at haLen
    have houtRoot : denotValB_semS orc rho [] [] (env (ruleIndex i)) =
        .ok (.array a) := by
      rw [← denotValB_semS_update_of_not_mem_fv
        hspec.toOracleSpec.fvIrrel rho y yv
        (env (ruleIndex i)) [] []
        (fun hm => hyPsi (hfvenv (ruleIndex i) hm)) (by simp)]
      exact hout
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
      denotValB_semS orc rho [] []
          (summand (Fin.castLE hNle i)) = .ok (.array (row i)) := by
    have hreshape := denotValB_semS_reshap_space_ok orc rho [] []
      (env (ruleIndex i)) sv (columns i)
      (hcolumnsDen i) (by simpa only [M] using hcolumnsLen i)
    have hcast : Fin.castLE hNle i = ruleIndex i := by
      apply Fin.ext
      rfl
    rw [hcast]
    simp only [summand, ValExpr.reshapBase]
    rw [denotValB_semS.eq_9, denotValB_semS.eq_7, hreshape]
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
      simp only [ruleIndex, ValSpace.rawFinOfDofUB,
        ValExpr.inferSpaceCtx, N, M]
      congr 1
      simp only [deltaRow]
      rw [FlatArray.get_ofFn]
      by_cases hkN : k / ValSpace.dof (orc rho [] []) sv <
          ValSpace.dof (orc rho [] []) sv'
      · simp [N, hkN, i.isLt]
      · simp [N, hkN]
  have hvsumInfer : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.vsum sv' (List.ofFn summand))) = N * M := by
    cases hlist : List.ofFn summand with
    | nil =>
        have hUBzero : ValSpace.dofUB sv' = 0 := by
          have hlen := congrArg List.length hlist
          simpa using hlen
        have hNzero : N = 0 := Nat.eq_zero_of_le_zero (by
          simpa only [hUBzero] using hNle)
        simp only [hlist, ValExpr.inferSpaceCtx, ValExpr.inferSpace,
          ValSpace.dof_empty, hNzero, zero_mul]
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
        simp only [hlist, ValExpr.inferSpaceCtx, ha, hsummandInfer,
          ValSpace.dof_tprod, N, M]
  have hvsum := raw_llam_vsum_rows_ok hNle summand row hsummand
    hvsumInfer (fun _ => rfl)
  let out : FlatArray := FlatArray.ofFn (N * M)
    (fun k => ∑ i : Fin N, (row i).get k)
  have hvsum' : denotValB_semS orc rho [] []
      (.vsum sv' (List.ofFn summand)) = .ok (.array out) := by
    simpa only [out, N, M, ValSpace.dof_tprod] using hvsum
  have hout : denotValB_semS orc rho [] []
      (ValExpr.sumAt sv' (List.ofFn summand)
        (.tprod sv' sv)) = .ok (.array out) := by
    rw [denotValB_semS_sumAt]
    exact denotValB_semS_reshap_space_ok orc rho [] []
      (.vsum sv' (List.ofFn summand)) (.tprod sv' sv) out hvsum'
      (by simp only [out, FlatArray.length_ofFn, ValSpace.dof_tprod, N, M])
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
  · simp only [Basis.tof, RawAgree]
    rw [LegacyAgree.space_iff]
    refine ⟨?_, ?_, ?_⟩
    · change ((denotBasis sigma (.tprod (.dual b') b)).atSpace
          (HSpace.tprod (HSpace.dual V) W)).length =
        ValSpace.dof (orc rho [] []) (.tprod sv' sv)
      rw [hbasisTensor, HSpace.tprodOfLists_length,
        HSpace.dualOfList_length, hlenDom, hlenCod,
        ValSpace.dof_tprod]
    · simp only [out, FlatArray.length_ofFn, ValSpace.dof_tprod, N, M]
    · change (denotTerm sigma
          (.llam (Basis.sof b') (Basis.sof b) e)).atSpace
            (HSpace.tprod (HSpace.dual V) W) =
        ∑ k : Fin (ValSpace.dof (orc rho [] []) (.tprod sv' sv)),
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

end GLang
