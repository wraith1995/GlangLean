import GLang.Proofs.Adequacy.Raw.Conversion.RawCobAdequacyCore
import GLang.Proofs.Adequacy.Raw.RawSpaceFFSAdequacy
import GLang.Numerics.Pseudoinverse.MoorePenroseChar
import GLang.Proofs.Source.InnerProduct

/-!
# Projected change-of-basis arms for raw adequacy

The four projected COB constructors compile a subspace change of basis as a
rectangular sandwich: inclusion into an ambient basis, an optional ambient
change of basis, and the Moore--Penrose projection back to the subspace.
This module proves that sandwich directly over exact-basis raw traces.
-/

namespace GLang

open scoped BigOperators TensorProduct
open Basis (BasisValid)

theorem raw_proj_basisValid_components
    {Gamma : NLCtx} {s : Space} {b0 b1 : Basis}
    (h : BasisValid Gamma (.proj s b0 b1)) :
    BasisValid Gamma b0 ∧ BasisValid Gamma b1 := by
  cases h <;> constructor <;> assumption

/-! ## Moore--Penrose projection of a submodule inclusion -/

/-- The Moore--Penrose inverse of a submodule inclusion is a left inverse.
Only the existing image/projection characterization is needed. -/
theorem raw_mooreInv_subtype_left (V : HSpace)
    (K : Submodule ℝ V.carrier) (x : K) :
    LinearMap.mooreInv (HSpace.ofSubmodule V K).innerIsIP V.innerIsIP
        K.subtype (K.subtype x) = x := by
  letI core1 : InnerProductSpace.Core ℝ V.carrier :=
    V.innerIsIP.toIPSCore
  letI nag1 : NormedAddCommGroup V.carrier :=
    InnerProductSpace.Core.toNormedAddCommGroup (cd := core1)
  letI ips1 : InnerProductSpace ℝ V.carrier :=
    InnerProductSpace.ofCore inferInstance
  apply Subtype.ext
  change K.subtype
      (LinearMap.mooreInv (HSpace.ofSubmodule V K).innerIsIP V.innerIsIP
        K.subtype (K.subtype x)) = K.subtype x
  rw [LinearMap.mooreInv_image_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr
    (LinearMap.mem_range_self K.subtype x)

/-- The denotations of `lembd` and `lproj` compose to the identity for a
kernel or cokernel, using the ambient domain space. -/
theorem raw_lproj_lembd_ker_coker (sigma : DEnv)
    {s0 s1 : Space} {e : Term} {s : Space}
    (hs : s = .ker s0 s1 e ∨ s = .coker s0 s1 e)
    (x : (denotSpace sigma s).carrier) :
    (denotTerm sigma (Term.lproj s s0)).asLinMap
        (denotSpace sigma s0) (denotSpace sigma s)
        ((denotTerm sigma (Term.lembd s)).asLinMap
          (denotSpace sigma s) (denotSpace sigma s0) x) = x := by
  rcases hs with rfl | rfl
  · let V0 := denotSpace sigma s0
    let V1 := denotSpace sigma s1
    let f := (denotTerm sigma e).asLinMap V0 V1
    let K : Submodule ℝ V0.carrier := LinearMap.ker f
    change DVal.asLinMap V0 (HSpace.ofSubmodule V0 K)
        (pinvTensorDVal (HSpace.ofSubmodule V0 K) V0
          (embedDVal (HSpace.ofSubmodule V0 K) V0 K.subtype))
        (DVal.asLinMap (HSpace.ofSubmodule V0 K) V0
          (embedDVal (HSpace.ofSubmodule V0 K) V0 K.subtype) x) = x
    rw [asLinMap_pinvTensorDVal, asLinMap_embedDVal]
    exact raw_mooreInv_subtype_left V0 K x
  · let V0 := denotSpace sigma s0
    let V1 := denotSpace sigma s1
    let f := (denotTerm sigma e).asLinMap V0 V1
    let K : Submodule ℝ V0.carrier :=
      Submodule.orthRel V0.innerProduct (LinearMap.ker f)
    change DVal.asLinMap V0 (HSpace.ofSubmodule V0 K)
        (pinvTensorDVal (HSpace.ofSubmodule V0 K) V0
          (embedDVal (HSpace.ofSubmodule V0 K) V0 K.subtype))
        (DVal.asLinMap (HSpace.ofSubmodule V0 K) V0
          (embedDVal (HSpace.ofSubmodule V0 K) V0 K.subtype) x) = x
    rw [asLinMap_pinvTensorDVal, asLinMap_embedDVal]
    exact raw_mooreInv_subtype_left V0 K x

/-- The denotations of `lembd` and `lproj` compose to the identity for an
image or coimage, using the ambient codomain space. -/
theorem raw_lproj_lembd_img_coimg (sigma : DEnv)
    {s0 s1 : Space} {e : Term} {s : Space}
    (hs : s = .img s0 s1 e ∨ s = .coimg s0 s1 e)
    (x : (denotSpace sigma s).carrier) :
    (denotTerm sigma (Term.lproj s s1)).asLinMap
        (denotSpace sigma s1) (denotSpace sigma s)
        ((denotTerm sigma (Term.lembd s)).asLinMap
          (denotSpace sigma s) (denotSpace sigma s1) x) = x := by
  rcases hs with rfl | rfl
  · let V0 := denotSpace sigma s0
    let V1 := denotSpace sigma s1
    let f := (denotTerm sigma e).asLinMap V0 V1
    let K : Submodule ℝ V1.carrier := LinearMap.range f
    change DVal.asLinMap V1 (HSpace.ofSubmodule V1 K)
        (pinvTensorDVal (HSpace.ofSubmodule V1 K) V1
          (embedDVal (HSpace.ofSubmodule V1 K) V1 K.subtype))
        (DVal.asLinMap (HSpace.ofSubmodule V1 K) V1
          (embedDVal (HSpace.ofSubmodule V1 K) V1 K.subtype) x) = x
    rw [asLinMap_pinvTensorDVal, asLinMap_embedDVal]
    exact raw_mooreInv_subtype_left V1 K x
  · let V0 := denotSpace sigma s0
    let V1 := denotSpace sigma s1
    let f := (denotTerm sigma e).asLinMap V0 V1
    let K : Submodule ℝ V1.carrier :=
      Submodule.orthRel V1.innerProduct (LinearMap.range f)
    change DVal.asLinMap V1 (HSpace.ofSubmodule V1 K)
        (pinvTensorDVal (HSpace.ofSubmodule V1 K) V1
          (embedDVal (HSpace.ofSubmodule V1 K) V1 K.subtype))
        (DVal.asLinMap (HSpace.ofSubmodule V1 K) V1
          (embedDVal (HSpace.ofSubmodule V1 K) V1 K.subtype) x) = x
    rw [asLinMap_pinvTensorDVal, asLinMap_embedDVal]
    exact raw_mooreInv_subtype_left V1 K x

/-! ## Reading rectangular matrices from ordinary term traces -/

private theorem raw_proj_fin_sum_cast_of_eq
    {M : Type} [AddCommMonoid M] {n m : Nat}
    (h : n = m) (f : Fin n -> M) :
    (∑ i, f i) = ∑ i : Fin m, f (Fin.cast h.symm i) := by
  subst h
  rfl

private theorem raw_proj_fin_sum_eq_zero_of_length_zero
    {M : Type} [AddCommMonoid M] {n : Nat} (hn : n = 0)
    (f : Fin n -> M) : (∑ i, f i) = 0 := by
  subst n
  simp

/-- A trace at `b0* ⊗ b1` presents the denoted linear map row by row.
The array index `j * |b1| + i` is the coefficient of output basis vector
`i` in the image of input basis vector `j`. -/
theorem raw_trace_linear_map_rows
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {b0 b1 : Basis} {e : Term} {env : ValExpr}
    {sv0 sv1 : ValSpace}
    (hdom : IsListBasis (denotSpace sigma (Basis.sof b0))
      ((denotBasis sigma b0).atSpace
        (denotSpace sigma (Basis.sof b0))))
    (hcod : IsListBasis (denotSpace sigma (Basis.sof b1))
      ((denotBasis sigma b1).atSpace
        (denotSpace sigma (Basis.sof b1))))
    (htrace : RawTermTraceAt orc sigma rho env
      (Basis.tof (.tprod (.dual b0) b1))
      (.space (.tprod sv0 sv1))
      (denotBasis sigma (.tprod (.dual b0) b1))
      (denotTerm sigma e)) :
    exists a : FlatArray,
      denotValB_semS orc rho [] [] env = .ok (.array a) /\
      a.length =
        ((denotBasis sigma b0).atSpace
          (denotSpace sigma (Basis.sof b0))).length *
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1))).length /\
      forall j : Fin
          ((denotBasis sigma b0).atSpace
            (denotSpace sigma (Basis.sof b0))).length,
        (denotTerm sigma e).asLinMap
            (denotSpace sigma (Basis.sof b0))
            (denotSpace sigma (Basis.sof b1))
            (((denotBasis sigma b0).atSpace
              (denotSpace sigma (Basis.sof b0))).get j) =
          ∑ i : Fin
              ((denotBasis sigma b1).atSpace
                (denotSpace sigma (Basis.sof b1))).length,
            a.get (j.val *
                ((denotBasis sigma b1).atSpace
                  (denotSpace sigma (Basis.sof b1))).length + i.val) •
              ((denotBasis sigma b1).atSpace
                (denotSpace sigma (Basis.sof b1))).get i := by
  let V0 := denotSpace sigma (Basis.sof b0)
  let V1 := denotSpace sigma (Basis.sof b1)
  let S := (denotBasis sigma b0).atSpace V0
  let T := (denotBasis sigma b1).atSpace V1
  obtain ⟨a, heval, hbLen, haLen, hcoords⟩ :=
    RawSpaceFFS.trace_array_coords (b := .tprod (.dual b0) b1)
      (v := env) (svb := .tprod sv0 sv1) rfl htrace
  simp only [Basis.sof, denotSpaceAux] at hbLen hcoords
  have hN : ValSpace.dof (orc rho [] []) (.tprod sv0 sv1) =
      S.length * T.length := by
    rw [RawSpaceFFS.denotBasis_tprod_dual_atSpace,
      HSpace.tprodOfLists_length, HSpace.dualOfList_length] at hbLen
    exact hbLen.symm
  have haLen' : a.length = S.length * T.length := haLen.trans hN
  rw [hN, RawSpaceFFS.denotBasis_tprod_dual_atSpace] at hcoords
  refine ⟨a, heval, haLen', ?_⟩
  intro j
  change (denotTerm sigma e).asLinMap V0 V1 (S.get j) =
    ∑ i : Fin T.length, a.get (j.val * T.length + i.val) • T.get i
  by_cases hz : T.length = 0
  · have hzero :
        (denotTerm sigma e).asLinMap V0 V1 (S.get j) = 0 := by
      calc
        _ = ∑ i : Fin T.length,
              (V1.dualVec T i
                ((denotTerm sigma e).asLinMap V0 V1 (S.get j))) •
                T.get i := hcod.sum_dual_smul _
        _ = 0 := raw_proj_fin_sum_eq_zero_of_length_zero hz _
    rw [hzero]
    exact (raw_proj_fin_sum_eq_zero_of_length_zero hz _).symm
  · have hpos : 0 < T.length := Nat.pos_of_ne_zero hz
    rw [RawSpaceFFS.asLinMap_eq_dualTensorHom_atSpace, hcoords,
      map_sum, LinearMap.sum_apply,
      ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j]
    · apply Finset.sum_congr rfl
      intro i _
      have hk :
          ((finProdFinEquiv (j, i) : Fin (S.length * T.length)) : Nat) =
            i.val + T.length * j.val := rfl
      have hlt : i.val + T.length * j.val <
          (V0.dualOfList S).length * T.length := by
        rw [HSpace.dualOfList_length]
        exact (finProdFinEquiv (j, i)).isLt
      obtain ⟨hdiv, hmod⟩ :=
        RawSpaceFFS.rowMajor_div_mod (i := j.val) i.isLt
      rw [hk]
      change (dualTensorHom ℝ V0.carrier V1.carrier
          (a.get (i.val + T.length * j.val) •
            (HSpace.tprodOfLists (HSpace.dual V0) V1
              (V0.dualOfList S) T).getD
                (i.val + T.length * j.val) 0)) (S.get j) = _
      rw [map_smul, LinearMap.smul_apply,
        RawSpaceFFS.tprodOfLists_getD _ _ _ _ _ hlt hpos,
        hdiv, hmod,
        RawSpaceFFS.dualOfList_getD_eq_dualVec V0 S j.isLt,
        List.getD_eq_getElem T 0 i.isLt, dualTensorHom_apply,
        hdom.dual_delta j j, if_pos rfl, smul_smul, mul_one,
        Nat.add_comm]
      rw [Nat.mul_comm T.length j.val]
      rw [List.get_eq_getElem]
    · intro i _ hij
      apply Finset.sum_eq_zero
      intro k _
      have hk :
          ((finProdFinEquiv (i, k) : Fin (S.length * T.length)) : Nat) =
            k.val + T.length * i.val := rfl
      have hlt : k.val + T.length * i.val <
          (V0.dualOfList S).length * T.length := by
        rw [HSpace.dualOfList_length]
        exact (finProdFinEquiv (i, k)).isLt
      obtain ⟨hdiv, hmod⟩ :=
        RawSpaceFFS.rowMajor_div_mod (i := i.val) k.isLt
      rw [hk]
      change (dualTensorHom ℝ V0.carrier V1.carrier
          (a.get (k.val + T.length * i.val) •
            (HSpace.tprodOfLists (HSpace.dual V0) V1
              (V0.dualOfList S) T).getD
                (k.val + T.length * i.val) 0)) (S.get j) = 0
      rw [map_smul, LinearMap.smul_apply,
        RawSpaceFFS.tprodOfLists_getD _ _ _ _ _ hlt hpos,
        hdiv, hmod,
        RawSpaceFFS.dualOfList_getD_eq_dualVec V0 S i.isLt,
        List.getD_eq_getElem T 0 k.isLt, dualTensorHom_apply,
        hdom.dual_delta i j, if_neg hij]
      simp
    · exact fun hmem => absurd (Finset.mem_univ j) hmem

/-! ## Rectangular matrix composition -/

/-- Algebraic composition of two row-oriented rectangular coordinate
matrices. -/
theorem raw_rectangular_comp_list {V : HSpace}
    (source middle target : List V.carrier)
    (a a0 a1 : FlatArray)
    (hsum0 : forall j : Fin source.length,
      source.get j = ∑ i : Fin middle.length,
        a0.get (j.val * middle.length + i.val) • middle.get i)
    (hsum1 : forall j : Fin middle.length,
      middle.get j = ∑ i : Fin target.length,
        a1.get (j.val * target.length + i.val) • target.get i)
    (hget : forall j i, j < source.length -> i < target.length ->
      a.get (j * target.length + i) =
        ∑ k ∈ Finset.range middle.length,
          a1.get (k * target.length + i) *
            a0.get (j * middle.length + k)) :
    forall j : Fin source.length,
      source.get j = ∑ i : Fin target.length,
        a.get (j.val * target.length + i.val) • target.get i := by
  intro j
  have hr :
      (∑ i : Fin target.length,
        a.get (j.val * target.length + i.val) • target.get i) =
      ∑ i : Fin target.length,
        (∑ k ∈ Finset.range middle.length,
          a1.get (k * target.length + i.val) *
            a0.get (j.val * middle.length + k)) • target.get i :=
    Finset.sum_congr rfl (fun i _ => by rw [hget _ _ j.isLt i.isLt])
  rw [hr, hsum0 j]
  simp only [hsum1, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  rw [Fin.sum_univ_eq_sum_range
    (fun k =>
      (a0.get (j.val * middle.length + k) *
        a1.get (k * target.length + o.val)) • target.get o)
    middle.length]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (a0.get _) (a1.get _)]

/-- Indexed-family form of rectangular composition.  This avoids any
irrelevant transports through `List.map` when an ambient basis is mapped by a
linear projection. -/
theorem raw_rectangular_comp_family {V : Type} [AddCommGroup V]
    [Module ℝ V] {nSource nMiddle nTarget : Nat}
    (source : Fin nSource -> V) (middle : Fin nMiddle -> V)
    (target : Fin nTarget -> V) (a a0 a1 : FlatArray)
    (hsum0 : forall j,
      source j = ∑ i, a0.get (j.val * nMiddle + i.val) • middle i)
    (hsum1 : forall j,
      middle j = ∑ i, a1.get (j.val * nTarget + i.val) • target i)
    (hget : forall j i, j < nSource -> i < nTarget ->
      a.get (j * nTarget + i) =
        ∑ k ∈ Finset.range nMiddle,
          a1.get (k * nTarget + i) * a0.get (j * nMiddle + k)) :
    forall j,
      source j = ∑ i, a.get (j.val * nTarget + i.val) • target i := by
  intro j
  have hr :
      (∑ i, a.get (j.val * nTarget + i.val) • target i) =
      ∑ i,
        (∑ k ∈ Finset.range nMiddle,
          a1.get (k * nTarget + i.val) *
            a0.get (j.val * nMiddle + k)) • target i :=
    Finset.sum_congr rfl (fun i _ => by rw [hget _ _ j.isLt i.isLt])
  rw [hr, hsum0 j]
  simp only [hsum1, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  rw [Fin.sum_univ_eq_sum_range
    (fun k =>
      (a0.get (j.val * nMiddle + k) *
        a1.get (k * nTarget + o.val)) • target o)
    nMiddle]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (a0.get _) (a1.get _)]

/-- Runtime `mtm` computes the same rectangular product as
`raw_rectangular_comp_list`.  The left operand has shape `middle × target`
and the right operand has shape `source × middle`. -/
theorem raw_mtm_rectangular
    (orc : FFSOracleSem) (rho : ValEnvSem)
    {left right : ValExpr} {aLeft aRight : FlatArray}
    {sSource sMiddle sTarget sAux : ValSpace}
    {nSource nMiddle nTarget : Nat}
    (hLeftInfer : ValExpr.inferSpaceCtx [] left =
      .tprod sMiddle sTarget)
    (hRightInfer : ValExpr.inferSpaceCtx [] right =
      .tprod sSource sMiddle)
    (hLeft : denotValB_semS orc rho [] [] left = .ok (.array aLeft))
    (hRight : denotValB_semS orc rho [] [] right = .ok (.array aRight))
    (hSource : ValSpace.dof (orc rho [] []) sSource = nSource)
    (hMiddle : ValSpace.dof (orc rho [] []) sMiddle = nMiddle)
    (hTarget : ValSpace.dof (orc rho [] []) sTarget = nTarget)
    (hLeftLen : aLeft.length = nMiddle * nTarget)
    (hRightLen : aRight.length = nSource * nMiddle) :
    exists a : FlatArray,
      denotValB_semS orc rho [] []
        (.mtm 0 0 sMiddle sAux left right) =
        .ok (.array a) /\
      a.length = nSource * nTarget /\
      forall j i, j < nSource -> i < nTarget ->
        a.get (j * nTarget + i) =
          ∑ k ∈ Finset.range nMiddle,
            aLeft.get (k * nTarget + i) *
              aRight.get (j * nMiddle + k) := by
  let out := FlatArray.ofFn (nSource * nTarget) fun q =>
    if q >= nSource * nTarget then 0
    else ∑ k ∈ Finset.range nMiddle,
      aLeft.get (nTarget * k + q % nTarget) *
        aRight.get (nMiddle * (q / nTarget) + k)
  have hval : denotValB_semS orc rho [] []
      (.mtm 0 0 sMiddle sAux left right) =
      .ok (.array out) := by
    rw [denotValB_semS.eq_13, hLeft, hRight]
    simp only [ValValSem.bindArrays, ValValSem.bindArray,
      hLeftInfer, hRightInfer, ValExpr.inferSpaceCtx,
      ValSpace.dof_tprod, hSource, hMiddle, hTarget,
      ValueShape.mtm, ValueShape.matrices, ValueShape.tensor, hLeftLen, hRightLen,
      and_self, if_true]
    rfl
  refine ⟨out, hval, ?_, ?_⟩
  · simp [out]
  · intro j i hj hi
    have hlt : j * nTarget + i < nSource * nTarget := by
      calc
        j * nTarget + i < j * nTarget + nTarget :=
          Nat.add_lt_add_left hi _
        _ = (j + 1) * nTarget := by
          rw [Nat.add_mul, one_mul]
        _ ≤ nSource * nTarget :=
          Nat.mul_le_mul_right nTarget (Nat.succ_le_iff.mpr hj)
    have hnle : ¬ (nSource * nTarget ≤ j * nTarget + i) :=
      Nat.not_le.mpr hlt
    have hdm := RawSpaceFFS.rowMajor_div_mod (i := j) hi
    have hdiv : (j * nTarget + i) / nTarget = j := by
      calc
        (j * nTarget + i) / nTarget =
            (i + nTarget * j) / nTarget := by
          rw [Nat.mul_comm, Nat.add_comm]
        _ = j := hdm.1
    have hmod : (j * nTarget + i) % nTarget = i := by
      calc
        (j * nTarget + i) % nTarget =
            (i + nTarget * j) % nTarget := by
          rw [Nat.mul_comm, Nat.add_comm]
        _ = i := hdm.2
    simp only [out, FlatArray.get_ofFn, hlt, if_true, ge_iff_le,
      hnle, if_false, hdiv, hmod]
    apply Finset.sum_congr rfl
    intro k _
    rw [Nat.mul_comm nTarget k, Nat.mul_comm nMiddle j]

/-! ## Projected kernel/cokernel constructor -/

theorem raw_arm_cob_proj_ker_coker
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
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
    (ihSv0 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (ihSv : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : RawMSpaceSubctx orc Gamma Psi s sv')
    (ihSv0' : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0') sv0')
    (ihCob : RawMCobSubctx orc Gamma Psi b0 env2 b0')
    (ihEmbd : RawMTermTraceSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (ihProj : RawMTermTraceSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0'))
      (.tprod (.dual b0') (.proj s b0' b1)) env1
      (.space (.tprod sv0' sv'))) :
    RawMCobSubctx orc Gamma Psi (.proj s b0 b1)
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
    raw_trace_linear_map_rows hBS hBA trEmbd
  obtain ⟨a1, ha1, ha1len, hrow1⟩ :=
    raw_trace_linear_map_rows hBA' hBT trProj

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

  simp only [CobAgree] at cobAgree
  obtain ⟨hA1len, a2, ha2, ha2len, hrow2⟩ := cobAgree
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
        rw [raw_proj_fin_sum_cast_of_eq hA1len.symm]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.val_cast]
        rw [List.getD_eq_getElem A1 0 i.isLt]
        rw [List.get_eq_getElem]

  obtain ⟨_, hSdim⟩ := raw_cob_basis_length orc hbSrc ihSv
    hsub hle hc
  obtain ⟨_, hTdim⟩ := raw_cob_basis_length orc hbTgt ihSv'
    hsub hle hc
  obtain ⟨_, hA0dim⟩ := raw_cob_basis_length orc hb0v ihSv0
    hsub hle hc
  obtain ⟨_, hA1dim0⟩ := raw_cob_basis_length orc hb0'v ihSv0'
    hsub hle hc
  have hA1dim : A1.length = ValSpace.dof (orc rho [] []) sv0' := by
    have h := hA1dim0
    rw [← hsofAmbient] at h
    simpa only [A1, W] using h

  have ha3Target : a3.length =
      ValSpace.dof (orc rho [] []) (.tprod sv sv0) := by
    simpa only [ValSpace.dof_tprod, S0, A0] using
      ha3len.trans (congrArg₂ (fun x y => x * y) hSdim hA0dim)
  have ha2Target : a2.length =
      ValSpace.dof (orc rho [] []) (.tprod sv0 sv0') := by
    simp only [ValSpace.dof_tprod]
    calc
      a2.length = A0.length * A0.length := by
        simpa only [A0] using ha2len
      _ = ValSpace.dof (orc rho [] []) sv0 *
          ValSpace.dof (orc rho [] []) sv0' := by
        exact congrArg₂ (fun x y => x * y) hA0dim
          (hA1len.symm.trans hA1dim)
  have ha1Target : a1.length =
      ValSpace.dof (orc rho [] []) (.tprod sv0' sv') := by
    have ha1len' : a1.length = A1.length * S1.length := by
      have h := ha1len
      rw [← hsofAmbient] at h
      simpa only [A1, S1, W, V] using h
    simpa only [ValSpace.dof_tprod] using
      ha1len'.trans (congrArg₂ (fun x y => x * y) hA1dim hTdim)

  have hr3 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env3 (.tprod sv sv0)) = .ok (.array a3) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env3
      (.tprod sv sv0) a3 ha3 ha3Target
  have hr2 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env2 (.tprod sv0 sv0')) = .ok (.array a2) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env2
      (.tprod sv0 sv0') a2 ha2 ha2Target
  have hr1 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env1 (.tprod sv0' sv')) = .ok (.array a1) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env1
      (.tprod sv0' sv') a1 ha1 ha1Target

  obtain ⟨a23, ha23, ha23len, hget23⟩ :=
    raw_mtm_rectangular orc rho (sAux := sv0)
      (left := ValExpr.reshapBase env2 (.tprod sv0 sv0'))
      (right := ValExpr.reshapBase env3 (.tprod sv sv0))
      rfl rfl hr2 hr3 hSdim.symm hA0dim.symm hA1dim.symm
      (by simpa [ValSpace.dof_tprod, ← hA0dim, ← hA1dim] using ha2Target)
      (by simpa [ValSpace.dof_tprod, ← hSdim, ← hA0dim] using ha3Target)
  obtain ⟨a, ha, halen, hget⟩ :=
    raw_mtm_rectangular orc rho (sAux := sv0')
      (left := ValExpr.reshapBase env1 (.tprod sv0' sv'))
      (right := .mtm 0 0 sv0 sv0
        (ValExpr.reshapBase env2 (.tprod sv0 sv0'))
        (ValExpr.reshapBase env3 (.tprod sv sv0)))
      rfl rfl hr1 ha23 hSdim.symm hA1dim.symm hTdim.symm
      (by simpa [ValSpace.dof_tprod, ← hA1dim, ← hTdim] using ha1Target) ha23len

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
  unfold CobAgree
  dsimp only
  refine ⟨by simpa only [S0, S1] using hSTlen, a, ha, ?_, ?_⟩
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
        rw [raw_proj_fin_sum_cast_of_eq hSTlen]
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val < S1.length := by
          simpa only [hSTlen] using i.isLt
        simp only [Fin.val_cast, hSTlen]
        rw [List.getD_eq_getElem S1 0 hi]
        rfl

theorem raw_arm_cob_facts_proj_ker_coker
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
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
    (ihSv0 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (_ihSv1 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : RawMSpaceSubctx orc Gamma Psi s sv')
    (ihSv0' : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0') sv0')
    (ihCob : RawCobFactsSubctx orc Gamma Psi b0 env2 b0')
    (ihEmbd : RawTermDofFactsSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (ihProj : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0'))
      (.tprod (.dual b0') (.proj s b0' b1)) env1
      (.space (.tprod sv0' sv'))) :
    RawCobFactsSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv0' sv0'
        (ValExpr.reshapBase env1 (.tprod sv0' sv'))
        (.mtm 0 0 sv0 sv0
          (ValExpr.reshapBase env2 (.tprod sv0 sv0'))
          (ValExpr.reshapBase env3 (.tprod sv sv0))))
      (.proj s b0' b1) := by
  exact ⟨raw_arm_cob_proj_ker_coker hbSrc hbTgt hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv0' hcob hembd hproj
      ihSv0 ihSv ihSv' ihSv0' ihCob.agree ihEmbd.trace ihProj.trace,
    raw_arm_cob_infer_proj_ker_coker hbSrc ihSv ihSv'⟩

/-! ## Projected kernel/cokernel, codomain-side annotation change -/

theorem raw_arm_cob_proj_ker_coker_cod
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
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
    (ihSv0 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (ihSv : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : RawMSpaceSubctx orc Gamma Psi s sv')
    (ihEmbd : RawMTermTraceSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (ihProj : RawMTermTraceSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0))
      (.tprod (.dual b0) (.proj s b0 b1')) env1
      (.space (.tprod sv0 sv'))) :
    RawMCobSubctx orc Gamma Psi (.proj s b0 b1)
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
    raw_trace_linear_map_rows hBS hBA trEmbd
  obtain ⟨a1, ha1, ha1len, hrow1⟩ :=
    raw_trace_linear_map_rows hBA hBT trProj

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

  obtain ⟨_, hSdim⟩ := raw_cob_basis_length orc hbSrc ihSv
    hsub hle hc
  obtain ⟨_, hTdim⟩ := raw_cob_basis_length orc hbTgt ihSv'
    hsub hle hc
  obtain ⟨_, hAdim⟩ := raw_cob_basis_length orc hb0v ihSv0
    hsub hle hc

  have ha3Target : a3.length =
      ValSpace.dof (orc rho [] []) (.tprod sv sv0) := by
    simpa only [ValSpace.dof_tprod, S0, A] using
      ha3len.trans (congrArg₂ (fun x y => x * y) hSdim hAdim)
  have ha1Target : a1.length =
      ValSpace.dof (orc rho [] []) (.tprod sv0 sv') := by
    simpa only [ValSpace.dof_tprod, A, S1] using
      ha1len.trans (congrArg₂ (fun x y => x * y) hAdim hTdim)
  have hr3 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env3 (.tprod sv sv0)) = .ok (.array a3) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env3
      (.tprod sv sv0) a3 ha3 ha3Target
  have hr1 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env1 (.tprod sv0 sv')) = .ok (.array a1) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env1
      (.tprod sv0 sv') a1 ha1 ha1Target

  obtain ⟨a, ha, halen, hget⟩ :=
    raw_mtm_rectangular orc rho (sAux := sv0)
      (left := ValExpr.reshapBase env1 (.tprod sv0 sv'))
      (right := ValExpr.reshapBase env3 (.tprod sv sv0))
      rfl rfl hr1 hr3 hSdim.symm hAdim.symm hTdim.symm
      (by simpa [ValSpace.dof_tprod, ← hAdim, ← hTdim] using ha1Target)
      (by simpa [ValSpace.dof_tprod, ← hSdim, ← hAdim] using ha3Target)

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
  unfold CobAgree
  dsimp only
  refine ⟨by simpa only [S0, S1] using hSTlen, a, ha, ?_, ?_⟩
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
        rw [raw_proj_fin_sum_cast_of_eq hSTlen]
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val < S1.length := by
          simpa only [hSTlen] using i.isLt
        simp only [Fin.val_cast, hSTlen]
        rw [List.getD_eq_getElem S1 0 hi]
        rfl

theorem raw_arm_cob_facts_proj_ker_coker_cod
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
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
    (ihSv0 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (ihSv : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : RawMSpaceSubctx orc Gamma Psi s sv')
    (ihEmbd : RawTermDofFactsSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b0) env3
      (.space (.tprod sv sv0)))
    (ihProj : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b0))
      (.tprod (.dual b0) (.proj s b0 b1')) env1
      (.space (.tprod sv0 sv'))) :
    RawCobFactsSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv0 sv0
        (ValExpr.reshapBase env1 (.tprod sv0 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv0)))
      (.proj s b0 b1') := by
  exact ⟨raw_arm_cob_proj_ker_coker_cod hbSrc hbTgt hs hsofb0
      hsofb1 hsofb1' hsv0 hsv hsv' hembd hproj
      ihSv0 ihSv ihSv' ihEmbd.trace ihProj.trace,
    raw_arm_cob_infer_proj_ker_coker_cod hbSrc ihSv ihSv'⟩

/-! ## Projected image/coimage, domain-side annotation change -/

theorem raw_arm_cob_proj_img_coimg_dom
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
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
    (ihSv1 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : RawMSpaceSubctx orc Gamma Psi s sv')
    (ihEmbd : RawMTermTraceSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (ihProj : RawMTermTraceSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1))
      (.tprod (.dual b1) (.proj s b0' b1)) env1
      (.space (.tprod sv1 sv'))) :
    RawMCobSubctx orc Gamma Psi (.proj s b0 b1)
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
    raw_trace_linear_map_rows hBS hBA trEmbd
  obtain ⟨a1, ha1, ha1len, hrow1⟩ :=
    raw_trace_linear_map_rows hBA hBT trProj

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

  obtain ⟨_, hSdim⟩ := raw_cob_basis_length orc hbSrc ihSv
    hsub hle hc
  obtain ⟨_, hTdim⟩ := raw_cob_basis_length orc hbTgt ihSv'
    hsub hle hc
  obtain ⟨_, hAdim⟩ := raw_cob_basis_length orc hb1v ihSv1
    hsub hle hc

  have ha3Target : a3.length =
      ValSpace.dof (orc rho [] []) (.tprod sv sv1) := by
    simpa only [ValSpace.dof_tprod, S0, A] using
      ha3len.trans (congrArg₂ (fun x y => x * y) hSdim hAdim)
  have ha1Target : a1.length =
      ValSpace.dof (orc rho [] []) (.tprod sv1 sv') := by
    simpa only [ValSpace.dof_tprod, A, S1] using
      ha1len.trans (congrArg₂ (fun x y => x * y) hAdim hTdim)
  have hr3 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env3 (.tprod sv sv1)) = .ok (.array a3) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env3
      (.tprod sv sv1) a3 ha3 ha3Target
  have hr1 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env1 (.tprod sv1 sv')) = .ok (.array a1) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env1
      (.tprod sv1 sv') a1 ha1 ha1Target

  obtain ⟨a, ha, halen, hget⟩ :=
    raw_mtm_rectangular orc rho (sAux := sv1)
      (left := ValExpr.reshapBase env1 (.tprod sv1 sv'))
      (right := ValExpr.reshapBase env3 (.tprod sv sv1))
      rfl rfl hr1 hr3 hSdim.symm hAdim.symm hTdim.symm
      (by simpa [ValSpace.dof_tprod, ← hAdim, ← hTdim] using ha1Target)
      (by simpa [ValSpace.dof_tprod, ← hSdim, ← hAdim] using ha3Target)

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
  unfold CobAgree
  dsimp only
  refine ⟨by simpa only [S0, S1] using hSTlen, a, ha, ?_, ?_⟩
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
        rw [raw_proj_fin_sum_cast_of_eq hSTlen]
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val < S1.length := by
          simpa only [hSTlen] using i.isLt
        simp only [Fin.val_cast, hSTlen]
        rw [List.getD_eq_getElem S1 0 hi]
        rfl

theorem raw_arm_cob_facts_proj_img_coimg_dom
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
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
    (ihSv1 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : RawMSpaceSubctx orc Gamma Psi s sv')
    (ihEmbd : RawTermDofFactsSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (ihProj : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1))
      (.tprod (.dual b1) (.proj s b0' b1)) env1
      (.space (.tprod sv1 sv'))) :
    RawCobFactsSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv1 sv1
        (ValExpr.reshapBase env1 (.tprod sv1 sv'))
        (ValExpr.reshapBase env3 (.tprod sv sv1)))
      (.proj s b0' b1) := by
  exact ⟨raw_arm_cob_proj_img_coimg_dom hbSrc hbTgt hs hsofb0
      hsofb1 hsofb0' hsv1 hsv hsv' hembd hproj
      ihSv1 ihSv ihSv' ihEmbd.trace ihProj.trace,
    raw_arm_cob_infer_proj_img_coimg_dom hbSrc ihSv ihSv'⟩

/-! ## Projected image/coimage constructor -/

theorem raw_arm_cob_proj_img_coimg
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
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
    (ihSv1 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : RawMSpaceSubctx orc Gamma Psi s sv')
    (ihSv1' : RawMSpaceSubctx orc Gamma Psi (Basis.sof b1') sv1')
    (ihCob : RawMCobSubctx orc Gamma Psi b1 env2 b1')
    (ihEmbd : RawMTermTraceSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (ihProj : RawMTermTraceSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1'))
      (.tprod (.dual b1') (.proj s b0 b1')) env1
      (.space (.tprod sv1' sv'))) :
    RawMCobSubctx orc Gamma Psi (.proj s b0 b1)
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
    raw_trace_linear_map_rows hBS hBA trEmbd
  obtain ⟨a1, ha1, ha1len, hrow1⟩ :=
    raw_trace_linear_map_rows hBA' hBT trProj

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

  simp only [CobAgree] at cobAgree
  obtain ⟨hA1len, a2, ha2, ha2len, hrow2⟩ := cobAgree
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
        rw [raw_proj_fin_sum_cast_of_eq hA1len.symm]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Fin.val_cast]
        rw [List.getD_eq_getElem A1 0 i.isLt]
        rw [List.get_eq_getElem]

  obtain ⟨_, hSdim⟩ := raw_cob_basis_length orc hbSrc ihSv
    hsub hle hc
  obtain ⟨_, hTdim⟩ := raw_cob_basis_length orc hbTgt ihSv'
    hsub hle hc
  obtain ⟨_, hA0dim⟩ := raw_cob_basis_length orc hb1v ihSv1
    hsub hle hc
  obtain ⟨_, hA1dim0⟩ := raw_cob_basis_length orc hb1'v ihSv1'
    hsub hle hc
  have hA1dim : A1.length = ValSpace.dof (orc rho [] []) sv1' := by
    have h := hA1dim0
    rw [← hsofAmbient] at h
    simpa only [A1, W] using h

  have ha3Target : a3.length =
      ValSpace.dof (orc rho [] []) (.tprod sv sv1) := by
    simpa only [ValSpace.dof_tprod, S0, A0] using
      ha3len.trans (congrArg₂ (fun x y => x * y) hSdim hA0dim)
  have ha2Target : a2.length =
      ValSpace.dof (orc rho [] []) (.tprod sv1 sv1') := by
    simp only [ValSpace.dof_tprod]
    calc
      a2.length = A0.length * A0.length := by
        simpa only [A0] using ha2len
      _ = ValSpace.dof (orc rho [] []) sv1 *
          ValSpace.dof (orc rho [] []) sv1' := by
        exact congrArg₂ (fun x y => x * y) hA0dim
          (hA1len.symm.trans hA1dim)
  have ha1Target : a1.length =
      ValSpace.dof (orc rho [] []) (.tprod sv1' sv') := by
    have ha1len' : a1.length = A1.length * S1.length := by
      have h := ha1len
      rw [← hsofAmbient] at h
      simpa only [A1, S1, W, V] using h
    simpa only [ValSpace.dof_tprod] using
      ha1len'.trans (congrArg₂ (fun x y => x * y) hA1dim hTdim)

  have hr3 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env3 (.tprod sv sv1)) = .ok (.array a3) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env3
      (.tprod sv sv1) a3 ha3 ha3Target
  have hr2 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env2 (.tprod sv1 sv1')) = .ok (.array a2) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env2
      (.tprod sv1 sv1') a2 ha2 ha2Target
  have hr1 : denotValB_semS orc rho [] []
      (ValExpr.reshapBase env1 (.tprod sv1' sv')) = .ok (.array a1) := by
    exact denotValB_semS_reshap_space_ok orc rho [] [] env1
      (.tprod sv1' sv') a1 ha1 ha1Target

  obtain ⟨a23, ha23, ha23len, hget23⟩ :=
    raw_mtm_rectangular orc rho (sAux := sv1)
      (left := ValExpr.reshapBase env2 (.tprod sv1 sv1'))
      (right := ValExpr.reshapBase env3 (.tprod sv sv1))
      rfl rfl hr2 hr3 hSdim.symm hA0dim.symm hA1dim.symm
      (by simpa [ValSpace.dof_tprod, ← hA0dim, ← hA1dim] using ha2Target)
      (by simpa [ValSpace.dof_tprod, ← hSdim, ← hA0dim] using ha3Target)
  obtain ⟨a, ha, halen, hget⟩ :=
    raw_mtm_rectangular orc rho (sAux := sv1')
      (left := ValExpr.reshapBase env1 (.tprod sv1' sv'))
      (right := .mtm 0 0 sv1 sv1
        (ValExpr.reshapBase env2 (.tprod sv1 sv1'))
        (ValExpr.reshapBase env3 (.tprod sv sv1)))
      rfl rfl hr1 ha23 hSdim.symm hA1dim.symm hTdim.symm
      (by simpa [ValSpace.dof_tprod, ← hA1dim, ← hTdim] using ha1Target) ha23len

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
  unfold CobAgree
  dsimp only
  refine ⟨by simpa only [S0, S1] using hSTlen, a, ha, ?_, ?_⟩
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
        rw [raw_proj_fin_sum_cast_of_eq hSTlen]
        apply Finset.sum_congr rfl
        intro i _
        have hi : i.val < S1.length := by
          simpa only [hSTlen] using i.isLt
        simp only [Fin.val_cast, hSTlen]
        rw [List.getD_eq_getElem S1 0 hi]
        rfl

theorem raw_arm_cob_facts_proj_img_coimg
    {orc : FFSOracleSem} {Gamma : NLCtx} {Psi : EvalCtx}
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
    (_ihSv0 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b0) sv0)
    (ihSv1 : RawMSpaceSubctx orc Gamma Psi (Basis.sof b1) sv1)
    (ihSv : RawMSpaceSubctx orc Gamma Psi s sv)
    (ihSv' : RawMSpaceSubctx orc Gamma Psi s sv')
    (ihSv1' : RawMSpaceSubctx orc Gamma Psi (Basis.sof b1') sv1')
    (ihCob : RawCobFactsSubctx orc Gamma Psi b1 env2 b1')
    (ihEmbd : RawTermDofFactsSubctx orc ∅ Gamma Psi (Term.lembd s)
      (.tprod (.dual (.proj s b0 b1)) b1) env3
      (.space (.tprod sv sv1)))
    (ihProj : RawTermDofFactsSubctx orc ∅ Gamma Psi
      (Term.lproj s (Basis.sof b1'))
      (.tprod (.dual b1') (.proj s b0 b1')) env1
      (.space (.tprod sv1' sv'))) :
    RawCobFactsSubctx orc Gamma Psi (.proj s b0 b1)
      (.mtm 0 0 sv1' sv1'
        (ValExpr.reshapBase env1 (.tprod sv1' sv'))
        (.mtm 0 0 sv1 sv1
          (ValExpr.reshapBase env2 (.tprod sv1 sv1'))
          (ValExpr.reshapBase env3 (.tprod sv sv1))))
      (.proj s b0 b1') := by
  exact ⟨raw_arm_cob_proj_img_coimg hbSrc hbTgt hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv1' hcob hembd hproj
      ihSv1 ihSv ihSv' ihSv1' ihCob.agree ihEmbd.trace ihProj.trace,
    raw_arm_cob_infer_proj_img_coimg hbSrc ihSv ihSv'⟩

end GLang
