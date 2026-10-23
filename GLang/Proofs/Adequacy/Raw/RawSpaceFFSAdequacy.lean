import GLang.Proofs.Adequacy.Raw.RawSpaceAdequacyCore
import GLang.Proofs.Adequacy.Foundations.AgreeBasics
import GLang.Proofs.Source.BasisSoundness

namespace GLang

open scoped BigOperators TensorProduct
open Basis (BasisValid)

namespace RawSpaceFFS

/-! ## World-local rank bridge -/

/-- The denoted witness, viewed as a map from the domain to the codomain. -/
noncomputable abbrev witnessMap (sigma : DEnv) (s0 s1 : GLang.Space)
    (e : GLang.Term) :
    (denotSpace sigma s0).carrier →ₗ[ℝ] (denotSpace sigma s1).carrier :=
  (denotTerm sigma e).asLinMap (denotSpace sigma s0)
    (denotSpace sigma s1)

theorem finrank_denotSpaceAux_dual (sigma : DEnv) (DeltaS : List DVal)
    (s : GLang.Space) :
    Module.finrank ℝ (denotSpaceAux sigma DeltaS (.dual s)).carrier =
      Module.finrank ℝ (denotSpaceAux sigma DeltaS s).carrier := by
  simp only [denotSpaceAux]
  exact Subspace.dual_finrank_eq

/-- The source shape of `s0* ⊗ s1`. -/
theorem srcShp_tprod_dual (sigma : DEnv) (s0 s1 : GLang.Space) :
    srcShp sigma [] (.tprod (.dual s0) s1) =
      [Module.finrank ℝ (denotSpace sigma s0).carrier,
        Module.finrank ℝ (denotSpace sigma s1).carrier] := by
  simp only [srcShp, finrank_denotSpaceAux_dual]

/-- Read the FFS leaf shape using the child space fact and the oracle's rank
contract. -/
theorem shpOf_ffs_eq
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : GLang.Space}
    {b : Basis} {v : ValExpr} {svb : ValSpace}
    (hb : Basis.sof b = .tprod (.dual s0) s1)
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) svb)
    (he : S.Term ∅ Gamma Psi e b v (.space svb))
    (p : ValFFSProp) {Psi' : EvalCtx} (hsub : Psi.Subctx Psi')
    (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
    (sigma : DEnv) (GammaV : ValCtx)
    (hle : NLCtxIncl Gamma Gamma')
    (hc : RawTypedConsistent orc Delta' Gamma' Psi' GammaV sigma rho) :
    ValSpace.shpOf (orc rho [] [])
        (.ffs p svb (ValExpr.reshapBase v svb)) =
      [ffsDim p
        [Module.finrank ℝ (denotSpace sigma s0).carrier,
          Module.finrank ℝ (denotSpace sigma s1).carrier]
        (ffsOperandRank orc rho [] [] svb
          (ValExpr.reshapBase v svb))] := by
  rw [ValSpace.shpOf_ffs,
    hspec.rank rho p svb (ValExpr.reshapBase v svb) rfl
      ((hc.typeFinite (he.mono hsub).toEvalT).space_inv.ffs
        ((hc.exprFinite (he.mono hsub).toOpStep).reshapBase
          (hc.typeFinite (he.mono hsub).toEvalT).space_inv))]
  have hshape := ihSpace hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [hb, srcShp_tprod_dual] at hshape
  rw [hshape]

/-! ## Coordinate rank mathematics -/

/-- A coordinate matrix in two list bases has the rank of the represented
linear map. -/
theorem coordMatrix_rank
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) :
    (hb0.coordMatrix hb1 f).rank =
      Module.finrank ℝ (LinearMap.range f) := by
  unfold IsListBasis.coordMatrix
  rw [Matrix.rank_eq_finrank_range_toLin _ hb1.toBasis hb0.toBasis,
    Matrix.toLin_toMatrix]

/-- A dual-basis coefficient expansion has coordinate matrix equal to the
transpose of its row-major coefficient matrix. -/
theorem coordMatrix_eq_denotAsMatrix_transpose_of_dualBasis
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (a : ℕ → ℝ)
    (phi : Fin vs0.length → (V0.carrier →ₗ[ℝ] ℝ))
    (hphi : forall i k : Fin vs0.length,
      phi i (vs0.get k) = if i = k then 1 else 0)
    (hf : forall u, f u =
      ∑ i : Fin vs0.length, ∑ j : Fin vs1.length,
        (a (vs1.length * i.val + j.val) * phi i u) • vs1.get j) :
    hb0.coordMatrix hb1 f =
      (denotAsMatrix vs0.length vs1.length a).transpose := by
  ext j i'
  rw [IsListBasis.coordMatrix, LinearMap.toMatrix_apply,
    IsListBasis.toBasis_apply, hf]
  have hsum :
      (∑ i : Fin vs0.length, ∑ j' : Fin vs1.length,
        (a (vs1.length * i.val + j'.val) * phi i (vs0.get i')) •
          vs1.get j') =
      ∑ j' : Fin vs1.length, (∑ i : Fin vs0.length,
        a (vs1.length * i.val + j'.val) * phi i (vs0.get i')) •
          vs1.get j' := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_smul]
  rw [hsum]
  have hc := congrFun (hb1.coords_sum_smul
    (fun j' : Fin vs1.length => ∑ i : Fin vs0.length,
      a (vs1.length * i.val + j'.val) * phi i (vs0.get i'))) j
  simp only [IsListBasis.coords] at hc
  rw [hc]
  simp only [hphi, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Matrix.transpose_apply, denotAsMatrix]

/-- Consequently the row-major coefficient matrix has the rank of the map. -/
theorem rank_denotAsMatrix_of_dualBasis
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (a : ℕ → ℝ)
    (phi : Fin vs0.length → (V0.carrier →ₗ[ℝ] ℝ))
    (hphi : forall i k : Fin vs0.length,
      phi i (vs0.get k) = if i = k then 1 else 0)
    (hf : forall u, f u =
      ∑ i : Fin vs0.length, ∑ j : Fin vs1.length,
        (a (vs1.length * i.val + j.val) * phi i u) • vs1.get j) :
    (denotAsMatrix vs0.length vs1.length a).rank =
      Module.finrank ℝ (LinearMap.range f) := by
  have hmatrix := coordMatrix_eq_denotAsMatrix_transpose_of_dualBasis
    hb0 hb1 f a phi hphi hf
  rw [← coordMatrix_rank hb0 hb1 f, hmatrix, Matrix.rank_transpose]

/-- Row-major division and remainder. -/
theorem rowMajor_div_mod {n1 i j : ℕ} (hj : j < n1) :
    (j + n1 * i) / n1 = i ∧ (j + n1 * i) % n1 = j := by
  have hpos : 0 < n1 := Nat.zero_lt_of_lt hj
  constructor
  · rw [Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hj,
      Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]

/-- `getD` form of the row-major tensor-product list lookup. -/
theorem tprodOfLists_getD
    (V0 V1 : HSpace) (vs0 : List V0.carrier) (vs1 : List V1.carrier)
    (k : ℕ) (hk : k < vs0.length * vs1.length)
    (hpos : 0 < vs1.length) :
    (HSpace.tprodOfLists V0 V1 vs0 vs1).getD k 0 =
      vs0.getD (k / vs1.length) 0 ⊗ₜ[ℝ]
        vs1.getD (k % vs1.length) 0 := by
  have hkList : k < (HSpace.tprodOfLists V0 V1 vs0 vs1).length := by
    rw [HSpace.tprodOfLists_length]
    exact hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkList,
    HSpace.tprodOfLists_getElem vs0 vs1 k hk hpos]
  have hi : k / vs1.length < vs0.length :=
    (Nat.div_lt_iff_lt_mul hpos).2 hk
  have hj : k % vs1.length < vs1.length := Nat.mod_lt _ hpos
  rw [List.getD_eq_getElem vs0 0 hi,
    List.getD_eq_getElem vs1 0 hj]
  simp only [Option.getD_some]

/-- `getD` access into the explicitly constructed dual list is the matching
dual coordinate functional. -/
theorem dualOfList_getD_eq_dualVec
    (V : HSpace) (vs : List V.carrier) {i : ℕ}
    (hi : i < vs.length) :
    (V.dualOfList vs).getD i 0 = V.dualVec vs ⟨i, hi⟩ := by
  have hlen : (V.dualOfList vs).length = vs.length :=
    HSpace.dualOfList_length V vs
  have hiDual : i < (V.dualOfList vs).length := hlen.symm ▸ hi
  rw [List.getD_eq_getElem (V.dualOfList vs) 0 hiDual]
  change (V.dualOfList vs).get ⟨i, hiDual⟩ = _
  refine (List.get_of_eq
    (HSpace.dualOfList_eq_finRange_map V vs) ⟨i, hiDual⟩).trans ?_
  simp

/-- Rank of a tensor expanded in the row-major product of a dual list basis
and a codomain list basis. -/
theorem rank_denotAsMatrix_of_tprodOfLists_dual
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (a : ℕ → ℝ)
    (t : (HSpace.tprod (HSpace.dual V0) V1).carrier)
    (ht : t = ∑ k : Fin (vs0.length * vs1.length),
      a k.val •
        (HSpace.tprodOfLists (HSpace.dual V0) V1
          (V0.dualOfList vs0) vs1).getD k.val 0) :
    (denotAsMatrix vs0.length vs1.length a).rank =
      Module.finrank ℝ
        (LinearMap.range (dualTensorHom ℝ V0.carrier V1.carrier t)) := by
  rcases Nat.eq_zero_or_pos vs1.length with hzero | hpos
  · have hrank0 : (denotAsMatrix vs0.length vs1.length a).rank = 0 := by
      have hle := Matrix.rank_le_width
        (denotAsMatrix vs0.length vs1.length a)
      simp only [hzero] at hle
      omega
    have ht0 : t = 0 := by
      rw [ht]
      apply Finset.sum_eq_zero
      intro k _
      exact Fin.elim0 (Fin.cast (by rw [hzero, Nat.mul_zero]) k)
    rw [hrank0, ht0, map_zero, LinearMap.range_zero, finrank_bot]
  · apply rank_denotAsMatrix_of_dualBasis hb0 hb1 _ a
      (HSpace.dualVec V0 vs0)
    · intro i k
      exact hb0.dual_delta i k
    · intro u
      rw [ht, map_sum, LinearMap.sum_apply,
        ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ =>
        Finset.sum_congr rfl fun j _ => ?_
      have hk :
          ((finProdFinEquiv (i, j) : Fin (vs0.length * vs1.length)) : ℕ) =
            j.val + vs1.length * i.val := rfl
      have hlt :
          j.val + vs1.length * i.val <
            (V0.dualOfList vs0).length * vs1.length := by
        rw [HSpace.dualOfList_length]
        exact (finProdFinEquiv (i, j)).isLt
      obtain ⟨hdiv, hmod⟩ := rowMajor_div_mod (i := i.val) j.isLt
      rw [hk, map_smul, LinearMap.smul_apply,
        tprodOfLists_getD _ _ _ _ _ hlt hpos,
        hdiv, hmod, dualTensorHom_apply,
        dualOfList_getD_eq_dualVec V0 vs0 i.isLt,
        List.getD_eq_getElem vs1 0 j.isLt, smul_smul, Nat.add_comm]
      rfl

/-! ## Denoted product-basis read-off -/

/-- Denotation of a dual basis at its own space. -/
theorem denotBasis_dual_atSpace (sigma : DEnv) (b : Basis) :
    (denotBasis sigma (.dual b)).atSpace
        (HSpace.dual (denotSpace sigma (Basis.sof b))) =
      (denotSpace sigma (Basis.sof b)).dualOfList
        ((denotBasis sigma b).atSpace
          (denotSpace sigma (Basis.sof b))) := by
  conv_lhs => rw [denotBasis]
  exact BasisDenot.atSpace_vecs_self _ _

/-- Denotation of `b0* ⊗ b1` is the row-major product of the two denoted
basis lists. -/
theorem denotBasis_tprod_dual_atSpace
    (sigma : DEnv) (b0 b1 : Basis) :
    (denotBasis sigma (.tprod (.dual b0) b1)).atSpace
        (HSpace.tprod
          (HSpace.dual (denotSpace sigma (Basis.sof b0)))
          (denotSpace sigma (Basis.sof b1))) =
      HSpace.tprodOfLists
        (HSpace.dual (denotSpace sigma (Basis.sof b0)))
        (denotSpace sigma (Basis.sof b1))
        ((denotSpace sigma (Basis.sof b0)).dualOfList
          ((denotBasis sigma b0).atSpace
            (denotSpace sigma (Basis.sof b0))))
        ((denotBasis sigma b1).atSpace
          (denotSpace sigma (Basis.sof b1))) := by
  conv_lhs => rw [denotBasis]
  rw [show denotSpace sigma (Basis.sof (.dual b0)) =
      HSpace.dual (denotSpace sigma (Basis.sof b0)) from rfl]
  rw [BasisDenot.atSpace_vecs_self, denotBasis_dual_atSpace]

/-- Reading a tensor-shaped source value as a map is `dualTensorHom` of its
projection at the dual tensor space. -/
theorem asLinMap_eq_dualTensorHom_atSpace
    (V0 V1 : HSpace) (d : DVal) :
    d.asLinMap V0 V1 =
      dualTensorHom ℝ V0.carrier V1.carrier
        (d.atSpace (HSpace.tprod (HSpace.dual V0) V1)) := by
  unfold DVal.asLinMap DVal.atSpace
  obtain ⟨Vt, t⟩ := d.asHil
  by_cases h :
      Vt.carrier = (Module.Dual ℝ V0.carrier ⊗[ℝ] V1.carrier)
  · simp only [h, dif_pos]
  · simp only [h, dif_neg, not_false_eq_true]
    rw [map_zero]

/-! ## Raw witness trace to rank equality -/

/-- At one raw world, an ordinary witness trace exposes its successful flat
coordinate array and its source coefficient expansion. -/
theorem trace_array_coords
    {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {svb : ValSpace}
    (htof : Basis.tof b = .space (Basis.sof b))
    (htrace : RawTermTraceAt orc sigma rho v (Basis.tof b)
      (.space svb) (denotBasis sigma b) (denotTerm sigma e)) :
    exists a : FlatArray,
      denotValB_semS orc rho [] [] v = .ok (.array a) ∧
      ((denotBasis sigma b).atSpace
          (denotSpace sigma (Basis.sof b))).length =
        ValSpace.dof (orc rho [] []) svb ∧
      a.length = ValSpace.dof (orc rho [] []) svb ∧
      (denotTerm sigma e).atSpace
          (denotSpace sigma (Basis.sof b)) =
        ∑ i : Fin (ValSpace.dof (orc rho [] []) svb),
          a.get i.val •
            ((denotBasis sigma b).atSpace
              (denotSpace sigma (Basis.sof b))).getD i.val 0 := by
  obtain ⟨out, heval, hagree⟩ := htrace.result
  rw [htof] at hagree
  cases out with
  | fn T f => simp only [RawAgree] at hagree
  | array a =>
      have hagree' : LegacyAgree orc sigma rho [] [] []
          (.space (Basis.sof b)) (.space svb) (denotBasis sigma b)
          (denotTerm sigma e) (.array a) := by
        simpa only [RawAgree] using hagree
      obtain ⟨hbLen, haLen, hcoords⟩ := LegacyAgree.space_iff.mp hagree'
      exact ⟨a, heval, hbLen, haLen, hcoords⟩

/-- The paired direct-mutual witness fact discharges the rank bridge at the
syntactic product-dual basis. -/
theorem witnessRank_of_tprod_dual
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : GLang.Space}
    {e : GLang.Term} {b0 b1 : Basis} {v : ValExpr} {svb : ValSpace}
    (hb : Basis.sof (.tprod (.dual b0) b1) =
      .tprod (.dual s0) s1)
    (htof : Basis.tof (.tprod (.dual b0) b1) =
      .space (Basis.sof (.tprod (.dual b0) b1)))
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) v
      (.space svb))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi
      (Basis.sof (.tprod (.dual b0) b1)) svb)
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) v (.space svb))
    {Psi' : EvalCtx} (hsub : Psi.Subctx Psi')
    (rho : ValEnvSem) (Delta' : LCtx) (Gamma' : NLCtx)
    (sigma : DEnv) (GammaV : ValCtx)
    (hle : NLCtxIncl Gamma Gamma')
    (hc : RawTypedConsistent orc Delta' Gamma' Psi' GammaV sigma rho) :
    ffsOperandRank orc rho [] [] svb (ValExpr.reshapBase v svb) =
      Module.finrank ℝ (LinearMap.range (witnessMap sigma s0 s1 e)) := by
  simp only [Basis.sof, Space.tprod.injEq, Space.dual.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have hshape : ValSpace.shpOf (orc rho [] []) svb =
      [Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier,
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier] := by
    have h := ihSpace hsub rho Delta' Gamma' sigma GammaV hle hc
    simp only [Basis.sof] at h
    rw [srcShp_tprod_dual] at h
    exact h
  have hN : ValSpace.dof (orc rho [] []) svb =
      Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier *
        Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier := by
    simp [ValSpace.dof, hshape]
  have hctx : RawCtxIncl ∅ Gamma Delta' Gamma' := by
    refine ⟨?_, hle⟩
    intro x s hx
    simp at hx
  have htrace := ihTerm.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hctx hc
  obtain ⟨a, heval, hbLen, haLen, hsum⟩ :=
    trace_array_coords htof htrace
  have haLenTarget := haLen
  rw [hN] at haLen hsum
  obtain ⟨hv0', hv1⟩ := (S.Term.basisValid he).tprod_inv
  have hv0 := hv0'.dual_inv
  have hlb0 := denotBasis_atSpace_isListBasis sigma Gamma' b0
    (raw_basisValid_mono hv0 hle) hc.ctxWF_nl hc.envWF_nl
  have hlb1 := denotBasis_atSpace_isListBasis sigma Gamma' b1
    (raw_basisValid_mono hv1 hle) hc.ctxWF_nl hc.envWF_nl
  have hd0 := hlb0.finrank_eq
  have hd1 := hlb1.finrank_eq
  have hsum' :
      (denotTerm sigma e).atSpace
        (HSpace.tprod
          (HSpace.dual (denotSpace sigma (Basis.sof b0)))
          (denotSpace sigma (Basis.sof b1))) =
      ∑ i : Fin
          (Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier *
            Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier),
        a.get i.val •
          (HSpace.tprodOfLists
            (HSpace.dual (denotSpace sigma (Basis.sof b0)))
            (denotSpace sigma (Basis.sof b1))
            ((denotSpace sigma (Basis.sof b0)).dualOfList
              ((denotBasis sigma b0).atSpace
                (denotSpace sigma (Basis.sof b0))))
            ((denotBasis sigma b1).atSpace
              (denotSpace sigma (Basis.sof b1)))).getD i.val 0 := by
    rw [← denotBasis_tprod_dual_atSpace]
    exact hsum
  have hrank :
      (denotAsMatrix
        (Module.finrank ℝ (denotSpace sigma (Basis.sof b0)).carrier)
        (Module.finrank ℝ (denotSpace sigma (Basis.sof b1)).carrier)
        a.get).rank =
      Module.finrank ℝ
        (LinearMap.range (witnessMap sigma
          (Basis.sof b0) (Basis.sof b1) e)) := by
    rw [witnessMap, asLinMap_eq_dualTensorHom_atSpace]
    rw [hd0, hd1] at hsum' ⊢
    exact rank_denotAsMatrix_of_tprodOfLists_dual
      hlb0 hlb1 a.get _ hsum'
  rw [← hrank]
  unfold ffsOperandRank
  rw [hshape]
  dsimp only
  have hreshap : denotValB_semS orc rho [] []
      (ValExpr.reshapBase v svb) = .ok (.array a) := by
    simpa only [ValExpr.reshapBase] using
      denotValB_semS_reshap_space_ok orc rho [] [] v svb a heval haLenTarget
  rw [hreshap]

end RawSpaceFFS

/-! ## The four `S.Space` producer arms -/

section RawSpaceFFSArms

variable {orc : FFSOracleSem}

/-- Kernel: `dim ker f = dim(domain) - rank f`. -/
theorem raw_arm_space_ker
    (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : GLang.Space}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {svb : ValSpace}
    (_hs : Nonempty (SValid Gamma (.ker s0 s1 e)))
    (hb : Basis.sof b = .tprod (.dual s0) s1)
    (hcompat : Basis.FFSMatrixCompatible b)
    (_hsvb : S.Space Gamma Psi (Basis.sof b) svb)
    (he : S.Term ∅ Gamma Psi e b v (.space svb))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) svb)
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e b v
      (.space svb)) :
    RawMSpaceSubctx orc Gamma Psi (.ker s0 s1 e)
      (.ffs .kernel svb (ValExpr.reshapBase v svb)) := by
  have htof := hcompat.tof_eq_space
  obtain ⟨b0, b1, rfl⟩ := hcompat
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [RawSpaceFFS.shpOf_ffs_eq hspec hb ihSpace he .kernel hsub
      rho Delta' Gamma' sigma GammaV hle hc,
    RawSpaceFFS.witnessRank_of_tprod_dual hb htof he ihSpace ihTerm
      hsub rho Delta' Gamma' sigma GammaV hle hc]
  simp only [srcShp, ffsDim, denotSpaceAux, RawSpaceFFS.witnessMap,
    denotSpace, denotTerm]
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (DVal.asLinMap (denotSpaceAux sigma [] s0)
      (denotSpaceAux sigma [] s1) (denotTermAux sigma [] e))
  congr 1
  exact Nat.sub_eq_of_eq_add (hrank.symm.trans (Nat.add_comm _ _))

/-- Cokernel: the orthogonal complement of the kernel has dimension equal to
the rank. -/
theorem raw_arm_space_coker
    (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : GLang.Space}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {svb : ValSpace}
    (_hs : Nonempty (SValid Gamma (.coker s0 s1 e)))
    (hb : Basis.sof b = .tprod (.dual s0) s1)
    (hcompat : Basis.FFSMatrixCompatible b)
    (_hsvb : S.Space Gamma Psi (Basis.sof b) svb)
    (he : S.Term ∅ Gamma Psi e b v (.space svb))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) svb)
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e b v
      (.space svb)) :
    RawMSpaceSubctx orc Gamma Psi (.coker s0 s1 e)
      (.ffs .cokernel svb (ValExpr.reshapBase v svb)) := by
  have htof := hcompat.tof_eq_space
  obtain ⟨b0, b1, rfl⟩ := hcompat
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [RawSpaceFFS.shpOf_ffs_eq hspec hb ihSpace he .cokernel hsub
      rho Delta' Gamma' sigma GammaV hle hc,
    RawSpaceFFS.witnessRank_of_tprod_dual hb htof he ihSpace ihTerm
      hsub rho Delta' Gamma' sigma GammaV hle hc]
  simp only [srcShp, ffsDim, denotSpaceAux, RawSpaceFFS.witnessMap,
    denotSpace, denotTerm]
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (DVal.asLinMap (denotSpaceAux sigma [] s0)
      (denotSpaceAux sigma [] s1) (denotTermAux sigma [] e))
  have horth := (denotSpaceAux sigma [] s0).finrank_add_finrank_orthRel
    (LinearMap.ker
      (DVal.asLinMap (denotSpaceAux sigma [] s0)
        (denotSpaceAux sigma [] s1) (denotTermAux sigma [] e)))
  have heq :
      Module.finrank ℝ
          (Submodule.orthRel (denotSpaceAux sigma [] s0).innerProduct
            (LinearMap.ker
              (DVal.asLinMap (denotSpaceAux sigma [] s0)
                (denotSpaceAux sigma [] s1)
                (denotTermAux sigma [] e)))) =
        Module.finrank ℝ
          (LinearMap.range
            (DVal.asLinMap (denotSpaceAux sigma [] s0)
              (denotSpaceAux sigma [] s1)
              (denotTermAux sigma [] e))) := by
    omega
  congr 1
  exact heq.symm

/-- Image: its dimension is the rank of the witness map. -/
theorem raw_arm_space_img
    (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : GLang.Space}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {svb : ValSpace}
    (_hs : Nonempty (SValid Gamma (.img s0 s1 e)))
    (hb : Basis.sof b = .tprod (.dual s0) s1)
    (hcompat : Basis.FFSMatrixCompatible b)
    (_hsvb : S.Space Gamma Psi (Basis.sof b) svb)
    (he : S.Term ∅ Gamma Psi e b v (.space svb))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) svb)
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e b v
      (.space svb)) :
    RawMSpaceSubctx orc Gamma Psi (.img s0 s1 e)
      (.ffs .image svb (ValExpr.reshapBase v svb)) := by
  have htof := hcompat.tof_eq_space
  obtain ⟨b0, b1, rfl⟩ := hcompat
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [RawSpaceFFS.shpOf_ffs_eq hspec hb ihSpace he .image hsub
      rho Delta' Gamma' sigma GammaV hle hc,
    RawSpaceFFS.witnessRank_of_tprod_dual hb htof he ihSpace ihTerm
      hsub rho Delta' Gamma' sigma GammaV hle hc]
  simp only [srcShp, ffsDim, denotSpaceAux, RawSpaceFFS.witnessMap,
    denotSpace, denotTerm]
  rfl

/-- Coimage: `dim codomain - rank f`. -/
theorem raw_arm_space_coimg
    (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {s0 s1 : GLang.Space}
    {e : GLang.Term} {b : Basis} {v : ValExpr} {svb : ValSpace}
    (_hs : Nonempty (SValid Gamma (.coimg s0 s1 e)))
    (hb : Basis.sof b = .tprod (.dual s0) s1)
    (hcompat : Basis.FFSMatrixCompatible b)
    (_hsvb : S.Space Gamma Psi (Basis.sof b) svb)
    (he : S.Term ∅ Gamma Psi e b v (.space svb))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) svb)
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e b v
      (.space svb)) :
    RawMSpaceSubctx orc Gamma Psi (.coimg s0 s1 e)
      (.ffs .coimage svb (ValExpr.reshapBase v svb)) := by
  have htof := hcompat.tof_eq_space
  obtain ⟨b0, b1, rfl⟩ := hcompat
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  rw [RawSpaceFFS.shpOf_ffs_eq hspec hb ihSpace he .coimage hsub
      rho Delta' Gamma' sigma GammaV hle hc,
    RawSpaceFFS.witnessRank_of_tprod_dual hb htof he ihSpace ihTerm
      hsub rho Delta' Gamma' sigma GammaV hle hc]
  simp only [srcShp, ffsDim, denotSpaceAux, RawSpaceFFS.witnessMap,
    denotSpace, denotTerm]
  have horth := (denotSpaceAux sigma [] s1).finrank_add_finrank_orthRel
    (LinearMap.range
      (DVal.asLinMap (denotSpaceAux sigma [] s0)
        (denotSpaceAux sigma [] s1) (denotTermAux sigma [] e)))
  congr 1
  exact Nat.sub_eq_of_eq_add (horth.symm.trans (Nat.add_comm _ _))

end RawSpaceFFSArms

end GLang
