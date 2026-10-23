import GLang.Proofs.Adequacy.Raw.Conversion.RawCobAdequacyCore
import GLang.Numerics.SVD.ValueSVD

namespace GLang

open scoped BigOperators

/-! ## Clean SVD and finite-basis algebra -/

/-- On a bijective square matrix, the SVD pseudo-inverse is a left inverse. -/
theorem raw_matrixSVDPinv_mul_eq_one_of_bijective {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hbij : Function.Bijective (Matrix.toLin' A)) :
    matrixSVDPinv A * A = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  apply hbij.1
  have h := congrArg (fun M => Matrix.toLin' M x)
    (matrixSVDPinv_mul_self A)
  simpa only [Matrix.toLin'_mul, Matrix.toLin'_one,
    LinearMap.comp_apply, id_eq] using h

/-- On a bijective square matrix, the SVD pseudo-inverse is a right inverse. -/
theorem raw_mul_matrixSVDPinv_eq_one_of_bijective {n : Nat}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hbij : Function.Bijective (Matrix.toLin' A)) :
    A * matrixSVDPinv A = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hbij.2 x
  have h := congrArg (fun M => Matrix.toLin' M y)
    (matrixSVDPinv_mul_self A)
  simpa only [Matrix.toLin'_mul, Matrix.toLin'_one,
    LinearMap.comp_apply, id_eq] using h

/-- The coordinate matrix of the identity between equally-indexed bases is
bijective on coordinate columns. -/
theorem Basis.raw_toMatrix_id_bijective {V ι : Type*}
    [AddCommGroup V] [Module ℝ V] [Fintype ι] [DecidableEq ι]
    (bS bT : Module.Basis ι ℝ V) :
    Function.Bijective
      (Matrix.toLin' (LinearMap.toMatrix bS bT LinearMap.id)) := by
  have hinj : Function.Injective
      (Matrix.toLin' (LinearMap.toMatrix bS bT LinearMap.id)) := by
    intro c d hcd
    have hc := LinearMap.toMatrix_mulVec_repr bS bT LinearMap.id
      (bS.equivFun.symm c)
    have hd := LinearMap.toMatrix_mulVec_repr bS bT LinearMap.id
      (bS.equivFun.symm d)
    have hreprc : ⇑(bS.repr (bS.equivFun.symm c)) = c :=
      bS.equivFun.apply_symm_apply c
    have hreprd : ⇑(bS.repr (bS.equivFun.symm d)) = d :=
      bS.equivFun.apply_symm_apply d
    rw [hreprc] at hc
    rw [hreprd] at hd
    simp only [LinearMap.id_apply] at hc hd
    simp only [Matrix.toLin'_apply] at hcd
    rw [hcd] at hc
    have heq :
        bT.equivFun (bS.equivFun.symm c) =
          bT.equivFun (bS.equivFun.symm d) := hc.symm.trans hd
    exact bS.equivFun.symm.injective (bT.equivFun.injective heq)
  have hunit : IsUnit (LinearMap.toMatrix bS bT LinearMap.id) :=
    Matrix.mulVec_injective_iff_isUnit.mp (by
      simpa only [Matrix.toLin'_apply] using hinj)
  exact ⟨hinj, by
    simpa only [Matrix.toLin'_apply] using
      (Matrix.mulVec_surjective_iff_isUnit.mpr hunit)⟩

/-- Reverse row expansions using a left inverse matrix. -/
theorem Basis.raw_reverse_row_expansion {V ι : Type*}
    [AddCommGroup V] [Module ℝ V] [Fintype ι] [DecidableEq ι]
    (bS bT : Module.Basis ι ℝ V) (A B : Matrix ι ι ℝ)
    (hrows : ∀ j, bS j = ∑ i, A j i • bT i) (hBA : B * A = 1) :
    ∀ j, bT j = ∑ i, B j i • bS i := by
  intro j
  simp_rw [hrows]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hentry : ∀ k, ∑ i, B j i * A i k = if j = k then 1 else 0 := by
    intro k
    have h := congrFun (congrFun hBA j) k
    simpa only [Matrix.mul_apply, Matrix.one_apply] using h
  conv_rhs =>
    enter [2, k]
    rw [← Finset.sum_smul]
  simp_rw [hentry]
  simp

/-- Row coefficients transpose when passing to dual bases. -/
theorem Basis.raw_dualBasis_row_expansion {V ι : Type*}
    [AddCommGroup V] [Module ℝ V] [Fintype ι] [DecidableEq ι]
    (bS bT : Module.Basis ι ℝ V) (A B : Matrix ι ι ℝ)
    (hrows : ∀ j, bS j = ∑ i, A j i • bT i) (hAB : A * B = 1) :
    ∀ j, bS.dualBasis j = ∑ i, B i j • bT.dualBasis i := by
  intro j
  apply bS.ext
  intro k
  rw [Module.Basis.dualBasis_apply_self]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [hrows]
  simp only [map_sum, map_smul, Module.Basis.dualBasis_apply_self,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hentry := congrFun (congrFun hAB k) j
  simpa only [Matrix.mul_apply, Matrix.one_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_comm]
    using hentry.symm

/-- List-level dual-coordinate transpose expansion. -/
theorem IsListBasis.raw_dualVec_transpose_expansion {V : HSpace}
    {S T : List V.carrier} (hS : IsListBasis V S)
    (hT : IsListBasis V T) (hlen : T.length = S.length)
    (A B : Matrix (Fin S.length) (Fin S.length) ℝ)
    (hrows : ∀ j : Fin S.length,
      S.getD j.val 0 = ∑ i : Fin S.length, A j i • T.getD i.val 0)
    (hAB : A * B = 1) :
    ∀ j : Fin S.length, V.dualVec S j =
      ∑ i : Fin S.length,
        B i j • V.dualVec T (Fin.cast hlen.symm i) := by
  intro j
  apply hS.toBasis.ext
  intro k
  rw [IsListBasis.toBasis_apply]
  rw [IsListBasis.dual_delta hS]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hrowget : S.get k =
      ∑ i : Fin S.length, A k i • T.getD i.val 0 := by
    simpa only [List.getD_eq_getElem S 0 k.isLt] using hrows k
  rw [hrowget]
  simp only [map_sum, map_smul, smul_eq_mul]
  have hdual (i x : Fin S.length) :
      V.dualVec T (Fin.cast hlen.symm i) (T.getD x.val 0) =
        if i = x then 1 else 0 := by
    rw [List.getD_eq_getElem T 0 (hlen.symm ▸ x.isLt)]
    have hd := IsListBasis.dual_delta hT
      (Fin.cast hlen.symm i) (Fin.cast hlen.symm x)
    simpa using hd
  simp only [hdual, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  have hentry := congrFun (congrFun hAB k) j
  simpa only [Matrix.mul_apply, Matrix.one_apply, mul_comm, eq_comm]
    using hentry.symm

/-- The SVD pseudo-inverse reverses a row expansion between finite bases. -/
theorem Basis.raw_svdPinv_reverse_rows {V : Type*} {n : Nat}
    [AddCommGroup V] [Module ℝ V]
    (bS bT : Module.Basis (Fin n) ℝ V)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hrows : ∀ j, bS j = ∑ i, A j i • bT i) :
    ∀ j, bT j = ∑ i, matrixSVDPinv A j i • bS i := by
  have hcoord : A.transpose =
      LinearMap.toMatrix bS bT LinearMap.id := by
    ext j i
    rw [LinearMap.toMatrix_apply, LinearMap.id_apply, hrows i]
    rw [bT.repr_sum_self]
    rfl
  have hbijAT : Function.Bijective (Matrix.toLin' A.transpose) := by
    rw [hcoord]
    exact Basis.raw_toMatrix_id_bijective bS bT
  have hunitAT : IsUnit A.transpose :=
    Matrix.mulVec_injective_iff_isUnit.mp (by
      simpa only [Matrix.toLin'_apply] using hbijAT.1)
  have hunitA : IsUnit A := by
    rwa [Matrix.isUnit_transpose] at hunitAT
  have hbijA : Function.Bijective (Matrix.toLin' A) := by
    constructor
    · simpa only [Matrix.toLin'_apply] using
        Matrix.mulVec_injective_iff_isUnit.mpr hunitA
    · simpa only [Matrix.toLin'_apply] using
        Matrix.mulVec_surjective_iff_isUnit.mpr hunitA
  exact Basis.raw_reverse_row_expansion bS bT A (matrixSVDPinv A)
    hrows (raw_matrixSVDPinv_mul_eq_one_of_bijective A hbijA)

/-- A basis-coordinate matrix has its SVD pseudo-inverse as a right inverse. -/
theorem Basis.raw_mul_svdPinv_eq_one_of_rows {V : Type*} {n : Nat}
    [AddCommGroup V] [Module ℝ V]
    (bS bT : Module.Basis (Fin n) ℝ V)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hrows : ∀ j, bS j = ∑ i, A j i • bT i) :
    A * matrixSVDPinv A = 1 := by
  have hcoord : A.transpose =
      LinearMap.toMatrix bS bT LinearMap.id := by
    ext j i
    rw [LinearMap.toMatrix_apply, LinearMap.id_apply, hrows i]
    rw [bT.repr_sum_self]
    rfl
  have hbijAT : Function.Bijective (Matrix.toLin' A.transpose) := by
    rw [hcoord]
    exact Basis.raw_toMatrix_id_bijective bS bT
  have hunitAT : IsUnit A.transpose :=
    Matrix.mulVec_injective_iff_isUnit.mp (by
      simpa only [Matrix.toLin'_apply] using hbijAT.1)
  have hunitA : IsUnit A := by
    rwa [Matrix.isUnit_transpose] at hunitAT
  have hbijA : Function.Bijective (Matrix.toLin' A) := by
    constructor
    · simpa only [Matrix.toLin'_apply] using
        Matrix.mulVec_injective_iff_isUnit.mpr hunitA
    · simpa only [Matrix.toLin'_apply] using
        Matrix.mulVec_surjective_iff_isUnit.mpr hunitA
  exact raw_mul_matrixSVDPinv_eq_one_of_bijective A hbijA

theorem raw_matrixSVDPinv_denotAsMatrix_cast {m n N : Nat}
    (f : Nat -> ℝ) (hm : m = N) (hn : n = N) (i j : Fin N) :
    matrixSVDPinv (denotAsMatrix m n f)
        (Fin.cast hn.symm i) (Fin.cast hm.symm j) =
      matrixSVDPinv (denotAsMatrix N N f) i j := by
  subst m
  subst n
  rfl

/-- Row-major read-off of an SVD pseudo-inverse at a common square size. -/
theorem raw_matrixAsDenot_svdPinv_denotAsMatrix_get {m n N : Nat}
    (f : Nat -> ℝ) (hm : m = N) (hn : n = N) (i j : Fin N) :
    matrixAsDenot (matrixSVDPinv (denotAsMatrix m n f))
        (i.val * N + j.val) =
      matrixSVDPinv (denotAsMatrix N N f) i j := by
  subst m
  subst n
  by_cases hN : N = 0
  · exact Fin.elim0 (hN ▸ i)
  · obtain ⟨hdiv, hmod⟩ := Nat.raw_rowMajor_div_mod i.isLt j.isLt
    simp [matrixAsDenot, hN, hdiv, hmod]

theorem Basis.raw_std_tof_dual_eq_dual_std_tof {b : Basis}
    (h : Basis.tof b = .space (Basis.sof b)) :
    Basis.std (Basis.tof (.dual b)) =
      .dual (Basis.std (Basis.tof b)) := by
  simp [Basis.tof, Basis.sof, h, Basis.std, Basis.stdSpace]

/-- `getD` access into the explicit dual list is the corresponding dual
coordinate functional. -/
theorem HSpace.raw_dualOfList_getD_eq_dualVec
    (V : HSpace) (vs : List V.carrier) {i : Nat}
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

/-! ## Value-level inverse read-off -/

/-- Row-major read-off for an inverse square value. -/
theorem raw_denotValB_semS_inv_get (orc : FFSOracleSem) (rho : ValEnvSem)
    {e : ValExpr} {a ainv : FlatArray} {sa sb : ValSpace} {N : Nat}
    (henv : denotValB_semS orc rho [] [] e = .ok (.array a))
    (hinv : denotValB_semS orc rho [] [] (.inv e) = .ok (.array ainv))
    (hsab : ValExpr.inferSpaceCtx [] e = .tprod sa sb)
    (hNa : ValSpace.dof (orc rho [] []) sa = N)
    (hNb : ValSpace.dof (orc rho [] []) sb = N) (j i : Fin N) :
    ainv.get (j.val * N + i.val) =
      matrixSVDPinv (denotAsMatrix N N a.get) j i := by
  rw [denotValB_semS.eq_25, henv] at hinv
  simp only [ValValSem.bindArray, hsab] at hinv
  have hshape : a.length =
      ValSpace.dof (orc rho [] []) sa * ValSpace.dof (orc rho [] []) sb := by
    by_contra hne
    simp only [hne, ↓reduceIte] at hinv
    cases hinv
  simp only [hshape, ↓reduceIte] at hinv
  injection hinv with hinv
  injection hinv with hinv
  subst ainv
  simp only [ValExpr.inferSpaceCtx, hsab, ValSpace.dof_tprod]
  have hidx : j.val * N + i.val <
      ValSpace.dof (orc rho [] []) sb * ValSpace.dof (orc rho [] []) sa := by
    rw [hNa, hNb]
    exact Nat.raw_rowMajor_lt j.isLt i.isLt
  rw [FlatArray.get_ofFn, if_pos hidx]
  exact raw_matrixAsDenot_svdPinv_denotAsMatrix_get
    a.get hNa hNb j i

/-- Row-major read-off for the transpose of an inverse square value. -/
theorem raw_denotValB_semS_vtrans_inv_get
    (orc : FFSOracleSem) (rho : ValEnvSem)
    {e : ValExpr} {a ainv aout : FlatArray} {sa sb : ValSpace} {N : Nat}
    (henv : denotValB_semS orc rho [] [] e = .ok (.array a))
    (hinv : denotValB_semS orc rho [] [] (.inv e) = .ok (.array ainv))
    (hout : denotValB_semS orc rho [] [] (.vtrans (.inv e)) =
      .ok (.array aout))
    (hsab : ValExpr.inferSpaceCtx [] e = .tprod sa sb)
    (hNa : ValSpace.dof (orc rho [] []) sa = N)
    (hNb : ValSpace.dof (orc rho [] []) sb = N) (j i : Fin N) :
    aout.get (j.val * N + i.val) =
      matrixSVDPinv (denotAsMatrix N N a.get) i j := by
  rw [denotValB_semS.eq_11, hinv] at hout
  simp only [ValValSem.bindArray] at hout
  split at hout <;> try contradiction
  injection hout with hout
  injection hout with hout
  subst aout
  simp only [ValExpr.inferSpaceCtx, hsab, ValSpace.dof_tprod, hNa, hNb]
  have hlt : j.val * N + i.val < N * N :=
    Nat.raw_rowMajor_lt j.isLt i.isLt
  obtain ⟨hdiv, hmod⟩ := Nat.raw_rowMajor_div_mod j.isLt i.isLt
  simp only [FlatArray.get_ofFn, hlt, Nat.not_le.mpr hlt, if_true,
    if_false, hdiv, hmod]
  simpa [Nat.mul_comm] using raw_denotValB_semS_inv_get
    orc rho henv hinv hsab hNa hNb i j

/-! ## Raw agreement arms -/

/-- Exact-basis agreement for the inverse COB constructor. -/
theorem raw_arm_cob_inverse (orc : FFSOracleSem)
    (_hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {env : ValExpr}
    (hinfer : RawCobInferSubctx orc Gamma Psi env b1)
    (hb0 : Basis.BasisValid Gamma b0)
    (hb1 : Basis.BasisValid Gamma b1)
    (h : S.Cob Gamma Psi b1 env b0)
    (ih : RawMCobSubctx orc Gamma Psi b1 env b0) :
    RawMCobSubctx orc Gamma Psi b0 (.inv env) b1 := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa, sb, hsab, hNa, hNb⟩ :=
    hinfer hsub rho Delta' Gamma' sigma GammaV hle hc
  have hA := ih hsub rho Delta' Gamma' sigma GammaV hle hc
  unfold CobAgree at hA ⊢
  dsimp only at hA ⊢
  have hsof := S.Cob.sof_eq h
  rw [hsof] at hA hNa hNb
  obtain ⟨hTlen, a, ha, halen, hrows⟩ := hA
  set V := denotSpace sigma (Basis.sof b0)
  set S0 := (denotBasis sigma b1).atSpace V
  set T0 := (denotBasis sigma b0).atSpace V
  have hbS : IsListBasis V S0 := by
    have hb := denotBasis_atSpace_isListBasis sigma Gamma' b1
      (raw_basisValid_mono hb1 hle) hc.ctxWF_nl hc.envWF_nl
    rw [hsof] at hb
    exact hb
  have hbT : IsListBasis V T0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hb0 hle) hc.ctxWF_nl hc.envWF_nl
  obtain ⟨ainv, hval⟩ :
      ∃ ainv, denotValB_semS orc rho [] [] (.inv env) =
        .ok (.array ainv) := by
    rw [denotValB_semS.eq_25, ha]
    simp only [ValValSem.bindArray, hsab]
    have hshape : a.length =
        ValSpace.dof (orc rho [] []) sa * ValSpace.dof (orc rho [] []) sb := by
      simpa only [hNa, hNb] using halen
    rw [if_pos hshape]
    exact ⟨_, rfl⟩
  let M : Matrix (Fin S0.length) (Fin S0.length) ℝ :=
    denotAsMatrix S0.length S0.length a.get
  let bT : Module.Basis (Fin S0.length) ℝ V.carrier :=
    hbT.toBasis.reindex (finCongr hTlen)
  have hbT_apply (i : Fin S0.length) : bT i = T0.getD i.val 0 := by
    rw [List.getD_eq_getElem T0 0 (hTlen.symm ▸ i.isLt)]
    simp [bT, Module.Basis.reindex_apply, IsListBasis.toBasis_apply]
  have hbS_apply (i : Fin S0.length) :
      hbS.toBasis i = S0.getD i.val 0 := by
    simp [IsListBasis.toBasis_apply]
  have hmrows : ∀ j, hbS.toBasis j = ∑ i, M j i • bT i := by
    intro j
    rw [hbS_apply, hrows j]
    apply Finset.sum_congr rfl
    intro i _
    rw [hbT_apply]
    simp [M, denotAsMatrix, Nat.mul_comm S0.length j.val]
  have hrev := Basis.raw_svdPinv_reverse_rows hbS.toBasis bT M hmrows
  rw [hTlen]
  refine ⟨rfl, ainv, hval, ?_, ?_⟩
  · rw [denotValB_semS.eq_25, ha] at hval
    simp only [ValValSem.bindArray, hsab] at hval
    have hshape : a.length =
        ValSpace.dof (orc rho [] []) sa * ValSpace.dof (orc rho [] []) sb := by
      simpa only [hNa, hNb] using halen
    simp only [hshape, ↓reduceIte] at hval
    injection hval with hval
    injection hval with hval
    subst ainv
    simp [ValExpr.inferSpaceCtx, hsab, hNa, hNb]
  · intro j
    rw [← hbT_apply j, hrev j]
    apply Finset.sum_congr rfl
    intro i _
    rw [hbS_apply]
    congr 1
    rw [raw_denotValB_semS_inv_get
      orc rho ha hval hsab hNa hNb j i]

/-- Paired agreement and inference facts for the inverse constructor. -/
theorem raw_arm_cob_inverse_facts (orc : FFSOracleSem)
    (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {env : ValExpr}
    (hb0 : Basis.BasisValid Gamma b0)
    (hb1 : Basis.BasisValid Gamma b1)
    (h : S.Cob Gamma Psi b1 env b0)
    (ih : RawCobFactsSubctx orc Gamma Psi b1 env b0) :
    RawCobFactsSubctx orc Gamma Psi b0 (.inv env) b1 :=
  ⟨raw_arm_cob_inverse orc hspec ih.infer hb0 hb1 h ih.agree,
    raw_arm_cob_infer_inverse hb0 hb1 h ih.infer⟩

/-- Exact-basis agreement for dual coordinates relative to the standard
basis: the coordinate matrix is the transpose of the inverse matrix. -/
theorem raw_arm_cob_dual_std (orc : FFSOracleSem)
    (_hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 : Basis} {env : ValExpr}
    (hinfer : RawCobInferSubctx orc Gamma Psi env b0)
    (htof : Basis.tof b0 = .space (Basis.sof b0))
    (hbS : Basis.BasisValid Gamma (.dual b0))
    (hbT : Basis.BasisValid Gamma
      (Basis.std (Basis.tof (.dual b0))))
    (_h : S.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih : RawMCobSubctx orc Gamma Psi b0 env
      (Basis.std (Basis.tof b0))) :
    RawMCobSubctx orc Gamma Psi (.dual b0) (.vtrans (.inv env))
      (Basis.std (Basis.tof (.dual b0))) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  obtain ⟨sa, sb, hsab, hNa, hNb⟩ :=
    hinfer hsub rho Delta' Gamma' sigma GammaV hle hc
  have hA := ih hsub rho Delta' Gamma' sigma GammaV hle hc
  unfold CobAgree at hA ⊢
  dsimp only at hA ⊢
  obtain ⟨hTlen, a, ha, halen, hrows⟩ := hA
  set V := denotSpace sigma (Basis.sof b0)
  set S0 := (denotBasis sigma b0).atSpace V
  set T0 := (denotBasis sigma (Basis.std (Basis.tof b0))).atSpace V
  have hstddual := Basis.raw_std_tof_dual_eq_dual_std_tof
    (b := b0) htof
  have hsofstd :
      Basis.sof (Basis.std (Basis.tof b0)) = Basis.sof b0 := by
    rw [htof]
    exact Basis.sof_stdSpace _
  have hbT0 : Basis.BasisValid Gamma
      (Basis.std (Basis.tof b0)) := by
    exact (hstddual ▸ hbT).dual_inv
  have hSb : IsListBasis V S0 :=
    denotBasis_atSpace_isListBasis sigma Gamma' b0
      (raw_basisValid_mono hbS.dual_inv hle)
      hc.ctxWF_nl hc.envWF_nl
  have hTb : IsListBasis V T0 := by
    have hb := denotBasis_atSpace_isListBasis sigma Gamma'
      (Basis.std (Basis.tof b0)) (raw_basisValid_mono hbT0 hle)
      hc.ctxWF_nl hc.envWF_nl
    rw [hsofstd] at hb
    exact hb
  let M : Matrix (Fin S0.length) (Fin S0.length) ℝ :=
    denotAsMatrix S0.length S0.length a.get
  let bT : Module.Basis (Fin S0.length) ℝ V.carrier :=
    hTb.toBasis.reindex (finCongr hTlen)
  have hbT_apply (i : Fin S0.length) : bT i = T0.getD i.val 0 := by
    rw [List.getD_eq_getElem T0 0 (hTlen.symm ▸ i.isLt)]
    simp [bT, Module.Basis.reindex_apply, IsListBasis.toBasis_apply]
  have hbS_apply (i : Fin S0.length) :
      hSb.toBasis i = S0.getD i.val 0 := by
    simp [IsListBasis.toBasis_apply]
  have hmrows : ∀ j, hSb.toBasis j = ∑ i, M j i • bT i := by
    intro j
    rw [hbS_apply, hrows j]
    apply Finset.sum_congr rfl
    intro i _
    rw [hbT_apply]
    simp [M, denotAsMatrix, Nat.mul_comm S0.length j.val]
  have hmrowsD : ∀ j : Fin S0.length,
      S0.getD j.val 0 = ∑ i, M j i • T0.getD i.val 0 := by
    intro j
    rw [hrows j]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp [M, denotAsMatrix, Nat.mul_comm S0.length j.val]
  have hright : M * matrixSVDPinv M = 1 :=
    Basis.raw_mul_svdPinv_eq_one_of_rows hSb.toBasis bT M hmrows
  have hdual := IsListBasis.raw_dualVec_transpose_expansion
    hSb hTb hTlen M (matrixSVDPinv M) hmrowsD hright
  have hsrc :
      (denotBasis sigma (.dual b0)).atSpace (HSpace.dual V) =
        V.dualOfList S0 := by
    simp only [denotBasis]
    exact BasisDenot.atSpace_vecs_self _ _
  have htgt :
      (denotBasis sigma
        (Basis.std (Basis.tof (.dual b0)))).atSpace (HSpace.dual V) =
        V.dualOfList T0 := by
    rw [hstddual]
    simp only [denotBasis]
    rw [hsofstd]
    exact BasisDenot.atSpace_vecs_self _ _
  obtain ⟨ainv, hinv⟩ :
      ∃ ainv, denotValB_semS orc rho [] [] (.inv env) =
        .ok (.array ainv) := by
    rw [denotValB_semS.eq_25, ha]
    simp only [ValValSem.bindArray, hsab]
    have hshape : a.length =
        ValSpace.dof (orc rho [] []) sa * ValSpace.dof (orc rho [] []) sb := by
      simpa only [hNa, hNb] using halen
    rw [if_pos hshape]
    exact ⟨_, rfl⟩
  have hinvLen : ainv.length =
      ValSpace.dof (orc rho [] []) sb * ValSpace.dof (orc rho [] []) sa := by
    have hinv' := hinv
    rw [denotValB_semS.eq_25, ha] at hinv'
    simp only [ValValSem.bindArray, hsab] at hinv'
    split at hinv' <;> try contradiction
    injection hinv' with heq
    injection heq with heq
    subst ainv
    simp only [ValValSem.arrayOf, FlatArray.length_ofFn,
      ValExpr.inferSpaceCtx, hsab, ValSpace.dof_tprod]
  have hguard : ValueShape.tensor (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.inv env)) ainv := by
    simpa only [ValExpr.inferSpaceCtx, hsab, ValueShape.tensor] using hinvLen
  obtain ⟨w, hval⟩ :
      ∃ w, denotValB_semS orc rho [] [] (.vtrans (.inv env)) =
        .ok (.array w) := by
    rw [denotValB_semS.eq_11, hinv]
    simp only [ValValSem.bindArray, if_pos hguard]
    exact ⟨_, rfl⟩
  have hdof : ValSpace.dof (orc rho [] [])
      (ValExpr.inferSpaceCtx [] (.vtrans (.inv env))) =
        S0.length * S0.length := by
    simp only [ValExpr.inferSpaceCtx, hsab, ValSpace.dof_tprod, hNa, hNb]
  change
    ((denotBasis sigma
        (Basis.std (Basis.tof (.dual b0)))).atSpace (HSpace.dual V)).length =
        ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length ∧
      ∃ w : FlatArray,
        denotValB_semS orc rho [] [] (.vtrans (.inv env)) =
          .ok (.array w) ∧
        w.length =
          ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length *
          ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length ∧
        ∀ j : Fin
            ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).length,
          ((denotBasis sigma (.dual b0)).atSpace (HSpace.dual V)).getD
              j.val 0 =
            ∑ i : Fin
                ((denotBasis sigma (.dual b0)).atSpace
                  (HSpace.dual V)).length,
              w.get (j.val *
                ((denotBasis sigma (.dual b0)).atSpace
                  (HSpace.dual V)).length + i.val) •
              ((denotBasis sigma
                (Basis.std (Basis.tof (.dual b0)))).atSpace
                  (HSpace.dual V)).getD i.val 0
  rw [hsrc, htgt, HSpace.dualOfList_length, HSpace.dualOfList_length]
  refine ⟨hTlen, w, hval, ?_, ?_⟩
  · rw [denotValB_semS.eq_11, hinv] at hval
    simp only [ValValSem.bindArray, if_pos hguard] at hval
    injection hval with hval
    injection hval with hval
    subst w
    simp [hdof]
  · intro j
    rw [HSpace.raw_dualOfList_getD_eq_dualVec V S0 j.isLt, hdual j]
    apply Finset.sum_congr rfl
    intro i _
    rw [HSpace.raw_dualOfList_getD_eq_dualVec V T0
      (hTlen.symm ▸ i.isLt)]
    congr 1
    rw [raw_denotValB_semS_vtrans_inv_get
      orc rho ha hinv hval hsab hNa hNb j i]

/-- Paired agreement and inference facts for the dual-standard constructor. -/
theorem raw_arm_cob_dual_std_facts (orc : FFSOracleSem)
    (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 : Basis} {env : ValExpr}
    (htof : Basis.tof b0 = .space (Basis.sof b0))
    (hbS : Basis.BasisValid Gamma (.dual b0))
    (hbT : Basis.BasisValid Gamma
      (Basis.std (Basis.tof (.dual b0))))
    (h : S.Cob Gamma Psi b0 env (Basis.std (Basis.tof b0)))
    (ih : RawCobFactsSubctx orc Gamma Psi b0 env
      (Basis.std (Basis.tof b0))) :
    RawCobFactsSubctx orc Gamma Psi (.dual b0) (.vtrans (.inv env))
      (Basis.std (Basis.tof (.dual b0))) :=
  ⟨raw_arm_cob_dual_std orc hspec ih.infer htof hbS hbT h ih.agree,
    raw_arm_cob_infer_dual_std ih.infer⟩

end GLang
