import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyEmbed
import GLang.Proofs.Adequacy.Raw.RawImageCoordsFull
import GLang.Numerics.Spectral.BasisCanonicalImage
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobFFSInference

namespace GLang

open scoped BigOperators
open Basis (BasisValid)

namespace RawCobImageSVDs

private theorem rowMajor_lt {m n i j : Nat}
    (hi : i < m) (hj : j < n) : i * n + j < m * n := by
  calc
    i * n + j < i * n + n := Nat.add_lt_add_left hj _
    _ = (i + 1) * n := by ring
    _ <= m * n := Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr hi)

private theorem rowMajor_div_mod {n i j : Nat} (hj : j < n) :
    (i * n + j) / n = i ∧ (i * n + j) % n = j := by
  have h := RawSpaceFFS.rowMajor_div_mod (i := i) hj
  simpa only [Nat.add_comm, Nat.mul_comm] using h

private theorem finSum_congr_size {A : Type} [AddCommMonoid A]
    {m n : Nat} (h : m = n) (F : Nat → A) :
    (∑ i : Fin m, F i.val) = ∑ i : Fin n, F i.val := by
  subst n
  rfl

def imageMap {V0 V1 : HSpace}
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (K : Submodule ℝ V0.carrier)
    (w : K) : LinearMap.range f :=
  ⟨f (Subtype.val w), LinearMap.mem_range_self f _⟩

@[simp] theorem imageMap_zero {V0 V1 : HSpace}
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (K : Submodule ℝ V0.carrier) :
    imageMap f K 0 = 0 :=
  Subtype.ext (by simp [imageMap])

/-- Lift the ambient `U`/`V` column equation into the cokernel/range
subtypes used by the two concrete projected bases. -/
theorem lifted_canonical_rows
    {V0 V1 : HSpace} {S0 : List V0.carrier} {S1 : List V1.carrier}
    (hb0 : IsListBasis V0 S0) (hb1 : IsListBasis V1 S1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier)
    (rawU : List V0.carrier) (rawV : List V1.carrier)
    (hrawU : rawU = List.ofCoords S0
      (BasisSpectral.canonicalBlocks (hb0.coordMatrix hb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).U)
    (hrawV : rawV = List.ofCoords S1
      (BasisSpectral.canonicalBlocks (hb0.coordMatrix hb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).V)
    (hsubU : ∀ x ∈ rawU,
      x ∈ Submodule.orthRel V0.innerProduct (LinearMap.ker f))
    (hsubV : ∀ x ∈ rawV, x ∈ LinearMap.range f) :
    forall j : Fin (BasisSpectral.canonicalBlocks (hb0.coordMatrix hb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r,
      ((HSpace.liftToSubmodule
          (Submodule.orthRel V0.innerProduct (LinearMap.ker f)) rawU).map
        (imageMap f (Submodule.orthRel V0.innerProduct
          (LinearMap.ker f)))).getD j.val 0 =
        ∑ i : Fin (BasisSpectral.canonicalBlocks (hb0.coordMatrix hb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r,
          (BasisSpectral.standardImageRows (hb0.coordMatrix hb1 f)) j i •
            (HSpace.liftToSubmodule (LinearMap.range f) rawV).getD i.val 0 := by
  intro j
  let g := BasisSpectral.canonicalBlocks (hb0.coordMatrix hb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one
  let K0 := Submodule.orthRel V0.innerProduct (LinearMap.ker f)
  let K1 := LinearMap.range f
  let U := HSpace.liftToSubmodule K0 rawU
  let V := HSpace.liftToSubmodule K1 rawV
  have hrawULen : rawU.length = g.r := by
    rw [hrawU, List.ofCoords_length]
  have hrawVLen : rawV.length = g.r := by
    rw [hrawV, List.ofCoords_length]
  have hULen : U.length = g.r := by
    exact (HSpace.liftToSubmodule_length_of_subset K0 rawU hsubU).trans hrawULen
  have hVLen : V.length = g.r := by
    exact (HSpace.liftToSubmodule_length_of_subset K1 rawV hsubV).trans hrawVLen
  have hjU : j.val < U.length := hULen.symm ▸ j.isLt
  have hjRaw : j.val < rawU.length := hrawULen.symm ▸ j.isLt
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change (((U.map (imageMap f K0)).getD j.val 0 : K1) : V1.carrier) =
    ∑ i : Fin g.r, (BasisSpectral.standardImageRows (hb0.coordMatrix hb1 f)) j i • ((V.getD i.val 0 : K1) : V1.carrier)
  calc
    (((U.map (imageMap f K0)).getD j.val 0 : K1) : V1.carrier) =
        f ((U.getD j.val 0 : K0) : V0.carrier) := by
      have hjMap : j.val < (U.map (imageMap f K0)).length := by
        simpa using hjU
      rw [List.getD_eq_getElem _ _ hjMap, List.getD_eq_getElem _ _ hjU]
      simp [imageMap]
    _ = f (rawU.get ⟨j.val, hjRaw⟩) := by
      rw [List.getD_eq_getElem U 0 hjU]
      exact congrArg f
        (HSpace.liftToSubmodule_get_val_of_subset K0 rawU hsubU
          ⟨j.val, hjU⟩)
    _ = f ((List.ofCoords S0 g.U).get
        (Fin.cast (List.ofCoords_length S0 g.U).symm j)) := by
      congr 1
      exact List.get_of_eq hrawU ⟨j.val, hjRaw⟩
    _ = ∑ i : Fin g.r, (BasisSpectral.standardImageRows (hb0.coordMatrix hb1 f)) j i •
        (List.ofCoords S1 g.V).get
          (Fin.cast (List.ofCoords_length S1 g.V).symm i) := by
      exact BasisSpectral.map_canonicalU_column hb0 hb1 f j
    _ = ∑ i : Fin g.r, (BasisSpectral.standardImageRows (hb0.coordMatrix hb1 f)) j i •
        ((V.getD i.val 0 : K1) : V1.carrier) := by
      apply Fintype.sum_congr
      intro i
      congr 2
      have hiV : i.val < V.length := hVLen.symm ▸ i.isLt
      have hiRaw : i.val < rawV.length := hrawVLen.symm ▸ i.isLt
      rw [List.getD_eq_getElem V 0 hiV]
      calc
        (List.ofCoords S1 g.V).get
            (Fin.cast (List.ofCoords_length S1 g.V).symm i) =
            rawV.get ⟨i.val, hiRaw⟩ := by
          exact (List.get_of_eq hrawV ⟨i.val, hiRaw⟩).symm
        _ = ((V.get ⟨i.val, hiV⟩ : K1) : V1.carrier) := by
          exact (HSpace.liftToSubmodule_get_val_of_subset K1 rawV hsubV
            ⟨i.val, hiV⟩).symm

/-! ## The `image_svds` constructor -/

theorem imageSVDNumericalFacts_of_spec
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {e : Term} {leev : ValExpr} {svb : ValSpace}
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) leev (.space svb))
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) leev (.space svb)) :
    RawTermEmbed.RawMEmbedNumericalFactsSubctx orc Gamma Psi
      b0 b1 e (ValExpr.reshapBase leev svb) (.imageCoords svb leev)
      (.tprod
        (.ffs .cokernel svb (ValExpr.reshapBase leev svb))
        (.ffs .image svb (ValExpr.reshapBase leev svb))) := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  intro sa sb ae hinfer hb0 hb1 hd0 hd1 heval hmatrix
  have hblocks := RawTermEmbed.ffs_oracle_block_dims hspec hb0 hb1
    (RawTermEmbed.embedWitnessLin sigma b0 b1 e)
    heval hinfer
    ((hc.exprFinite (he.mono hsub).toOpStep).reshapBase
      (hc.typeFinite (he.mono hsub).toEvalT).space_inv) hd0 hd1 hmatrix
  change svb = .tprod sa sb at hinfer
  subst svb
  exact ⟨hblocks, rfl⟩

/-- Exact-basis agreement for canonical image-coordinate conversion. Standard
ambient bases supply identity metrics; the full signed conversion expresses
mapped canonical cokernel columns in the independently canonical image basis. -/
theorem raw_arm_cob_image_svds_of_numerical
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {e : Term} {leev : ValExpr} {s0 s1 : Space} {svb : ValSpace}
    (hbSrc : BasisValid Gamma
      (.image (.proj (.coker s0 s1 e) b0 b1)))
    (_hbTgt : BasisValid Gamma (.proj (.img s0 s1 e) b0 b1))
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (hb0 : Basis.isStd b0) (hb1 : Basis.isStd b1)
    (hsvb : S.Space Gamma Psi
      (Basis.sof (.tprod (.dual b0) b1)) svb)
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) leev
      (.space svb))
    (_ihSpace : RawMSpaceSubctx orc Gamma Psi
      (Basis.sof (.tprod (.dual b0) b1)) svb)
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) leev (.space svb))
    (hnum : RawTermEmbed.RawMEmbedNumericalFactsSubctx orc Gamma Psi
      b0 b1 e (ValExpr.reshapBase leev svb) (.imageCoords svb leev)
      (.tprod
        (.ffs .cokernel svb (ValExpr.reshapBase leev svb))
        (.ffs .image svb (ValExpr.reshapBase leev svb)))) :
    RawMCobSubctx orc Gamma Psi
      (.image (.proj (.coker s0 s1 e) b0 b1))
      (.reshap (.imageCoords svb leev)
        (.space (.tprod
          (.ffs .cokernel svb (ValExpr.reshapBase leev svb))
          (.ffs .image svb (ValExpr.reshapBase leev svb))))
        (.space (ValExpr.inferSpaceCtx [] (.imageCoords svb leev))))
      (.proj (.img s0 s1 e) b0 b1) := by
  subst s0
  subst s1
  change S.Space Gamma Psi
    (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)) svb at hsvb
  obtain ⟨sv0, sv1, rfl⟩ := hsvb.tprod_value_inv
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  ·
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
        (raw_basisValid_mono hb0v hle) hc.ctxWF_nl hc.envWF_nl
    have hlb1 : IsListBasis V1 S1 :=
      denotBasis_atSpace_isListBasis sigma Gamma' b1
        (raw_basisValid_mono hb1v hle) hc.ctxWF_nl hc.envWF_nl
    have horth0 := denotBasis_orthonormal_of_isStd sigma Gamma' b0
      (raw_basisValid_mono hb0v hle) hb0
    have horth1 := denotBasis_orthonormal_of_isStd sigma Gamma' b1
      (raw_basisValid_mono hb1v hle) hb1
    have hgram0 : IsListBasis.gram V0 S0 = 1 :=
      IsListBasis.gram_eq_one_of_orthonormal V0 S0 horth0
    have hgram1 : IsListBasis.gram V1 S1 = 1 :=
      IsListBasis.gram_eq_one_of_orthonormal V1 S1 horth1
    have hctx : RawCtxIncl ∅ Gamma Delta' Gamma' := by
      refine ⟨?_, hle⟩
      intro x s hx
      simp at hx
    have trE := ihTerm.trace hsub (Graded.CtxDisj.empty Gamma)
      rho Delta' Gamma' sigma GammaV hctx hc
    have hshapeE := trE.dims
    simp only [Basis.tof, Basis.sof, RawAgreeDimsAt] at hshapeE
    change ValSpace.shpOf (orc rho [] [])
        (.tprod sv0 sv1) =
      srcShp sigma [] (.tprod (.dual (Basis.sof b0)) (Basis.sof b1))
        at hshapeE
    rw [RawSpaceFFS.srcShp_tprod_dual] at hshapeE
    simp only [ValSpace.shpOf_tprod] at hshapeE
    have hdsv0 : ValSpace.dof (orc rho [] []) sv0 =
        Module.finrank ℝ V0.carrier := by
      injection hshapeE
    have hdsv1 : ValSpace.dof (orc rho [] []) sv1 =
        Module.finrank ℝ V1.carrier := by
      injection hshapeE with _ htail
      injection htail
    have hdshape := ihTerm.dof rfl hsub rho Delta' Gamma' sigma GammaV hle hc
    obtain ⟨sa, sb, hinfer⟩ := eq_tprod_of_shpOf_eq hdshape
    rw [hinfer] at hdshape
    have hfac := tprod_factor_dof_eq_of_shpOf_eq hdshape
    have hd0 : ValSpace.dof (orc rho [] []) sa = S0.length :=
      hfac.1.trans (hdsv0.trans hlb0.finrank_eq)
    have hd1 : ValSpace.dof (orc rho [] []) sb = S1.length :=
      hfac.2.trans (hdsv1.trans hlb1.finrank_eq)
    obtain ⟨ae, heval, haelen, hM⟩ :=
      RawTermEmbed.trace_witness_matrix hlb0 hlb1 trE
    have hd0' : ValSpace.dof (orc rho [] []) sv0 = S0.length :=
      hdsv0.trans hlb0.finrank_eq
    have hd1' : ValSpace.dof (orc rho [] []) sv1 = S1.length :=
      hdsv1.trans hlb1.finrank_eq
    have hevalR := denotValB_semS_reshap_spaces_ok orc rho [] [] leev
      (.tprod sv0 sv1) (.tprod sv0 sv1) ae heval
      (by simpa only [ValSpace.dof_tprod, hd0', hd1'] using haelen) rfl
    obtain ⟨hblocks, _houtputShape⟩ :=
      hnum hsub rho Delta' Gamma' sigma GammaV hle hc
        rfl hlb0 hlb1 hd0' hd1' hevalR hM
    have hcoker : orc rho [] [] .cokernel (.tprod sv0 sv1)
        (ValExpr.reshapBase leev (.tprod sv0 sv1)) =
        (hlb0.coordMatrix hlb1 f).rank := hblocks.2.1
    have himage : orc rho [] [] .image (.tprod sv0 sv1)
        (ValExpr.reshapBase leev (.tprod sv0 sv1)) =
        (hlb0.coordMatrix hlb1 f).rank := hblocks.2.2.1
    obtain ⟨out, hout, houtLen, houtGet⟩ :=
      RawImageCoords.eval orc rho sv0 sv1 leev S0.length S1.length
        (hlb0.coordMatrix hlb1 f) ae hd0' hd1' heval haelen hM hcoker himage
    have houtSource : out.length = ValSpace.dof (orc rho [] [])
        (ValExpr.inferSpaceCtx [] (ValExpr.imageCoords (.tprod sv0 sv1) leev)) := by
      rw [ValExpr.imageCoords_inferSpaceCtx, ValSpace.dof_tprod,
        ValSpace.dof_ffs, ValSpace.dof_ffs, hcoker, himage, houtLen]
    have hreshape := denotValB_semS_reshap_spaces_ok orc rho [] []
      (ValExpr.imageCoords (.tprod sv0 sv1) leev)
      (.tprod
        (.ffs .cokernel (.tprod sv0 sv1) (ValExpr.reshapBase leev (.tprod sv0 sv1)))
        (.ffs .image (.tprod sv0 sv1) (ValExpr.reshapBase leev (.tprod sv0 sv1))))
      (ValExpr.inferSpaceCtx [] (ValExpr.imageCoords (.tprod sv0 sv1) leev))
      out hout houtSource rfl
    let K0 : Submodule ℝ V0.carrier :=
      Submodule.orthRel V0.innerProduct (LinearMap.ker f)
    let K1 : Submodule ℝ V1.carrier := LinearMap.range f
    let rawU : List V0.carrier := BasisFSV.fsvLeft V0 V1 f
      (fun mu => decide (mu ≠ 0)) S0 S1
    let rawV : List V1.carrier := BasisFSV.fsvRight V0 V1 f
      (fun mu => decide (mu ≠ 0)) S0 S1
    let U := HSpace.liftToSubmodule K0 rawU
    let V := HSpace.liftToSubmodule K1 rawV
    have hrawU : rawU = List.ofCoords S0
        (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).U := by
      calc
        rawU = List.ofCoords S0 (hlb0.canonical hlb1 f).U :=
          BasisFSV.fsvLeft_eq_canonicalU hlb0 hlb1 f
        _ = List.ofCoords S0
            (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).U := by
          exact congrArg (fun g : BasisSpectral.CanonicalBlocks S0.length S1.length => List.ofCoords S0 g.U)
            (BasisSpectral.canonicalBlocks_congr _ hlb0.gram_posDef hlb1.gram_posDef
              Matrix.PosDef.one Matrix.PosDef.one hgram0 hgram1)
    have hrawV : rawV = List.ofCoords S1
        (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).V := by
      calc
        rawV = List.ofCoords S1 (hlb0.canonical hlb1 f).V :=
          BasisFSV.fsvRight_eq_canonicalV hlb0 hlb1 f
        _ = List.ofCoords S1
            (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).V := by
          exact congrArg (fun g : BasisSpectral.CanonicalBlocks S0.length S1.length => List.ofCoords S1 g.V)
            (BasisSpectral.canonicalBlocks_congr _ hlb0.gram_posDef hlb1.gram_posDef
              Matrix.PosDef.one Matrix.PosDef.one hgram0 hgram1)
    have hsubU : ∀ x ∈ rawU, x ∈ K0 := by
      exact BasisFSV.fsvLeft_subset_coker V0 V1 f S0 S1
    have hsubV : ∀ x ∈ rawV, x ∈ K1 := by
      exact BasisFSV.fsvRight_subset_range V0 V1 f S0 S1
    have hsource :
        (denotBasis sigma
          (.image (.proj
            (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1))).atSpace
          (HSpace.ofSubmodule V1 K1) =
        U.map (imageMap f K0) := by
      simp [V0, V1, S0, S1, f, K0, K1, rawU, U, imageMap,
        denotSpace, denotSpaceAux, denotTerm, denotBasis,
        Basis.sof, BasisDenot.atSpace_vecs_self]
    have htarget :
        (denotBasis sigma
          (.proj (.img (Basis.sof b0) (Basis.sof b1) e) b0 b1)).atSpace
          (HSpace.ofSubmodule V1 K1) = V := by
      simp [V0, V1, S0, S1, f, K1, rawV, V, denotSpace,
        denotTerm, denotBasis, Basis.sof, BasisDenot.atSpace_vecs_self]
    have hULen : U.length = (BasisSpectral.canonicalBlocks
        (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r := by
      exact (HSpace.liftToSubmodule_length_of_subset K0 rawU hsubU).trans
        (by rw [hrawU, List.ofCoords_length])
    have hVLen : V.length = (BasisSpectral.canonicalBlocks
        (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r := by
      exact (HSpace.liftToSubmodule_length_of_subset K1 rawV hsubV).trans
        (by rw [hrawV, List.ofCoords_length])
    unfold CobAgree
    dsimp only
    simp only [Basis.sof, denotSpace, denotSpaceAux]
    simp only [V0, V1, f, K0, K1, hsource, htarget]
    have hSourceLen : (U.map (imageMap f K0)).length =
        (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r := by
      simpa using hULen
    have hSourceBasisLen :
        ((denotBasis sigma
          (.image (.proj
            (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1))).atSpace
          (HSpace.ofSubmodule V1 K1)).length =
            (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r :=
      (congrArg List.length hsource).trans hSourceLen
    refine ⟨?_, out, hreshape, ?_, ?_⟩
    · exact hVLen.trans hSourceLen.symm
    · rw [houtLen, hSourceLen]
      rfl
    · intro j
      have hNExact :
          (BasisDenot.atSpace
            ((denotSpaceAux sigma [] (Basis.sof b1)).ofSubmodule
              (DVal.asLinMap
                (denotSpaceAux sigma [] (Basis.sof b0))
                (denotSpaceAux sigma [] (Basis.sof b1))
                (denotTermAux sigma [] e)).range)
            (denotBasis sigma
              (.image (.proj
                (.coker (Basis.sof b0) (Basis.sof b1) e) b0 b1)))).length =
            (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r := by
        simpa only [V0, V1, f, K1, denotSpace, denotTerm] using
          hSourceBasisLen
      let j' : Fin (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r :=
        Fin.cast hNExact j
      have hrow := lifted_canonical_rows hlb0 hlb1 f rawU rawV
        hrawU hrawV hsubU hsubV j'
      change (U.map (imageMap f K0)).getD j.val 0 = _
      rw [hSourceLen]
      have hrow' :
          (U.map (imageMap f K0)).getD j.val 0 =
            ∑ i : Fin (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r,
              out.get (j.val *
                (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r + i.val) •
                V.getD i.val 0 := by
        calc
          (U.map (imageMap f K0)).getD j.val 0 =
              (U.map (imageMap f K0)).getD j'.val 0 := rfl
          _ = ∑ i : Fin (BasisSpectral.canonicalBlocks
                (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r,
                (BasisSpectral.standardImageRows (hlb0.coordMatrix hlb1 f)) j' i •
                  V.getD i.val 0 := by
            simpa only [U, V, K0, K1] using hrow
          _ = ∑ i : Fin (BasisSpectral.canonicalBlocks
                (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r,
                out.get (j.val *
                  (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r + i.val) •
                    V.getD i.val 0 := by
            apply Fintype.sum_congr
            intro i
            rw [← houtGet j' i]
            rfl
      exact hrow'.trans
        (finSum_congr_size hNExact (fun i =>
          out.get (j.val *
            (BasisSpectral.canonicalBlocks (hlb0.coordMatrix hlb1 f) 1 1 Matrix.PosDef.one Matrix.PosDef.one).r + i) •
              V.getD i 0)).symm

/-- Backwards-compatible spelling: a global `OracleSpec` constructs the
local packet and then invokes the assumption-free algebraic core. -/
theorem raw_arm_cob_image_svds
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {e : Term} {leev : ValExpr} {s0 s1 : Space} {svb : ValSpace}
    (hbSrc : BasisValid Gamma
      (.image (.proj (.coker s0 s1 e) b0 b1)))
    (hbTgt : BasisValid Gamma (.proj (.img s0 s1 e) b0 b1))
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (hb0 : Basis.isStd b0) (hb1 : Basis.isStd b1)
    (hsvb : S.Space Gamma Psi
      (Basis.sof (.tprod (.dual b0) b1)) svb)
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) leev
      (.space svb))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi
      (Basis.sof (.tprod (.dual b0) b1)) svb)
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) leev (.space svb)) :
    RawMCobSubctx orc Gamma Psi
      (.image (.proj (.coker s0 s1 e) b0 b1))
      (.reshap (.imageCoords svb leev)
        (.space (.tprod
          (.ffs .cokernel svb (ValExpr.reshapBase leev svb))
          (.ffs .image svb (ValExpr.reshapBase leev svb))))
        (.space (ValExpr.inferSpaceCtx [] (.imageCoords svb leev))))
      (.proj (.img s0 s1 e) b0 b1) :=
  raw_arm_cob_image_svds_of_numerical hbSrc hbTgt hs0 hs1 hb0 hb1
    hsvb he ihSpace ihTerm (imageSVDNumericalFacts_of_spec hspec he ihTerm)

/-- Paired agreement/inference payload consumed by the direct five-way
recursor at `S.Cob.image_svds`. -/
theorem raw_arm_cob_image_svds_facts
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {e : Term} {leev : ValExpr} {s0 s1 : Space} {svb : ValSpace}
    (hbSrc : BasisValid Gamma
      (.image (.proj (.coker s0 s1 e) b0 b1)))
    (hbTgt : BasisValid Gamma (.proj (.img s0 s1 e) b0 b1))
    (hs0 : Basis.sof b0 = s0) (hs1 : Basis.sof b1 = s1)
    (hb0 : Basis.isStd b0) (hb1 : Basis.isStd b1)
    (hsvb : S.Space Gamma Psi
      (Basis.sof (.tprod (.dual b0) b1)) svb)
    (he : S.Term ∅ Gamma Psi e (.tprod (.dual b0) b1) leev
      (.space svb))
    (ihSpace : RawMSpaceSubctx orc Gamma Psi
      (Basis.sof (.tprod (.dual b0) b1)) svb)
    (ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi e
      (.tprod (.dual b0) b1) leev (.space svb)) :
    RawCobFactsSubctx orc Gamma Psi
      (.image (.proj (.coker s0 s1 e) b0 b1))
      (.reshap (.imageCoords svb leev)
        (.space (.tprod
          (.ffs .cokernel svb (ValExpr.reshapBase leev svb))
          (.ffs .image svb (ValExpr.reshapBase leev svb))))
        (.space (ValExpr.inferSpaceCtx [] (.imageCoords svb leev))))
      (.proj (.img s0 s1 e) b0 b1) :=
  ⟨raw_arm_cob_image_svds hspec hbSrc hbTgt hs0 hs1 hb0 hb1
      hsvb he ihSpace ihTerm,
    raw_arm_cob_infer_image_svds hspec hbSrc hbTgt hs0 hs1 hb0 hb1
      hsvb he ihSpace ihTerm⟩

end RawCobImageSVDs

end GLang
