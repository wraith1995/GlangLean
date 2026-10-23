import GLang.Proofs.Adequacy.Raw.Conversion.RawCobAdequacyCore
import GLang.Proofs.Adequacy.Foundations.AgreeBasics
import GLang.Proofs.Adequacy.Raw.Terms.RawTermsRREFLexInd
import GLang.Proofs.Adequacy.Raw.Terms.RawTermsRREFZero

/-!
# RREF boundary for raw change-of-basis adequacy

The value-level RREF implementation is connected to the source language's
greedy `HSpace.lexInd` basis selection by the proved RREF/LexInd contract.
Both that coordinate correspondence and the complete semantic
change-of-basis arm below follow from the existing decomposition fields.

The companion `inferSpaceCtx`/matrix-shape conclusion for `terms_rref` is
also constructive in `RawCobAdequacyCore.raw_arm_cob_infer_terms_rref`.
-/

namespace GLang

open scoped BigOperators
open Basis (BasisValid)

/-- The numerical correspondence required by the terms/RREF arm: the
standard row-reduction implementation selects exactly the columns selected
by the source semantics' left-to-right independent-subsequence operation. -/
theorem standardRREFLexInd : StandardRREFLexIndContract :=
  standardRREFLexInd_proved

private theorem Basis.rref_ne_frame_of_tof_space {b : Basis}
    (htof : Basis.tof b = .space (Basis.sof b)) :
    ∀ c0 c1, b ≠ .frame c0 c1 := by
  intro c0 c1 h
  subst b
  simp [Basis.tof] at htof

/-- Neither endpoint of a strengthened COB derivation is a dependent frame. -/
private theorem S.Cob.rref_ne_frame :
    ∀ {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {env : ValExpr},
      S.Cob Gamma Psi b0 env b1 →
        (∀ c0 c1, b0 ≠ .frame c0 c1) ∧ (∀ c0 c1, b1 ≠ .frame c0 c1)
  | _, _, _, _, _, .inverse _ _ h =>
      ⟨(S.Cob.rref_ne_frame h).2, (S.Cob.rref_ne_frame h).1⟩
  | _, _, _, _, _, .trans _ _ h0 h1 _ =>
      ⟨(S.Cob.rref_ne_frame h0).1, (S.Cob.rref_ne_frame h1).2⟩
  | _, _, _, _, _, .tprod .. =>
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  | _, _, _, _, _, .dsum .. =>
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  | _, _, _, _, _, .dual_std .. =>
      ⟨(fun _ _ h => by cases h),
        (fun _ _ h => by simp [Basis.tof, Basis.std, Basis.sof, Basis.stdSpace] at h)⟩
  | _, _, _, _, _, .image .. =>
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  | _, _, _, _, _, .image_svds .. =>
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  | _, _, _, _, _, .proj_ker_coker .. =>
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  | _, _, _, _, _, .proj_img_coimg .. =>
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  | _, _, _, _, _, .terms_rref _ _ hbb _ _ =>
      ⟨(S.Cob.rref_ne_frame hbb).1, (fun _ _ h => by cases h)⟩
  | _, _, _, _, _, .refl _ htof _ =>
      ⟨Basis.rref_ne_frame_of_tof_space htof,
        Basis.rref_ne_frame_of_tof_space htof⟩
  | _, _, _, _, _, .proj_ker_coker_cod .. =>
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  | _, _, _, _, _, .proj_img_coimg_dom .. =>
      ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h)⟩

/-- Evaluating `RREFRep` on the term-coordinate chain and an existing COB
matrix yields the COB from the source basis to the greedily selected term
basis.  The proof consumes the proved numerical `standardRREFLexInd` correspondence;
the term-row coordinates, flat-array layout, zero-dimensional case, and
change-of-basis equation are all derived constructively. -/
theorem raw_arm_cob_terms_rref_boundary
    {orc : FFSOracleSem}
    {Gamma : NLCtx} {Psi : EvalCtx}
    {b b' : Basis} {e : Term} {es : List Term}
    {env0 env1 : ValExpr} {sv : ValSpace} {tauV : ValTy}
    (_hbS : BasisValid Gamma b)
    (_hbT : BasisValid Gamma (.terms (Basis.sof b') (e :: es) b'))
    (_hbb : S.Cob Gamma Psi b env1 b')
    (_hch : S.Term ∅ Gamma Psi (.dsumChain e es)
      (.dsumChain b' es.length) env0 tauV)
    (_hsv : S.Space Gamma Psi (Basis.sof b) sv)
    (_ihCob : RawCobFactsSubctx orc Gamma Psi b env1 b')
    (_ihTerm : RawTermDofFactsSubctx orc ∅ Gamma Psi (.dsumChain e es)
      (.dsumChain b' es.length) env0 tauV)
    (_ihSpace : RawMSpaceSubctx orc Gamma Psi (Basis.sof b) sv) :
    RawMCobSubctx orc Gamma Psi b
      (ValExpr.reshapBase
        (.rrefRep env0
          (ValExpr.reshapBase env1 (.tprod sv sv)))
        (.tprod sv sv))
      (.terms (Basis.sof b') (e :: es) b') := by
  intro Psi' hsub rho Delta' Gamma' sigma GammaV hle hc
  have hOld := _ihCob.agree hsub rho Delta' Gamma' sigma GammaV hle hc
  have hIncl : RawCtxIncl ∅ Gamma Delta' Gamma' := by
    refine ⟨?_, hle⟩
    intro x s hx
    cases hx
  have hTrace := _ihTerm.trace hsub (Graded.CtxDisj.empty Gamma)
    rho Delta' Gamma' sigma GammaV hIncl hc
  obtain ⟨hb', _hsof', _hsvalid, hterms⟩ := _hbT.terms_inv
  have hnf' := (S.Cob.rref_ne_frame _hbb).2
  have htof' : Basis.tof b' = .space (Basis.sof b') := by
    cases b' with
    | frame c0 c1 => exact False.elim (hnf' c0 c1 rfl)
    | empty | one | dual | dsum | tprod | proj | image | terms => rfl
  have htofChain := Basis.tof_dsumChain htof' es.length
  have htyChain := _hch.ty
  rw [htofChain] at htyChain
  obtain ⟨svChain, rfl, _hspaceChain⟩ := S.Ty.source_space_inv htyChain
  obtain ⟨out0, h0, hA0⟩ := hTrace.result
  rw [htofChain] at hA0
  cases out0 with
  | fn T f => simpa only [RawAgree] using hA0
  | array a0 =>
      simp only [RawAgree] at hA0
      have hChainLen := LegacyAgree.length hA0
      have hChainCoords := LegacyAgree.coords hA0
      have hsof : Basis.sof b = Basis.sof b' := S.Cob.sof_eq _hbb
      unfold CobAgree at hOld
      dsimp only at hOld
      rw [hsof] at hOld
      obtain ⟨hBlen, a1, h1, ha1len, hSource⟩ := hOld
      let V := denotSpace sigma (Basis.sof b')
      let B := (denotBasis sigma b').atSpace V
      let S0 := (denotBasis sigma b).atSpace V
      let xs := (e :: es).map (fun t => (denotTerm sigma t).atSpace V)
      have hBasis : IsListBasis V B := by
        exact denotBasis_atSpace_isListBasis sigma Gamma' b'
          (raw_basisValid_mono hb' hle) hc.ctxWF_nl hc.envWF_nl
      let x : Nat → V.carrier := fun j =>
        (denotTerm sigma ((e :: es).getD j default)).atSpace V
      have hcomponents : ∀ j : Fin (es.length + 1),
          denotTerm sigma ((e :: es).getD j.val default) =
            .hil ⟨V, x j.val⟩ := by
        intro j
        have hj : j.val < (e :: es).length := by
          simpa only [List.length_cons] using j.isLt
        have hmem : (e :: es)[j.val] ∈ e :: es := List.getElem_mem hj
        obtain ⟨ht⟩ := hasType_mono_nl_raw
          (hterms (e :: es)[j.val] hmem) hle
        have hsnd := (soundness ht hc.ctxWF_nl hc.envWF_nl).1
        change (denotTerm sigma (e :: es)[j.val]).matchesShape (.hil V) at hsnd
        obtain ⟨z, hz⟩ := DVal.matchesShape_hil_eq hsnd
        rw [List.getD_eq_getElem (e :: es) default hj]
        dsimp only [x]
        rw [List.getD_eq_getElem (e :: es) default hj]
        rw [hz, DVal.atSpace_hil_self]
      have hChainDen := denotTerm_dsumChain_eq_hil_dsumPow
        sigma V e es x hcomponents
      change ((denotBasis sigma (Basis.dsumChain b' es.length)).atSpace
          (denotSpace sigma (Basis.sof (Basis.dsumChain b' es.length)))).length =
            ValSpace.dof (orc rho [] []) svChain ∧
        a0.length = ValSpace.dof (orc rho [] []) svChain at hChainLen
      change (denotTerm sigma (Term.dsumChain e es)).atSpace
          (denotSpace sigma (Basis.sof (Basis.dsumChain b' es.length))) =
        ∑ i : Fin (ValSpace.dof (orc rho [] []) svChain),
          a0.get i.val •
            ((denotBasis sigma (Basis.dsumChain b' es.length)).atSpace
              (denotSpace sigma
                (Basis.sof (Basis.dsumChain b' es.length)))).getD i.val 0
          at hChainCoords
      rw [Basis.sof_dsumChain, denotSpace_dsumChain,
        denotBasis_dsumChain_at_dsumPow] at hChainLen hChainCoords
      rw [hChainDen, DVal.atSpace_hil_self] at hChainCoords
      rw [Fin.raw_sum_cast_of_eq hChainLen.1.symm] at hChainCoords
      simp only [Fin.val_cast] at hChainCoords
      have hRowsNat := HSpace.dsumPow_coordinates V B es.length
        (fun j => x j.val) a0.get hChainCoords
      have hTerms : ∀ j : Fin xs.length,
          xs.get j = ∑ i : Fin B.length,
            a0.get (j.val * B.length + i.val) • B.get i := by
        intro j
        have hj : j.val < (e :: es).length := by
          simpa only [xs, List.length_map, List.length_cons] using j.isLt
        let q : Fin (es.length + 1) := ⟨j.val, by simpa using hj⟩
        have hr := hRowsNat q
        dsimp only [x] at hr
        rw [List.getD_eq_getElem (e :: es) default hj] at hr
        have hxj : xs.get j =
            (denotTerm sigma (e :: es)[j.val]).atSpace V := by
          change (List.map (fun t => (denotTerm sigma t).atSpace V)
            (e :: es)).get _ = _
          rw [List.get_eq_getElem, List.getElem_map]
        rw [hxj, hr]
        apply Finset.sum_congr rfl
        intro i _
        rw [List.getD_eq_get B 0 i]
      change B.length = S0.length at hBlen
      rw [← hBlen] at ha1len hSource
      have hSourceMatrix : ∀ j : Fin B.length,
          S0.getD j.val 0 = ∑ r : Fin B.length,
            denotAsMatrix B.length B.length a1.get j r •
              B.getD r.val 0 := by
        intro j
        simpa only [denotAsMatrix, Nat.mul_comm B.length j.val] using hSource j
      have hMatrix := termsRREFRepMatrix_cob_of_coordinates
        (standardRREFLexInd_implies_coordinate standardRREFLexInd)
        V B S0 xs hBasis a0.get a1.get hSourceMatrix hTerms
      dsimp only at hMatrix
      have hTargetEq :
          (denotBasis sigma
              (.terms (Basis.sof b') (e :: es) b')).atSpace V =
            V.lexInd (xs ++ B) := by
        dsimp only [V, xs, B]
        simp only [denotBasis]
        rw [BasisDenot.atSpace_vecs_self]
      obtain ⟨_hSourceBasis, hSdim⟩ := raw_cob_basis_length orc _hbS
        _ihSpace hsub hle hc
      rw [hsof] at hSdim
      change S0.length = ValSpace.dof (orc rho [] []) sv at hSdim
      have hBdim : B.length = ValSpace.dof (orc rho [] []) sv :=
        hBlen.trans hSdim
      have ha0len : a0.length = xs.length * B.length := by
        calc
          a0.length = ValSpace.dof (orc rho [] []) svChain := hChainLen.2
          _ = (V.dsumPowBasis B es.length).length := hChainLen.1.symm
          _ = xs.length * B.length := by
            simp only [HSpace.dsumPowBasis_length, xs, List.length_map,
              List.length_cons]
      unfold CobAgree
      dsimp only
      rw [hsof]
      change ((denotBasis sigma
          (.terms (Basis.sof b') (e :: es) b')).atSpace V).length =
            S0.length ∧ _
      rw [hTargetEq, ← hBlen]
      by_cases hzero : B.length = 0
      · have hsv0 : ValSpace.dof (orc rho [] []) sv = 0 := hBdim.symm.trans hzero
        have ha00 : a0.length = 0 := by rw [ha0len, hzero, Nat.mul_zero]
        have ha10 : a1.length = 0 := by rw [ha1len, hzero, Nat.zero_mul]
        have hout := denotValB_semS_termsRREFRep_zero_ok orc rho
          h0 h1 hsv0 ha00 ha10
        refine ⟨?_, FlatArray.ofFn 0
          (termsRREFRepDenot 0 0 a0.get a1.get), hout, ?_, ?_⟩
        · simpa only [hzero] using hMatrix.1
        · simp only [FlatArray.length_ofFn, hzero, Nat.zero_mul]
        · intro j
          exact Fin.elim0 (hzero ▸ j)
      · have hpos : 0 < B.length := Nat.pos_of_ne_zero hzero
        have hsvN : ValSpace.dof (orc rho [] []) sv = B.length := hBdim.symm
        have hout := denotValB_semS_termsRREFRep_ok orc rho
          h0 h1 hsvN ha0len ha1len hpos
        refine ⟨hMatrix.1, FlatArray.ofFn (B.length * B.length)
          (termsRREFRepDenot B.length xs.length a0.get a1.get), hout,
          FlatArray.length_ofFn _ _, ?_⟩
        intro j
        rw [hMatrix.2 j]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        rw [FlatArray.get_ofFn_lt _ _ _
          (Nat.raw_rowMajor_lt j.isLt i.isLt)]
        exact (termsRREFRepDenot_entry a0.get a1.get j i).symm

end GLang
