import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCob
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyEmbed

/-! Partial canonical fundamental-space evaluation and inclusion coordinates. -/
namespace GLang.PartialAdequacy
open scoped TensorProduct
open PartialValueEval

variable {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
  {Γ : List ValTy} {Δ : List ValValSem}

theorem eval_canonicalFSV {p : ValFFSProp} {e g h : ValExpr}
    {a ag ah : FlatArray} {sa sb : ValSpace} {m n : Nat}
    {r : ValueCanonicalFSV.ResultMatrix}
    (he : denotValB_partial orc ρ Γ Δ e = .ok (.array a))
    (hg : denotValB_partial orc ρ Γ Δ g = .ok (.array ag))
    (hh : denotValB_partial orc ρ Γ Δ h = .ok (.array ah))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod sa sb)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok m)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok n)
    (hgd : ∃ k, (ValExpr.inferSpaceCtx Γ g).dofPartial (orc ρ Γ Δ) = .ok k)
    (hhd : ∃ k, (ValExpr.inferSpaceCtx Γ h).dofPartial (orc ρ Γ Δ) = .ok k)
    (hout : (ValExpr.inferSpaceCtx Γ (.canonicalFSV p e g h)).dofPartial
      (orc ρ Γ Δ) = .ok (r.rows*r.cols))
    (hleaf : ValueCanonicalFSV.eval p m n a ag ah = .ok r) :
    denotValB_partial orc ρ Γ Δ (.canonicalFSV p e g h) = .ok (.array r.flatten) := by
  have hab := dof_tprod_ok ha hb
  rw [denotValB_partial_canonicalFSV]
  rw [guard_ok (by
    intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨_,hinfer ▸ hab⟩
    · exact hgd
    · exact hhd
    · exact ⟨_,hout⟩)]
  simp only [he,hg,hh,ValValSem.bindArrays3,ValValSem.bindArray,hinfer,
    dof_numbers _ _ _ ha,dof_numbers _ _ _ hb,hleaf,dof_numbers _ _ _ hout,if_true]

theorem eval_transpose {e : ValExpr} {sa sb : ValSpace}
    {r : ValueCanonicalFSV.ResultMatrix}
    (he : denotValB_partial orc ρ Γ Δ e = .ok (.array r.flatten))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod sa sb)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok r.rows)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok r.cols) :
    ∃ out, denotValB_partial orc ρ Γ Δ (.vtrans e) = .ok (.array out) ∧
      out.length = r.cols*r.rows ∧
      ∀ (j : Fin r.cols) (i : Fin r.rows),
        out.get (j.val*r.rows+i.val) = r.data i j := by
  have hab := dof_tprod_ok ha hb
  have hba := dof_tprod_ok hb ha
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx,hinfer]
  rw [guard_ok (by
    intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨_,hab⟩
    · exact ⟨_,hba⟩)]
  have hshape : ValueShape.tensor (numbers (orc ρ Γ Δ)) (.tprod sa sb) r.flatten := by
    simp [ValueShape.tensor,ValueCanonicalFSV.ResultMatrix.flatten,
      dof_numbers _ _ _ ha,dof_numbers _ _ _ hb]
  simp only [he,ValValSem.bindArray,if_pos hshape,dof_numbers _ _ _ ha,
    dof_numbers _ _ _ hb,dof_numbers _ _ _ hba,ValValSem.arrayOf]
  refine ⟨_,rfl,FlatArray.length_ofFn _ _,?_⟩
  intro j i
  have hlt : j.val*r.rows+i.val < r.cols*r.rows := by nlinarith [j.isLt,i.isLt]
  rw [FlatArray.get_ofFn_lt _ _ _ hlt,if_neg (Nat.not_le.mpr hlt)]
  obtain ⟨hdiv,hmod⟩ := RawSpaceFFS.rowMajor_div_mod (i := j.val) i.isLt
  have hdiv' : (j.val*r.rows+i.val)/r.rows = j.val := by
    simpa only [Nat.add_comm,Nat.mul_comm] using hdiv
  have hmod' : (j.val*r.rows+i.val)%r.rows = i.val := by
    simpa only [Nat.add_comm,Nat.mul_comm] using hmod
  rw [hdiv',hmod']
  exact r.flatten_get i j

theorem canonical_leaf_dimensions {p : ValFFSProp} {m n : Nat}
    {a ag ah : FlatArray} {r : ValueCanonicalFSV.ResultMatrix}
    (hleaf : ValueCanonicalFSV.eval p m n a ag ah = .ok r) :
    r.rows = p.ambient m n ∧
      r.cols = ffsDim p [m,n] (denotAsMatrix m n a.get).rank := by
  obtain ⟨hs,hg,hh⟩ := ValueCanonicalFSV.eval_success_valid p m n a ag ah r hleaf
  have heq := ValueCanonicalFSV.eval_ok p m n a ag ah hs hg hh
  have hr := Except.ok.inj (hleaf.symm.trans heq)
  rw [hr]
  cases p <;> simp [ValueCanonicalFSV.select, ValFFSProp.ambient, ffsDim, Matrix.rank_transpose]

theorem canonical_dimensions {p : ValFFSProp} {e : ValExpr}
    {a ag ah : FlatArray} {sa sb : ValSpace} {m n : Nat}
    {r : ValueCanonicalFSV.ResultMatrix}
    (he : denotValB_partial PartialDirectOracle.oracle ρ Γ Δ e = .ok (.array a))
    (ha : sa.dofPartial (PartialDirectOracle.oracle ρ Γ Δ) = .ok m)
    (hb : sb.dofPartial (PartialDirectOracle.oracle ρ Γ Δ) = .ok n)
    (hleaf : ValueCanonicalFSV.eval p m n a ag ah = .ok r)
    (hf : ValueQueryDependencies.Finite (.space Γ (.ffs p (.tprod sa sb) e))) :
    (p.ambient sa sb).dofPartial (PartialDirectOracle.oracle ρ Γ Δ) = .ok r.rows ∧
    ValSpace.dofPartial (PartialDirectOracle.oracle ρ Γ Δ)
      (.ffs p (.tprod sa sb) e) = .ok r.cols := by
  have hdim := canonical_leaf_dimensions hleaf
  have hlen := (ValueCanonicalFSV.eval_success_valid p m n a ag ah r hleaf).1.1
  have hparent : ValSpace.shpOfPartial (PartialDirectOracle.oracle ρ Γ Δ) (.tprod sa sb) =
      .ok [m,n] := by
    rw [ValSpace.shpOfPartial,ha]
    simp [hb,bind,Except.bind,pure,Except.pure]
  have hquery := PartialDirectLocality.oracle_matrix ρ Γ Δ p (.tprod sa sb) e m n a
    hf hparent he hlen
  constructor
  · rw [hdim.1]
    cases p <;> simpa only [ValFFSProp.ambient] using (by first | exact ha | exact hb)
  · rw [ValSpace.dofPartial,ValSpace.shpOfPartial,hquery]
    simp [bind,Except.bind,pure,Except.pure,hdim.2]

theorem canonical_transpose_direct {p : ValFFSProp} {e g h : ValExpr}
    {a ag ah : FlatArray} {sa sb : ValSpace} {m n : Nat}
    {r : ValueCanonicalFSV.ResultMatrix}
    (he : denotValB_partial PartialDirectOracle.oracle ρ Γ Δ e = .ok (.array a))
    (hg : denotValB_partial PartialDirectOracle.oracle ρ Γ Δ g = .ok (.array ag))
    (hh : denotValB_partial PartialDirectOracle.oracle ρ Γ Δ h = .ok (.array ah))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod sa sb)
    (ha : sa.dofPartial (PartialDirectOracle.oracle ρ Γ Δ) = .ok m)
    (hb : sb.dofPartial (PartialDirectOracle.oracle ρ Γ Δ) = .ok n)
    (hgd : ∃ k, (ValExpr.inferSpaceCtx Γ g).dofPartial (PartialDirectOracle.oracle ρ Γ Δ) = .ok k)
    (hhd : ∃ k, (ValExpr.inferSpaceCtx Γ h).dofPartial (PartialDirectOracle.oracle ρ Γ Δ) = .ok k)
    (hleaf : ValueCanonicalFSV.eval p m n a ag ah = .ok r)
    (hf : ValueQueryDependencies.Finite (.expr Γ e)) :
    ∃ out, denotValB_partial PartialDirectOracle.oracle ρ Γ Δ
      (.vtrans (.canonicalFSV p e g h)) = .ok (.array out) ∧
      out.length = r.cols*r.rows ∧
      ∀ (j : Fin r.cols) (i : Fin r.rows), out.get (j.val*r.rows+i.val) = r.data i j := by
  obtain ⟨hdrow,hdcol⟩ := canonical_dimensions he ha hb hleaf ((hinfer ▸ hf.inferSpace).ffs hf)
  have hi : ValExpr.inferSpaceCtx Γ (.canonicalFSV p e g h) =
      .tprod (p.ambient sa sb) (.ffs p (.tprod sa sb) e) := by
    cases p <;> simp only [ValExpr.canonicalFSV, ValExpr.inferSpaceCtx, hinfer, ValFFSProp.ambient]
  have hout : (ValExpr.inferSpaceCtx Γ (.canonicalFSV p e g h)).dofPartial
      (PartialDirectOracle.oracle ρ Γ Δ) = .ok (r.rows*r.cols) := by
    rw [hi]
    exact dof_tprod_ok hdrow hdcol
  exact eval_transpose (eval_canonicalFSV he hg hh hinfer ha hb hgd hhd hout hleaf)
    hi hdrow hdcol

/-- Common source-agreement endpoint for all four subspace inclusions. The
subspace basis is obtained by lifting the selected ambient columns. -/
theorem embedding_of_columns {σ : DEnv} {Ds : List DVal}
    {sSub sAmb : Space} {svSub svAmb : ValSpace}
    (K : Submodule ℝ (denotSpaceAux σ Ds sAmb).carrier)
    (hsSub : denotSpaceAux σ Ds sSub = HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K)
    (S : List (denotSpaceAux σ Ds sAmb).carrier) {k : Nat}
    (U : Matrix (Fin S.length) (Fin k) ℝ)
    (raw : List (denotSpaceAux σ Ds sAmb).carrier)
    (hraw : raw = List.ofCoords S U)
    (hsub : ∀ x ∈ raw, x ∈ K)
    (hbsub : IsListBasis (HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K)
      (HSpace.liftToSubmodule K raw))
    {program : ValExpr} {out : FlatArray}
    (heval : denotValB_partial orc ρ Γ Δ program = .ok (.array out))
    (hlen : out.length = k*S.length)
    (hget : ∀ (j : Fin k) (i : Fin S.length), out.get (j.val*S.length+i.val) = U i j)
    (hdSub : svSub.dofPartial (orc ρ Γ Δ) = .ok k)
    (hdAmb : svAmb.dofPartial (orc ρ Γ Δ) = .ok S.length) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod (.dual sSub) sAmb))
      (.space (.tprod svSub svAmb))
      (.vecs (HSpace.tprod (HSpace.dual (HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K))
        (denotSpaceAux σ Ds sAmb))
        (HSpace.tprodOfLists _ _
          ((HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K).dualOfList
            (HSpace.liftToSubmodule K raw)) S))
      (embedDVal (HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K)
        (denotSpaceAux σ Ds sAmb) K.subtype)
      (denotValB_partial orc ρ Γ Δ program) := by
  have hlift : (HSpace.liftToSubmodule K raw).length = k := by
    rw [HSpace.liftToSubmodule_length_of_subset K raw hsub,hraw,List.ofCoords_length]
  have hB : (HSpace.tprodOfLists
      (HSpace.dual (HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K))
      (denotSpaceAux σ Ds sAmb)
      ((HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K).dualOfList
        (HSpace.liftToSubmodule K raw)) S).length = k*S.length := by
    rw [HSpace.tprodOfLists_length,HSpace.dualOfList_length,hlift]
  have hcoords := RawTermEmbed.subtype_tensor_ofCoords (denotSpaceAux σ Ds sAmb) K S
    U raw hraw hsub hbsub out hget
  rw [hB,← Fin.sum_univ_eq_sum_range] at hcoords
  refine ⟨_,heval,?_⟩
  simp only [Agree]
  have hspace : denotSpaceAux σ Ds (.tprod (.dual sSub) sAmb) =
      HSpace.tprod (HSpace.dual (HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K))
        (denotSpaceAux σ Ds sAmb) := by
    simp only [denotSpaceAux]
    rw [hsSub]
  rw [hspace]
  simp only [BasisDenot.atSpace_vecs_self]
  refine ⟨_,dof_tprod_ok hdSub hdAmb,hB,hlen,?_⟩
  change (embedDVal (HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K)
      (denotSpaceAux σ Ds sAmb) K.subtype).atSpace
      (HSpace.tprod (HSpace.dual (HSpace.ofSubmodule (denotSpaceAux σ Ds sAmb) K))
        (denotSpaceAux σ Ds sAmb)) = _
  simp only [embedDVal,DVal.atSpace_hil_self]
  exact hcoords

end GLang.PartialAdequacy
