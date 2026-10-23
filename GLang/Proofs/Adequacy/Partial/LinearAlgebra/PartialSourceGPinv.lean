import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourcePinv
import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyGPinvT

namespace GLang.PartialAdequacy
open scoped BigOperators Matrix TensorProduct
open PartialValueEval
variable {orc : PartialFFSOracleSem} {ρ : ValEnvSem} {Γ : List ValTy} {Δ : List ValValSem}

/-- The actual guarded evaluator computes the Gram-weighted inverse when all
three stored arrays have the required sizes. -/
theorem eval_gpinv {e g h : ValExpr} {a ag ah : FlatArray} {sa sb : ValSpace} {m n : Nat}
    (he : denotValB_partial orc ρ Γ Δ e = .ok (.array a))
    (hg : denotValB_partial orc ρ Γ Δ g = .ok (.array ag))
    (hh : denotValB_partial orc ρ Γ Δ h = .ok (.array ah))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod sa sb)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok m)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok n)
    (hgd : ∃ d, (ValExpr.inferSpaceCtx Γ g).dofPartial (orc ρ Γ Δ) = .ok d)
    (hhd : ∃ d, (ValExpr.inferSpaceCtx Γ h).dofPartial (orc ρ Γ Δ) = .ok d)
    (hshape : GSVDInputsShape m n a ag ah) :
    denotValB_partial orc ρ Γ Δ (.gpinv e g h) =
      .ok (.array (FlatArray.ofFn (n*m)
        (matrixAsDenot (matrixGSVDPinv (denotAsMatrix m n a.get).transpose
          (denotAsMatrix m m ag.get) (denotAsMatrix n n ah.get)).transpose))) := by
  have hab := dof_tprod_ok ha hb
  have hba := dof_tprod_ok hb ha
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx,hinfer]
  rw [guard_ok (by
    intro s hs
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨_,hab⟩
    · exact hgd
    · exact hhd
    · exact ⟨_,hba⟩)]
  simp only [he,hg,hh,ValValSem.bindArrays3,ValValSem.bindArray,
    dof_numbers _ _ _ ha,dof_numbers _ _ _ hb,dof_numbers _ _ _ hba,
    if_pos hshape,ValValSem.arrayOf]
  generalize hma : ValSpace.dof (numbers (orc ρ Γ Δ)) sa = m' at ⊢
  generalize hnb : ValSpace.dof (numbers (orc ρ Γ Δ)) sb = n' at ⊢
  rw [dof_numbers _ _ _ ha] at hma
  rw [dof_numbers _ _ _ hb] at hnb
  subst m'; subst n'
  rfl

variable {σ : DEnv} {Ds : List DVal}

theorem gpinv_tensor {s₀ s₁ : Space} {sa sb : ValSpace} {x : DVal} {e : ValExpr}
    {vs₀ : List (denotSpaceAux σ Ds s₀).carrier}
    {vs₁ : List (denotSpaceAux σ Ds s₁).carrier}
    (hb₀ : IsListBasis (denotSpaceAux σ Ds s₀) vs₀)
    (hb₁ : IsListBasis (denotSpaceAux σ Ds s₁) vs₁)
    {g h : ValExpr} {ag ah : FlatArray}
    (hg : denotValB_partial orc ρ Γ Δ g = .ok (.array ag))
    (hh : denotValB_partial orc ρ Γ Δ h = .ok (.array ah))
    (hgd : ∃ d, (ValExpr.inferSpaceCtx Γ g).dofPartial (orc ρ Γ Δ) = .ok d)
    (hhd : ∃ d, (ValExpr.inferSpaceCtx Γ h).dofPartial (orc ρ Γ Δ) = .ok d)
    (hgl : ag.length = vs₀.length*vs₀.length)
    (hhl : ah.length = vs₁.length*vs₁.length)
    (hG : denotAsMatrix vs₀.length vs₀.length ag.get =
      IsListBasis.gram (denotSpaceAux σ Ds s₀) vs₀)
    (hH : denotAsMatrix vs₁.length vs₁.length ah.get =
      IsListBasis.gram (denotSpaceAux σ Ds s₁) vs₁)
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod sa sb)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok vs₀.length)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok vs₁.length)
    (harg : ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod (.dual s₀) s₁))
      (.space (.tprod sa sb))
      (.vecs (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₀)) (denotSpaceAux σ Ds s₁))
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s₀).dualOfList vs₀) vs₁))
      x (denotValB_partial orc ρ Γ Δ e)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space (.tprod (.dual s₁) s₀))
      (.space (.tprod sb sa))
      (.vecs (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₁)) (denotSpaceAux σ Ds s₀))
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s₁).dualOfList vs₁) vs₀))
      (pinvTensorDVal (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁) x)
      (denotValB_partial orc ρ Γ Δ (.gpinv e g h)) := by
  obtain ⟨v,he,hagree⟩ := harg
  obtain ⟨a,n,rfl,hd,_,hlen,hcoords⟩ := hagree.array
  have hdim := dof_tprod_ok ha hb
  have hdim' := dof_tprod_ok hb ha
  have hn : n = vs₀.length * vs₁.length := Except.ok.inj (hd.symm.trans hdim)
  rw [hn] at hlen hcoords
  have hc : x.atSpace (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₀))
      (denotSpaceAux σ Ds s₁)) = ∑ k : Fin (vs₀.length*vs₁.length), a.get k.val •
        (HSpace.tprodOfLists _ _ ((denotSpaceAux σ Ds s₀).dualOfList vs₀) vs₁).getD k.val 0 := by
    simpa only [denotSpaceAux,BasisDenot.atSpace_vecs_self] using hcoords
  have hM := coordMatrix_eq_of_tensor_coords hb₀ hb₁ a.get _ hc
  rw [← RawSpaceFFS.asLinMap_eq_dualTensorHom_atSpace] at hM
  have hm := RawTermGPinvT.mooreTensor_eq_flat_gpinv_sum hb₀ hb₁
    (x.asLinMap (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁))
  rw [hM,← hG,← hH] at hm
  refine ⟨_,eval_gpinv he hg hh hinfer ha hb hgd hhd ⟨hlen,hgl,hhl⟩,?_⟩
  simp only [Agree,denotSpaceAux,BasisDenot.atSpace_vecs_self]
  refine ⟨_,hdim',?_,FlatArray.length_ofFn _ _,?_⟩
  · rw [HSpace.tprodOfLists_length,HSpace.dualOfList_length]
  · change (pinvTensorDVal (denotSpaceAux σ Ds s₀) (denotSpaceAux σ Ds s₁) x).atSpace
      (HSpace.tprod (HSpace.dual (denotSpaceAux σ Ds s₁)) (denotSpaceAux σ Ds s₀)) = _
    simp only [pinvTensorDVal,DVal.atSpace_hil_self]
    rw [hm]
    apply Finset.sum_congr rfl
    intro k _
    rw [FlatArray.get_ofFn_lt _ _ _ k.isLt]
    rfl

end GLang.PartialAdequacy
