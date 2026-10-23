import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceFFS
import GLang.Proofs.Adequacy.Raw.Conversion.RawCobInverse

/-! Change-of-basis equations for actual partial evaluation. -/
namespace GLang.PartialAdequacy
open scoped TensorProduct
open PartialValueEval

/-- Rows of the matrix are target-basis coordinates of source-basis vectors. -/
def CobRows {V : HSpace} (source target : List V.carrier) (a : FlatArray) : Prop :=
  target.length = source.length ∧ a.length = source.length * source.length ∧
  ∀ j : Fin source.length, source.getD j.val 0 =
    ∑ i : Fin source.length, a.get (j.val * source.length + i.val) • target.getD i.val 0

def CobResult (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) {V : HSpace}
    (source target : List V.carrier) (e : ValExpr) : Prop :=
  ∃ a, denotValB_partial orc ρ Γ Δ e = .ok (.array a) ∧ CobRows source target a

def CobAgree (orc : PartialFFSOracleSem) (σ : DEnv) (ρ : ValEnvSem)
    (bSrc bTgt : Basis) (e : ValExpr) : Prop :=
  let V := denotSpace σ (Basis.sof bSrc)
  CobResult orc ρ [] [] ((denotBasis σ bSrc).atSpace V) ((denotBasis σ bTgt).atSpace V) e

variable {orc : PartialFFSOracleSem} {ρ : ValEnvSem}
  {Γ : List ValTy} {Δ : List ValValSem}

theorem dof_tprod_ok {s t : ValSpace} {m n : Nat}
    (hs : s.dofPartial (orc ρ Γ Δ) = .ok m)
    (ht : t.dofPartial (orc ρ Γ Δ) = .ok n) :
    ValSpace.dofPartial (orc ρ Γ Δ) (.tprod s t) = .ok (m*n) := by
  rw [ValSpace.dofPartial, ValSpace.shpOfPartial, hs]
  simp [ht, bind, Except.bind, pure, Except.pure]

theorem guard_ok {ss : List ValSpace}
    (h : ∀ s ∈ ss, ∃ n, s.dofPartial (orc ρ Γ Δ) = .ok n)
    (f : FFSOracle → Except DimError ValValSem) :
    withDimensions (orc ρ Γ Δ) ss f = f (numbers (orc ρ Γ Δ)) := by
  unfold withDimensions
  rw [(dimensions_ok_iff _ _).2 h]

theorem eval_inv {e : ValExpr} {a : FlatArray} {sa sb : ValSpace} {m n : Nat}
    (he : denotValB_partial orc ρ Γ Δ e = .ok (.array a))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod sa sb)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok m)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok n)
    (hlen : a.length = m*n) :
    denotValB_partial orc ρ Γ Δ (.inv e) =
      .ok (.array (FlatArray.ofFn (n*m)
        (matrixAsDenot (matrixSVDPinv (denotAsMatrix m n a.get))))) := by
  have hab := dof_tprod_ok ha hb
  have hba := dof_tprod_ok hb ha
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx, hinfer]
  rw [guard_ok (by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨_,hab⟩
    · exact ⟨_,hba⟩)]
  simp only [he, ValValSem.bindArray, dof_numbers _ _ _ ha,
    dof_numbers _ _ _ hb, dof_numbers _ _ _ hba, hlen, ↓reduceIte, ValValSem.arrayOf]
  generalize hma : ValSpace.dof (numbers (orc ρ Γ Δ)) sa = m' at ⊢
  generalize hnb : ValSpace.dof (numbers (orc ρ Γ Δ)) sb = n' at ⊢
  rw [dof_numbers _ _ _ ha] at hma
  rw [dof_numbers _ _ _ hb] at hnb
  subst m'; subst n'
  rfl

theorem cob_inverse {V : HSpace} {source target : List V.carrier} {e : ValExpr}
    {sa sb : ValSpace}
    (hs : IsListBasis V source) (ht : IsListBasis V target)
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod sa sb)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok source.length)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok source.length)
    (h : CobResult orc ρ Γ Δ source target e) :
    CobResult orc ρ Γ Δ target source (.inv e) := by
  obtain ⟨a,he,hTlen,halen,hrows⟩ := h
  let M := denotAsMatrix source.length source.length a.get
  let bT : Module.Basis (Fin source.length) ℝ V.carrier :=
    ht.toBasis.reindex (finCongr hTlen)
  have hbT (i : Fin source.length) : bT i = target.getD i.val 0 := by
    rw [List.getD_eq_getElem target 0 (hTlen.symm ▸ i.isLt)]
    simp [bT, Module.Basis.reindex_apply, IsListBasis.toBasis_apply]
  have hbS (i : Fin source.length) : hs.toBasis i = source.getD i.val 0 := by
    simp [IsListBasis.toBasis_apply]
  have hmrows : ∀ j, hs.toBasis j = ∑ i, M j i • bT i := by
    intro j
    rw [hbS, hrows j]
    apply Finset.sum_congr rfl
    intro i _
    rw [hbT]
    simp [M, denotAsMatrix, Nat.mul_comm source.length j.val]
  have hrev := Basis.raw_svdPinv_reverse_rows hs.toBasis bT M hmrows
  refine ⟨_,eval_inv he hinfer ha hb halen,?_,?_,?_⟩
  · exact hTlen.symm
  · simp only [FlatArray.length_ofFn, hTlen]
  · intro j
    have hj : j.val < source.length := hTlen ▸ j.isLt
    have hrev' := hrev ⟨j.val,hj⟩
    rw [hbT] at hrev'
    rw [hrev', Fin.raw_sum_cast_of_eq hTlen]
    apply Finset.sum_congr rfl
    intro i _
    rw [hbS]
    congr 1
    rw [FlatArray.get_ofFn_lt _ _ _ (by
      simp only [hTlen, Fin.val_cast]
      exact Nat.raw_rowMajor_lt hj i.isLt)]
    simpa only [M, Fin.val_cast, hTlen] using
      (raw_matrixAsDenot_svdPinv_denotAsMatrix_get a.get rfl rfl ⟨j.val,hj⟩ i).symm

theorem eval_mtm_square {e₀ e₁ : ValExpr} {a₀ a₁ : FlatArray}
    {sv sa sb sc sd : ValSpace} {n : Nat}
    (he₀ : denotValB_partial orc ρ Γ Δ e₀ = .ok (.array a₀))
    (he₁ : denotValB_partial orc ρ Γ Δ e₁ = .ok (.array a₁))
    (hi₀ : ValExpr.inferSpaceCtx Γ e₀ = .tprod sa sb)
    (hi₁ : ValExpr.inferSpaceCtx Γ e₁ = .tprod sc sd)
    (hv : sv.dofPartial (orc ρ Γ Δ) = .ok n)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok n)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok n)
    (hc : sc.dofPartial (orc ρ Γ Δ) = .ok n)
    (hd : sd.dofPartial (orc ρ Γ Δ) = .ok n)
    (hlen₀ : a₀.length = n*n) (hlen₁ : a₁.length = n*n) :
    denotValB_partial orc ρ Γ Δ (.mtm 0 0 sv sv e₀ e₁) =
      .ok (.array (FlatArray.ofFn (n*n) (fun i =>
        if i ≥ n*n then 0 else ∑ k ∈ Finset.range n,
          a₀.get (n*k+i%n) * a₁.get (n*(i/n)+k)))) := by
  have hab := dof_tprod_ok ha hb
  have hcd := dof_tprod_ok hc hd
  have hcb := dof_tprod_ok hc hb
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx, hi₀, hi₁]
  rw [guard_ok (by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨_,hv⟩
    · exact ⟨_,hab⟩
    · exact ⟨_,hcd⟩
    · exact ⟨_,hcb⟩)]
  have hshape : ValueShape.mtm (numbers (orc ρ Γ Δ)) sv
      (.tprod sa sb) (.tprod sc sd) a₀ a₁ := by
    simp only [ValueShape.mtm, ValueShape.matrices, ValueShape.tensor,
      dof_numbers _ _ _ ha, dof_numbers _ _ _ hb, dof_numbers _ _ _ hc,
      dof_numbers _ _ _ hd, dof_numbers _ _ _ hv, hlen₀, hlen₁, and_self]
  simp only [he₀,he₁,ValValSem.bindArrays,ValValSem.bindArray,if_pos hshape,
    dof_numbers _ _ _ hb,dof_numbers _ _ _ hc,dof_numbers _ _ _ hv,
    dof_numbers _ _ _ hcb,ValValSem.arrayOf]

theorem cob_trans {V : HSpace} {source middle target : List V.carrier}
    {e₀ e₁ : ValExpr} {sv sa sb sc sd : ValSpace}
    (hi₀ : ValExpr.inferSpaceCtx Γ e₀ = .tprod sa sb)
    (hi₁ : ValExpr.inferSpaceCtx Γ e₁ = .tprod sc sd)
    (hv : sv.dofPartial (orc ρ Γ Δ) = .ok source.length)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok source.length)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok source.length)
    (hc : sc.dofPartial (orc ρ Γ Δ) = .ok source.length)
    (hd : sd.dofPartial (orc ρ Γ Δ) = .ok source.length)
    (h₀ : CobResult orc ρ Γ Δ source middle e₀)
    (h₁ : CobResult orc ρ Γ Δ middle target e₁) :
    CobResult orc ρ Γ Δ source target (.mtm 0 0 sv sv e₁ e₀) := by
  obtain ⟨a₀,he₀,hm,hlen₀,hrows₀⟩ := h₀
  obtain ⟨a₁,he₁,ht,hlen₁,hrows₁⟩ := h₁
  rw [hm] at ht hlen₁ hrows₁
  refine ⟨_,eval_mtm_square he₁ he₀ hi₁ hi₀ hv hc hd ha hb hlen₁ hlen₀,
    ht,FlatArray.length_ofFn _ _,?_⟩
  apply raw_cobAgree_trans_list source middle target _ a₀ a₁ hrows₀ hrows₁
  intro j i hj hi
  have hlt := Nat.raw_rowMajor_lt hj hi
  rw [FlatArray.get_ofFn_lt _ _ _ hlt, if_neg (Nat.not_le.mpr hlt)]
  obtain ⟨hdiv,hmod⟩ := Nat.raw_rowMajor_div_mod hj hi
  rw [hdiv,hmod]

theorem eval_ttv_square {matrix vector : ValExpr} {a b : FlatArray}
    {sv sa sb : ValSpace} {n : Nat}
    (hm : denotValB_partial orc ρ Γ Δ matrix = .ok (.array a))
    (he : denotValB_partial orc ρ Γ Δ vector = .ok (.array b))
    (him : ValExpr.inferSpaceCtx Γ matrix = .tprod sa sb)
    (hie : ValExpr.inferSpaceCtx Γ vector = sv)
    (hv : sv.dofPartial (orc ρ Γ Δ) = .ok n)
    (ha : sa.dofPartial (orc ρ Γ Δ) = .ok n)
    (hb : sb.dofPartial (orc ρ Γ Δ) = .ok n)
    (hlenA : a.length = n*n) (hlenB : b.length = n) :
    denotValB_partial orc ρ Γ Δ (.ttv sv matrix vector) =
      .ok (.array (FlatArray.ofFn n (fun i => if i ≥ n then 0 else
        ∑ j ∈ Finset.range n, a.get (n*j+i) * b.get j))) := by
  have hab := dof_tprod_ok ha hb
  rw [denotValB_partial]
  simp only [ValExpr.inferSpaceCtx, him, hie]
  rw [guard_ok (by
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact ⟨_,hv⟩
    · exact ⟨_,hab⟩
    · exact ⟨_,hv⟩
    · exact ⟨_,hb⟩)]
  have hshape : ValueShape.ttv (numbers (orc ρ Γ Δ)) sv (.tprod sa sb) sv a b := by
    simp only [ValueShape.ttv, ValueShape.pair,
      dof_numbers _ _ _ ha, dof_numbers _ _ _ hb, dof_numbers _ _ _ hab,
      dof_numbers _ _ _ hv, hlenA, hlenB, and_self]
  simp only [hm,he,ValValSem.bindArrays,ValValSem.bindArray,if_pos hshape,
    dof_numbers _ _ _ hb,dof_numbers _ _ _ hv,ValValSem.arrayOf]

/-- A successful coordinate conversion preserves source denotation. -/
theorem cob_apply {σ : DEnv} {Ds : List DVal} {s : Space} {sv sa sb : ValSpace}
    {source target : BasisDenot} {x : DVal} {matrix vector : ValExpr}
    (him : ValExpr.inferSpaceCtx Γ matrix = .tprod sa sb)
    (hie : ValExpr.inferSpaceCtx Γ vector = sv)
    (ha : sa.dofPartial (orc ρ Γ Δ) =
      .ok (source.atSpace (denotSpaceAux σ Ds s)).length)
    (hb : sb.dofPartial (orc ρ Γ Δ) =
      .ok (source.atSpace (denotSpaceAux σ Ds s)).length)
    (hm : CobResult orc ρ Γ Δ (source.atSpace (denotSpaceAux σ Ds s))
      (target.atSpace (denotSpaceAux σ Ds s)) matrix)
    (he : ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) source x
      (denotValB_partial orc ρ Γ Δ vector)) :
    ResultAgree orc σ ρ Ds Γ Δ (.space s) (.space sv) target x
      (denotValB_partial orc ρ Γ Δ (.ttv sv matrix vector)) := by
  obtain ⟨a,hm,htlen,halen,hrows⟩ := hm
  obtain ⟨v,he,hagree⟩ := he
  obtain ⟨b,n,rfl,hv,hslen,hblen,hcoords⟩ := hagree.array
  rw [← hslen] at hv hblen hcoords
  refine ⟨_,eval_ttv_square hm he him hie hv ha hb halen hblen,?_⟩
  simp only [Agree]
  refine ⟨_,hv,htlen,FlatArray.length_ofFn _ _,?_⟩
  rw [hcoords]
  simp only [hrows, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [FlatArray.get_ofFn_lt _ _ _ i.isLt, if_neg (Nat.not_le.mpr i.isLt)]
  rw [Finset.sum_smul, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, Nat.mul_comm]

theorem cob_refl {V : HSpace} (source : List V.carrier) {sv : ValSpace}
    (hd : sv.dofPartial (orc ρ Γ Δ) = .ok source.length) :
    CobResult orc ρ Γ Δ source source (.idelta sv) := by
  have hd₂ := dof_tprod_ok hd hd
  rw [CobResult, denotValB_partial]
  rw [guard_ok (by simpa only [List.mem_singleton] using
    (fun s (hs : s = sv) => hs ▸ (show ∃ n, sv.dofPartial (orc ρ Γ Δ) = .ok n from ⟨_,hd⟩)))]
  simp only [ValExpr.inferSpaceCtx,dof_numbers _ _ _ hd₂,dof_numbers _ _ _ hd,
    ValValSem.arrayOf]
  refine ⟨_,rfl,rfl,FlatArray.length_ofFn _ _,?_⟩
  intro j
  have hg : ∀ i : Fin source.length,
      (FlatArray.ofFn (source.length * source.length) (fun k =>
        if source.length = 0 then 0 else if k < source.length * source.length then
          if k/source.length = k%source.length ∧ k/source.length < source.length
            then (1 : ℝ) else 0 else 0)).get (j.val*source.length+i.val) =
        if j = i then 1 else 0 := by
    intro i
    have hlt := Nat.raw_rowMajor_lt j.isLt i.isLt
    have hn : source.length ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt j.isLt)
    obtain ⟨hdiv,hmod⟩ := Nat.raw_rowMajor_div_mod j.isLt i.isLt
    rw [FlatArray.get_ofFn_lt _ _ _ hlt]
    simp [hn,hlt,hdiv,hmod,j.isLt,Fin.val_inj]
  simp only [hg,ite_smul,one_smul,zero_smul,Finset.sum_ite_eq,
    Finset.mem_univ,if_true]

theorem cob_reshape {V : HSpace} {source target : List V.carrier} {e : ValExpr}
    {sv : ValSpace}
    (hd : sv.dofPartial (orc ρ Γ Δ) = .ok (source.length * source.length))
    (h : CobResult orc ρ Γ Δ source target e) :
    CobResult orc ρ Γ Δ source target (.reshap e (.space sv) (.space sv)) := by
  obtain ⟨a,he,hrows⟩ := h
  refine ⟨a,?_,hrows⟩
  rw [denotValB_partial,he]
  simp [reshapeInferred,reshapeBetween,reshapeArray,hd,hrows.2.1]

end GLang.PartialAdequacy
