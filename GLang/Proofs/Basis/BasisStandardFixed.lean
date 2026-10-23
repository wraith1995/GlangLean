import GLang.Proofs.Basis.BasisOrthonormalAt
import GLang.Proofs.Source.SourceLN

/-! # Valid standard bases are fixed by reconstruction from their type. -/
namespace GLang

theorem Basis.BasisValid.std_tof_eq {ε : NLCtx} {b : Basis}
    (hb : Basis.BasisValid ε b) (hstd : Basis.isStd b) :
    Basis.std (Basis.tof b) = b := by
  induction hb with
  | empty => rfl
  | one => rfl
  | dual hb ht ih =>
      have h := ih hstd
      rw [ht] at h
      simpa only [Basis.tof, Basis.sof, Basis.std, Basis.stdSpace] using congrArg Basis.dual h
  | dsum h0 h1 ht0 ht1 ih0 ih1 =>
      have h0 := ih0 hstd.1
      have h1 := ih1 hstd.2
      rw [ht0] at h0
      rw [ht1] at h1
      simpa only [Basis.tof, Basis.sof, Basis.std, Basis.stdSpace] using congrArg₂ Basis.dsum h0 h1
  | tprod h0 h1 ht0 ht1 ih0 ih1 =>
      have h0 := ih0 hstd.1
      have h1 := ih1 hstd.2
      rw [ht0] at h0
      rw [ht1] at h1
      simpa only [Basis.tof, Basis.sof, Basis.std, Basis.stdSpace] using congrArg₂ Basis.tprod h0 h1
  | proj_ker h0 h1 ht0 ht1 he ih0 ih1
  | proj_coker h0 h1 ht0 ht1 he ih0 ih1
  | proj_img h0 h1 ht0 ht1 he ih0 ih1
  | proj_coimg h0 h1 ht0 ht1 he ih0 ih1 =>
      have h0 := ih0 hstd.1
      have h1 := ih1 hstd.2
      rw [ht0] at h0
      rw [ht1] at h1
      simp only [Basis.tof, Basis.sof, Basis.std, Basis.stdSpace]
      exact congrArg₂ _ h0 h1
  | image => exact False.elim hstd
  | terms => exact False.elim hstd
  | @frame ε b0 b1 L hb0 hbody ih0 ih1 =>
      have h0 := ih0 hstd.1
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
        (L ∪ Basis.fv b1 ∪ Basis.fv (Basis.std (Basis.tof b1)))
      simp only [Finset.mem_union, not_or] at hx
      have hopen := ih1 x hx.1.1 ((Basis.isStd_openVar x b1).symm ▸ hstd.2)
      simp only [Basis.openVar, Basis.tof_openRec, Basis.std_openRec] at hopen
      have h1 := congrArg (Basis.closeRec 0 x) hopen
      rw [Basis.close_openVar x _ hx.2 0, Basis.close_openVar x _ hx.1.2 0] at h1
      exact congrArg₂ Basis.frame h0 h1

end GLang
