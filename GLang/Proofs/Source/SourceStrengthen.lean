import GLang.Proofs.Basis.Binding
import GLang.Proofs.Source.Soundness
import GLang.Graded.Strengthening

/-!
# Nonlinear source-context strengthening

This module isolates the source metatheorem needed to transport adequacy's
contextual basis-dimension law through a fresh operational binding.  The first
lemma below shows that strengthening the three source judgments embedded in a
`BasisValid` derivation is sufficient to strengthen the basis derivation
itself.  Keeping this structural lift separate makes the remaining obligation
precise: prove the judgment-level laws (directly or through the graded bridge),
then instantiate this lemma.
-/

namespace GLang

/-- Removing an unused nonlinear binding from source space validity. -/
def SValidNLEraseLaw : Type :=
  ∀ {Γ : NLCtx} {x : Name} {τx : Ty} {s : Space},
    CtxWF ∅ Γ → x ∉ Γ → x ∉ Space.fv s →
      SValid (Finmap.insert x τx Γ) s → SValid Γ s

/-- Removing an unused nonlinear binding from source type validity. -/
def TValidNLEraseLaw : Type :=
  ∀ {Γ : NLCtx} {x : Name} {τx τ : Ty} {k : Kind},
    CtxWF ∅ Γ → x ∉ Γ → x ∉ Ty.fv τ →
      TValid (Finmap.insert x τx Γ) τ k → TValid Γ τ k

/-- Removing an unused nonlinear binding from source term typing with empty
linear context.  This is the only term-typing form embedded by `BasisValid`. -/
def HasTypeEmptyNLEraseLaw : Type :=
  ∀ {Γ : NLCtx} {x : Name} {τx τ : Ty} {e : Term},
    CtxWF ∅ Γ → x ∉ Γ → x ∉ Term.fv e → x ∉ Ty.fv τ →
      HasType ∅ (Finmap.insert x τx Γ) e τ → HasType ∅ Γ e τ

/-- Structural lift of nonlinear strengthening through basis validity.  The
cofinite frame case enlarges its avoid set by the erased name, commutes the two
distinct inserts, and applies the induction hypothesis to the opened body. -/
theorem Basis.BasisValid.erase_insert_of_not_mem_fv_of_laws
    (hs : SValidNLEraseLaw) (ht : TValidNLEraseLaw)
    (he : HasTypeEmptyNLEraseLaw)
    {Γ : NLCtx} {x : Name} {τx : Ty} {b : Basis}
    (hctx : CtxWF ∅ Γ) (hxΓ : x ∉ Γ) (hxb : x ∉ Basis.fv b)
    (hb : Basis.BasisValid (Finmap.insert x τx Γ) b) :
    Basis.BasisValid Γ b := by
  generalize hΓx : Finmap.insert x τx Γ = Γx at hb
  induction hb generalizing Γ x τx with
  | empty => exact .empty
  | one => exact .one
  | dual hb htof ih =>
      exact .dual (ih hctx hxΓ (by simpa [Basis.fv] using hxb) hΓx) htof
  | dsum hb₀ hb₁ htof₀ htof₁ ih₀ ih₁ =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hxb
      exact .dsum (ih₀ hctx hxΓ hxb.1 hΓx) (ih₁ hctx hxΓ hxb.2 hΓx)
        htof₀ htof₁
  | tprod hb₀ hb₁ htof₀ htof₁ ih₀ ih₁ =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hxb
      exact .tprod (ih₀ hctx hxΓ hxb.1 hΓx) (ih₁ hctx hxΓ hxb.2 hΓx)
        htof₀ htof₁
  | proj_ker hb₀ hb₁ hsof₀ hsof₁ hterm ih₀ ih₁ =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hxb
      rw [← hΓx] at hterm
      refine .proj_ker (ih₀ hctx hxΓ hxb.1.2 hΓx) (ih₁ hctx hxΓ hxb.2 hΓx) hsof₀ hsof₁ ?_
      exact ⟨he hctx hxΓ hxb.1.1.2
        (by simpa [Ty.fv, Space.fv] using ⟨hxb.1.1.1.1, hxb.1.1.1.2⟩) hterm.some⟩
  | proj_coker hb₀ hb₁ hsof₀ hsof₁ hterm ih₀ ih₁ =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hxb
      rw [← hΓx] at hterm
      refine .proj_coker (ih₀ hctx hxΓ hxb.1.2 hΓx) (ih₁ hctx hxΓ hxb.2 hΓx) hsof₀ hsof₁ ?_
      exact ⟨he hctx hxΓ hxb.1.1.2
        (by simpa [Ty.fv, Space.fv] using ⟨hxb.1.1.1.1, hxb.1.1.1.2⟩) hterm.some⟩
  | proj_img hb₀ hb₁ hsof₀ hsof₁ hterm ih₀ ih₁ =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hxb
      rw [← hΓx] at hterm
      refine .proj_img (ih₀ hctx hxΓ hxb.1.2 hΓx) (ih₁ hctx hxΓ hxb.2 hΓx) hsof₀ hsof₁ ?_
      exact ⟨he hctx hxΓ hxb.1.1.2
        (by simpa [Ty.fv, Space.fv] using ⟨hxb.1.1.1.1, hxb.1.1.1.2⟩) hterm.some⟩
  | proj_coimg hb₀ hb₁ hsof₀ hsof₁ hterm ih₀ ih₁ =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hxb
      rw [← hΓx] at hterm
      refine .proj_coimg (ih₀ hctx hxΓ hxb.1.2 hΓx) (ih₁ hctx hxΓ hxb.2 hΓx) hsof₀ hsof₁ ?_
      exact ⟨he hctx hxΓ hxb.1.1.2
        (by simpa [Ty.fv, Space.fv] using ⟨hxb.1.1.1.1, hxb.1.1.1.2⟩) hterm.some⟩
  | image hb hsof hterm ih =>
      simp only [Basis.fv] at hxb
      rw [← hΓx] at hterm
      refine .image (ih hctx hxΓ hxb hΓx) hsof ?_
      have hxsof : x ∉ Space.fv (Basis.sof _) := fun hm => hxb (Basis.fv_sof_subset _ hm)
      rw [hsof] at hxsof
      simp only [Space.fv, Finset.mem_union, not_or] at hxsof
      exact ⟨he hctx hxΓ hxsof.2
        (by simpa [Ty.fv, Space.fv] using ⟨hxsof.1.1, hxsof.1.2⟩) hterm.some⟩
  | terms hb htof hsvalid hterms hne ih =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hxb
      rw [← hΓx] at hsvalid hterms
      refine .terms (ih hctx hxΓ hxb.1.2 hΓx) htof ⟨hs hctx hxΓ hxb.1.1 hsvalid.some⟩ ?_ hne
      intro e he_mem
      exact ⟨he hctx hxΓ (fun hxe => hxb.2 (Term.mem_fvList.mpr ⟨e, he_mem, hxe⟩))
        (by simpa [Ty.fv] using hxb.1.1) (hterms e he_mem).some⟩
  | frame L hb₀ hbody ih₀ ihbody =>
      rename_i εframe bdom bcod
      simp only [Basis.fv, Finset.mem_union, not_or] at hxb
      have hbdom := ih₀ hctx hxΓ hxb.1 hΓx
      have hdomvalid := hbdom.tof_valid_structural
      have hbody' : ∀ y, y ∉ (L ∪ {x}) ∪ Γ.keys →
          Basis.BasisValid (Finmap.insert y (Basis.tof bdom) Γ)
            (Basis.openVar y bcod) := by
        intro y hy
        simp only [Finset.mem_union, not_or] at hy
        have hyL : y ∉ L := hy.1.1
        have hyΓ : y ∉ Γ := fun hm => hy.2 (Finmap.mem_keys.mpr hm)
        have hyx : y ≠ x := by
          intro h; subst y
          exact hy.1.2 (Finset.mem_singleton_self x)
        have hxopen : x ∉ Basis.fv (Basis.openVar y bcod) := by
          intro hx
          have hm := Basis.fv_openRec_subset 0 (.var y) bcod hx
          rcases Finset.mem_union.mp hm with hm | hm
          · exact hxb.2 hm
          · have hxy : x = y := by simpa [Term.fv] using hm
            exact hyx hxy.symm
        have hxinsert : x ∉ Finmap.insert y (Basis.tof bdom) Γ := by
          rw [Finmap.mem_insert]
          intro hm
          exact hm.elim (Ne.symm hyx) hxΓ
        have hcomm :
            Finmap.insert y (Basis.tof bdom) (Finmap.insert x τx Γ) =
              Finmap.insert x τx (Finmap.insert y (Basis.tof bdom) Γ) := by
          exact Finmap.insert_insert_of_ne Γ (Ne.symm hyx)
        have heq :
            Finmap.insert x τx (Finmap.insert y (Basis.tof bdom) Γ) =
              Finmap.insert y (Basis.tof bdom) εframe := by
          rw [← hcomm, hΓx]
        have hctx' : CtxWF ∅ (Finmap.insert y (Basis.tof bdom) Γ) :=
          CtxWF.insert_nl hctx Finmap.notMem_empty hyΓ (TValid.fv_closure hdomvalid.some)
        exact ihbody y hyL hctx' hxinsert hxopen heq
      exact .frame ((L ∪ {x}) ∪ Γ.keys) hbdom hbody'

/-! ## Discharging the judgment laws through the graded calculus -/

namespace Graded

theorem erase_asTypeCtx_insert {Γ : NLCtx} {x : Name} {τx : Ty} (hxΓ : x ∉ Γ) :
    Function.update (asTypeCtx (Finmap.insert x τx Γ)) x none = asTypeCtx Γ := by
  funext z
  rcases eq_or_ne z x with rfl | hzx
  · simp [asTypeCtx, Finmap.lookup_eq_none.mpr hxΓ]
  · simp [asTypeCtx, Function.update_of_ne hzx, Finmap.lookup_insert_of_ne _ hzx]

end Graded

/-- Source space-validity nonlinear strengthening, proved by forward graded
bridge, coordinate erasure, and the backward formation bridge. -/
noncomputable def sValidNLErase : SValidNLEraseLaw := by
  intro Γ x τx s hctx hxΓ hxs hs
  have hg := Graded.svalidBridge hs
  have hg' := Graded.gsvalid_eraseName hg
    (Graded.typeViewFreshAt_insert hctx hxΓ) hxs
  rw [Graded.erase_asTypeCtx_insert hxΓ] at hg'
  exact Graded.svalidBwd hg' (fun _ _ h => h)

/-- Source type-validity nonlinear strengthening through the graded bridge. -/
noncomputable def tValidNLErase : TValidNLEraseLaw := by
  intro Γ x τx τ k hctx hxΓ hxτ ht
  have hg := Graded.tvalidBridge ht
  have hg' := Graded.gtvalid_eraseName hg
    (Graded.typeViewFreshAt_insert hctx hxΓ) hxτ
  rw [Graded.erase_asTypeCtx_insert hxΓ] at hg'
  exact Graded.tvalidBwd hg' (fun _ _ h => h)

/-- Empty-linear source typing nonlinear strengthening through graded
coordinate erasure.  The graded proof is where `promote` disappears. -/
noncomputable def hasTypeEmptyNLErase : HasTypeEmptyNLEraseLaw := by
  intro Γ x τx τ e hctx hxΓ hxe hxτ ht
  have hg := Graded.hasTypeBridge (Graded.CtxDisj.empty _) ht
  have hg' := Graded.ghastype_eraseName hg
    (Graded.typeFreshAt_tr_empty_insert hctx hxΓ) hxe hxτ
  rw [Graded.eraseName_tr_empty_insert hxΓ] at hg'
  exact Graded.hasTypeBridgeBwd (Graded.CtxDisj.empty _) hg'

/-- **Source nonlinear strengthening for valid bases.** Removing a fresh,
FV-unused nonlinear binding from a valid basis is derivable under the
pre-extension well-formed source context; no strengthening axiom remains. -/
theorem Basis.BasisValid.erase_insert_of_not_mem_fv
    {Γ : NLCtx} {x : Name} {τx : Ty} {b : Basis}
    (hctx : CtxWF ∅ Γ) (hxΓ : x ∉ Γ) (hxb : x ∉ Basis.fv b)
    (hb : Basis.BasisValid (Finmap.insert x τx Γ) b) :
    Basis.BasisValid Γ b :=
  hb.erase_insert_of_not_mem_fv_of_laws
    sValidNLErase tValidNLErase hasTypeEmptyNLErase hctx hxΓ hxb

end GLang
