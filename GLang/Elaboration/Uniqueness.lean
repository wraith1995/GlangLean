import GLang.Elaboration.Supporting.SourceAnnotationContext
import GLang.Proofs.Source.SourceContextInductive
import Mathlib.Data.Fintype.EquivFin
/-!
# Uniqueness of implementation annotations

Equal surface syntax has a unique well-typed annotated representative and a
unique result type. The induction is stronger than the fixed-context result:
linear/nonlinear partitions may differ, provided shared names have equal
assigned types. Promotion and context splitting preserve this invariant.

The proof is mutual over space formation, type formation, subspace formation,
and term typing. Cofinite binders are opened at a common fresh name; the
opening/closing laws recover equality of both the body and dependent type.
No typing rules or denotational definitions are changed.
-/

namespace GLang
set_option maxRecDepth 4096

mutual
 /-- Formation recovers all hidden fundamental-subspace annotations. -/
 theorem SValid.erase_unique {ε s} (h : SValid ε s) {ε' t} (h' : SValid ε' t)
     (hc : SourceCtxCompatible ∅ ε ∅ ε') (he : s.erase = t.erase) : s = t :=
   match h with
   | .empty => by cases h' <;> simp_all [Space.erase]
   | .real => by cases h' <;> simp_all [Space.erase]
   | .dual hs => by
     cases h' <;> simp only [Space.erase, Surface.Space.dual.injEq, reduceCtorEq] at he
     rename_i t ht
     exact congrArg Space.dual (hs.erase_unique ht hc he)
   | .dsum ha hb => by
     cases h' <;> simp only [Space.erase, Surface.Space.dsum.injEq, reduceCtorEq] at he
     rename_i a b ha' hb'
     obtain ⟨rfl, rfl⟩ := And.intro (ha.erase_unique ha' hc he.1) (hb.erase_unique hb' hc he.2)
     rfl
   | .tprod ha hb => by
     cases h' <;> simp only [Space.erase, Surface.Space.tprod.injEq, reduceCtorEq] at he
     rename_i a b ha' hb'
     obtain ⟨rfl, rfl⟩ := And.intro (ha.erase_unique ha' hc he.1) (hb.erase_unique hb' hc he.2)
     rfl
   | .ker ha hb ht => by
     cases h' <;> simp only [Space.erase, Surface.Space.ker.injEq, reduceCtorEq] at he
     rename_i e a b ha' hb' ht'
     obtain ⟨rfl, hety⟩ := ht.erase_unique ht' hc he
     cases hety
     rfl
   | .coker ha hb ht => by
     cases h' <;> simp only [Space.erase, Surface.Space.coker.injEq, reduceCtorEq] at he
     rename_i e a b ha' hb' ht'
     obtain ⟨rfl, hety⟩ := ht.erase_unique ht' hc he
     cases hety
     rfl
   | .img ha hb ht => by
     cases h' <;> simp only [Space.erase, Surface.Space.img.injEq, reduceCtorEq] at he
     rename_i e a b ha' hb' ht'
     obtain ⟨rfl, hety⟩ := ht.erase_unique ht' hc he
     cases hety
     rfl
   | .coimg ha hb ht => by
     cases h' <;> simp only [Space.erase, Surface.Space.coimg.injEq, reduceCtorEq] at he
     rename_i e a b ha' hb' ht'
     obtain ⟨rfl, hety⟩ := ht.erase_unique ht' hc he
     cases hety
     rfl

 termination_by structural h

 /-- Type formation recovers annotations, including beneath dependent binders. -/
 theorem TValid.erase_unique {ε τ k} (h : TValid ε τ k) {ε' υ k'} (h' : TValid ε' υ k')
     (hc : SourceCtxCompatible ∅ ε ∅ ε') (he : τ.erase = υ.erase) : τ = υ :=
   match h with
   | .space hs => by
     cases h' <;> simp only [Ty.erase, Surface.Ty.space.injEq, reduceCtorEq] at he
     rename_i t ht
     exact congrArg Ty.space (hs.erase_unique ht hc he)
   | @TValid.piTy ε a b k₀ k₁ L ha hb => by
     cases h' <;> simp only [Ty.erase, Surface.Ty.piTy.injEq, reduceCtorEq] at he
     rename_i a' b' k₀' k₁' L' ha' hb'
     have hedom := ha.erase_unique ha' hc he.1
     subst a'
     obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ L' ∪ Ty.fv b ∪ Ty.fv b')
     simp only [Finset.mem_union, not_or] at hx
     have heopen : (Ty.openVar x b).erase = (Ty.openVar x b').erase := by
       simp only [Ty.openVar, Ty.erase_openRec, Term.erase]
       rw [he.2]
     have hbEq := (hb x hx.1.1.1).erase_unique (hb' x hx.1.1.2)
       (hc.insertNL x a Finmap.notMem_empty Finmap.notMem_empty) heopen
     have hclosed := congrArg (Ty.closeRec 0 x) hbEq
     simp only [Ty.openVar, Ty.close_openVar x b hx.1.2,
       Ty.close_openVar x b' hx.2] at hclosed
     exact congrArg (Ty.piTy a) hclosed

 termination_by structural h

 /-- An erased formed subspace uniquely determines its annotation and ambient space. -/
 theorem SubType.erase_unique {ε s t} (h : SubType ε s t) {ε' s' t'} (h' : SubType ε' s' t')
     (hc : SourceCtxCompatible ∅ ε ∅ ε') (he : s.erase = s'.erase) : s = s' ∧ t = t' :=
   match h with
   | .sub_ker ha hb ht => by
     cases h' <;> simp only [Space.erase, Surface.Space.ker.injEq, reduceCtorEq] at he
     rename_i e a b ha' hb' ht'
     obtain ⟨rfl, hety⟩ := ht.erase_unique ht' hc he
     cases hety
     exact ⟨rfl, rfl⟩
   | .sub_coker ha hb ht => by
     cases h' <;> simp only [Space.erase, Surface.Space.coker.injEq, reduceCtorEq] at he
     rename_i e a b ha' hb' ht'
     obtain ⟨rfl, hety⟩ := ht.erase_unique ht' hc he
     cases hety
     exact ⟨rfl, rfl⟩
   | .sub_img ha hb ht => by
     cases h' <;> simp only [Space.erase, Surface.Space.img.injEq, reduceCtorEq] at he
     rename_i e a b ha' hb' ht'
     obtain ⟨rfl, hety⟩ := ht.erase_unique ht' hc he
     cases hety
     exact ⟨rfl, rfl⟩
   | .sub_coimg ha hb ht => by
     cases h' <;> simp only [Space.erase, Surface.Space.coimg.injEq, reduceCtorEq] at he
     rename_i e a b ha' hb' ht'
     obtain ⟨rfl, hety⟩ := ht.erase_unique ht' hc he
     cases hety
     exact ⟨rfl, rfl⟩

 termination_by structural h

 /-- Compatible contexts and equal erasures determine the annotated term and its type. -/
 theorem HasType.erase_unique {Δ ε e τ} (h : HasType Δ ε e τ)
     {Δ' ε' e' τ'} (h' : HasType Δ' ε' e' τ')
     (hc : SourceCtxCompatible Δ ε Δ' ε') (he : e.erase = e'.erase) : e = e' ∧ τ = τ' := by
   obtain ⟨Δ', ε', h', hcore, bindings₂⟩ := h'.coreView
   have hc := hc.mono (fun _ _ h => h) bindings₂
   exact match h with
   | .promote lin hdΔ hdε hf h => by
     exact h.erase_unique h'
       (hc.mono (fun x υ b => (SourceBinding.promote_iff _ _ _ x υ hdΔ hdε).mp b)
         (fun _ _ b => b)) he
   | .zero hs => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.zero.injEq, reduceCtorEq] at he
     rename_i s hs'
     have hsEq := hs.erase_unique hs' hc.nonlin he
     cases hsEq
     exact ⟨rfl, rfl⟩
   | .inner hs => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.inner.injEq, reduceCtorEq] at he
     rename_i s hs'
     have hsEq := hs.erase_unique hs' hc.nonlin he
     cases hsEq
     exact ⟨rfl, rfl⟩
   | .real_lit r => by
     cases h' <;> simp_all [HasType.IsCore, Term.erase]
   | @HasType.var_lin ε x s => by
     have hvar : e' = .var x := by
       cases e' <;> simp_all [Term.erase]
     subst e'
     have hty := hc _ _ _ (HasType.var_lin.var_sourceBinding) h'.var_sourceBinding
     exact ⟨rfl, hty⟩
   | @HasType.var_nlin ε x τ hl => by
     have hvar : e' = .var x := by
       cases e' <;> simp_all [Term.erase]
     subst e'
     exact ⟨rfl, hc _ _ _ (Or.inr hl) h'.var_sourceBinding⟩
   | .embed hs => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.embed.injEq, reduceCtorEq] at he
     rename_i a b hs'
     obtain ⟨rfl, rfl⟩ := hs.erase_unique hs' hc.nonlin he
     exact ⟨rfl, rfl⟩
   | .smul hs hd h₀ h₁ => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.smul.injEq, reduceCtorEq] at he
     rename_i Δ₀' Δ₁' e₀' e₁' s' hd' hs' h₀' h₁'
     obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.split hd hd').1 he.1
     obtain ⟨rfl, ht₁⟩ := h₁.erase_unique h₁' (hc.split hd hd').2 he.2
     exact ⟨rfl, ht₁⟩
   | .add hs h₀ h₁ => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.add.injEq, reduceCtorEq] at he
     rename_i e₀' e₁' s' hs' h₀' h₁'
     obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' hc he.1
     obtain ⟨rfl, ht₁⟩ := h₁.erase_unique h₁' hc he.2
     exact ⟨rfl, ht₁⟩
   | .dsumE hs₀ hs₁ h₀ h₁ => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.dsumE.injEq, reduceCtorEq] at he
     rename_i e₀' e₁' s₀' s₁' hs₀' hs₁' h₀' h₁'
     obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' hc he.1
     obtain ⟨rfl, ht₁⟩ := h₁.erase_unique h₁' hc he.2
     cases ht₀
     cases ht₁
     exact ⟨rfl, rfl⟩
   | .tprodE hs₀ hs₁ hd h₀ h₁ => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.tprodE.injEq, reduceCtorEq] at he
     rename_i Δ₀' Δ₁' e₀' e₁' s₀' s₁' hd' hs₀' hs₁' h₀' h₁'
     obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.split hd hd').1 he.1
     obtain ⟨rfl, ht₁⟩ := h₁.erase_unique h₁' (hc.split hd hd').2 he.2
     cases ht₀
     cases ht₁
     exact ⟨rfl, rfl⟩
   | .pinv_tensor hs₀ hs₁ ht => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.pinv.injEq, reduceCtorEq] at he
     case pinv_tensor e a b ha' hb' ht' =>
       obtain ⟨rfl, htEq⟩ := ht.erase_unique ht' hc he
       cases htEq
       exact ⟨rfl, rfl⟩
     case pinv_dual e a ha' ht' =>
       obtain ⟨rfl, htEq⟩ := ht.erase_unique ht' hc he
       cases htEq
   | .pinv_dual hs ht => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.pinv.injEq, reduceCtorEq] at he
     case pinv_tensor e a b ha' hb' ht' =>
       obtain ⟨rfl, htEq⟩ := ht.erase_unique ht' hc he
       cases htEq
     case pinv_dual e a ha' ht' =>
       obtain ⟨rfl, htEq⟩ := ht.erase_unique ht' hc he
       cases htEq
       exact ⟨rfl, rfl⟩
   | .app_linear hs₀ hs₁ hd h₀ h₁ => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.app.injEq, reduceCtorEq] at he
     case app_linear Δ₀' Δ₁' e₀' e₁' a b hd' ha' hb' h₀' h₁' =>
       obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.split hd hd').1 he.1
       cases ht₀
       obtain ⟨rfl, ht₁⟩ := h₁.erase_unique h₁' (hc.split hd hd').2 he.2
       exact ⟨rfl, rfl⟩
     case app_inner Δ₀' Δ₁' e₀' e₁' a hd' ha' h₀' h₁' =>
       obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.split hd hd').1 he.1
       cases ht₀
     case app_nonlinear e₀' e₁' a b h₀' h₁' =>
       obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.splitLeft hd).1 he.1
       cases ht₀
   | .app_inner hs hd h₀ h₁ => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.app.injEq, reduceCtorEq] at he
     case app_linear Δ₀' Δ₁' e₀' e₁' a b hd' ha' hb' h₀' h₁' =>
       obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.split hd hd').1 he.1
       cases ht₀
     case app_inner Δ₀' Δ₁' e₀' e₁' a hd' ha' h₀' h₁' =>
       obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.split hd hd').1 he.1
       cases ht₀
       obtain ⟨rfl, ht₁⟩ := h₁.erase_unique h₁' (hc.split hd hd').2 he.2
       exact ⟨rfl, rfl⟩
     case app_nonlinear e₀' e₁' a b h₀' h₁' =>
       obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.splitLeft hd).1 he.1
       cases ht₀
   | .app_nonlinear h₀ h₁ => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.app.injEq, reduceCtorEq] at he
     case app_linear Δ₀' Δ₁' e₀' e₁' a b hd' ha' hb' h₀' h₁' =>
       obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.splitRight hd').1 he.1
       cases ht₀
     case app_inner Δ₀' Δ₁' e₀' e₁' a hd' ha' h₀' h₁' =>
       obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' (hc.splitRight hd').1 he.1
       cases ht₀
     case app_nonlinear e₀' e₁' a b h₀' h₁' =>
       obtain ⟨rfl, ht₀⟩ := h₀.erase_unique h₀' hc he.1
       cases ht₀
       obtain ⟨rfl, ht₁⟩ := h₁.erase_unique h₁' hc he.2
       exact ⟨rfl, rfl⟩
   | @HasType.llam_real Δ ε s e L hs hb => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.llam.injEq, reduceCtorEq] at he
     case llam_real s' body' L' hs' hb' =>
       have hdom := hs.erase_unique hs' hc.nonlin he.1
       subst s'
       obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
         (L ∪ L' ∪ ε.keys ∪ ε'.keys ∪ Term.fv e ∪ Term.fv body')
       simp only [Finset.mem_union, not_or] at hx
       have hci := hc.insertLin x s
         (by simpa only [Finmap.mem_keys] using hx.1.1.1.2)
         (by simpa only [Finmap.mem_keys] using hx.1.1.2)
       obtain ⟨hbody, hty⟩ := (hb x hx.1.1.1.1.1).erase_unique
         (hb' x hx.1.1.1.1.2) hci (Term.erase_openVar_congr he.2 x)
       have hbodyEq := Term.eq_of_openVar_eq x hx.1.2 hx.2 hbody
       cases hbodyEq
       cases hty
       exact ⟨rfl, rfl⟩
     case llam_tensor a' b' body' L' hn' ha' hb' hbody' =>
       have hdom := hs.erase_unique ha' hc.nonlin he.1
       subst a'
       obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
         (L ∪ L' ∪ ε.keys ∪ ε'.keys ∪ Term.fv e ∪ Term.fv body')
       simp only [Finset.mem_union, not_or] at hx
       have hci := hc.insertLin x s
         (by simpa only [Finmap.mem_keys] using hx.1.1.1.2)
         (by simpa only [Finmap.mem_keys] using hx.1.1.2)
       obtain ⟨hbody, hty⟩ := (hb x hx.1.1.1.1.1).erase_unique
         (hbody' x hx.1.1.1.1.2) hci (Term.erase_openVar_congr he.2 x)
       cases hty
       exact (hn' rfl).elim
   | @HasType.llam_tensor Δ ε s₀ s e L hn hs₀ hs hb => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.llam.injEq, reduceCtorEq] at he
     case llam_real s' body' L' hs' hb' =>
       have hdom := hs₀.erase_unique hs' hc.nonlin he.1
       subst s'
       obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
         (L ∪ L' ∪ ε.keys ∪ ε'.keys ∪ Term.fv e ∪ Term.fv body')
       simp only [Finset.mem_union, not_or] at hx
       have hci := hc.insertLin x s₀
         (by simpa only [Finmap.mem_keys] using hx.1.1.1.2)
         (by simpa only [Finmap.mem_keys] using hx.1.1.2)
       obtain ⟨hbody, hty⟩ := (hb x hx.1.1.1.1.1).erase_unique
         (hb' x hx.1.1.1.1.2) hci (Term.erase_openVar_congr he.2 x)
       cases hty
       exact (hn rfl).elim
     case llam_tensor a' b' body' L' hn' ha' hb' hbody' =>
       have hdom := hs₀.erase_unique ha' hc.nonlin he.1
       subst a'
       obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
         (L ∪ L' ∪ ε.keys ∪ ε'.keys ∪ Term.fv e ∪ Term.fv body')
       simp only [Finset.mem_union, not_or] at hx
       have hci := hc.insertLin x s₀
         (by simpa only [Finmap.mem_keys] using hx.1.1.1.2)
         (by simpa only [Finmap.mem_keys] using hx.1.1.2)
       obtain ⟨hbody, hty⟩ := (hb x hx.1.1.1.1.1).erase_unique
         (hbody' x hx.1.1.1.1.2) hci (Term.erase_openVar_congr he.2 x)
       have hbodyEq := Term.eq_of_openVar_eq x hx.1.2 hx.2 hbody
       cases hbodyEq
       cases hty
       exact ⟨rfl, rfl⟩
   | @HasType.nllam ε a b k₀ k₁ body L hv hb => by
     cases h' <;> simp only [HasType.IsCore] at hcore
     all_goals simp only [Term.erase, Surface.Term.nllam.injEq, reduceCtorEq] at he
     rename_i a' b' k₀' k₁' body' L' hv' hb'
     match hv, hv' with
     | .piTy K ha hcod, .piTy K' ha' hcod' =>
       have hdom := ha.erase_unique ha' hc.nonlin he.1
       subst a'
       obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
         (L ∪ L' ∪ Term.fv body ∪ Term.fv body' ∪ Ty.fv b ∪ Ty.fv b')
       simp only [Finset.mem_union, not_or] at hx
       have hci := hc.insertNL x a Finmap.notMem_empty Finmap.notMem_empty
       obtain ⟨hbody, hty⟩ := (hb x hx.1.1.1.1.1).erase_unique
         (hb' x hx.1.1.1.1.2) hci (Term.erase_openVar_congr he.2 x)
       have hbodyEq := Term.eq_of_openVar_eq x hx.1.1.1.2 hx.1.1.2 hbody
       have htyEq := Ty.eq_of_openVar_eq x hx.1.2 hx.2 hty
       cases hbodyEq
       cases htyEq
       exact ⟨rfl, rfl⟩

 termination_by structural h
end
/-- In one disjoint context, equal source erasures give equal annotations and result types.
Only namespace disjointness is required; full context formation is not needed. -/
theorem HasType.annotation_unique_of_disjoint {Δ ε e₁ e₂ τ₁ τ₂}
    (hd : ∀ x, x ∈ Δ → x ∉ ε)
    (h₁ : HasType Δ ε e₁ τ₁) (h₂ : HasType Δ ε e₂ τ₂)
    (he : e₁.erase = e₂.erase) : e₁ = e₂ ∧ τ₁ = τ₂ :=
  h₁.erase_unique h₂ (fun _ _ _ b₁ b₂ => SourceBinding.functional hd b₁ b₂) he

theorem HasType.annotation_unique {Δ ε e₁ e₂ τ₁ τ₂}
    (hwf : InductiveCtxWF Δ ε)
    (h₁ : HasType Δ ε e₁ τ₁) (h₂ : HasType Δ ε e₂ τ₂)
    (he : e₁.erase = e₂.erase) : e₁ = e₂ ∧ τ₁ = τ₂ :=
  annotation_unique_of_disjoint hwf.toSourceContextWF.scoping.disjoint h₁ h₂ he

/-- A fully annotated term also has a unique type in a well-formed context. -/
theorem HasType.type_unique {Δ ε e τ₁ τ₂} (hwf : InductiveCtxWF Δ ε)
    (h₁ : HasType Δ ε e τ₁) (h₂ : HasType Δ ε e τ₂) : τ₁ = τ₂ :=
  (annotation_unique hwf h₁ h₂ rfl).2

/-- Denotation is independent of the choice of well-typed implementation annotations.
The semantic environment is arbitrary: annotation equality is already syntactic. -/
theorem HasType.denot_eq_of_erase_eq {Δ ε e₁ e₂ τ₁ τ₂}
    (hwf : InductiveCtxWF Δ ε)
    (h₁ : HasType Δ ε e₁ τ₁) (h₂ : HasType Δ ε e₂ τ₂)
    (he : e₁.erase = e₂.erase) (σ : DEnv) : denotTerm σ e₁ = denotTerm σ e₂ :=
  congrArg (denotTerm σ) (annotation_unique hwf h₁ h₂ he).1

/-- Space annotation uniqueness in a fixed nonlinear context. -/
theorem SValid.annotation_unique {ε s₁ s₂}
    (h₁ : SValid ε s₁) (h₂ : SValid ε s₂) (he : s₁.erase = s₂.erase) : s₁ = s₂ :=
  h₁.erase_unique h₂
    (fun _ _ _ b₁ b₂ => SourceBinding.functional
      (fun _ hx => (Finmap.notMem_empty hx).elim) b₁ b₂) he

/-- Type annotation uniqueness in a fixed nonlinear context. -/
theorem TValid.annotation_unique {ε τ₁ τ₂ k₁ k₂}
    (h₁ : TValid ε τ₁ k₁) (h₂ : TValid ε τ₂ k₂) (he : τ₁.erase = τ₂.erase) : τ₁ = τ₂ :=
  h₁.erase_unique h₂
    (fun _ _ _ b₁ b₂ => SourceBinding.functional
      (fun _ hx => (Finmap.notMem_empty hx).elim) b₁ b₂) he

/-- A formed subspace's ambient space is unique in a fixed nonlinear context. -/
theorem SubType.annotation_unique {ε s₁ s₂ t₁ t₂}
    (h₁ : SubType ε s₁ t₁) (h₂ : SubType ε s₂ t₂)
    (he : s₁.erase = s₂.erase) : s₁ = s₂ ∧ t₁ = t₂ :=
  h₁.erase_unique h₂
    (fun _ _ _ b₁ b₂ => SourceBinding.functional
      (fun _ hx => (Finmap.notMem_empty hx).elim) b₁ b₂) he

end GLang
