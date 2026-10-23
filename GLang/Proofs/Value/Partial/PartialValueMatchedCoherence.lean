import GLang.Proofs.Value.Partial.PartialValueRawCoherence
import GLang.Proofs.Value.Binding.ValueMatchedOpening
import GLang.Proofs.Value.Binding.ValueWeaken
import GLang.Proofs.Adequacy.Foundations.ValueSoundnessSemS

namespace GLang.PartialValueDomains
open ValueDependency PaperValueDomains

/-- Fresh environment extension retains partial raw runtime membership. -/
theorem PartialEnvironmentsRelated.update {orc : PartialFFSOracleSem}
    {ε : ValCtx} {ρ ρ' : ValEnvSem} (h : PartialEnvironmentsRelated orc ε ρ ρ')
    (hf : PartialDirectFv.OracleFresh orc) (x : VName) (d : ValTy) (v v' : ValValSem)
    (hs : x ∉ ε.fvSupport) (hd : x ∉ d.fv)
    (hv : PartialRuntimeRelated d (PartialWorldType orc ⟨ρ,[],[]⟩ d)
      (PartialWorldType orc ⟨ρ',[],[]⟩ d) v v') :
    PartialEnvironmentsRelated orc (Finmap.insert x d ε) (ρ.update x v) (ρ'.update x v') := by
  intro y t ht
  by_cases hy : y = x
  · subst y
    simp only [Finmap.lookup_insert,Option.some.injEq] at ht
    subst t
    simpa only [ValEnvSem.update_same,PartialWorldType,
      PartialDirectFv.type_eq hf ρ x v d [] [] (by simp [ValTyCtxFresh]) hd,
      PartialDirectFv.type_eq hf ρ' x v' d [] [] (by simp [ValTyCtxFresh]) hd] using hv
  · rw [Finmap.lookup_insert_of_ne _ hy] at ht
    have hty := ValCtx.not_mem_fv_of_not_mem_support hs ht
    have hh := h y t ht
    simpa only [ValEnvSem.update_other ρ x y v hy, ValEnvSem.update_other ρ' x y v' hy,PartialWorldType,
      PartialDirectFv.type_eq hf ρ x v t [] [] (by simp [ValTyCtxFresh]) hty,
      PartialDirectFv.type_eq hf ρ' x v' t [] [] (by simp [ValTyCtxFresh]) hty] using hh

/-- Only annotated variables that agree with the current typing context demand
declaration coherence. This is an induction input for the current syntax. -/
def MatchedAnnotationsRawCoherent (orc : PartialFFSOracleSem) (ε : ValCtx)
    (ρ ρ' : ValEnvSem) (xs : List (VName × ValTy)) : Prop :=
  ∀ x a, (x, a) ∈ xs → ε.lookup x = some a →
    PartialRawTypeCoherent orc a ⟨ρ, [], []⟩ ⟨ρ', [], []⟩

theorem MatchedAnnotationsRawCoherent.mono {orc : PartialFFSOracleSem} {ε : ValCtx}
    {ρ ρ' : ValEnvSem} {xs ys : List (VName × ValTy)}
    (h : MatchedAnnotationsRawCoherent orc ε ρ ρ' ys) (hs : xs ⊆ ys) :
    MatchedAnnotationsRawCoherent orc ε ρ ρ' xs :=
  fun x a hx hl => h x a (hs hx) hl

/-- The value-environment assumption is global; declaration coherence is
restricted to matched annotations in the syntax currently being proved. -/
structure RawMatchedContextRelated (orc : PartialFFSOracleSem) (ε : ValCtx)
    (ρ ρ' : ValEnvSem) (xs : List (VName × ValTy)) : Prop where
  valid : Nonempty (ValCtxValid ε)
  values : PartialEnvironmentsRelated orc ε ρ ρ'
  coherent : MatchedAnnotationsRawCoherent orc ε ρ ρ' xs

theorem RawMatchedContextRelated.mono {orc : PartialFFSOracleSem} {ε : ValCtx}
    {ρ ρ' : ValEnvSem} {xs ys : List (VName × ValTy)}
    (h : RawMatchedContextRelated orc ε ρ ρ' ys) (hs : xs ⊆ ys) :
    RawMatchedContextRelated orc ε ρ ρ' xs :=
  ⟨h.valid, h.values, h.coherent.mono hs⟩

private theorem fresh_raw_type_coherent {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    (ρ ρ' : ValEnvSem) (x : VName) (v v' : ValValSem) (a : ValTy)
    (hfresh : x ∉ a.fv)
    (h : PartialRawTypeCoherent orc a ⟨ρ, [], []⟩ ⟨ρ', [], []⟩) :
    PartialRawTypeCoherent orc a ⟨ρ.update x v, [], []⟩ ⟨ρ'.update x v', [], []⟩ :=
  PartialRawTypeCoherent.fresh hirr a ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ x v v'
    (by simp [ValTyCtxFresh]) (by simp [ValTyCtxFresh]) hfresh h

/-- The matched coherence motive is stable under the actual fresh opening.
Only syntactic occurrence inversion and fresh oracle locality are needed. -/
theorem matchedRawCoherence_opening {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    (ε : ValCtx) (ρ ρ' : ValEnvSem) (xs ys : List (VName × ValTy))
    (x : VName) (d : ValTy) (v v' : ValValSem)
    (hinverse : ∀ y a, (y, a) ∈ ys →
      (∃ b j, (y, b) ∈ xs ∧ a = ValTy.openRec j (.var x d) b) ∨
        (y, a) ∈ exprAnnotations (.var x d))
    (hbody : MatchedAnnotationsRawCoherent orc ε ρ ρ' xs)
    (hdom : MatchedAnnotationsRawCoherent orc ε ρ ρ' (typeAnnotations d))
    (hd : PartialRawTypeCoherent orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (hname : ∀ y a, (y, a) ∈ xs → y ≠ x)
    (hann : x ∉ annotationSupport xs) (hdfresh : x ∉ d.fv)
    (hstored : ∀ y a, ε.lookup y = some a → x ∉ a.fv) :
    MatchedAnnotationsRawCoherent orc (Finmap.insert x d ε)
      (ρ.update x v) (ρ'.update x v') ys := by
  intro y a hya hlookup
  rcases hinverse y a hya with ⟨b, j, hb, hab⟩ | hu
  · have hyx := hname y b hb
    rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
    have hba := opened_annotation_eq x d b a j
      (annotationSupport_fresh hann hb) (hstored _ _ hlookup) hab.symm
    subst b
    exact fresh_raw_type_coherent hirr ρ ρ' x v v' a
      (hstored _ _ hlookup) (hbody y a hb hlookup)
  · simp only [exprAnnotations, List.mem_cons, Prod.mk.injEq] at hu
    rcases hu with ⟨hy, ha⟩ | hu
    · subst y
      subst a
      exact fresh_raw_type_coherent hirr ρ ρ' x v v' d hdfresh hd
    · have hy : y ∈ d.fv := by
        rw [typeAnnotations_fv]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(y, a), hu, rfl⟩)
      have hyx : y ≠ x := by intro heq; subst y; exact hdfresh hy
      rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
      exact fresh_raw_type_coherent hirr ρ ρ' x v v' a
        (hstored _ _ hlookup) (hdom y a hu hlookup)

/-- Binder extension for the weaker, syntax-local correspondence motive.
It retains original context validity and all stored runtime relations. -/
theorem RawMatchedContextRelated.update_opening {orc : PartialFFSOracleSem}
    (hirr : PartialDirectFv.OracleFresh orc) {ε : ValCtx} {ρ ρ' : ValEnvSem}
    {xs ys : List (VName × ValTy)} (h : RawMatchedContextRelated orc ε ρ ρ' xs)
    (x : VName) (d : ValTy) (v v' : ValValSem) {k : ValKind}
    (ht : ValTValid ε d k) (hx : x ∉ ε) (hsupport : x ∉ ε.fvSupport)
    (hinverse : ∀ y a, (y, a) ∈ ys →
      (∃ b j, (y, b) ∈ xs ∧ a = ValTy.openRec j (.var x d) b) ∨
        (y, a) ∈ exprAnnotations (.var x d))
    (hdom : MatchedAnnotationsRawCoherent orc ε ρ ρ' (typeAnnotations d))
    (hd : PartialRawTypeCoherent orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (hv : PartialRuntimeRelated d (PartialWorldType orc ⟨ρ, [], []⟩ d) (PartialWorldType orc ⟨ρ', [], []⟩ d) v v')
    (hname : ∀ y a, (y, a) ∈ xs → y ≠ x)
    (hann : x ∉ annotationSupport xs) (hdfresh : x ∉ d.fv) :
    RawMatchedContextRelated orc (Finmap.insert x d ε)
      (ρ.update x v) (ρ'.update x v') ys := by
  refine ⟨?_, h.values.update hirr x d v v' hsupport hdfresh hv,
    matchedRawCoherence_opening hirr ε ρ ρ' xs ys x d v v' hinverse h.coherent hdom hd
      hname hann hdfresh (fun _ _ hl => ValCtx.not_mem_fv_of_not_mem_support hsupport hl)⟩
  obtain ⟨hvalid⟩ := h.valid
  refine ⟨?_⟩
  intro y a hl
  by_cases hyx : y = x
  · subst y
    simp only [Finmap.lookup_insert, Option.some.injEq] at hl
    subst a
    exact ⟨k, ht.weaken hx⟩
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hl
    obtain ⟨ka, ha⟩ := hvalid y a hl
    exact ⟨ka, ha.weaken hx⟩

theorem RawMatchedContextRelated.update_type_open {orc : PartialFFSOracleSem}
    (hirr : PartialDirectFv.OracleFresh orc) {ε : ValCtx} {ρ ρ' : ValEnvSem}
    (t : ValTy) (h : RawMatchedContextRelated orc ε ρ ρ' (typeAnnotations t))
    (x : VName) (d : ValTy) (v v' : ValValSem) {k : ValKind}
    (ht : ValTValid ε d k) (hx : x ∉ ε) (hsupport : x ∉ ε.fvSupport)
    (hdom : MatchedAnnotationsRawCoherent orc ε ρ ρ' (typeAnnotations d))
    (hd : PartialRawTypeCoherent orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (hv : PartialRuntimeRelated d (PartialWorldType orc ⟨ρ, [], []⟩ d) (PartialWorldType orc ⟨ρ', [], []⟩ d) v v')
    (hfree : x ∉ t.fv) (hann : x ∉ annotationSupport (typeAnnotations t))
    (hdfresh : x ∉ d.fv) :
    RawMatchedContextRelated orc (Finmap.insert x d ε)
      (ρ.update x v) (ρ'.update x v') (typeAnnotations (ValTy.openVar x d t)) := by
  apply h.update_opening hirr x d v v' ht hx hsupport
    (fun y a ha => typeAnnotations_open_inverse t y a 0 (.var x d) ha)
    hdom hd hv ?_ hann hdfresh
  intro y a ha heq
  subst y
  apply hfree
  rw [typeAnnotations_fv]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(x, a), ha, rfl⟩)

theorem RawMatchedContextRelated.update_expr_open {orc : PartialFFSOracleSem}
    (hirr : PartialDirectFv.OracleFresh orc) {ε : ValCtx} {ρ ρ' : ValEnvSem}
    (e : ValExpr) (h : RawMatchedContextRelated orc ε ρ ρ' (exprAnnotations e))
    (x : VName) (d : ValTy) (v v' : ValValSem) {k : ValKind}
    (ht : ValTValid ε d k) (hx : x ∉ ε) (hsupport : x ∉ ε.fvSupport)
    (hdom : MatchedAnnotationsRawCoherent orc ε ρ ρ' (typeAnnotations d))
    (hd : PartialRawTypeCoherent orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (hv : PartialRuntimeRelated d (PartialWorldType orc ⟨ρ, [], []⟩ d) (PartialWorldType orc ⟨ρ', [], []⟩ d) v v')
    (hfree : x ∉ e.fv) (hann : x ∉ annotationSupport (exprAnnotations e))
    (hdfresh : x ∉ d.fv) :
    RawMatchedContextRelated orc (Finmap.insert x d ε)
      (ρ.update x v) (ρ'.update x v') (exprAnnotations (ValExpr.openVar x d e)) := by
  apply h.update_opening hirr x d v v' ht hx hsupport
    (fun y a ha => exprAnnotations_open_inverse e y a 0 (.var x d) ha)
    hdom hd hv ?_ hann hdfresh
  intro y a ha heq
  subst y
  apply hfree
  rw [exprAnnotations_fv]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(x, a), ha, rfl⟩)

/-- Strict syntax-size descent discharges the matched declaration input from
formation validity. The step is the original type-validity induction theorem;
it is not an assumption about evaluation of an arbitrary term. -/
theorem rawTypeCoherent_of_matched_step (orc : PartialFFSOracleSem) (ε : ValCtx)
    (ρ ρ' : ValEnvSem) (hvalid : ValCtxValid ε)
    (hvalues : PartialEnvironmentsRelated orc ε ρ ρ')
    (step : ∀ (t : ValTy) (k : ValKind), ValTValid ε t k →
      RawMatchedContextRelated orc ε ρ ρ' (typeAnnotations t) →
      PartialRawTypeCoherent orc t ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (t : ValTy) (k : ValKind) (ht : ValTValid ε t k) :
    PartialRawTypeCoherent orc t ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ := by
  apply step t k ht
  refine ⟨⟨hvalid⟩, hvalues, ?_⟩
  intro x a ha hl
  obtain ⟨ka, hka⟩ := hvalid x a hl
  exact rawTypeCoherent_of_matched_step orc ε ρ ρ' hvalid hvalues step a ka hka
termination_by t.size
decreasing_by exact typeAnnotations_rank t x a ha

/-- Pairwise-family variant of annotation-size descent. It supplies all
self and cross coherence needed by supported dependent PER reasoning. -/
theorem rawTypeCoherent_of_matched_family_step (orc : PartialFFSOracleSem) (ε : ValCtx)
    {I : Type} (ρ : I → ValEnvSem) (hvalid : ValCtxValid ε)
    (hvalues : ∀ i j, PartialEnvironmentsRelated orc ε (ρ i) (ρ j))
    (step : ∀ (t : ValTy) (k : ValKind), ValTValid ε t k →
      (∀ i j, RawMatchedContextRelated orc ε (ρ i) (ρ j) (typeAnnotations t)) →
      ∀ i j, PartialRawTypeCoherent orc t ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩)
    (t : ValTy) (k : ValKind) (ht : ValTValid ε t k) :
    ∀ i j, PartialRawTypeCoherent orc t ⟨ρ i, [], []⟩ ⟨ρ j, [], []⟩ := by
  apply step t k ht
  intro i j
  refine ⟨⟨hvalid⟩, hvalues i j, ?_⟩
  intro x a ha hl
  obtain ⟨ka, hka⟩ := hvalid x a hl
  exact rawTypeCoherent_of_matched_family_step orc ε ρ hvalid hvalues step a ka hka i j
termination_by t.size
decreasing_by exact typeAnnotations_rank t x a ha

end GLang.PartialValueDomains
