import GLang.Proofs.Value.Presentation.PaperValueFreshCoherence
import GLang.Proofs.Value.Binding.ValueMatchedOpening

namespace GLang.PaperValueDomains
open ValueDependency

/-- Only annotated variables that agree with the current typing context demand
declaration coherence. This is an induction input for the current syntax. -/
def MatchedAnnotationsCoherent (orc : FFSOracleSem) (ε : ValCtx)
    (ρ ρ' : ValEnvSem) (xs : List (VName × ValTy)) : Prop :=
  ∀ x a, (x, a) ∈ xs → ε.lookup x = some a →
    TypeCoherent orc a ⟨ρ, [], []⟩ ⟨ρ', [], []⟩

theorem MatchedAnnotationsCoherent.mono {orc : FFSOracleSem} {ε : ValCtx}
    {ρ ρ' : ValEnvSem} {xs ys : List (VName × ValTy)}
    (h : MatchedAnnotationsCoherent orc ε ρ ρ' ys) (hs : xs ⊆ ys) :
    MatchedAnnotationsCoherent orc ε ρ ρ' xs :=
  fun x a hx hl => h x a (hs hx) hl

/-- The value-environment assumption is global; declaration coherence is
restricted to matched annotations in the syntax currently being proved. -/
structure MatchedContextRelated (orc : FFSOracleSem) (ε : ValCtx)
    (ρ ρ' : ValEnvSem) (xs : List (VName × ValTy)) : Prop where
  valid : Nonempty (ValCtxValid ε)
  values : EnvironmentsRelated orc ε ρ ρ'
  coherent : MatchedAnnotationsCoherent orc ε ρ ρ' xs

theorem MatchedContextRelated.mono {orc : FFSOracleSem} {ε : ValCtx}
    {ρ ρ' : ValEnvSem} {xs ys : List (VName × ValTy)}
    (h : MatchedContextRelated orc ε ρ ρ' ys) (hs : xs ⊆ ys) :
    MatchedContextRelated orc ε ρ ρ' xs :=
  ⟨h.valid, h.values, h.coherent.mono hs⟩

theorem ContextRelated.matched {orc : FFSOracleSem} {ε : ValCtx}
    {ρ ρ' : ValEnvSem} (h : ContextRelated orc ε ρ ρ')
    (xs : List (VName × ValTy)) : MatchedContextRelated orc ε ρ ρ' xs :=
  ⟨h.valid, fun x a hl => (h.bindings x a hl).2,
    fun x a _ hl => (h.bindings x a hl).1⟩

private theorem fresh_type_coherent {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (ρ ρ' : ValEnvSem) (x : VName) (v v' : ValValSem) (a : ValTy)
    (hfresh : x ∉ a.fv)
    (h : TypeCoherent orc a ⟨ρ, [], []⟩ ⟨ρ', [], []⟩) :
    TypeCoherent orc a ⟨ρ.update x v, [], []⟩ ⟨ρ'.update x v', [], []⟩ :=
  TypeCoherent.fiber_transport orc a _ _ _ _
    (FiberAgreement.fresh hirr a _ _ x v v'
      (by simp [ValTyCtxFresh]) (by simp [ValTyCtxFresh]) hfresh) h

/-- The matched coherence motive is stable under the actual fresh opening.
Only syntactic occurrence inversion and fresh oracle locality are needed. -/
theorem matchedCoherence_opening {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (ε : ValCtx) (ρ ρ' : ValEnvSem) (xs ys : List (VName × ValTy))
    (x : VName) (d : ValTy) (v v' : ValValSem)
    (hinverse : ∀ y a, (y, a) ∈ ys →
      (∃ b j, (y, b) ∈ xs ∧ a = ValTy.openRec j (.var x d) b) ∨
        (y, a) ∈ exprAnnotations (.var x d))
    (hbody : MatchedAnnotationsCoherent orc ε ρ ρ' xs)
    (hdom : MatchedAnnotationsCoherent orc ε ρ ρ' (typeAnnotations d))
    (hd : TypeCoherent orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (hname : ∀ y a, (y, a) ∈ xs → y ≠ x)
    (hann : x ∉ annotationSupport xs) (hdfresh : x ∉ d.fv)
    (hstored : ∀ y a, ε.lookup y = some a → x ∉ a.fv) :
    MatchedAnnotationsCoherent orc (Finmap.insert x d ε)
      (ρ.update x v) (ρ'.update x v') ys := by
  intro y a hya hlookup
  rcases hinverse y a hya with ⟨b, j, hb, hab⟩ | hu
  · have hyx := hname y b hb
    rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
    have hba := opened_annotation_eq x d b a j
      (annotationSupport_fresh hann hb) (hstored _ _ hlookup) hab.symm
    subst b
    exact fresh_type_coherent hirr ρ ρ' x v v' a
      (hstored _ _ hlookup) (hbody y a hb hlookup)
  · simp only [exprAnnotations, List.mem_cons, Prod.mk.injEq] at hu
    rcases hu with ⟨hy, ha⟩ | hu
    · subst y
      subst a
      exact fresh_type_coherent hirr ρ ρ' x v v' d hdfresh hd
    · have hy : y ∈ d.fv := by
        rw [typeAnnotations_fv]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(y, a), hu, rfl⟩)
      have hyx : y ≠ x := by intro heq; subst y; exact hdfresh hy
      rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
      exact fresh_type_coherent hirr ρ ρ' x v v' a
        (hstored _ _ hlookup) (hdom y a hu hlookup)

/-- Stored runtime relations survive a fresh binder without assuming coherence
of every declaration in the context. -/
theorem EnvironmentsRelated.update {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    {ε : ValCtx} {ρ ρ' : ValEnvSem} (h : EnvironmentsRelated orc ε ρ ρ')
    (x : VName) (d : ValTy) (v v' : ValValSem)
    (hsupport : x ∉ ε.fvSupport) (hfresh : x ∉ d.fv)
    (hv : RuntimeRelated orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ v v') :
    EnvironmentsRelated orc (Finmap.insert x d ε) (ρ.update x v) (ρ'.update x v') := by
  intro y a hl
  by_cases hyx : y = x
  · subst y
    simp only [Finmap.lookup_insert, Option.some.injEq] at hl
    subst a
    rw [ValEnvSem.update_same, ValEnvSem.update_same]
    exact runtime_fiber_transport orc d _ _ _ _
      (FiberAgreement.fresh hirr d _ _ x v v'
        (by simp [ValTyCtxFresh]) (by simp [ValTyCtxFresh]) hfresh) v v' hv
  · rw [Finmap.lookup_insert_of_ne _ hyx] at hl
    rw [ValEnvSem.update_other _ _ _ _ hyx, ValEnvSem.update_other _ _ _ _ hyx]
    exact runtime_fiber_transport orc a _ _ _ _
      (FiberAgreement.fresh hirr a _ _ x v v'
        (by simp [ValTyCtxFresh]) (by simp [ValTyCtxFresh])
        (ValCtx.not_mem_fv_of_not_mem_support hsupport hl)) _ _ (h y a hl)

/-- Binder extension for the weaker, syntax-local correspondence motive.
It retains original context validity and all stored runtime relations. -/
theorem MatchedContextRelated.update_opening {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc) {ε : ValCtx} {ρ ρ' : ValEnvSem}
    {xs ys : List (VName × ValTy)} (h : MatchedContextRelated orc ε ρ ρ' xs)
    (x : VName) (d : ValTy) (v v' : ValValSem) {k : ValKind}
    (ht : ValTValid ε d k) (hx : x ∉ ε) (hsupport : x ∉ ε.fvSupport)
    (hinverse : ∀ y a, (y, a) ∈ ys →
      (∃ b j, (y, b) ∈ xs ∧ a = ValTy.openRec j (.var x d) b) ∨
        (y, a) ∈ exprAnnotations (.var x d))
    (hdom : MatchedAnnotationsCoherent orc ε ρ ρ' (typeAnnotations d))
    (hd : TypeCoherent orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (hv : RuntimeRelated orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ v v')
    (hname : ∀ y a, (y, a) ∈ xs → y ≠ x)
    (hann : x ∉ annotationSupport xs) (hdfresh : x ∉ d.fv) :
    MatchedContextRelated orc (Finmap.insert x d ε)
      (ρ.update x v) (ρ'.update x v') ys := by
  refine ⟨?_, h.values.update hirr x d v v' hsupport hdfresh hv,
    matchedCoherence_opening hirr ε ρ ρ' xs ys x d v v' hinverse h.coherent hdom hd
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

theorem MatchedContextRelated.update_type_open {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc) {ε : ValCtx} {ρ ρ' : ValEnvSem}
    (t : ValTy) (h : MatchedContextRelated orc ε ρ ρ' (typeAnnotations t))
    (x : VName) (d : ValTy) (v v' : ValValSem) {k : ValKind}
    (ht : ValTValid ε d k) (hx : x ∉ ε) (hsupport : x ∉ ε.fvSupport)
    (hdom : MatchedAnnotationsCoherent orc ε ρ ρ' (typeAnnotations d))
    (hd : TypeCoherent orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (hv : RuntimeRelated orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ v v')
    (hfree : x ∉ t.fv) (hann : x ∉ annotationSupport (typeAnnotations t))
    (hdfresh : x ∉ d.fv) :
    MatchedContextRelated orc (Finmap.insert x d ε)
      (ρ.update x v) (ρ'.update x v') (typeAnnotations (ValTy.openVar x d t)) := by
  apply h.update_opening hirr x d v v' ht hx hsupport
    (fun y a ha => typeAnnotations_open_inverse t y a 0 (.var x d) ha)
    hdom hd hv ?_ hann hdfresh
  intro y a ha heq
  subst y
  apply hfree
  rw [typeAnnotations_fv]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(x, a), ha, rfl⟩)

theorem MatchedContextRelated.update_expr_open {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc) {ε : ValCtx} {ρ ρ' : ValEnvSem}
    (e : ValExpr) (h : MatchedContextRelated orc ε ρ ρ' (exprAnnotations e))
    (x : VName) (d : ValTy) (v v' : ValValSem) {k : ValKind}
    (ht : ValTValid ε d k) (hx : x ∉ ε) (hsupport : x ∉ ε.fvSupport)
    (hdom : MatchedAnnotationsCoherent orc ε ρ ρ' (typeAnnotations d))
    (hd : TypeCoherent orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (hv : RuntimeRelated orc d ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ v v')
    (hfree : x ∉ e.fv) (hann : x ∉ annotationSupport (exprAnnotations e))
    (hdfresh : x ∉ d.fv) :
    MatchedContextRelated orc (Finmap.insert x d ε)
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
theorem typeCoherent_of_matched_step (orc : FFSOracleSem) (ε : ValCtx)
    (ρ ρ' : ValEnvSem) (hvalid : ValCtxValid ε)
    (hvalues : EnvironmentsRelated orc ε ρ ρ')
    (step : ∀ (t : ValTy) (k : ValKind), ValTValid ε t k →
      MatchedContextRelated orc ε ρ ρ' (typeAnnotations t) →
      TypeCoherent orc t ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (t : ValTy) (k : ValKind) (ht : ValTValid ε t k) :
    TypeCoherent orc t ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ := by
  apply step t k ht
  refine ⟨⟨hvalid⟩, hvalues, ?_⟩
  intro x a ha hl
  obtain ⟨ka, hka⟩ := hvalid x a hl
  exact typeCoherent_of_matched_step orc ε ρ ρ' hvalid hvalues step a ka hka
termination_by t.size
decreasing_by exact typeAnnotations_rank t x a ha

/-- Once the syntax-local original type theorem is proved, the existing
formation-valid, runtime-related environment contract yields ContextRelated
without adding declaration coherence to its premises. -/
theorem contextRelated_of_matched_step (orc : FFSOracleSem) (ε : ValCtx)
    (ρ ρ' : ValEnvSem) (hvalid : ValCtxValid ε)
    (hvalues : EnvironmentsRelated orc ε ρ ρ')
    (step : ∀ (t : ValTy) (k : ValKind), ValTValid ε t k →
      MatchedContextRelated orc ε ρ ρ' (typeAnnotations t) →
      TypeCoherent orc t ⟨ρ, [], []⟩ ⟨ρ', [], []⟩) :
    ContextRelated orc ε ρ ρ' := by
  refine ⟨⟨hvalid⟩, ?_⟩
  intro x t hl
  obtain ⟨k, ht⟩ := hvalid x t hl
  exact ⟨typeCoherent_of_matched_step orc ε ρ ρ' hvalid hvalues step t k ht,
    hvalues x t hl⟩

end GLang.PaperValueDomains
