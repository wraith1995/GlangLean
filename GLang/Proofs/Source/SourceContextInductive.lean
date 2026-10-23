import GLang.Annotated.Context
import GLang.Proofs.Source.SourceSoundnessStrong
import GLang.Proofs.Adequacy.Foundations.Consistent

namespace GLang

namespace Metatheory

structure SourceContextWF (Δ : LCtx) (ε : NLCtx) : Prop where
  scoping : CtxWF Δ ε
  formed : Nonempty (SourceCtxValid Δ ε)

end Metatheory

private theorem scope_linear {Δ ε x s}
    (h : CtxWF Δ ε) (hxε : x ∉ ε)
    (hfv : ∀ y ∈ Space.fv s, y ∈ ε) :
    CtxWF (Finmap.insert x s Δ) ε := by
  refine ⟨?_, ?_, h.nl_fv_in_ε⟩
  · intro y hy
    rcases Finmap.mem_insert.mp hy with rfl | hy
    · exact hxε
    · exact h.disjoint y hy
  · intro y t hl z hz
    by_cases hy : y = x
    · subst y
      simp only [Finmap.lookup_insert, Option.some.injEq] at hl
      cases hl
      exact hfv z hz
    · rw [Finmap.lookup_insert_of_ne _ hy] at hl
      exact h.lin_fv_in_ε y t hl z hz

private theorem scope_nonlinear {Δ ε x τ}
    (h : CtxWF Δ ε) (hxΔ : x ∉ Δ)
    (hfv : ∀ y ∈ Ty.fv τ, y ∈ ε) :
    CtxWF Δ (Finmap.insert x τ ε) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy hm
    rcases Finmap.mem_insert.mp hm with rfl | hm
    · exact hxΔ hy
    · exact h.disjoint y hy hm
  · intro y s hl z hz
    exact Finmap.mem_insert.mpr (Or.inr (h.lin_fv_in_ε y s hl z hz))
  · intro y t hl z hz
    apply Finmap.mem_insert.mpr
    apply Or.inr
    by_cases hy : y = x
    · subst y
      simp only [Finmap.lookup_insert, Option.some.injEq] at hl
      cases hl
      exact hfv z hz
    · rw [Finmap.lookup_insert_of_ne _ hy] at hl
      exact h.nl_fv_in_ε y t hl z hz

/-- Inductive construction supplies the complete flat context condition used by
source-term soundness. Nonlinear extension weakens every existing formation
judgment into the larger nonlinear context. -/
theorem InductiveCtxWF.toSourceContextWF {Δ ε} (h : InductiveCtxWF Δ ε) :
    Metatheory.SourceContextWF Δ ε := by
  induction h with
  | empty =>
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro x hx
        exact (Finmap.notMem_empty hx).elim
      · intro x s hl
        simp only [Finmap.lookup_empty] at hl
        cases hl
      · intro x τ hl
        simp only [Finmap.lookup_empty] at hl
        cases hl
    · intro x s hl
      simp at hl
    · intro x τ hl
      simp at hl
  | @linear Δ ε x s ctx hxΔ hxε hfv hs ih =>
    obtain ⟨hv⟩ := ih.formed
    refine ⟨scope_linear ih.scoping hxε hfv, ⟨?_, hv.nonlinear⟩⟩
    intro y t hl
    by_cases hy : y = x
    · subst y
      simp only [Finmap.lookup_insert, Option.some.injEq] at hl
      cases hl
      exact hs
    · rw [Finmap.lookup_insert_of_ne _ hy] at hl
      exact hv.linear y t hl
  | @nonlinear Δ ε x τ k ctx hxΔ hxε hfv ht ih =>
    obtain ⟨hv⟩ := ih.formed
    refine ⟨scope_nonlinear ih.scoping hxΔ hfv, ⟨?_, ?_⟩⟩
    · intro y s hl
      exact SValid.weakenInsertNL x τ hxε (hv.linear y s hl)
    · intro y t hl
      by_cases hy : y = x
      · subst y
        simp only [Finmap.lookup_insert, Option.some.injEq] at hl
        cases hl
        exact ⟨k, TValid.weakenInsertNL x τ hxε ht⟩
      · rw [Finmap.lookup_insert_of_ne _ hy] at hl
        obtain ⟨j, hj⟩ := hv.nonlinear y t hl
        exact ⟨j, TValid.weakenInsertNL x τ hxε hj⟩

/-- Source denotational soundness using the inductive context condition directly. -/
theorem InductiveCtxWF.sourceTermSoundness
    {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty} {σ : DEnv}
    (hctx : InductiveCtxWF Δ ε) (htyped : HasType Δ ε e τ)
    (henv : EnvWF σ Δ ε) : StrongSourceSoundProp σ Δ ε e τ := by
  have flat := hctx.toSourceContextWF
  obtain ⟨valid⟩ := flat.formed
  exact strongSourceSoundnessProp htyped flat.scoping henv valid

end GLang
