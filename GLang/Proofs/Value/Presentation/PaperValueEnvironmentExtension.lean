import GLang.Proofs.Value.Presentation.PaperValueFullCorrespondence

/-! Extensional environment formation at the external-input boundary.
Internally computed bindings inherit the condition from original typing;
external callbacks must supply it. No operational premises are changed. -/
namespace GLang.PaperValueResults
open PaperValueDomains

/-- Import an extensional runtime value at a fresh, valid declaration. -/
theorem EnvWF.extend {ε : ValCtx} {ρ : ValEnvSem} (hρ : EnvWF ε ρ)
    {x : VName} {τ : ValTy} {k : ValKind} {v : ValValSem}
    (ht : ValTValid ε τ k) (hx : x ∉ ε) (hs : x ∉ ε.fvSupport)
    (hf : x ∉ τ.fv)
    (hv : RuntimeRelated directOracle τ ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩ v v) :
    EnvWF (Finmap.insert x τ ε) (ρ.update x v) := by
  refine ⟨?_, hρ.2.update directOracle_spec.fvIrrel x τ v v hs hf hv⟩
  obtain ⟨hc⟩ := hρ.1
  refine ⟨?_⟩
  intro y a hl
  by_cases hy : y = x
  · subst y
    simp only [Finmap.lookup_insert, Option.some.injEq] at hl
    subst a
    exact ⟨k, ht.weaken hx⟩
  · rw [Finmap.lookup_insert_of_ne _ hy] at hl
    obtain ⟨ka, ha⟩ := hc y a hl
    exact ⟨ka, ha.weaken hx⟩

/-- A successful originally typed computation automatically supplies the
extensionality required by environment extension, at arbitrary higher order. -/
theorem EnvWF.extend_of_eval {ε : ValCtx} {ρ : ValEnvSem} (hρ : EnvWF ε ρ)
    {x : VName} {e : ValExpr} {τ : ValTy} {v : ValValSem}
    (he : ValHasType ε e τ) (hx : x ∉ ε) (hs : x ∉ ε.fvSupport)
    (hf : x ∉ τ.fv)
    (hv : denotValB_semS directOracle ρ [] [] e = .ok v) :
    EnvWF (Finmap.insert x τ ε) (ρ.update x v) := by
  obtain ⟨hc⟩ := hρ.1
  obtain ⟨k, ht⟩ := he.regular hc
  apply hρ.extend ht hx hs hf
  have hr := (valueDomainSoundness ρ hρ he).2
  simpa only [hv, PartialRel] using hr

end GLang.PaperValueResults
