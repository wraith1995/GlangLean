import GLang.Proofs.Value.Presentation.PaperValueDependentCoherence
import GLang.Proofs.Adequacy.Foundations.FvIrrel
import GLang.Proofs.Adequacy.Foundations.ValueSoundnessSemS
import GLang.Proofs.Value.Binding.ValueWeaken
import GLang.Proofs.Value.Soundness.ValueSoundVals

/-! Fresh named bindings preserve dependent type and value relations. The proof
uses the established free-variable locality of the oracle, not a premise about
equivalence of arbitrary evaluations. -/
namespace GLang.PaperValueDomains

def World.update (w : World) (x : VName) (v : ValValSem) : World :=
  ⟨w.env.update x v, w.types, w.values⟩

private theorem reify_heq {T U : ValTypeSem} (h : T = U)
    {a : T.El} {b : U.El} (hab : HEq a b) :
    ValValSem.fromEl T a = ValValSem.fromEl U b := by
  cases h
  cases eq_of_heq hab
  rfl

theorem SpaceOracleAgreement.fresh {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (w : World) (x : VName) (v : ValValSem) (hG : ValTyCtxFresh x w.types)
    (s : ValSpace) (hx : x ∉ ValSpace.fv s) :
    SpaceOracleAgreement (orc w.env w.types w.values)
      (orc (w.update x v).env w.types w.values) s := by
  cases s with
  | empty | real => trivial
  | dsum s t | tprod s t =>
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hx
      exact ⟨SpaceOracleAgreement.fresh hirr w x v hG s hx.1,
        SpaceOracleAgreement.fresh hirr w x v hG t hx.2⟩
  | ffs p s e =>
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hx
      exact (hirr w.env x v w.types w.values p s e hG hx.1 hx.2).symm
termination_by sizeOf s

private theorem push_update {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (w : World) (x : VName) (v : ValValSem) (hG : ValTyCtxFresh x w.types)
    (τ : ValTy) (hx : x ∉ ValTy.fv τ)
    (a : (w.denot orc τ).El) (a' : ((w.update x v).denot orc τ).El)
    (ha : HEq a a') :
    (w.update x v).push orc τ a' = (w.push orc τ a).update x v := by
  have ht : (w.update x v).denot orc τ = w.denot orc τ :=
    denotValTyS_update_of_not_mem_fv hirr w.env x v τ w.types w.values hG hx
  have hv := reify_heq ht ha.symm
  simp only [World.update] at hv
  simp only [World.push, World.update]
  rw [hv]

/-- Freshness extends through every dependent arrow fibre, including its actual
reified argument stack. No equality of unrelated callbacks is required. -/
theorem FiberAgreement.fresh {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (τ : ValTy) (w w' : World) (x : VName) (v v' : ValValSem)
    (hG : ValTyCtxFresh x w.types) (hG' : ValTyCtxFresh x w'.types)
    (hx : x ∉ ValTy.fv τ) :
    FiberAgreement orc τ w w' (w.update x v) (w'.update x v') := by
  cases τ with
  | space s =>
      exact ⟨SpaceOracleAgreement.fresh hirr w x v hG s hx,
        SpaceOracleAgreement.fresh hirr w' x v' hG' s hx⟩
  | piTy d c =>
      simp only [ValTy.fv, Finset.mem_union, not_or] at hx
      refine ⟨FiberAgreement.fresh hirr d w w' x v v' hG hG' hx.1, ?_⟩
      intro a b a' b' ha hb _
      rw [push_update hirr w x v hG d hx.1 a a' ha,
        push_update hirr w' x v' hG' d hx.1 b b' hb]
      exact FiberAgreement.fresh hirr c (w.push orc d a) (w'.push orc d b)
        x v v' (ValTyCtxFresh.cons hx.1 hG) (ValTyCtxFresh.cons hx.1 hG') hx.2
termination_by sizeOf τ

/-- A scoped relational input context: declared types have coherent dependent
fibres and their stored values preserve related inputs. -/
structure ContextRelated (orc : FFSOracleSem) (ε : ValCtx)
    (ρ ρ' : ValEnvSem) : Prop where
  valid : Nonempty (ValCtxValid ε)
  bindings : ∀ x τ, ε.lookup x = some τ →
    TypeCoherent orc τ ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ ∧
    RuntimeRelated orc τ ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ (ρ x) (ρ' x)

/-- Freshly binding related values preserves the full dependent context
contract. Type validity is weakened using the original typing judgment. -/
theorem ContextRelated.update {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    {ε : ValCtx} {ρ ρ' : ValEnvSem} (h : ContextRelated orc ε ρ ρ')
    (x : VName) (τ : ValTy) (v v' : ValValSem) {k : ValKind}
    (ht : ValTValid ε τ k) (hx : x ∉ ε) (hsupport : x ∉ ε.fvSupport)
    (hfresh : x ∉ ValTy.fv τ)
    (hc : TypeCoherent orc τ ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
    (hv : RuntimeRelated orc τ ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ v v') :
    ContextRelated orc (Finmap.insert x τ ε) (ρ.update x v) (ρ'.update x v') := by
  constructor
  · obtain ⟨hvalid⟩ := h.valid
    refine ⟨?_⟩
    intro z u hz
    by_cases hzx : z = x
    · subst z
      simp only [Finmap.lookup_insert, Option.some.injEq] at hz
      subst u
      exact ⟨k, ht.weaken hx⟩
    · rw [Finmap.lookup_insert_of_ne _ hzx] at hz
      obtain ⟨ku, hu⟩ := hvalid z u hz
      exact ⟨ku, hu.weaken hx⟩
  · intro z u hz
    by_cases hzx : z = x
    · subst z
      simp only [Finmap.lookup_insert, Option.some.injEq] at hz
      subst u
      rw [ValEnvSem.update_same, ValEnvSem.update_same]
      have hf := FiberAgreement.fresh hirr τ ⟨ρ, [], []⟩ ⟨ρ', [], []⟩
        x v v' (by simp [ValTyCtxFresh]) (by simp [ValTyCtxFresh]) hfresh
      exact ⟨TypeCoherent.fiber_transport orc τ _ _ _ _ hf hc,
        runtime_fiber_transport orc τ _ _ _ _ hf v v' hv⟩
    · rw [Finmap.lookup_insert_of_ne _ hzx] at hz
      rw [ValEnvSem.update_other _ _ _ _ hzx, ValEnvSem.update_other _ _ _ _ hzx]
      obtain ⟨hc, hv⟩ := h.bindings z u hz
      have hf := FiberAgreement.fresh hirr u ⟨ρ, [], []⟩ ⟨ρ', [], []⟩
        x v v' (by simp [ValTyCtxFresh]) (by simp [ValTyCtxFresh])
        (ValCtx.not_mem_fv_of_not_mem_support hsupport hz)
      exact ⟨TypeCoherent.fiber_transport orc u _ _ _ _ hf hc,
        runtime_fiber_transport orc u _ _ _ _ hf (ρ z) (ρ' z) hv⟩

end GLang.PaperValueDomains
