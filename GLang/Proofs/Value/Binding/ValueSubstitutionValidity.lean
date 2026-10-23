import GLang.Proofs.Value.Runtime.RuntimeValueSubstitution
import GLang.Proofs.Value.Runtime.RuntimeValueFormation
import GLang.Proofs.Value.Runtime.RuntimeValueEmbedding
import GLang.Proofs.Value.Soundness.ValueSoundVals

namespace GLang

/-- Extending a valid context with a fresh, well-formed declaration is valid. -/
noncomputable def ValCtxValid.insert {Γv : ValCtx} {x : VName} {τ : ValTy} {k : ValKind}
    (hc : ValCtxValid Γv) (hx : x ∉ Γv) (ht : ValTValid Γv τ k) :
    ValCtxValid (Finmap.insert x τ Γv) := by
  intro y u hu
  by_cases hy : y = x
  · subst y
    have heq : τ = u := Option.some.inj (by simpa using hu)
    subst u
    exact ⟨k, ht.weaken hx⟩
  · have hold : Γv.lookup y = some u := by
      simpa [Finmap.lookup_insert_of_ne _ hy] using hu
    obtain ⟨ku, hv⟩ := hc y u hold
    exact ⟨ku, hv.weaken hx⟩

/-- Substitution retains formation of every declaration in the reduced context. -/
noncomputable def ValCtxValid.subst {ε : ValCtx} {x : VName} {u : ValExpr} {τx : ValTy}
    (hv : ValCtxValid ε) (sd : ValSubstData x u ε τx) :
    ValCtxValid (ValCtx.substMap x u (ε.erase x)) := by
  intro y τ hy
  have hex := ValCtx.substMap_lookup_inv x u (ε.erase x) y τ hy
  let t := hex.choose
  have ht := hex.choose_spec.1
  have htau := hex.choose_spec.2
  change τ = ValTy.subst x u t at htau
  have hne : y ≠ x := by intro he; subst y; simp at ht
  have hlookup : ε.lookup y = some t := by
    exact (Finmap.lookup_erase_ne hne).symm.trans ht
  obtain ⟨k, hk⟩ := hv y t hlookup
  exact ⟨k, htau.symm ▸ hk.subst sd⟩

namespace RuntimeValue

/-- Runtime typing has the same context-substitution formation property. -/
noncomputable def ValCtxValid.subst {ε : ValCtx} {x : VName} {u : ValExpr} {τx : ValTy}
    (hv : ValCtxValid ε) (sd : ValSubstData x u ε τx) :
    ValCtxValid (ValCtx.substMap x u (ε.erase x)) := by
  intro y τ hy
  have hex := ValCtx.substMap_lookup_inv x u (ε.erase x) y τ hy
  let t := hex.choose
  have ht := hex.choose_spec.1
  have htau := hex.choose_spec.2
  change τ = ValTy.subst x u t at htau
  have hne : y ≠ x := by intro he; subst y; simp at ht
  have hlookup : ε.lookup y = some t := by
    exact (Finmap.lookup_erase_ne hne).symm.trans ht
  obtain ⟨k, hk⟩ := hv y t hlookup
  exact ⟨k, htau.symm ▸ hk.subst sd⟩

end RuntimeValue
end GLang
