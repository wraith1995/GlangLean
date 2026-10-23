import GLang.Proofs.Value.Runtime.RuntimeValueCorrespondence

namespace GLang.PaperValueDomainResults
open PartialValueDomains PaperValueDomains PaperValueDomains.ExtensionalQuotient

noncomputable abbrev ValueDomain (τ : ValTy)
    (T : Except DimError (PartialValType τ)) (hc : PartialCoherent τ T T) : Type :=
  Except DimError (partialRecursiveDomain τ T hc).Carrier

/-- Successful runtime membership at the actual partial interpretation.
At function types this includes the prescribed argument carrier and prevents
malformed successful callbacks from being mistaken for legitimate errors. -/
noncomputable abbrev Member (ρ : ValEnvSem) (τ : ValTy) (v : ValValSem) : Prop :=
  PartialRuntimeRelated τ (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ)
    (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ) v v

/-- The frozen environment definition, with formation and non-error
membership required separately for each declared binding. -/
theorem environment_iff (ε : ValCtx) (ρ : ValEnvSem) :
    RuntimeValue.PartialEnvWF PartialDirectOracle.oracle ε ρ ↔
      ∀ x τ, ε.lookup x = some τ →
        (∃ k, Nonempty (RuntimeValue.ValTValid ε τ k)) ∧ Member ρ τ (ρ x) := by
  constructor
  · rintro ⟨⟨hc⟩, hm⟩ x τ hx
    obtain ⟨k, hk⟩ := hc x τ hx
    exact ⟨⟨k, ⟨hk⟩⟩, hm x τ hx⟩
  · intro h
    refine ⟨⟨fun x τ hx => ?_⟩, fun x τ hx => (h x τ hx).2⟩
    exact ⟨((h x τ hx).1).choose, ((h x τ hx).1).choose_spec.some⟩

/-- Successful array membership is exactly the successful dynamic dimension
and the array's length. A failed dimension is not dimension zero. -/
theorem member_space_iff (ρ : ValEnvSem) (s : ValSpace) (a : FlatArray) :
    Member ρ (.space s) (.array a) ↔
      s.dofPartial (PartialDirectOracle.oracle ρ [] []) = .ok a.length := by
  unfold Member
  cases h : s.dofPartial (PartialDirectOracle.oracle ρ [] []) <;>
    simp [denotValTyPartial, h, PartialRuntimeRelated, PartialRelated,
      PartialValType.space, eq_comm]

/-- Coherence of the entire recursive domain follows from value formation
and the same environment premise used by value soundness. -/
theorem type_coherent {ε : ValCtx} {ρ : ValEnvSem} {τ : ValTy} {k : ValKind}
    (hρ : RuntimeValue.PartialEnvWF PartialDirectOracle.oracle ε ρ)
    (ht : RuntimeValue.ValTValid ε τ k) :
    PartialCoherent τ (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ)
      (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ) := by
  obtain ⟨hc⟩ := hρ.1
  exact (RuntimeValue.partial_originalType_coherent_family ht hc
    (fun _ : Unit => ρ) (fun _ _ => hρ.2) () ()).toCoherent _ _ _ _

/-- Every successful mathematical value, including an arbitrary dependent
higher-order function, has a well-formed runtime representative. This is
semantic representability, not definability by a value-language program. -/
theorem representable (τ : ValTy) (T : Except DimError (PartialValType τ))
    (hc : PartialCoherent τ T T) (a : (partialRecursiveDomain τ T hc).Carrier) :
    ∃ v : ValValSem, PartialRuntimeRelated τ T T v v ∧
      ∃ (r : τ.carrierEl) (hr : PartialRelated τ T T r r),
        τ.carrierFromVal v = .ok r ∧
        (partialRecursiveDomain τ T hc).equiv (Quotient.mk _ ⟨r, hr⟩) = a := by
  let model := partialRecursiveDomain τ T hc
  let q := model.equiv.symm a
  let r := q.out
  refine ⟨τ.carrierToVal r.val, partial_reify_related τ T T _ _ r.property,
    r.val, r.property, carrier_roundtrip τ r.val, ?_⟩
  change model.equiv (Quotient.mk _ q.out) = a
  rw [Quotient.out_eq]
  exact model.equiv.apply_symm_apply a

/-- Declared values decode successfully to supported representatives. Raw
membership is stronger than mere successful decoding, especially at functions. -/
theorem environment_member {ε : ValCtx} {ρ : ValEnvSem}
    (hρ : RuntimeValue.PartialEnvWF PartialDirectOracle.oracle ε ρ)
    {x : VName} {τ : ValTy} (hx : ε.lookup x = some τ) :
    ∃ r : τ.carrierEl, τ.carrierFromVal (ρ x) = .ok r ∧
      PartialRelated τ (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ)
        (denotValTyPartial PartialDirectOracle.oracle ρ [] [] τ) r r := by
  obtain ⟨a, b, ha, hb, hab⟩ := partial_extract_related τ _ _ _ _ (hρ.2 x τ hx)
  have heq : a = b := Except.ok.inj (ha.symm.trans hb)
  subst b
  exact ⟨a, ha, hab⟩

end GLang.PaperValueDomainResults
