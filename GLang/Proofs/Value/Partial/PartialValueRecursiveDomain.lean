import GLang.Proofs.Value.Partial.PartialValueRelation

/-! The supported quotient of a coherent partial type is exactly its recursive
mathematical domain: empty at a failed type, finite arrays at a successful
space, and all dependent partial functions at a successful function type. -/
namespace GLang.PartialValueDomains
open PaperValueDomains PaperValueDomains.ExtensionalQuotient

namespace PER
/-- Identical supported relations give canonically identical domains. -/
def domainEquiv {A : Type} (P Q : ExtensionalQuotient.PER A)
    (h : ∀ a b, P.rel a b ↔ Q.rel a b) : P.Domain ≃ Q.Domain where
  toFun := Quotient.map (fun a => ⟨a.val,(h _ _).1 a.property⟩) (fun _ _ hab => (h _ _).1 hab)
  invFun := Quotient.map (fun a => ⟨a.val,(h _ _).2 a.property⟩) (fun _ _ hab => (h _ _).2 hab)
  left_inv a := Quotient.inductionOn a (fun _ => rfl)
  right_inv a := Quotient.inductionOn a (fun _ => rfl)
end PER

private def FiberClass {d : ValTy} (D : PartialValType d)
    (hd : PartialCoherent d (.ok D) (.ok D))
    (q : (partialPER d (.ok D) hd).Domain) :=
  {a : (partialPER d (.ok D) hd).Support // Quotient.mk _ a = q}

private theorem fiber_coherent {d c : ValTy} (D : PartialValType d)
    (F : d.carrierEl → Except DimError (PartialValType c))
    (hc : PartialCoherent (.piTy d c) (.ok (D,F)) (.ok (D,F)))
    (q : (partialPER d (.ok D) hc.1).Domain)
    (a b : FiberClass D hc.1 q) : PartialCoherent c (F a.val.val) (F b.val.val) :=
  hc.2 _ _ (Quotient.exact (a.property.trans b.property.symm))

private theorem pi_rel_iff {d c : ValTy} (D : PartialValType d)
    (F : d.carrierEl → Except DimError (PartialValType c))
    (hc : PartialCoherent (.piTy d c) (.ok (D,F)) (.ok (D,F)))
    (f g : (.piTy d c : ValTy).carrierEl) :
    (partialPER (.piTy d c) (.ok (D,F)) hc).rel f g ↔
      (PER.dependentArrow (partialPER d (.ok D) hc.1)
        (fun q => partialPER c (F q.out.val) (hc.2 _ _ q.out.property))).rel f g := by
  let P := partialPER d (.ok D) hc.1
  have transport (a b : P.Support) (hab : P.rel a.val b.val) :
      PartialRel (PartialRelated c (F a.val) (F b.val)) (f a.val) (g b.val) ↔
      PartialRel (PartialRelated c (F (Quotient.mk _ a : P.Domain).out.val)
        (F (Quotient.mk _ a : P.Domain).out.val)) (f a.val) (g b.val) := by
    let q : P.Domain := Quotient.mk _ a
    let aa : FiberClass D hc.1 q := ⟨a,rfl⟩
    let bb : FiberClass D hc.1 q := ⟨b,Quotient.sound (P.symm hab)⟩
    let rr : FiberClass D hc.1 q := ⟨q.out,Quotient.out_eq q⟩
    have hl := partialFamily_laws c (fun z : FiberClass D hc.1 q => F z.val.val)
      (fiber_coherent D F hc q)
    cases ha : f a.val <;> cases hb : g b.val <;> simp only [PartialRel]
    exact hl.transport aa bb rr rr _ _
  constructor
  · intro h a b hab
    exact (transport a b hab).1 (h a.val b.val hab)
  · intro h a b hab
    let aa : P.Support := ⟨a,P.trans hab (P.symm hab)⟩
    let bb : P.Support := ⟨b,P.trans (P.symm hab) hab⟩
    exact (transport aa bb hab).2 (h aa bb hab)

/-- Full recursive success domain for a partially interpreted coherent type.
A failed result fibre is represented by `Empty`, so its error alternative is
the only possible outcome at that argument. -/
noncomputable def partialRecursiveDomain : (τ : ValTy) →
    (T : Except DimError (PartialValType τ)) → (hc : PartialCoherent τ T T) →
    DomainModel (partialPER τ T hc)
  | .space s, .error e, hc => ⟨Empty,
      (PER.domainEquiv _ (PER.empty _) (by intro a b; rfl)).trans (PER.emptyEquiv _)⟩
  | .piTy d c, .error e, hc => ⟨Empty,
      (PER.domainEquiv _ (PER.empty _) (by intro a b; rfl)).trans (PER.emptyEquiv _)⟩
  | .space s, .ok n, hc => ⟨SizedFlatArray n,
      (PER.domainEquiv _ (Representation.space s n).per (by intro a b; rfl)).trans
        (Representation.space s n).equiv⟩
  | .piTy d c, .ok (D,F), hc =>
      let P := partialPER d (.ok D) hc.1
      let RD := partialRecursiveDomain d (.ok D) hc.1
      let RC := fun q : P.Domain => partialRecursiveDomain c (F q.out.val) (hc.2 _ _ q.out.property)
      ⟨(a : RD.Carrier) → Except DimError (RC (RD.equiv.symm a)).Carrier,
        (PER.domainEquiv _ (PER.dependentArrow P (fun q =>
          partialPER c (F q.out.val) (hc.2 _ _ q.out.property)))
          (pi_rel_iff D F hc)).trans
        ((PER.dependentFunctionEquiv P (fun q =>
          partialPER c (F q.out.val) (hc.2 _ _ q.out.property))).trans
          ((Equiv.piCongrRight (fun q => (PER.resultEquiv _).trans
            (exceptEquiv (RC q).equiv))).trans (Equiv.piCongrLeft' _ RD.equiv)))⟩

noncomputable def partialRecursiveResultEquiv (τ : ValTy)
    (T : Except DimError (PartialValType τ)) (hc : PartialCoherent τ T T) :
    (partialPER τ T hc).result.Domain ≃ Except DimError (partialRecursiveDomain τ T hc).Carrier :=
  (PER.resultEquiv _).trans
    (exceptEquiv (partialRecursiveDomain τ T hc).equiv)

@[simp] theorem partialRecursiveResultEquiv_error (τ : ValTy)
    (T : Except DimError (PartialValType τ)) (hc : PartialCoherent τ T T) (err : DimError) :
    partialRecursiveResultEquiv τ T hc (Quotient.mk _ ⟨.error err,rfl⟩) = .error err := rfl

end GLang.PartialValueDomains
