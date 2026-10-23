import GLang.Proofs.Value.Presentation.PaperValueQuotient
import GLang.Value.TypeInterpretation

/-! Extensional domains with partial dependent fibres. -/
namespace GLang.PartialValueDomains
open PaperValueDomains PaperValueDomains.ExtensionalQuotient

namespace PER
variable {A B : Type}

/-- Supported quotients commute with adjoining explicit errors. -/
def resultDecode (P : ExtensionalQuotient.PER A) : P.result.Domain → Except DimError P.Domain :=
  Quotient.lift (fun r => match r.val, r.property with
    | .error e, _ => .error e
    | .ok a, ha => .ok (Quotient.mk _ ⟨a,ha⟩)) (by
      intro a b h
      rcases a with ⟨a,ha⟩
      rcases b with ⟨b,hb⟩
      cases a <;> cases b
      · exact congrArg Except.error h
      · exact False.elim h
      · exact False.elim h
      · exact congrArg Except.ok (Quotient.sound h))

def resultEncode (P : ExtensionalQuotient.PER A) : Except DimError P.Domain → P.result.Domain
  | .error e => Quotient.mk _ ⟨.error e,rfl⟩
  | .ok a => Quotient.liftOn a (fun a => Quotient.mk _ ⟨.ok a.val,a.property⟩)
      (fun _ _ h => Quotient.sound h)

def resultEquiv (P : ExtensionalQuotient.PER A) : P.result.Domain ≃ Except DimError P.Domain where
  toFun := resultDecode P
  invFun := resultEncode P
  left_inv r := by
    refine Quotient.inductionOn r ?_
    rintro ⟨r,hr⟩
    cases r <;> rfl
  right_inv r := by
    cases r with
    | error e => rfl
    | ok a => exact Quotient.inductionOn a (fun _ => rfl)

/-- No successful value inhabits a failed type interpretation. -/
def empty (A : Type) : PER A where
  rel _ _ := False
  symm := False.elim
  trans := False.elim

/-- A dependent function family indexed by extensional input classes. -/
def dependentArrow (P : PER A) (Q : P.Domain → PER B) : PER (A → Except DimError B) where
  rel f g := ∀ a b : P.Support, P.rel a.val b.val →
    (Q (Quotient.mk _ a)).result.rel (f a.val) (g b.val)
  symm := by
    intro f g h a b hab
    have he : (Quotient.mk _ a : P.Domain) = Quotient.mk _ b := Quotient.sound hab
    rw [he]
    exact (Q _).result.symm (h b a (P.symm hab))
  trans := by
    intro f g h hfg hgh a b hab
    exact (Q _).result.trans (hfg a a a.property) (hgh a b hab)

/-- Application of function classes is defined on input classes, including
error-only fibres, and is independent of both representatives. -/
noncomputable def dependentApply (P : PER A) (Q : P.Domain → PER B)
    (f : (dependentArrow P Q).Domain) (a : P.Domain) : (Q a).result.Domain :=
  Quotient.liftOn f (fun f => Quotient.mk _ ⟨f.val a.out.val, by
    have h := f.property a.out a.out a.out.property
    simpa only [Quotient.out_eq] using h⟩)
    (fun f g h => Quotient.sound (by
      have hh := h a.out a.out a.out.property
      simpa only [Quotient.out_eq] using hh))

noncomputable def sectionRepresentative (P : PER A) (Q : P.Domain → PER B)
    (F : (a : P.Domain) → (Q a).result.Domain) : (dependentArrow P Q).Support := by
  classical
  refine ⟨fun a => if ha : P.rel a a then (F (Quotient.mk _ ⟨a, ha⟩)).out.val
    else .error .mismatch, ?_⟩
  intro a b hab
  have he : (Quotient.mk _ a : P.Domain) = Quotient.mk _ b := Quotient.sound hab
  dsimp only
  rw [dif_pos a.property, dif_pos b.property]
  change (Q (Quotient.mk _ a)).result.rel
    (F (Quotient.mk _ a)).out.val (F (Quotient.mk _ b)).out.val
  have transport : ∀ q q' : P.Domain, q = q' →
      (Q q).result.rel (F q).out.val (F q').out.val := by
    intro q q' hq
    subst q'
    exact (F q).out.property
  exact transport _ _ he

theorem dependentApply_sectionRepresentative (P : PER A) (Q : P.Domain → PER B)
    (F : (a : P.Domain) → (Q a).result.Domain) :
    dependentApply P Q (Quotient.mk _ (sectionRepresentative P Q F)) = F := by
  funext a
  change Quotient.mk _ ⟨_, _⟩ = F a
  have he : (sectionRepresentative P Q F).val a.out.val = (F a).out.val := by
    simp only [sectionRepresentative, dif_pos a.out.property]
    change (F (Quotient.mk _ a.out)).out.val = (F a).out.val
    rw [Quotient.out_eq]
  calc
    _ = Quotient.mk _ (F a).out := congrArg (Quotient.mk _) (Subtype.ext he)
    _ = F a := Quotient.out_eq _

theorem dependentApply_injective (P : PER A) (Q : P.Domain → PER B) :
    Function.Injective (dependentApply P Q) := by
  intro f g h
  induction f using Quotient.inductionOn with | _ f =>
   induction g using Quotient.inductionOn with | _ g =>
    apply Quotient.sound
    intro a b hab
    let q : P.Domain := Quotient.mk _ a
    have haq : P.rel a.val q.out.val := Quotient.exact (Quotient.out_eq q).symm
    have hqb : P.rel q.out.val b.val := P.trans (P.symm haq) hab
    have hmid := Quotient.exact (congrFun h q)
    have hleft := f.property a q.out haq
    have hright := g.property q.out b hqb
    have hright' : (Q q).result.rel (g.val q.out.val) (g.val b.val) := by
      simpa only [Quotient.out_eq] using hright
    exact (Q q).result.trans ((Q q).result.trans hleft hmid) hright'

/-- Every dependent mathematical section has a runtime representative, and
extensional application determines its quotient class uniquely. -/
noncomputable def dependentFunctionEquiv (P : PER A) (Q : P.Domain → PER B) :
    (dependentArrow P Q).Domain ≃ ((a : P.Domain) → (Q a).result.Domain) where
  toFun := dependentApply P Q
  invFun F := Quotient.mk _ (sectionRepresentative P Q F)
  left_inv f := dependentApply_injective P Q (dependentApply_sectionRepresentative P Q _)
  right_inv := dependentApply_sectionRepresentative P Q

/-- Failed type interpretations have an empty success domain. -/
def emptyEquiv (A : Type) : (empty A).Domain ≃ Empty where
  toFun q := Quotient.liftOn q (fun a => False.elim a.property) (by
    intro a; exact False.elim a.property)
  invFun := Empty.elim
  left_inv q := Quotient.inductionOn q (fun a => False.elim a.property)
  right_inv := fun e => Empty.elim e

/-- A failed fibre only has the explicit error result, never a fabricated
zero-dimensional array. -/
theorem empty_result_error (A : Type) (r : (empty A).result.Support) :
    r.val = .error .mismatch := by
  rcases r with ⟨r, hr⟩
  cases r with
  | error e => cases e; rfl
  | ok a => exact False.elim hr

end PER

/-- Map only the successful part of a result equivalence. -/
def exceptEquiv {A B : Type} (e : A ≃ B) : Except DimError A ≃ Except DimError B where
  toFun r := r.map e
  invFun r := r.map e.symm
  left_inv r := by cases r <;> simp [Except.map]
  right_inv r := by cases r <;> simp [Except.map]

structure DomainModel {A : Type} (P : ExtensionalQuotient.PER A) where
  Carrier : Type
  equiv : P.Domain ≃ Carrier

/-- A representation records a full extensional mathematical domain, not just
membership of raw callbacks. Constructors below can be iterated at any order. -/
structure Representation (τ : ValTy) where
  per : ExtensionalQuotient.PER τ.carrierEl
  Carrier : Type
  equiv : per.Domain ≃ Carrier

namespace Representation

def failed (τ : ValTy) : Representation τ := ⟨PER.empty _, Empty, PER.emptyEquiv _⟩

def space (s : ValSpace) (n : Nat) : Representation (.space s) where
  per := ExtensionalQuotient.PER.arrays n
  Carrier := SizedFlatArray n
  equiv := {
    toFun := Quotient.lift (fun a => ⟨a.val, a.property.2.1⟩)
      (fun _ _ h => Subtype.ext h.1)
    invFun := fun a => Quotient.mk _ ⟨a.val, rfl, a.property, a.property⟩
    left_inv := fun a => Quotient.inductionOn a (fun a => Quotient.sound a.property)
    right_inv := fun _ => rfl }

/-- Dependent partial functions between recursively represented domains.
`C` may select `failed` at any input, even when the domain itself succeeds. -/
noncomputable def piTy {d c : ValTy} (D : Representation d)
    (C : D.per.Domain → Representation c) : Representation (.piTy d c) where
  per := PER.dependentArrow D.per (fun q => (C q).per)
  Carrier := (a : D.Carrier) → Except DimError (C (D.equiv.symm a)).Carrier
  equiv := (PER.dependentFunctionEquiv D.per (fun q => (C q).per)).trans
    ((Equiv.piCongrRight (fun q => (PER.resultEquiv _).trans
      (exceptEquiv (C q).equiv))).trans (Equiv.piCongrLeft' _ D.equiv))

noncomputable def resultEquiv {τ : ValTy} (R : Representation τ) :
    R.per.result.Domain ≃ Except DimError R.Carrier :=
  (PER.resultEquiv _).trans (exceptEquiv R.equiv)

@[simp] theorem resultEquiv_error {τ : ValTy} (R : Representation τ) (e : DimError) :
    R.resultEquiv (Quotient.mk _ ⟨.error e, rfl⟩) = .error e := rfl

/-- Result conversion is exact, including its success/error distinction. -/
@[simp] theorem resultEquiv_ok {τ : ValTy} (R : Representation τ) (a : R.per.Support) :
    R.resultEquiv (Quotient.mk _ ⟨.ok a.val, a.property⟩) =
      .ok (R.equiv (Quotient.mk _ a)) := rfl

end Representation
end GLang.PartialValueDomains
