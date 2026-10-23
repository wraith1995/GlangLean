import GLang.Proofs.Value.Presentation.PaperValueDependentQuotient
import GLang.Value.ResultDomains

/-! Mathematical domains of supported values: finite arrays and dependent
partial functions. These equivalences preserve individual error constructors. -/
namespace GLang.PaperValueDomains
open ExtensionalQuotient

namespace ExtensionalQuotient.PER
universe u
variable {A : Type u}

def resultDecode (P : PER A) : P.result.Domain → Except DimError P.Domain :=
  Quotient.lift (fun r => match r.val, r.property with
    | .error e, _ => .error e
    | .ok a, ha => .ok (Quotient.mk _ ⟨a, ha⟩)) (by
      intro a b h
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      cases a <;> cases b
      · exact congrArg Except.error h
      · exact False.elim h
      · exact False.elim h
      · exact congrArg Except.ok (Quotient.sound h))

def resultEncode (P : PER A) : Except DimError P.Domain → P.result.Domain
  | .error e => Quotient.mk _ ⟨.error e, rfl⟩
  | .ok a => Quotient.liftOn a (fun a => Quotient.mk _ ⟨.ok a.val, a.property⟩)
      (fun _ _ h => Quotient.sound h)

/-- Taking the supported quotient commutes with adjoining explicit errors. -/
def resultEquiv (P : PER A) : P.result.Domain ≃ Except DimError P.Domain where
  toFun := P.resultDecode
  invFun := P.resultEncode
  left_inv r := by
    refine Quotient.inductionOn r ?_
    rintro ⟨r, hr⟩
    cases r <;> rfl
  right_inv r := by
    cases r with
    | error e => rfl
    | ok a => exact Quotient.inductionOn a (fun _ => rfl)

end ExtensionalQuotient.PER

/-- Space values are exactly arrays of the interpreted dimension. -/
noncomputable def spaceDomainEquiv (orc : FFSOracleSem) (s : ValSpace) (w : World)
    (hc : TypeCoherent orc (.space s) w w) :
    (dependentPER orc (.space s) w hc).Domain ≃
      SizedFlatArray (ValSpace.dof (orc w.env w.types w.values) s) where
  toFun := Quotient.lift (fun a => ⟨a.val, a.property.2.1⟩)
    (fun _ _ h => Subtype.ext h.1)
  invFun a := Quotient.mk _ ⟨a.val, rfl, a.property, a.property⟩
  left_inv a := Quotient.inductionOn a (fun a => Quotient.sound a.property)
  right_inv _ := rfl

section Functions
variable (orc : FFSOracleSem) (d c : ValTy) (w : World)
variable (hc : TypeCoherent orc (.piTy d c) w w)

abbrev DependentSection := (q : (dependentPER orc d w hc.1).Domain) →
  (dependentResultPER orc d c w hc q).result.Domain

noncomputable def sectionAt (F : DependentSection orc d c w hc)
    (q : (dependentPER orc d w hc.1).Domain)
    (a : DependentArgument orc d w hc.1 q) :
    Except DimError ((w.push orc d a.val.val).denot orc c).El :=
  (F q).out.val.map (cast (World.carrier_eq orc c
    (w.push orc d q.out.val) (w.push orc d a.val.val)))

theorem sectionAt_related (F : DependentSection orc d c w hc)
    (q : (dependentPER orc d w hc.1).Domain)
    (a b : DependentArgument orc d w hc.1 q) :
    PartialRel (Related orc c (w.push orc d a.val.val) (w.push orc d b.val.val))
      (sectionAt orc d c w hc F q a) (sectionAt orc d c w hc F q b) := by
  apply PartialRel.map
  · intro x y hxy
    exact ((coherentFamily_laws orc c (dependentArgumentWorld orc d w hc.1 q)
      (dependentFibre_coherent orc d c w hc q)).transport
      ⟨q.out, Quotient.out_eq q⟩ ⟨q.out, Quotient.out_eq q⟩ a b
      x y _ _ (cast_heq _ _).symm (cast_heq _ _).symm).1 hxy
  · exact (F q).out.property

noncomputable def sectionLift (F : DependentSection orc d c w hc)
    (a : (dependentPER orc d w hc.1).Support) :=
  sectionAt orc d c w hc F (Quotient.mk _ a) ⟨a, rfl⟩

theorem sectionLift_eq (F : DependentSection orc d c w hc)
    (a : (dependentPER orc d w hc.1).Support)
    (q : (dependentPER orc d w hc.1).Domain) (ha : Quotient.mk _ a = q) :
    sectionLift orc d c w hc F a = sectionAt orc d c w hc F q ⟨a, ha⟩ := by
  subst q
  rfl

theorem sectionLift_related (F : DependentSection orc d c w hc)
    (a b : (dependentPER orc d w hc.1).Support) (hab : Related orc d w w a.val b.val) :
    PartialRel (Related orc c (w.push orc d a.val) (w.push orc d b.val))
      (sectionLift orc d c w hc F a) (sectionLift orc d c w hc F b) := by
  rw [sectionLift_eq orc d c w hc F b (Quotient.mk _ a) (Quotient.sound (related_symm orc d w w _ _ hab))]
  exact sectionAt_related orc d c w hc F _ ⟨a, rfl⟩
    ⟨b, Quotient.sound (related_symm orc d w w _ _ hab)⟩

noncomputable def sectionRepresentative (F : DependentSection orc d c w hc) :
    (dependentPER orc (.piTy d c) w hc).Support := by
  classical
  refine ⟨fun a => if ha : Related orc d w w a a then
    sectionLift orc d c w hc F ⟨a, ha⟩ else .error .mismatch, ?_⟩
  intro a b hab
  have haa := (dependentPER orc d w hc.1).trans hab ((dependentPER orc d w hc.1).symm hab)
  have hbb := (dependentPER orc d w hc.1).trans ((dependentPER orc d w hc.1).symm hab) hab
  dsimp only
  change Related orc d w w a a at haa
  change Related orc d w w b b at hbb
  rw [dif_pos haa, dif_pos hbb]
  exact sectionLift_related orc d c w hc F ⟨a, haa⟩ ⟨b, hbb⟩ hab

theorem dependentApply_sectionRepresentative (F : DependentSection orc d c w hc) :
    dependentApply orc d c w hc (Quotient.mk _ (sectionRepresentative orc d c w hc F)) = F := by
  funext q
  change Quotient.mk _ ⟨_, _⟩ = F q
  have he : (sectionRepresentative orc d c w hc F).val q.out.val = (F q).out.val := by
    dsimp only [sectionRepresentative]
    have hq : Related orc d w w q.out.val q.out.val := q.out.property
    rw [dif_pos hq]
    change sectionLift orc d c w hc F q.out = _
    rw [sectionLift_eq orc d c w hc F q.out q (Quotient.out_eq q)]
    change (F q).out.val.map id = (F q).out.val
    exact congrFun Except.map_id _
  calc
    _ = Quotient.mk _ (F q).out := congrArg (Quotient.mk _) (Subtype.ext he)
    _ = F q := Quotient.out_eq _

private theorem family_partial_trans {I : Type} (τ : ValTy) (ws : I → World)
    (hco : ∀ i j, TypeCoherent orc τ (ws i) (ws j)) (i j k : I)
    {x : Except DimError ((ws i).denot orc τ).El}
    {y : Except DimError ((ws j).denot orc τ).El}
    {z : Except DimError ((ws k).denot orc τ).El}
    (hxy : PartialRel (Related orc τ (ws i) (ws j)) x y)
    (hyz : PartialRel (Related orc τ (ws j) (ws k)) y z) :
    PartialRel (Related orc τ (ws i) (ws k)) x z := by
  cases x <;> cases y <;> cases z <;> simp_all [PartialRel]
  exact (coherentFamily_laws orc τ ws hco).trans i j k _ _ _ hxy hyz

theorem dependentApply_injective : Function.Injective (dependentApply orc d c w hc) := by
  intro f g h
  induction f using Quotient.inductionOn with | _ f =>
   induction g using Quotient.inductionOn with | _ g =>
    apply Quotient.sound
    intro a b hab
    let P := dependentPER orc d w hc.1
    have haa : P.rel a a := P.trans hab (P.symm hab)
    have hbb : P.rel b b := P.trans (P.symm hab) hab
    let q : P.Domain := Quotient.mk _ ⟨a, haa⟩
    let aa : DependentArgument orc d w hc.1 q := ⟨⟨a, haa⟩, rfl⟩
    let bb : DependentArgument orc d w hc.1 q := ⟨⟨b, hbb⟩, Quotient.sound (P.symm hab)⟩
    let rr : DependentArgument orc d w hc.1 q := ⟨q.out, Quotient.out_eq q⟩
    have hmid : PartialRel (Related orc c (w.push orc d q.out.val) (w.push orc d q.out.val))
        (f.val q.out.val) (g.val q.out.val) := Quotient.exact (congrFun h q)
    have hleft := f.property a q.out.val (dependentArgument_related orc d w hc.1 q aa rr)
    have hright := g.property q.out.val b (dependentArgument_related orc d w hc.1 q rr bb)
    exact family_partial_trans orc c (dependentArgumentWorld orc d w hc.1 q)
      (dependentFibre_coherent orc d c w hc q) aa rr bb
      (family_partial_trans orc c (dependentArgumentWorld orc d w hc.1 q)
        (dependentFibre_coherent orc d c w hc q) aa rr rr hleft hmid) hright

/-- Every mathematical dependent partial section has a supported representative;
application completely determines the represented function. -/
noncomputable def functionDomainEquiv :
    (dependentPER orc (.piTy d c) w hc).Domain ≃ DependentSection orc d c w hc where
  toFun := dependentApply orc d c w hc
  invFun F := Quotient.mk _ (sectionRepresentative orc d c w hc F)
  left_inv _ := dependentApply_injective orc d c w hc
    (dependentApply_sectionRepresentative orc d c w hc _)
  right_inv := dependentApply_sectionRepresentative orc d c w hc

end Functions
/-- Mapping the successful part of a partial result leaves errors unchanged. -/
def exceptEquiv {A B : Type} (e : A ≃ B) : Except DimError A ≃ Except DimError B where
  toFun r := r.map e
  invFun r := r.map e.symm
  left_inv r := by cases r <;> simp [Except.map]
  right_inv r := by cases r <;> simp [Except.map]

/-- A mathematical success domain together with its runtime representation. -/
structure DomainModel {A : Type} (P : PER A) where
  Carrier : Type
  equiv : P.Domain ≃ Carrier

/-- Recursively remove runtime representatives: a space denotes sized arrays;
a function denotes all partial dependent functions between recursive domains.
The fibre is selected using a representative of the mathematical input;
`dependentApply_representative` identifies every other choice. -/
noncomputable def recursiveDomain (orc : FFSOracleSem) :
    (τ : ValTy) → (w : World) → (hc : TypeCoherent orc τ w w) →
      DomainModel (dependentPER orc τ w hc)
  | .space s, w, hc => ⟨_, spaceDomainEquiv orc s w hc⟩
  | .piTy d c, w, hc =>
    let D := recursiveDomain orc d w hc.1
    let C := fun q : (dependentPER orc d w hc.1).Domain =>
      recursiveDomain orc c (w.push orc d q.out.val) (hc.2 _ _ q.out.property)
    ⟨(a : D.Carrier) → Except DimError (C (D.equiv.symm a)).Carrier,
      (functionDomainEquiv orc d c w hc).trans
        ((Equiv.piCongrRight (fun q =>
          (PER.resultEquiv _).trans (exceptEquiv (C q).equiv))).trans
          (Equiv.piCongrLeft' _ D.equiv))⟩

noncomputable def recursiveResultEquiv (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w) :
    (dependentPER orc τ w hc).result.Domain ≃
      Except DimError (recursiveDomain orc τ w hc).Carrier :=
  (PER.resultEquiv _).trans (exceptEquiv (recursiveDomain orc τ w hc).equiv)

/-- Applying the mathematical function agrees with quotient application,
including dependent output fibres and errors. -/
theorem recursiveDomain_apply (orc : FFSOracleSem) (d c : ValTy) (w : World)
    (hc : TypeCoherent orc (.piTy d c) w w)
    (f : (dependentPER orc (.piTy d c) w hc).Domain)
    (a : (recursiveDomain orc d w hc.1).Carrier) :
    (recursiveDomain orc (.piTy d c) w hc).equiv f a =
      let q := (recursiveDomain orc d w hc.1).equiv.symm a
      recursiveResultEquiv orc c (w.push orc d q.out.val) (hc.2 _ _ q.out.property)
        (dependentApply orc d c w hc f q) := rfl

@[simp] theorem recursiveResultEquiv_error (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w) (e : DimError) :
    recursiveResultEquiv orc τ w hc (Quotient.mk _ ⟨.error e, rfl⟩) = .error e := rfl

@[simp] theorem recursiveResultEquiv_ok (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w) (a : (dependentPER orc τ w hc).Support) :
    recursiveResultEquiv orc τ w hc (Quotient.mk _ ⟨.ok a.val, a.property⟩) =
      .ok ((recursiveDomain orc τ w hc).equiv (Quotient.mk _ a)) := rfl

end GLang.PaperValueDomains
