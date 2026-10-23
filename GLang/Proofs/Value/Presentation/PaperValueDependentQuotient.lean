import GLang.Proofs.Value.Presentation.PaperValueCoherentFamily
import GLang.Proofs.Value.Presentation.PaperValueQuotient

/-! Supported quotient domains for arbitrary dependent types. Coherence is a
local type property; no equality on unrelated current queries is required. -/
namespace GLang.PaperValueDomains
universe u
open ExtensionalQuotient

noncomputable def dependentPER (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w) : PER (w.denot orc τ).El where
  rel := Related orc τ w w
  symm := fun h => related_symm orc τ w w _ _ h
  trans := fun h k =>
    (coherentFamily_laws orc τ (fun _ : Unit => w) (fun _ _ => hc)).trans
      () () () _ _ _ h k

/-- The same typed representative determines the same supported domain member
when transported between coherent worlds. -/
noncomputable def coherentFamily_supportMap {I : Type u} (orc : FFSOracleSem)
    (τ : ValTy) (w : I → World) (hc : ∀ i j, TypeCoherent orc τ (w i) (w j))
    (i j : I) (a : (dependentPER orc τ (w i) (hc i i)).Support) :
    (dependentPER orc τ (w j) (hc j j)).Support :=
  ⟨cast (World.carrier_eq orc τ (w i) (w j)) a.val,
    ((coherentFamily_laws orc τ w hc).transport i i j j _ _ _ _
      (cast_heq _ _).symm (cast_heq _ _).symm).1 a.property⟩

noncomputable def coherentFamily_classMap {I : Type u} (orc : FFSOracleSem)
    (τ : ValTy) (w : I → World) (hc : ∀ i j, TypeCoherent orc τ (w i) (w j))
    (i j : I) :
    (dependentPER orc τ (w i) (hc i i)).Domain →
      (dependentPER orc τ (w j) (hc j j)).Domain :=
  Quotient.map (coherentFamily_supportMap orc τ w hc i j) (by
    intro a b hab
    exact ((coherentFamily_laws orc τ w hc).transport i i j j _ _ _ _
      (cast_heq _ _).symm (cast_heq _ _).symm).1 hab)

/-- Transport back to the original world preserves the quotient class. -/
theorem coherentFamily_classMap_roundtrip {I : Type u} (orc : FFSOracleSem)
    (τ : ValTy) (w : I → World) (hc : ∀ i j, TypeCoherent orc τ (w i) (w j))
    (i j : I) (a : (dependentPER orc τ (w i) (hc i i)).Domain) :
    coherentFamily_classMap orc τ w hc j i (coherentFamily_classMap orc τ w hc i j a) = a := by
  refine Quotient.inductionOn a ?_
  intro a
  apply Quotient.sound
  have he : HEq
      (coherentFamily_supportMap orc τ w hc j i
        (coherentFamily_supportMap orc τ w hc i j a)).val a.val :=
    (cast_heq _ _).trans (cast_heq _ _)
  exact ((coherentFamily_laws orc τ w hc).transport i i i i _ _ _ _
    he.symm HEq.rfl).1 a.property

noncomputable def coherentFamily_resultMap {I : Type u} (orc : FFSOracleSem)
    (τ : ValTy) (w : I → World) (hc : ∀ i j, TypeCoherent orc τ (w i) (w j))
    (i j : I) :
    (dependentPER orc τ (w i) (hc i i)).result.Domain →
      (dependentPER orc τ (w j) (hc j j)).result.Domain :=
  Quotient.map (fun r => ⟨r.val.map (cast (World.carrier_eq orc τ (w i) (w j))),
    PartialRel.map _ _ (fun a b hab =>
      ((coherentFamily_laws orc τ w hc).transport i i j j _ _ _ _
        (cast_heq _ _).symm (cast_heq _ _).symm).1 hab) r.property⟩)
    (fun a b hab => PartialRel.map _ _ (fun x y hxy =>
      ((coherentFamily_laws orc τ w hc).transport i i j j _ _ _ _
        (cast_heq _ _).symm (cast_heq _ _).symm).1 hxy) hab)

/-- A dependent result fibre is chosen from an input quotient class. The
representative-independence law below supplies its canonical identifications. -/
noncomputable def dependentResultPER (orc : FFSOracleSem) (d c : ValTy) (w : World)
    (hc : TypeCoherent orc (.piTy d c) w w)
    (q : (dependentPER orc d w hc.1).Domain) :=
  dependentPER orc c (w.push orc d q.out.val) (hc.2 _ _ q.out.property)

/-- Application of a supported function class to an input class. Its result
retains the distinction between successful values and errors. -/
noncomputable def dependentApply (orc : FFSOracleSem) (d c : ValTy) (w : World)
    (hc : TypeCoherent orc (.piTy d c) w w)
    (f : (dependentPER orc (.piTy d c) w hc).Domain)
    (q : (dependentPER orc d w hc.1).Domain) :
    (dependentResultPER orc d c w hc q).result.Domain :=
  Quotient.liftOn f (fun f => Quotient.mk _
    ⟨f.val q.out.val, f.property _ _ q.out.property⟩)
    (fun _ _ hfg => Quotient.sound (hfg _ _ q.out.property))

def DependentArgument (orc : FFSOracleSem) (d : ValTy) (w : World)
    (hc : TypeCoherent orc d w w) (q : (dependentPER orc d w hc).Domain) :=
  {a : (dependentPER orc d w hc).Support // Quotient.mk _ a = q}

noncomputable def dependentArgumentWorld (orc : FFSOracleSem) (d : ValTy) (w : World)
    (hc : TypeCoherent orc d w w) (q : (dependentPER orc d w hc).Domain)
    (a : DependentArgument orc d w hc q) : World := w.push orc d a.val.val

theorem dependentArgument_related (orc : FFSOracleSem) (d : ValTy) (w : World)
    (hc : TypeCoherent orc d w w) (q : (dependentPER orc d w hc).Domain)
    (a b : DependentArgument orc d w hc q) : Related orc d w w a.val.val b.val.val :=
  Quotient.exact (a.property.trans b.property.symm)

theorem dependentFibre_coherent (orc : FFSOracleSem) (d c : ValTy) (w : World)
    (hc : TypeCoherent orc (.piTy d c) w w)
    (q : (dependentPER orc d w hc.1).Domain)
    (a b : DependentArgument orc d w hc.1 q) :
    TypeCoherent orc c (dependentArgumentWorld orc d w hc.1 q a)
      (dependentArgumentWorld orc d w hc.1 q b) :=
  hc.2 _ _ (dependentArgument_related orc d w hc.1 q a b)

/-- Any supported representative of the same input class gives the same
application result after the canonical identification of its dependent fibre. -/
theorem dependentApply_representative (orc : FFSOracleSem) (d c : ValTy) (w : World)
    (hc : TypeCoherent orc (.piTy d c) w w)
    (f : (dependentPER orc (.piTy d c) w hc).Support)
    (q : (dependentPER orc d w hc.1).Domain)
    (a : DependentArgument orc d w hc.1 q) :
    coherentFamily_resultMap orc c (dependentArgumentWorld orc d w hc.1 q)
      (dependentFibre_coherent orc d c w hc q) a ⟨q.out,Quotient.out_eq q⟩
      (Quotient.mk _ ⟨f.val a.val.val, f.property _ _ a.val.property⟩) =
        dependentApply orc d c w hc (Quotient.mk _ f) q := by
  apply Quotient.sound
  have h := f.property a.val.val q.out.val
    (dependentArgument_related orc d w hc.1 q a ⟨q.out,Quotient.out_eq q⟩)
  have hh := PartialRel.map
    (cast (World.carrier_eq orc c (dependentArgumentWorld orc d w hc.1 q a)
      (w.push orc d q.out.val))) id
    (fun r s hrs =>
      ((coherentFamily_laws orc c (dependentArgumentWorld orc d w hc.1 q)
        (dependentFibre_coherent orc d c w hc q)).transport
        a ⟨q.out,Quotient.out_eq q⟩ ⟨q.out,Quotient.out_eq q⟩ ⟨q.out,Quotient.out_eq q⟩
        r s _ s (cast_heq _ _).symm HEq.rfl).1 hrs) h
  simpa only [Except.map_id] using hh

/-- Checked interpretation of a supported runtime result into the actual
error-preserving quotient domain. -/
noncomputable def checkedResultClass (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w) (r : Except DimError ValValSem)
    (hr : PartialRel (RuntimeRelated orc τ w w) r r) :
    (dependentPER orc τ w hc).result.Domain :=
  Quotient.mk _ ⟨r.bind (ValValSem.toElChecked (w.denot orc τ)),
    extract_checked_results_related orc τ w w r r hr⟩

/-- Related runtime computations determine the same checked quotient result
under the canonical identification between their coherent worlds. -/
theorem coherentFamily_checkedResultClass_eq {I : Type u} (orc : FFSOracleSem)
    (τ : ValTy) (w : I → World) (hc : ∀ i j, TypeCoherent orc τ (w i) (w j))
    (r : I → Except DimError ValValSem)
    (hr : ∀ i j, PartialRel (RuntimeRelated orc τ (w i) (w j)) (r i) (r j))
    (i j : I) :
    coherentFamily_resultMap orc τ w hc i j (checkedResultClass orc τ (w i) (hc i i) (r i) (hr i i)) =
      checkedResultClass orc τ (w j) (hc j j) (r j) (hr j j) := by
  apply Quotient.sound
  have h := extract_checked_results_related orc τ (w i) (w j) (r i) (r j) (hr i j)
  have hm := PartialRel.map (cast (World.carrier_eq orc τ (w i) (w j))) id
    (fun a b hab => ((coherentFamily_laws orc τ w hc).transport i j j j
      a b _ b (cast_heq _ _).symm HEq.rfl).1 hab) h
  simpa only [Except.map_id] using hm

theorem checkedResultClass_eq (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w) (r r' : Except DimError ValValSem)
    (hr : PartialRel (RuntimeRelated orc τ w w) r r)
    (hr' : PartialRel (RuntimeRelated orc τ w w) r' r')
    (h : PartialRel (RuntimeRelated orc τ w w) r r') :
    checkedResultClass orc τ w hc r hr = checkedResultClass orc τ w hc r' hr' :=
  Quotient.sound (extract_checked_results_related orc τ w w r r' h)

end GLang.PaperValueDomains
