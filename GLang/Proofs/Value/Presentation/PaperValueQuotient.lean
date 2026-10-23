import GLang.Proofs.Value.Presentation.PaperValueExtensionality

/-! Extensional quotients of represented values. Dependent fiber shapes descend under world compatibility. -/
namespace GLang.PaperValueDomains

universe u v

namespace ExtensionalQuotient

/-- A partial equivalence relation need not relate malformed representatives
to themselves. Quotients below retain exactly its self-related support. -/
structure PER (A : Type u) where
  rel : A → A → Prop
  symm : ∀ {a b}, rel a b → rel b a
  trans : ∀ {a b c}, rel a b → rel b c → rel a c

namespace PER

variable {A : Type u} {B : Type v}

def Support (P : PER A) := {a : A // P.rel a a}

def supportSetoid (P : PER A) : Setoid P.Support where
  r a b := P.rel a.val b.val
  iseqv := ⟨fun a => a.property, fun h => P.symm h, fun h k => P.trans h k⟩

def Domain (P : PER A) := Quotient P.supportSetoid

/-- Error constructors remain distinct, and errors never equal successes. -/
def result (P : PER A) : PER (Except DimError A) where
  rel := PartialRel P.rel
  symm := PartialRel.symm (fun _ _ h => P.symm h)
  trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp_all [PartialRel]
    exact P.trans hab hbc

@[simp] theorem result_error_eq_iff (P : PER A) (e e' : DimError) :
    (Quotient.mk _ ⟨Except.error e, rfl⟩ : P.result.Domain) =
      Quotient.mk _ ⟨Except.error e', rfl⟩ ↔ e = e' := by
  rw [Quotient.eq]
  rfl

/-- The quotient preserves the distinction between an error and a value. -/
theorem result_error_ne_ok (P : PER A) (e : DimError) (a : P.Support) :
    (Quotient.mk _ ⟨Except.error e, rfl⟩ : P.result.Domain) ≠
      Quotient.mk _ ⟨Except.ok a.val, a.property⟩ := by
  intro h
  exact Quotient.exact h

/-- Relational function space: functions must preserve equivalent supported
arguments, including agreement on success versus failure. -/
def arrow (P : PER A) (Q : PER B) : PER (A → Except DimError B) where
  rel f g := ∀ a b, P.rel a b → PartialRel Q.rel (f a) (g b)
  symm := by
    intro f g h a b hab
    exact PartialRel.symm (fun _ _ h => Q.symm h) (h b a (P.symm hab))
  trans := by
    intro f g h hfg hgh a b hab
    exact Q.result.trans (hfg a a (P.trans hab (P.symm hab))) (hgh a b hab)

/-- Application is well-defined simultaneously in both quotient arguments.
This applies unchanged to nested arrow PERs, hence to higher-order functions. -/
def apply (P : PER A) (Q : PER B) :
    (P.arrow Q).Domain → P.Domain → Q.result.Domain :=
  fun f a => Quotient.liftOn₂ f a
    (fun f a => Quotient.mk _ ⟨f.val a.val, f.property a.val a.val a.property⟩)
    (by
      intro f a g b hfg hab
      exact Quotient.sound (hfg a.val b.val hab))

@[simp] theorem apply_mk (P : PER A) (Q : PER B)
    (f : (P.arrow Q).Support) (a : P.Support) :
    P.apply Q (Quotient.mk _ f) (Quotient.mk _ a) =
      Quotient.mk _ ⟨f.val a.val, f.property a.val a.val a.property⟩ := rfl

/-- Sized arrays give an actual PER without any semantic coherence premise. -/
def arrays (n : Nat) : PER FlatArray where
  rel a b := a = b ∧ a.length = n ∧ b.length = n
  symm := fun h => ⟨h.1.symm, h.2.2, h.2.1⟩
  trans := fun h k => ⟨h.1.trans k.1, h.2.1, k.2.2⟩

/-- A concrete second-order domain: functionals on array-to-array functions. -/
def functionals (input output result : Nat) :=
  ((arrays input).arrow (arrays output)).arrow (arrays result)

end PER

/-- Same-world first-order relatedness is a PER even with dependent output
sizes: equal supported arrays select literally the same pushed world. -/
def firstOrderPER (orc : FFSOracleSem) (w : World) (s t : ValSpace) :
    PER (w.denot orc (.piTy (.space s) (.space t))).El where
  rel := Related orc (.piTy (.space s) (.space t)) w w
  symm := fun h => related_symm orc _ w w _ _ h
  trans := by
    intro f g h hfg hgh
    apply (firstOrder_related_iff orc w s t f h).2
    intro a ha
    have hfg' := (firstOrder_related_iff orc w s t f g).1 hfg a ha
    have hgh' := (firstOrder_related_iff orc w s t g h).1 hgh a ha
    exact (PER.arrays (ValSpace.dof
      (orc (w.push orc (.space s) a).env (w.push orc (.space s) a).types
        (w.push orc (.space s) a).values) t)).result.trans hfg' hgh'

/-- Extensional equality on successful inputs characterizes quotient equality;
outputs retain their errors, not just their successful scalar observations. -/
theorem firstOrder_quotient_eq_iff (orc : FFSOracleSem) (w : World) (s t : ValSpace)
    (f g : (firstOrderPER orc w s t).Support) :
    (Quotient.mk _ f : (firstOrderPER orc w s t).Domain) = Quotient.mk _ g ↔
      ∀ a, a.length = ValSpace.dof (orc w.env w.types w.values) s →
        f.val a = g.val a := by
  rw [Quotient.eq]
  constructor
  · intro h a ha
    have hr := (firstOrder_related_iff orc w s t f.val g.val).1 h a ha
    cases hf : f.val a <;> cases hg : g.val a <;> simp_all [PartialRel, Related]
  · intro h
    apply (firstOrder_related_iff orc w s t f.val g.val).2
    intro a ha
    rw [← h a ha]
    exact (firstOrder_related_iff orc w s t f.val f.val).1 f.property a ha

/-- The PER-arrow construction agrees with the actual logical relation at a
concrete higher-order type in every world. Its dimensions are independent of
the oracle, so no all-query world compatibility is required. -/
theorem real_functional_related_iff (orc : FFSOracleSem) (w w' : World)
    (f : (w.denot orc
      (.piTy (.piTy (.space .real) (.space .real)) (.space .real))).El)
    (g : (w'.denot orc
      (.piTy (.piTy (.space .real) (.space .real)) (.space .real))).El) :
    Related orc (.piTy (.piTy (.space .real) (.space .real)) (.space .real))
      w w' f g ↔ (PER.functionals 1 1 1).rel f g := by
  simp only [Related, PER.functionals, PER.arrow, PER.arrays, ValSpace.dof_real, denotValTyS]
  rfl

/-- Query-local fibre construction: only oracle leaves occurring in the
specified result space must agree. This avoids an all-query oracle premise. -/
noncomputable def fibreShapeOfLeaves (orc : FFSOracleSem) (w : World) (τ : ValTy)
    (P : PER (w.denot orc τ).El) (s : ValSpace)
    (hLeaves : ∀ a b, P.rel a b →
      SpaceOracleAgreement
        (orc (w.push orc τ a).env (w.push orc τ a).types (w.push orc τ a).values)
        (orc (w.push orc τ b).env (w.push orc τ b).types (w.push orc τ b).values) s) :
    P.Domain → List Nat :=
  Quotient.lift
    (fun a => ValSpace.shpOf
      (orc (w.push orc τ a.val).env (w.push orc τ a.val).types
        (w.push orc τ a.val).values) s)
    (fun a b hab => (leafAgreement_shapes _ _ s (hLeaves a.val b.val hab)).1)

/-- The successful dependent space fibre is defined over the quotient input,
not over a selected callback representative. -/
def ArrayFibre {A : Type u} (P : PER A) (shape : P.Domain → List Nat)
    (a : P.Domain) := {v : FlatArray // v.length = (shape a).foldr (· * ·) 1}

@[simp] theorem arrayFibre_at_rep (orc : FFSOracleSem) (w : World) (τ : ValTy)
    (P : PER (w.denot orc τ).El) (s : ValSpace) (hLeaves)
    (a : P.Support) (v : FlatArray) :
    v.length = ((fibreShapeOfLeaves orc w τ P s hLeaves) (Quotient.mk _ a)).foldr (· * ·) 1 ↔
      v.length = ValSpace.dof
        (orc (w.push orc τ a.val).env (w.push orc τ a.val).types
          (w.push orc τ a.val).values) s := by
  simp only [fibreShapeOfLeaves, Quotient.lift_mk, ValSpace.dof]

/-- A dependent fibre's shape is a function of the input equivalence class,
provided the chosen PER entails the semantic relation and compatible worlds
are closed under related argument pushes. Neither condition is hidden. -/
noncomputable def fibreShape {orc : FFSOracleSem} {W : World → World → Prop}
    (hW : WorldCompatibility orc W) (w : World) (hw : W w w)
    (τ : ValTy) (P : PER (w.denot orc τ).El)
    (hP : ∀ a b, P.rel a b → Related orc τ w w a b)
    (s : ValSpace) : P.Domain → List Nat :=
  Quotient.lift
    (fun a => ValSpace.shpOf
      (orc (w.push orc τ a.val).env (w.push orc τ a.val).types
        (w.push orc τ a.val).values) s)
    (fun a b hab => compatible_fibre_shapes hW hw τ a.val b.val (hP _ _ hab) s)

/-- First-order arguments supply the required PER unconditionally; only the
oracle/world coherence remains a premise for their dependent fibre shapes. -/
noncomputable def firstOrderFibreShape {orc : FFSOracleSem} {W : World → World → Prop}
    (hW : WorldCompatibility orc W) (w : World) (hw : W w w)
    (s t result : ValSpace) : (firstOrderPER orc w s t).Domain → List Nat :=
  fibreShape hW w hw (.piTy (.space s) (.space t)) (firstOrderPER orc w s t)
    (fun _ _ h => h) result

end ExtensionalQuotient
end GLang.PaperValueDomains
