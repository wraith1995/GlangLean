import GLang.Proofs.Value.Presentation.PaperValueExtensionality
open GLang GLang.PaperValueDomains
namespace ExtensionalityTests

variable (orc : FFSOracleSem) (w : World)

def always : FlatArray → Except DimError FlatArray := fun _ => .ok (FlatArray.zeros 1)
def onlyValid : FlatArray → Except DimError FlatArray :=
  fun a => if a.length = 1 then .ok (FlatArray.zeros 1) else .error .mismatch

def probe : (FlatArray → Except DimError FlatArray) → Except DimError FlatArray :=
  fun f => match f FlatArray.empty with
    | .error e => .error e
    | .ok _ => .ok (FlatArray.zeros 1)

theorem callbacks_related :
    Related orc (.piTy (.space .real) (.space .real)) w w always onlyValid := by
  intro a b hab
  have hb : b.length = 1 := by simpa [Related] using hab.2.2
  simp only [always, onlyValid, hb, if_pos, PartialRel]
  simp [Related, FlatArray.zeros, FlatArray.ofFn]

theorem probe_not_parametric :
    ¬ Related orc (.piTy (.piTy (.space .real) (.space .real)) (.space .real))
      w w probe probe := by
  intro hp
  have h := hp always onlyValid (callbacks_related orc w)
  simp [probe, always, onlyValid, FlatArray.empty, FlatArray.ofFn, PartialRel] at h

-- Successful results cannot be identified with failures.
example : ¬ PartialRel (fun (_ _ : Nat) => True) (.ok 1) (.error .mismatch) := by
  simp [PartialRel]
example : PartialRel (fun (_ _ : Nat) => False) (.error .mismatch) (.error .mismatch) := rfl

-- A constant partial function satisfies the contract at every higher-order
-- input type. No extensionality premise is smuggled into the result.
example (τ : ValTy) :
    Related orc (.piTy τ (.space .real)) w w
      (fun _ => .error .mismatch) (fun _ => .error .mismatch) := by
  intro a b _
  rfl

example (τ : ValTy) :
    Related orc (.piTy τ (.space .real)) w w
      (fun _ => .ok (FlatArray.zeros 1)) (fun _ => .ok (FlatArray.zeros 1)) := by
  intro a b _
  simp [PartialRel, Related, FlatArray.zeros, FlatArray.ofFn]

#print axioms related_symm
#print axioms reify_related
#print axioms extract_related
#print axioms applyTyped_related
#print axioms extract_results_related
#print axioms eval_lambda_related
#print axioms compatible_fibre_shapes
#print axioms probe_not_parametric
end ExtensionalityTests

namespace ExtensionalityTests
-- Only the queries that occur in the shape need agree; unrelated queries are
-- not assumed equal by this lemma.
example (left right : FFSOracle) (p : ValFFSProp) (s : ValSpace) (e : ValExpr)
    (h : left p s e = right p s e) :
    ValSpace.dof left (.tprod .real (.ffs p s e)) =
      ValSpace.dof right (.tprod .real (.ffs p s e)) :=
  (leafAgreement_shapes left right (.tprod .real (.ffs p s e)) ⟨True.intro, h⟩).2

example (q : FFSOracle) :
    WorldCompatibility (FFSOracleSem.const q) (fun _ _ => True) :=
  constantOracle_compatible q
#print axioms leafAgreement_shapes
#print axioms constantOracle_compatible
end ExtensionalityTests

namespace ExtensionalityTests
-- A real evaluator result, with an arbitrary (possibly higher-order) domain.
-- This verifies a definable lambda, beyond the conditional lambda lemma.
example (orc : FFSOracleSem) (w w' : World) (τ : ValTy) (r : ℝ) :
    PartialRel (RuntimeRelated orc (.piTy τ (.space .real)) w w')
      (denotValB_semS orc w.env w.types w.values (.vlam τ (.space .real) (.rlit r)))
      (denotValB_semS orc w'.env w'.types w'.values (.vlam τ (.space .real) (.rlit r))) := by
  apply eval_lambda_related
  intro a b _
  simp only [denotValB_semS, ValExpr.inferSpaceCtx, ValSpace.dof_real]
  simp [PartialRel, RuntimeRelated, Related, ValValSem.arrayOf, FlatArray.ofFn]
end ExtensionalityTests
