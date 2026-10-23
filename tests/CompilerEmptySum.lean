import GLang.Proofs.Value.Typing.ValueSumAt
import GLang.Operational.Ordinary

namespace GLang.CompilerEmptySum

def source : Term := .llam .empty .empty (.zero .empty)
def basis : Basis := .tprod (.dual .empty) .empty
def output : ValExpr := ValExpr.sumAt .empty [] (.tprod .empty .empty)

def sourceTyped : HasType ∅ ∅ source (Basis.tof basis) :=
  .llam_tensor ∅ (by simp) .empty .empty (fun _ _ => .zero .empty)

theorem compiles : ValExpr.OpStep ∅ source basis output := by
  have h := ValExpr.OpStep.llam_assemble (Ψ := ∅) (b' := .empty) (b := .empty)
    (e := .zero .empty) (sv' := .empty) (sv := .empty) (env := fun _ : Fin 0 => ValExpr.rlit 0)
    rfl (.empty) (.empty) ∅ (fun _ _ i => i.elim0)
  simpa only [source, basis, output, ValSpace.dofUB, List.ofFn_zero, Basis.sof] using h

/-- The produced value has the original value typing, even though its output
space is a tensor and the empty family's own type is literally `empty`. -/
def outputTyped : ValHasType ∅ output (.space (.tprod .empty .empty)) :=
  .sumAt .empty (.tprod .empty .empty) (fun _ h => False.elim (List.not_mem_nil h))

theorem old_annotation_not_typed (τ : ValTy) :
    ¬ Nonempty (ValHasType ∅
      (ValExpr.reshapBase (.vsum .empty []) (.tprod .empty .empty)) τ) := by
  rintro ⟨h⟩
  cases h with
  | reshap hv _ _ =>
    cases hv with
    | vsum _ _ _ hempty => cases hempty rfl

#print axioms compiles
#print axioms outputTyped
#print axioms old_annotation_not_typed
end GLang.CompilerEmptySum
