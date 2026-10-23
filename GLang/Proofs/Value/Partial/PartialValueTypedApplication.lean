import GLang.Proofs.Value.Partial.PartialValueApplicationTransport
import GLang.Proofs.Value.Partial.PartialValueOriginalFamily

namespace GLang.PartialValueDomains
open PaperValueDomains

/-- Independently typed operands and a well-formed output suffice for the
recursive runtime application bridge. No syntactic equality of argument/domain
or output/instantiated-codomain annotations is required. -/
theorem partial_applyBetween_typed_family {ε : ValCtx} {ef ea : ValExpr}
    {d c a out : ValTy} {k : ValKind}
    (hf : ValHasType ε ef (.piTy d c)) (ha : ValHasType ε ea a)
    (ho : ValTValid ε out k) (hctx : ValCtxValid ε) {I : Type}
    (ρ : I → ValEnvSem)
    (hρ : ∀ i j, PartialEnvironmentsRelated PartialDirectOracle.oracle ε (ρ i) (ρ j))
    (i j : I) :
    PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle out ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
      (PartialValueEval.applyBetween PartialDirectOracle.oracle (ρ i) [] [] d c a out
        (denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] ef)
        (denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] ea))
      (PartialValueEval.applyBetween PartialDirectOracle.oracle (ρ j) [] [] d c a out
        (denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] ef)
        (denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] ea)) := by
  have hfs := partial_originalExpr_result_family hf hctx ρ hρ
  have has := partial_originalExpr_result_family ha hctx ρ hρ
  have hos := partial_originalType_coherent_family ho hctx ρ hρ
  have hfr := (hfs i j).1
  have har := (has i j).1
  cases hfi : denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] ef <;>
    cases hfj : denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] ef <;>
    simp only [hfi,hfj,PartialRel] at hfr
  · simp only [PartialValueEval.applyBetween,PartialRel]
  cases hai : denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] ea <;>
    cases haj : denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] ea <;>
    simp only [hai,haj,PartialRel] at har
  · simp only [PartialValueEval.applyBetween,PartialRel]
  exact partial_applyBetween_family PartialDirectOracle.oracle d c a out
    (fun p : ULift.{1} I => ⟨ρ p.down,[],[]⟩)
    (fun p q => (hfs p.down q.down).2)
    (fun p q => (has p.down q.down).2)
    (fun p q => hos p.down q.down) ⟨i⟩ ⟨j⟩ _ _ _ _ hfr har

end GLang.PartialValueDomains
