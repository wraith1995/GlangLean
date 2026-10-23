/-
GLang.PreservationV2_Reshape — the generic `reshape_cob` arm of the gen-4
value preservation induction (term judgment).

`term_reshape_v2` discharges the conjunction (EvalT ∧ ReshapEq, regularity,
fv-closure) for `.reshap v τv_tgt τv_src`. Both annotations are explicit
realizations of the basis type. The realized type of a `.reshap _ τ _` is
exactly its target `τ`; the source annotation contributes only to free-variable
closure here.
-/
import GLang.Proofs.Preservation.PreservationV2Helpers
import GLang.Operational.Ordinary

namespace GLang

theorem term_reshape_v2 {Ψ : EvalCtx} {ρ' : Finset VName} {b : Basis} {v : ValExpr}
    {τv_src τv_tgt : ValTy}
    (_hsrc : ValTy.EvalT Ψ (Basis.tof b) τv_src)
    (htgt : ValTy.EvalT Ψ (Basis.tof b) τv_tgt)
    (hsrcfv : ValTy.fv τv_src ⊆ ρ')
    (htgtfv : ValTy.fv τv_tgt ⊆ ρ')
    (ih : (∃ τv, ValTy.EvalT Ψ (Basis.tof b) τv ∧ ReshapEq (ValExpr.inferType v) τv)
         ∧ ValTyOk (ValExpr.inferType v)
         ∧ (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ ρ')) :
    (∃ τv, ValTy.EvalT Ψ (Basis.tof b) τv
          ∧ ReshapEq (ValExpr.inferType (.reshap v τv_tgt τv_src)) τv)
    ∧ ValTyOk (ValExpr.inferType (.reshap v τv_tgt τv_src))
    ∧ (ValTy.fv (ValExpr.inferType
          (.reshap v τv_tgt τv_src)) ∪
        ValExpr.fv (.reshap v τv_tgt τv_src) ⊆ ρ') := by
  have htgtval := (evalT_valid htgt).some
  simp only [ValExpr.inferType_reshap]
  refine ⟨⟨τv_tgt, htgt, ReshapEq.refl htgtval⟩,
    ⟨τv_tgt.structuralKind, ⟨htgtval⟩⟩, ?_⟩
  ·
    have hvfv : ValExpr.fv v ⊆ ρ' :=
      Finset.Subset.trans Finset.subset_union_right ih.2.2
    simp only [ValExpr.fv]
    exact Finset.union_subset htgtfv
      (Finset.union_subset (Finset.union_subset hvfv htgtfv) hsrcfv)

end GLang
