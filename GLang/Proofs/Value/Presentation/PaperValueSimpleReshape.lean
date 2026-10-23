import GLang.Proofs.Value.Presentation.PaperValueSimpleTypes
import GLang.Proofs.Value.Presentation.PaperValueReshapeExtensionality

/-! Arbitrary-order simple-type reshape respects the world-independent runtime
relation. Both local-stack presentations are retained by the evaluator; simple
fibres permit transport between their different runtime representatives. -/
namespace GLang.PaperValueDomains

/-- Paired-context reshape preserves the simple runtime relation at every
arrow depth. Different kinds and incompatible dimensions yield related errors. -/
theorem SimpleTy.reshape_between_related (target source : SimpleTy) (orc : FFSOracleSem)
    (w w' : World) (Γt Γt' : List ValTy) (Δt Δt' : List ValValSem)
    (v v' : ValValSem) (hv : source.runtimeRel v v') :
    PartialRel target.runtimeRel
      (reshapDenotSemBetweenS orc w.env Γt Δt w.types w.values v target.toValTy source.toValTy)
      (reshapDenotSemBetweenS orc w'.env Γt' Δt' w'.types w'.values v' target.toValTy source.toValTy) := by
  classical
  cases target with
  | space st =>
    cases source with
    | space ss =>
      apply (SimpleTy.resultRelated_iff (.space st) orc (w.restack Γt Δt) (w'.restack Γt' Δt') _ _).1
      exact reshape_between_space_related orc ss.toValSpace st.toValSpace
        w w' Γt Γt' Δt Δt' v v'
        ((SimpleTy.runtimeRelated_iff (.space ss) orc w w' v v').2 hv)
        (by simp)
    | arrow a b =>
      cases v <;> cases v' <;> try exact hv.elim
      simp only [SimpleTy.toValTy, reshapDenotSemBetweenS, PartialRel]
  | arrow td tc =>
    cases source with
    | space ss => simp only [SimpleTy.toValTy, reshapDenotSemBetweenS, PartialRel]
    | arrow sd sc =>
      let wt := w.restack Γt Δt
      let wt' := w'.restack Γt' Δt'
      apply (SimpleTy.resultRelated_iff (.arrow td tc) orc wt wt' _ _).1
      simp only [SimpleTy.toValTy, reshapDenotSemBetweenS, PartialRel, RuntimeRelated]
      refine ⟨rfl, rfl, ?_⟩
      intro a b hab
      have hargT := reify_checked_related orc td.toValTy wt wt' a b hab
      simp only [World.denot, wt, wt', World.restack] at hargT
      cases hfa : ValValSem.fromElChecked (denotValTyS orc w.env Γt Δt td.toValTy) a <;>
        cases hfb : ValValSem.fromElChecked (denotValTyS orc w'.env Γt' Δt' td.toValTy) b <;>
        simp only [hfa, hfb, PartialRel] at hargT ⊢
      · rename_i argT argT'
        have hdom := SimpleTy.reshape_between_related sd td orc wt wt'
          w.types w'.types w.values w'.values argT argT'
          ((td.runtimeRelated_iff orc wt wt' argT argT').1 hargT)
        simp only [wt, wt', World.restack] at hdom
        cases hsa : reshapDenotSemBetweenS orc w.env w.types w.values Γt Δt argT sd.toValTy td.toValTy <;>
          cases hsb : reshapDenotSemBetweenS orc w'.env w'.types w'.values Γt' Δt' argT' sd.toValTy td.toValTy <;>
          simp only [hsa, hsb, PartialRel] at hdom ⊢
        · rename_i argS argS'
          obtain ⟨x, y, hx, hy, hxy⟩ := extract_related orc sd.toValTy w w' argS argS'
            ((sd.runtimeRelated_iff orc w w' argS argS').2 hdom)
          simp only [World.denot] at hx hy
          rw [hx, hy]
          have happ := applyTyped_related orc sd.toValTy sc.toValTy w w' v v'
            ((SimpleTy.runtimeRelated_iff (.arrow sd sc) orc w w' v v').2 hv) x y hxy
          cases hpa : v.applyTyped x <;> cases hpb : v'.applyTyped y <;>
            simp only [hpa, hpb, PartialRel] at happ ⊢
          · rename_i res res'
            have hout := SimpleTy.reshape_between_related tc sc orc
              (w.restack (sd.toValTy :: w.types) (argS :: w.values))
              (w'.restack (sd.toValTy :: w'.types) (argS' :: w'.values))
              (td.toValTy :: Γt) (td.toValTy :: Γt') (argT :: Δt) (argT' :: Δt') res res'
              ((sc.runtimeRelated_iff orc (w.push orc sd.toValTy x) (w'.push orc sd.toValTy y) res res').1 happ)
            simpa only [PartialRel] using
              (tc.resultRelated_iff orc (wt.push orc td.toValTy a) (wt'.push orc td.toValTy b) _ _).2 hout

termination_by sizeOf target + sizeOf source

/-- Public equal-stack reshape at arbitrary simple types. -/
theorem SimpleTy.reshape_related (target source : SimpleTy) (orc : FFSOracleSem)
    (w w' : World) (v v' : ValValSem) (hv : source.runtimeRel v v') :
    PartialRel target.runtimeRel
      (reshapDenotSemS orc w.env w.types w.values v target.toValTy source.toValTy)
      (reshapDenotSemS orc w'.env w'.types w'.values v' target.toValTy source.toValTy) := by
  simpa only [reshapDenotSemS_eq_between] using
    SimpleTy.reshape_between_related target source orc w w'
      w.types w'.types w.values w'.values v v' hv

/-- The immediate operand relation suffices for the actual reshape expression,
including arbitrary nested arrows and all checked error branches. -/
theorem SimpleTy.eval_reshape_related (target source : SimpleTy) (orc : FFSOracleSem)
    (w w' : World) (e e' : ValExpr)
    (he : PartialRel source.runtimeRel
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semS orc w'.env w'.types w'.values e')) :
    PartialRel target.runtimeRel
      (denotValB_semS orc w.env w.types w.values (.reshap e target.toValTy source.toValTy))
      (denotValB_semS orc w'.env w'.types w'.values (.reshap e' target.toValTy source.toValTy)) := by
  rw [denotValB_semS.eq_17, denotValB_semS.eq_17]
  cases hl : denotValB_semS orc w.env w.types w.values e <;>
    cases hr : denotValB_semS orc w'.env w'.types w'.values e' <;>
    simp only [hl, hr, PartialRel] at he
  · cases he; rfl
  · exact SimpleTy.reshape_related target source orc w w' _ _ he

end GLang.PaperValueDomains
