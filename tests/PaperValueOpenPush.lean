import GLang.Proofs.Value.Presentation.PaperValueOpenPush

open GLang GLang.PaperValueDomains GLang.DirectOracleReshape

-- A function whose result dimension depends on the distinguished outer
-- matrix binder. Opening changes the FFS witness beneath the function binder.
example (W W' : OpenPushWorld directOracle) (hG : W.G = W'.G) (hu : W.u = W'.u) :
    let τ := ValTy.piTy (.space .real)
      (.space (.ffs .kernel (.tprod .real .real) (.bvar 1)))
    TypePresentation directOracle (ValTy.openRec W.G.length W.u τ) τ
      W.namedWorld W'.namedWorld W.pushedWorld W'.pushedWorld := by
  apply openPush_presentation _ W W' hG hu
  all_goals simp [ValTy.fv, ValSpace.fv, ValExpr.fv]

#print axioms presentation_related_transport
#print axioms runtime_presentation_transport
#print axioms openPush_presentation
#print axioms runtime_related_openPush
#print axioms eval_related_openPush
