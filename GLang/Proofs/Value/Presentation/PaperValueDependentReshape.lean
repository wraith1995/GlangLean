import GLang.Proofs.Value.Presentation.PaperValueDependentCoherence
import GLang.Proofs.Value.Presentation.PaperValueReshapeExtensionality

/-! Full dependent reshape under explicit local fibre/query coherence.
No field assumes evaluator invariance. The recursive certificate records
which type leaves must survive the runtime representation changes at binders. -/
namespace GLang.PaperValueDomains

/-- Local obligations of dependent reshape. Base cases mention only target
FFS leaves. Arrow cases recurse on domain conversion, then require typed-leaf
transport and recursive result conversion at the actual runtime stacks. -/
def ReshapeCoherent (orc : FFSOracleSem) : ValTy → ValTy → World → World →
    List ValTy → List ValTy → List ValValSem → List ValValSem → Prop
  | .space st, .space _, w, w', Γt, Γt', Δt, Δt' =>
      SpaceOracleAgreement (orc w.env Γt Δt) (orc w'.env Γt' Δt') st
  | .space _, .piTy _ _, _, _, _, _, _, _ => True
  | .piTy _ _, .space _, _, _, _, _, _, _ => True
  | .piTy td tc, .piTy sd sc, w, w', Γt, Γt', Δt, Δt' =>
      let wt := w.restack Γt Δt
      let wt' := w'.restack Γt' Δt'
      ReshapeCoherent orc sd td wt wt' w.types w'.types w.values w'.values ∧
      ∀ a b, Related orc td wt wt' a b →
      ∀ argT argT', ValValSem.fromElChecked (wt.denot orc td) a = .ok argT →
        ValValSem.fromElChecked (wt'.denot orc td) b = .ok argT' →
        RuntimeRelated orc td wt wt' argT argT' →
      ∀ argS argS',
        reshapDenotSemBetweenS orc w.env w.types w.values Γt Δt argT sd td = .ok argS →
        reshapDenotSemBetweenS orc w'.env w'.types w'.values Γt' Δt' argT' sd td = .ok argS' →
        RuntimeRelated orc sd w w' argS argS' →
      ∀ x y, ValValSem.toEl (w.denot orc sd) argS = .ok x →
        ValValSem.toEl (w'.denot orc sd) argS' = .ok y → Related orc sd w w' x y →
      let ws := w.restack (sd :: w.types) (argS :: w.values)
      let ws' := w'.restack (sd :: w'.types) (argS' :: w'.values)
      let ut := w.restack (td :: Γt) (argT :: Δt)
      let ut' := w'.restack (td :: Γt') (argT' :: Δt')
      FiberAgreement orc sc (w.push orc sd x) (w'.push orc sd y) ws ws' ∧
      FiberAgreement orc tc ut ut' (wt.push orc td a) (wt'.push orc td b) ∧
      ReshapeCoherent orc tc sc ws ws' (td :: Γt) (td :: Γt') (argT :: Δt) (argT' :: Δt')
  termination_by target source _ _ _ _ _ _ => sizeOf target + sizeOf source

/-- Actual paired-stack reshape respects the full dependent logical relation
when its local typed-query/fibre obligations hold. -/
theorem reshape_between_dependent_related (target source : ValTy) (orc : FFSOracleSem)
    (w w' : World) (Γt Γt' : List ValTy) (Δt Δt' : List ValValSem)
    (v v' : ValValSem) (hv : RuntimeRelated orc source w w' v v')
    (hc : ReshapeCoherent orc target source w w' Γt Γt' Δt Δt') :
    PartialRel (RuntimeRelated orc target (w.restack Γt Δt) (w'.restack Γt' Δt'))
      (reshapDenotSemBetweenS orc w.env Γt Δt w.types w.values v target source)
      (reshapDenotSemBetweenS orc w'.env Γt' Δt' w'.types w'.values v' target source) := by
  classical
  cases target with
  | space st =>
    cases source with
    | space ss =>
      simp only [ReshapeCoherent] at hc
      exact reshape_between_space_related orc ss st w w' Γt Γt' Δt Δt' v v' hv
        (leafAgreement_shapes _ _ st hc).2
    | piTy d c =>
      cases v <;> cases v' <;> try exact hv.elim
      simp only [reshapDenotSemBetweenS, PartialRel]
  | piTy td tc =>
    cases source with
    | space ss => simp only [reshapDenotSemBetweenS, PartialRel]
    | piTy sd sc =>
      simp only [ReshapeCoherent] at hc
      let wt := w.restack Γt Δt
      let wt' := w'.restack Γt' Δt'
      simp only [reshapDenotSemBetweenS, PartialRel, RuntimeRelated]
      refine ⟨rfl, rfl, ?_⟩
      intro a b hab
      have hargT := reify_checked_related orc td wt wt' a b hab
      simp only [World.denot, wt, wt', World.restack] at hargT
      cases hfa : ValValSem.fromElChecked (denotValTyS orc w.env Γt Δt td) a <;>
        cases hfb : ValValSem.fromElChecked (denotValTyS orc w'.env Γt' Δt' td) b <;>
        simp only [hfa, hfb, PartialRel] at hargT ⊢
      · rename_i argT argT'
        have hdom := reshape_between_dependent_related sd td orc wt wt'
          w.types w'.types w.values w'.values argT argT' hargT hc.1
        simp only [wt, wt', World.restack] at hdom
        cases hsa : reshapDenotSemBetweenS orc w.env w.types w.values Γt Δt argT sd td <;>
          cases hsb : reshapDenotSemBetweenS orc w'.env w'.types w'.values Γt' Δt' argT' sd td <;>
          simp only [hsa, hsb, PartialRel] at hdom ⊢
        · rename_i argS argS'
          obtain ⟨x, y, hx, hy, hxy⟩ := extract_related orc sd w w' argS argS' hdom
          have hcoh := hc.2 a b hab argT argT' hfa hfb hargT argS argS' hsa hsb hdom x y hx hy hxy
          simp only [World.denot] at hx hy
          rw [hx, hy]
          have happ := applyTyped_related orc sd sc w w' v v' hv x y hxy
          cases hpa : v.applyTyped x <;> cases hpb : v'.applyTyped y <;>
            simp only [hpa, hpb, PartialRel] at happ ⊢
          · rename_i res res'
            have hres := runtime_fiber_transport orc sc _ _ _ _ hcoh.1 res res' happ
            have hout := reshape_between_dependent_related tc sc orc
              (w.restack (sd :: w.types) (argS :: w.values))
              (w'.restack (sd :: w'.types) (argS' :: w'.values))
              (td :: Γt) (td :: Γt') (argT :: Δt) (argT' :: Δt') res res' hres hcoh.2.2
            have hm := PartialRel.map (fun v => v) (fun v => v)
              (fun p q hp => runtime_fiber_transport orc tc _ _ _ _ hcoh.2.1 p q hp) hout
            simp only [World.restack] at hm
            cases hlo : reshapDenotSemBetweenS orc w.env (td :: Γt) (argT :: Δt)
                (sd :: w.types) (argS :: w.values) res tc sc <;>
              cases hro : reshapDenotSemBetweenS orc w'.env (td :: Γt') (argT' :: Δt')
                (sd :: w'.types) (argS' :: w'.values) res' tc sc <;>
              simpa only [hlo, hro, Except.map, PartialRel] using hm
termination_by sizeOf target + sizeOf source

/-- Equal-stack dependent reshape with its local fibre obligations. -/
theorem reshape_dependent_related (target source : ValTy) (orc : FFSOracleSem)
    (w w' : World) (v v' : ValValSem) (hv : RuntimeRelated orc source w w' v v')
    (hc : ReshapeCoherent orc target source w w' w.types w'.types w.values w'.values) :
    PartialRel (RuntimeRelated orc target w w')
      (reshapDenotSemS orc w.env w.types w.values v target source)
      (reshapDenotSemS orc w'.env w'.types w'.values v' target source) := by
  simpa only [reshapDenotSemS_eq_between, World.restack] using
    reshape_between_dependent_related target source orc w w'
      w.types w'.types w.values w'.values v v' hv hc

/-- The live dependent reshape expression, requiring only the operand relation
and local type/query coherence, never the desired evaluation conclusion. -/
theorem eval_reshape_dependent_related (target source : ValTy) (orc : FFSOracleSem)
    (w w' : World) (e e' : ValExpr)
    (he : PartialRel (RuntimeRelated orc source w w')
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semS orc w'.env w'.types w'.values e'))
    (hc : ReshapeCoherent orc target source w w' w.types w'.types w.values w'.values) :
    PartialRel (RuntimeRelated orc target w w')
      (denotValB_semS orc w.env w.types w.values (.reshap e target source))
      (denotValB_semS orc w'.env w'.types w'.values (.reshap e' target source)) := by
  rw [denotValB_semS.eq_17, denotValB_semS.eq_17]
  cases hl : denotValB_semS orc w.env w.types w.values e <;>
    cases hr : denotValB_semS orc w'.env w'.types w'.values e' <;>
    simp only [hl, hr, PartialRel] at he
  · cases he; rfl
  · exact reshape_dependent_related target source orc w w' _ _ he hc

end GLang.PaperValueDomains
