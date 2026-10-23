import GLang.Proofs.Value.Presentation.PaperValueRawPresentation
import GLang.Proofs.Value.Presentation.PaperValueCoherentFamily

namespace GLang.PaperValueDomains
open DirectOracleReshape

/-- Formation coherence is stable under related actual runtime bindings.
Keeping the binding raw covers both ordinary and checked codec presentations. -/
def RawTypeCoherent (orc : FFSOracleSem) : ValTy → World → World → Prop
  | .space s, w, w' =>
      SpaceOracleAgreement (orc w.env w.types w.values) (orc w'.env w'.types w'.values) s
  | .piTy d c, w, w' => RawTypeCoherent orc d w w' ∧
      ∀ v v', RuntimeRelated orc d w w' v v' →
        RawTypeCoherent orc c (w.rawPush d v) (w'.rawPush d v')

theorem RawTypeCoherent.toCoherent (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (h : RawTypeCoherent orc τ w w') : TypeCoherent orc τ w w' := by
  cases τ with
  | space s => exact h
  | piTy d c =>
    refine ⟨h.1.toCoherent orc d w w', ?_⟩
    intro a b hab
    exact (h.2 _ _ (reify_related orc d w w' a b hab)).toCoherent orc c _ _
termination_by sizeOf τ

/-- Full raw coherence respects fresh named opening, at arbitrary binder depth. -/
theorem rawCoherent_openPush (τ : ValTy) (W W' : OpenPushWorld directOracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u)
    (hy : W.y ∉ ValTy.fv τ) (hy' : W'.y ∉ ValTy.fv τ)
    (h : RawTypeCoherent directOracle (ValTy.openRec W.G.length W.u τ)
      W.namedWorld W'.namedWorld) :
    RawTypeCoherent directOracle τ W.pushedWorld W'.pushedWorld := by
  cases τ with
  | space s => exact spaceAgreement_openPush s W W' hG hu hy hy' h
  | piTy d c =>
    simp only [ValTy.fv, Finset.mem_union, not_or] at hy hy'
    refine ⟨rawCoherent_openPush d W W' hG hu hy.1 hy'.1 h.1, ?_⟩
    intro v v' hv
    have hp := (openPush_presentation d W W' hG hu hy.1 hy'.1).symm
      directOracle _ d (ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u d) _ _ _ _
    have hn := runtime_presentation_transport directOracle d _
      (ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u d).symm
      _ _ _ _ hp v v' hv
    let E := W.extend d v hy.1
    let E' := W'.extend d v' hy'.1
    have he : E.namedWorld = W.namedWorld.rawPush (ValTy.openRec W.G.length W.u d) v := by
      simp only [E, OpenPushWorld.namedWorld, OpenPushWorld.extend, OpenPushWorld.namedRho, World.rawPush]
      rfl
    have he' : E'.namedWorld = W'.namedWorld.rawPush (ValTy.openRec W.G.length W.u d) v' := by
      change World.mk W'.namedRho (ValTy.openRec W'.G.length W'.u d :: W'.namedG)
        (v' :: W'.namedD) = _
      simp only [← hG, ← hu, World.rawPush, OpenPushWorld.namedWorld]
    have ht : RawTypeCoherent directOracle (ValTy.openRec E.G.length E.u c)
        E.namedWorld E'.namedWorld := by
      simpa only [E, OpenPushWorld.extend_depth, OpenPushWorld.extend_u, he, he'] using h.2 v v' hn
    have ho := rawCoherent_openPush c E E'
      (by simpa [E, E', OpenPushWorld.extend] using congrArg (List.cons d) hG)
      (by simpa [E,E'] using hu) hy.2 hy'.2 ht
    simpa only [E,E',OpenPushWorld.pushedWorld,OpenPushWorld.pushedRho,
      OpenPushWorld.pushedG,OpenPushWorld.pushedD,OpenPushWorld.extend,
      List.cons_append,World.rawPush] using ho
termination_by sizeOf τ

/-- Fresh named updates preserve coherence even below raw runtime binders. -/
theorem RawTypeCoherent.fresh {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (τ : ValTy) (w w' : World) (x : VName) (v v' : ValValSem)
    (hG : ValTyCtxFresh x w.types) (hG' : ValTyCtxFresh x w'.types)
    (hx : x ∉ ValTy.fv τ) (h : RawTypeCoherent orc τ w w') :
    RawTypeCoherent orc τ (w.update x v) (w'.update x v') := by
  cases τ with
  | space s =>
    exact SpaceOracleAgreement.trans _ _ _ s
      (SpaceOracleAgreement.symm _ _ s (SpaceOracleAgreement.fresh hirr w x v hG s hx))
      (SpaceOracleAgreement.trans _ _ _ s h (SpaceOracleAgreement.fresh hirr w' x v' hG' s hx))
  | piTy d c =>
    simp only [ValTy.fv, Finset.mem_union, not_or] at hx
    refine ⟨h.1.fresh hirr d w w' x v v' hG hG' hx.1, ?_⟩
    intro a b hab
    have hab0 := (runtime_fiber_transport_iff orc d w w' _ _
      (FiberAgreement.fresh hirr d w w' x v v' hG hG' hx.1) a b).2 hab
    exact (h.2 a b hab0).fresh hirr c (w.rawPush d a) (w'.rawPush d b)
      x v v' (ValTyCtxFresh.cons hx.1 hG) (ValTyCtxFresh.cons hx.1 hG') hx.2
termination_by sizeOf τ

end GLang.PaperValueDomains
