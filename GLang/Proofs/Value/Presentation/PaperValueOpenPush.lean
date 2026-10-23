import GLang.Proofs.Value.Presentation.PaperValueTypePresentation
import GLang.Proofs.Adequacy.Total.DirectOracle

noncomputable section
namespace GLang.PaperValueDomains
open DirectOracleReshape DirectOracleOpenPush

/-- Named and stack presentations of a fresh bound slot. -/
def _root_.GLang.DirectOracleReshape.OpenPushWorld.namedWorld (W : OpenPushWorld directOracle) : World :=
  ⟨W.namedRho, W.namedG, W.namedD⟩
def _root_.GLang.DirectOracleReshape.OpenPushWorld.pushedWorld (W : OpenPushWorld directOracle) : World :=
  ⟨W.pushedRho, W.pushedG, W.pushedD⟩

/-- Exact current evaluation, including errors and functions. -/
theorem _root_.GLang.DirectOracleReshape.OpenPushWorld.eval_open (W : OpenPushWorld directOracle)
    (e : ValExpr) (hy : W.y ∉ ValExpr.fv e) :
    denotValB_semS directOracle W.namedRho W.namedG W.namedD
      (ValExpr.openRec W.G.length W.u e) =
    denotValB_semS directOracle W.pushedRho W.pushedG W.pushedD e :=
  DirectOracleEval.valueOpenPushEvalPrefix_from_leaf directOracle
    directOracle_spec.valueOpenPushOracleCoherent W.length_eq W.sigma_lc
    W.y_sigma W.y_G hy

theorem _root_.GLang.DirectOracleReshape.OpenPushWorld.carrier_open (W : OpenPushWorld directOracle) (τ : ValTy) :
    (W.namedWorld.denot directOracle (ValTy.openRec W.G.length W.u τ)).El =
      (W.pushedWorld.denot directOracle τ).El := by
  simp only [World.denot, OpenPushWorld.namedWorld, OpenPushWorld.pushedWorld,
    denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]

/-- Selected argument fibres push exactly the same runtime representation. -/
theorem _root_.GLang.DirectOracleReshape.OpenPushWorld.reify_open (W : OpenPushWorld directOracle)
    (τ : ValTy) (hy : W.y ∉ ValTy.fv τ)
    (a : (W.namedWorld.denot directOracle (ValTy.openRec W.G.length W.u τ)).El)
    (b : (W.pushedWorld.denot directOracle τ).El) (hab : HEq a b) :
    ValValSem.fromEl (W.namedWorld.denot directOracle (ValTy.openRec W.G.length W.u τ)) a =
      ValValSem.fromEl (W.pushedWorld.denot directOracle τ) b := by
  exact (fromEl_valueOpenPush_from_leaf directOracle_spec.valueOpenPushOracleCoherent
    W.length_eq rfl W.sigma_lc W.y_sigma W.y_G τ hy b a hab.symm).symm

private theorem reify_open_aligned (W : OpenPushWorld directOracle)
    (k : Nat) (u : ValExpr) (hk : k = W.G.length) (hu : u = W.u)
    (τ : ValTy) (hy : W.y ∉ ValTy.fv τ)
    (a : (W.namedWorld.denot directOracle (ValTy.openRec k u τ)).El)
    (b : (W.pushedWorld.denot directOracle τ).El) (hab : HEq a b) :
    ValValSem.fromEl (W.namedWorld.denot directOracle (ValTy.openRec k u τ)) a =
      ValValSem.fromEl (W.pushedWorld.denot directOracle τ) b := by
  subst k
  subst u
  exact W.reify_open τ hy a b hab

/-- Base relations transport between two independently valued paired worlds. -/
theorem related_space_openPush (W W' : OpenPushWorld directOracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u) (s : ValSpace)
    (hy : W.y ∉ ValSpace.fv s) (hy' : W'.y ∉ ValSpace.fv s)
    (a b : FlatArray) :
    Related directOracle (.space (ValSpace.openRec W.G.length W.u s))
      W.namedWorld W'.namedWorld a b ↔
    Related directOracle (.space s) W.pushedWorld W'.pushedWorld a b := by
  have h := dof_valueOpenPush_local directOracle_spec.valueOpenPushOracleCoherent W s hy
  have h' := dof_valueOpenPush_local directOracle_spec.valueOpenPushOracleCoherent W' s hy'
  simp only [← hG, ← hu] at h'
  simp only [Related, OpenPushWorld.namedWorld, OpenPushWorld.pushedWorld,
    World.denot, h, h']
  rfl

/-- Every corresponding FFS leaf transports, not merely its enclosing dof. -/
theorem spaceAgreement_openPush (s : ValSpace) (W W' : OpenPushWorld directOracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u)
    (hy : W.y ∉ ValSpace.fv s) (hy' : W'.y ∉ ValSpace.fv s)
    (h : SpaceOracleAgreement (directOracle W.namedRho W.namedG W.namedD)
      (directOracle W'.namedRho W'.namedG W'.namedD)
      (ValSpace.openRec W.G.length W.u s)) :
    SpaceOracleAgreement (directOracle W.pushedRho W.pushedG W.pushedD)
      (directOracle W'.pushedRho W'.pushedG W'.pushedD) s := by
  cases s with
  | empty => trivial
  | real => trivial
  | dsum s t | tprod s t =>
    simp only [ValSpace.fv, Finset.mem_union, not_or] at hy hy'
    exact ⟨spaceAgreement_openPush s W W' hG hu hy.1 hy'.1 h.1,
      spaceAgreement_openPush t W W' hG hu hy.2 hy'.2 h.2⟩
  | ffs p s e =>
    simp only [ValSpace.fv, Finset.mem_union, not_or] at hy hy'
    have hl := directOracle_spec.valueOpenPushOracleCoherent
      (rho := W.rho) (w := W.w) (p := p) W.length_eq W.sigma_lc
      W.y_sigma W.y_G hy.1 hy.2
    have hr := directOracle_spec.valueOpenPushOracleCoherent
      (rho := W'.rho) (w := W'.w) (p := p) W'.length_eq W'.sigma_lc
      W'.y_sigma W'.y_G hy'.1 hy'.2
    change directOracle W.namedRho W.namedG W.namedD p
      (ValSpace.openRec W.G.length W.u s) (ValExpr.openRec W.G.length W.u e) =
      directOracle W.pushedRho W.pushedG W.pushedD p s e at hl
    change directOracle W'.namedRho W'.namedG W'.namedD p
      (ValSpace.openRec W'.G.length W'.u s) (ValExpr.openRec W'.G.length W'.u e) =
      directOracle W'.pushedRho W'.pushedG W'.pushedD p s e at hr
    rw [← hG, ← hu] at hr
    exact Eq.trans hl.symm (Eq.trans h hr)
termination_by sizeOf s

/-- Full dependent presentation coherence through a fresh-name/bound-slot
change, at arbitrary arrow depth. The oracle law is the proved current law. -/
theorem openPush_presentation (τ : ValTy) (W W' : OpenPushWorld directOracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u)
    (hy : W.y ∉ ValTy.fv τ) (hy' : W'.y ∉ ValTy.fv τ) :
    TypePresentation directOracle (ValTy.openRec W.G.length W.u τ) τ
      W.namedWorld W'.namedWorld W.pushedWorld W'.pushedWorld := by
  cases τ with
  | space s =>
    have h := dof_valueOpenPush_local directOracle_spec.valueOpenPushOracleCoherent W s hy
    have h' := dof_valueOpenPush_local directOracle_spec.valueOpenPushOracleCoherent W' s hy'
    simp only [← hG, ← hu] at h'
    exact ⟨h, h'⟩
  | piTy d c =>
    simp only [ValTy.fv, Finset.mem_union, not_or] at hy hy'
    refine ⟨openPush_presentation d W W' hG hu hy.1 hy'.1, ?_⟩
    intro a b a' b' ha hb
    have hra := W.reify_open d hy.1 a a' ha
    have hrb : ValValSem.fromEl
        (W'.namedWorld.denot directOracle (ValTy.openRec W.G.length W.u d)) b =
        ValValSem.fromEl (W'.pushedWorld.denot directOracle d) b' := by
      exact reify_open_aligned W' W.G.length W.u (congrArg List.length hG)
        hu d hy'.1 b b' hb
    let E := W.extend d (ValValSem.fromEl (W.pushedWorld.denot directOracle d) a') hy.1
    let E' := W'.extend d (ValValSem.fromEl (W'.pushedWorld.denot directOracle d) b') hy'.1
    have hn : E.namedWorld = W.namedWorld.push directOracle
        (ValTy.openRec W.G.length W.u d) a := by
      simp only [E, OpenPushWorld.namedWorld, OpenPushWorld.extend_namedG,
        OpenPushWorld.extend_namedD, OpenPushWorld.extend, OpenPushWorld.namedRho,
        World.push, ← hra]
      rfl
    have hn' : E'.namedWorld = W'.namedWorld.push directOracle
        (ValTy.openRec W.G.length W.u d) b := by
      change World.mk W'.namedRho
        (ValTy.openRec W'.G.length W'.u d :: W'.namedG)
        (ValValSem.fromEl (W'.pushedWorld.denot directOracle d) b' :: W'.namedD) = _
      simp only [← hG, ← hu, ← hrb, World.push, OpenPushWorld.namedWorld]
    have hp : E.pushedWorld = W.pushedWorld.push directOracle d a' := by
      simp [E, OpenPushWorld.pushedWorld, OpenPushWorld.extend,
        OpenPushWorld.pushedRho, OpenPushWorld.pushedG, OpenPushWorld.pushedD, World.push]
    have hp' : E'.pushedWorld = W'.pushedWorld.push directOracle d b' := by
      simp [E', OpenPushWorld.pushedWorld, OpenPushWorld.extend,
        OpenPushWorld.pushedRho, OpenPushWorld.pushedG, OpenPushWorld.pushedD, World.push]
    have hc := openPush_presentation c E E'
      (by simpa [E, E', OpenPushWorld.extend] using congrArg (List.cons d) hG)
      (by simpa [E, E'] using hu) hy.2 hy'.2
    simpa only [E, OpenPushWorld.extend_depth, OpenPushWorld.extend_u,
      hn, hn', hp, hp'] using hc
termination_by sizeOf τ

/-- Dependent type coherence itself survives opening at arbitrary arrow depth. -/
theorem typeCoherent_openPush (τ : ValTy) (W W' : OpenPushWorld directOracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u)
    (hy : W.y ∉ ValTy.fv τ) (hy' : W'.y ∉ ValTy.fv τ)
    (h : TypeCoherent directOracle (ValTy.openRec W.G.length W.u τ)
      W.namedWorld W'.namedWorld) :
    TypeCoherent directOracle τ W.pushedWorld W'.pushedWorld := by
  cases τ with
  | space s => exact spaceAgreement_openPush s W W' hG hu hy hy' h
  | piTy d c =>
    simp only [ValTy.fv, Finset.mem_union, not_or] at hy hy'
    refine ⟨typeCoherent_openPush d W W' hG hu hy.1 hy'.1 h.1, ?_⟩
    intro a' b' hab'
    have hA := W.carrier_open d
    have hB := presentation_carrier directOracle
      (ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u d) W'.namedWorld W'.pushedWorld
    let a := cast hA.symm a'
    let b := cast hB.symm b'
    have ha : HEq a a' := cast_heq hA.symm a'
    have hb : HEq b b' := cast_heq hB.symm b'
    have hab := (presentation_related_transport directOracle _ d
      (ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u d) _ _ _ _
      (openPush_presentation d W W' hG hu hy.1 hy'.1) a b a' b' ha hb).2 hab'
    have hra := W.reify_open d hy.1 a a' ha
    have hrb : ValValSem.fromEl
        (W'.namedWorld.denot directOracle (ValTy.openRec W.G.length W.u d)) b =
        ValValSem.fromEl (W'.pushedWorld.denot directOracle d) b' := by
      exact reify_open_aligned W' W.G.length W.u (congrArg List.length hG)
        hu d hy'.1 b b' hb
    let E := W.extend d (ValValSem.fromEl (W.pushedWorld.denot directOracle d) a') hy.1
    let E' := W'.extend d (ValValSem.fromEl (W'.pushedWorld.denot directOracle d) b') hy'.1
    have hn : E.namedWorld = W.namedWorld.push directOracle
        (ValTy.openRec W.G.length W.u d) a := by
      simp only [E, OpenPushWorld.namedWorld, OpenPushWorld.extend_namedG,
        OpenPushWorld.extend_namedD, OpenPushWorld.extend, OpenPushWorld.namedRho,
        World.push, ← hra]
      rfl
    have hn' : E'.namedWorld = W'.namedWorld.push directOracle
        (ValTy.openRec W.G.length W.u d) b := by
      change World.mk W'.namedRho
        (ValTy.openRec W'.G.length W'.u d :: W'.namedG)
        (ValValSem.fromEl (W'.pushedWorld.denot directOracle d) b' :: W'.namedD) = _
      simp only [← hG, ← hu, ← hrb, World.push, OpenPushWorld.namedWorld]
    have hp : E.pushedWorld = W.pushedWorld.push directOracle d a' := by
      simp [E, OpenPushWorld.pushedWorld, OpenPushWorld.extend,
        OpenPushWorld.pushedRho, OpenPushWorld.pushedG, OpenPushWorld.pushedD, World.push]
    have hp' : E'.pushedWorld = W'.pushedWorld.push directOracle d b' := by
      simp [E', OpenPushWorld.pushedWorld, OpenPushWorld.extend,
        OpenPushWorld.pushedRho, OpenPushWorld.pushedG, OpenPushWorld.pushedD, World.push]
    have hcod := h.2 a b hab
    have hcod' : TypeCoherent directOracle (ValTy.openRec E.G.length E.u c)
        E.namedWorld E'.namedWorld := by
      simpa only [E, OpenPushWorld.extend_depth, OpenPushWorld.extend_u, hn, hn'] using hcod
    have hout := typeCoherent_openPush c E E'
      (by simpa [E, E', OpenPushWorld.extend] using congrArg (List.cons d) hG)
      (by simpa [E, E'] using hu) hy.2 hy'.2 hcod'
    simpa only [hp, hp'] using hout
termination_by sizeOf τ

/-- The complete dependent runtime relation survives the named-to-stack
presentation change; latent higher-order callbacks need not be identical. -/
theorem runtime_related_openPush (τ : ValTy) (W W' : OpenPushWorld directOracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u)
    (hy : W.y ∉ ValTy.fv τ) (hy' : W'.y ∉ ValTy.fv τ)
    (v v' : ValValSem)
    (h : RuntimeRelated directOracle (ValTy.openRec W.G.length W.u τ)
      W.namedWorld W'.namedWorld v v') :
    RuntimeRelated directOracle τ W.pushedWorld W'.pushedWorld v v' :=
  runtime_presentation_transport directOracle _ τ
    (ValSoundOfDenot.ValTy.SameShape_openRec _ _ τ) _ _ _ _
    (openPush_presentation τ W W' hG hu hy hy') v v' h

/-- Cofinite body induction conclusions transport to the exact runtime pushes
used by the evaluator, at every dependent result type and prefix depth. -/
theorem eval_related_openPush (τ : ValTy) (e : ValExpr)
    (W W' : OpenPushWorld directOracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u)
    (hy : W.y ∉ ValTy.fv τ) (hy' : W'.y ∉ ValTy.fv τ)
    (he : W.y ∉ ValExpr.fv e) (he' : W'.y ∉ ValExpr.fv e)
    (h : PartialRel
      (RuntimeRelated directOracle (ValTy.openRec W.G.length W.u τ) W.namedWorld W'.namedWorld)
      (denotValB_semS directOracle W.namedRho W.namedG W.namedD
        (ValExpr.openRec W.G.length W.u e))
      (denotValB_semS directOracle W'.namedRho W'.namedG W'.namedD
        (ValExpr.openRec W.G.length W.u e))) :
    PartialRel (RuntimeRelated directOracle τ W.pushedWorld W'.pushedWorld)
      (denotValB_semS directOracle W.pushedRho W.pushedG W.pushedD e)
      (denotValB_semS directOracle W'.pushedRho W'.pushedG W'.pushedD e) := by
  have hl := W.eval_open e he
  have hr := W'.eval_open e he'
  rw [← hG, ← hu] at hr
  rw [hl, hr] at h
  cases ha : denotValB_semS directOracle W.pushedRho W.pushedG W.pushedD e <;>
    cases hb : denotValB_semS directOracle W'.pushedRho W'.pushedG W'.pushedD e <;>
    simp only [ha, hb, PartialRel] at h ⊢
  exact runtime_related_openPush τ W W' hG hu hy hy' _ _ h

end GLang.PaperValueDomains
