import GLang.Proofs.Value.Binding.ValueWorldRawPush
import GLang.Proofs.Value.Presentation.PaperValuePresentationConversions
import GLang.Proofs.Value.Presentation.PaperValueOpenPush
import GLang.Proofs.Value.Presentation.PaperValueFreshCoherence

/-! Exact type presentation under identical raw stack extensions. -/
namespace GLang.PaperValueDomains
open ValSoundOfDenot

/-- A type-only condition: corresponding base dimensions, and corresponding
codomains after any identical raw argument is stored on both sides. -/
def RawTypePresentation (orc : FFSOracleSem) : ValTy → ValTy → World → World → Prop
  | .space s, .space t, w, u =>
      ValSpace.dof (orc w.env w.types w.values) s = ValSpace.dof (orc u.env u.types u.values) t
  | .piTy d c, .piTy d' c', w, u =>
      RawTypePresentation orc d d' w u ∧
        ∀ v, RawTypePresentation orc c c' (w.rawPush d v) (u.rawPush d' v)
  | _, _, _, _ => False

/-- Identical types in the same runtime world have identical presentations. -/
theorem RawTypePresentation.refl (orc : FFSOracleSem) (τ : ValTy) (w : World) :
    RawTypePresentation orc τ τ w w := by
  cases τ with
  | space s => rfl
  | piTy d c => exact ⟨RawTypePresentation.refl orc d w,
      fun v => RawTypePresentation.refl orc c (w.rawPush d v)⟩
termination_by sizeOf τ

theorem RawTypePresentation.sameShape (orc : FFSOracleSem) (τ υ : ValTy)
    (w u : World) (hp : RawTypePresentation orc τ υ w u) : ValTy.SameShape τ υ := by
  cases τ <;> cases υ
  case space.space => trivial
  case space.piTy => exact hp.elim
  case piTy.space => exact hp.elim
  case piTy.piTy d c d' c' =>
    exact ⟨RawTypePresentation.sameShape orc d d' w u hp.1,
      RawTypePresentation.sameShape orc c c' _ _ (hp.2 ValValSem.default)⟩
termination_by sizeOf τ

/-- Exact ordinary reification, without requiring supported input values. -/
theorem RawTypePresentation.fromEl (orc : FFSOracleSem) (τ υ : ValTy)
    (w u : World) (hp : RawTypePresentation orc τ υ w u)
    (a : (w.denot orc τ).El) (b : (u.denot orc υ).El) (hab : HEq a b) :
    ValValSem.fromEl (w.denot orc τ) a = ValValSem.fromEl (u.denot orc υ) b := by
  cases τ <;> cases υ
  case space.space s t =>
    obtain rfl := eq_of_heq hab
    change ValSpace.dof _ s = ValSpace.dof _ t at hp
    simp only [denotValTyS, ValValSem.fromEl, hp]
  case space.piTy => exact hp.elim
  case piTy.space => exact hp.elim
  case piTy.piTy d c d' c' =>
    have hs := hp.sameShape orc (.piTy d c) (.piTy d' c') w u
    have hd := presentation_carrier orc hs.1 w u
    have hfamilies : HEq
        (fun x : (w.denot orc d).El => Except DimError ((w.push orc d x).denot orc c).El)
        (fun y : (u.denot orc d').El => Except DimError ((u.push orc d' y).denot orc c').El) := by
      refine Function.hfunext hd ?_
      intro x y _
      exact heq_of_eq (congrArg (Except DimError)
        (presentation_carrier orc hs.2 (w.push orc d x) (u.push orc d' y)))
    simp only [denotValTyS, ValValSem.fromEl]
    apply ValValSem.fn_congr _ _ hd
    intro x
    let y := cast hd x
    have hxy : HEq x y := (cast_heq hd x).symm
    have hraw := RawTypePresentation.fromEl orc d d' w u hp.1 x y hxy
    have hout : HEq (a x) (b y) := heq_app_dep hd hfamilies hab hxy
    apply except_map_heq_congr
      (presentation_carrier orc hs.2 (w.push orc d x) (u.push orc d' y))
      (a x) (b y) hout
    intro r r' hr
    have hc : RawTypePresentation orc c c' (w.push orc d x) (u.push orc d' y) := by
      simpa only [World.push, World.rawPush, hraw] using hp.2 (ValValSem.fromEl (w.denot orc d) x)
    exact RawTypePresentation.fromEl orc c c' _ _ hc r r' hr
termination_by sizeOf τ

/-- The raw condition entails the ordinary typed-carrier presentation. -/
theorem RawTypePresentation.toPresentation (orc : FFSOracleSem) (τ υ : ValTy)
    (w u : World) (hp : RawTypePresentation orc τ υ w u) :
    TypePresentation orc τ υ w w u u := by
  cases τ <;> cases υ
  case space.space s t => exact ⟨hp,hp⟩
  case space.piTy => exact hp.elim
  case piTy.space => exact hp.elim
  case piTy.piTy d c d' c' =>
    refine ⟨RawTypePresentation.toPresentation orc d d' w u hp.1, ?_⟩
    intro a b a' b' ha hb
    have hleft := hp.1.fromEl orc d d' w u a a' ha
    have hright := hp.1.fromEl orc d d' w u b b' hb
    have hl : RawTypePresentation orc c c' (w.push orc d a) (u.push orc d' a') := by
      simpa only [World.push, World.rawPush, hleft] using hp.2 (ValValSem.fromEl (w.denot orc d) a)
    have hr : RawTypePresentation orc c c' (w.push orc d b) (u.push orc d' b') := by
      simpa only [World.push, World.rawPush, hright] using hp.2 (ValValSem.fromEl (w.denot orc d) b)
    exact TypePresentation.pair orc c c' (hl.sameShape orc c c' _ _) _ _ _ _
      (hl.toPresentation orc c c' _ _) (hr.toPresentation orc c c' _ _)
termination_by sizeOf τ

 theorem RawTypePresentation.symm (orc : FFSOracleSem) (τ υ : ValTy)
    (w u : World) (hp : RawTypePresentation orc τ υ w u) :
    RawTypePresentation orc υ τ u w := by
  cases τ <;> cases υ
  case space.space => exact Eq.symm hp
  case space.piTy => exact hp.elim
  case piTy.space => exact hp.elim
  case piTy.piTy d c d' c' =>
    exact ⟨hp.1.symm orc d d' w u, fun v => (hp.2 v).symm orc c c' _ _⟩
termination_by sizeOf τ

 theorem RawTypePresentation.trans (orc : FFSOracleSem) (τ υ ζ : ValTy)
    (w u z : World) (hp : RawTypePresentation orc τ υ w u)
    (hq : RawTypePresentation orc υ ζ u z) : RawTypePresentation orc τ ζ w z := by
  cases τ <;> cases υ <;> cases ζ
  case space.space.space => exact Eq.trans hp hq
  case piTy.piTy.piTy d c d' c' d'' c'' =>
    exact ⟨hp.1.trans orc d d' d'' w u z hq.1,
      fun v => (hp.2 v).trans orc c c' c'' _ _ _ (hq.2 v)⟩
  all_goals first | exact hp.elim | exact hq.elim
termination_by sizeOf τ

/-- Exact raw presentation also survives the actual fresh-name/stack bridge. -/
theorem rawPresentation_openPush (τ : ValTy)
    (W : DirectOracleReshape.OpenPushWorld directOracle) (hy : W.y ∉ ValTy.fv τ) :
    RawTypePresentation directOracle (ValTy.openRec W.G.length W.u τ) τ
      W.namedWorld W.pushedWorld := by
  cases τ with
  | space s =>
    exact DirectOracleReshape.dof_valueOpenPush_local
      directOracle_spec.valueOpenPushOracleCoherent W s hy
  | piTy d c =>
    simp only [ValTy.fv, Finset.mem_union, not_or] at hy
    refine ⟨rawPresentation_openPush d W hy.1, ?_⟩
    intro v
    have h := rawPresentation_openPush c (W.extend d v hy.1) hy.2
    simpa only [DirectOracleReshape.OpenPushWorld.namedWorld,
      DirectOracleReshape.OpenPushWorld.pushedWorld, DirectOracleReshape.OpenPushWorld.namedRho,
      DirectOracleReshape.OpenPushWorld.namedG, DirectOracleReshape.OpenPushWorld.namedD,
      DirectOracleReshape.OpenPushWorld.pushedRho, DirectOracleReshape.OpenPushWorld.pushedG,
      DirectOracleReshape.OpenPushWorld.pushedD, DirectOracleReshape.OpenPushWorld.extend,
      DirectOracleReshape.OpenPushWorld.u, ValTy.closePrefix, List.length_cons,
      List.cons_append, World.rawPush] using h
termination_by sizeOf τ

/-- The original cofinite type IH, for arbitrary raw bindings, closes the exact
raw presentation of a dependent function type. -/
theorem rawPresentation_pi_open (ρ ρ' : ValEnvSem) (x : VName)
    (d c d' c' : ValTy)
    (hp : RawTypePresentation directOracle d d' ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩)
    (hd : ValTy.lc d) (hd' : ValTy.lc d')
    (hxd : x ∉ ValTy.fv d) (hxd' : x ∉ ValTy.fv d')
    (hxc : x ∉ ValTy.fv c) (hxc' : x ∉ ValTy.fv c')
    (hbody : ∀ v, RawTypePresentation directOracle (ValTy.openVar x d c) (ValTy.openVar x d' c')
      ⟨ρ.update x v,[],[]⟩ ⟨ρ'.update x v,[],[]⟩) :
    RawTypePresentation directOracle (.piTy d c) (.piTy d' c') ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ := by
  refine ⟨hp, ?_⟩
  intro v
  let W : DirectOracleReshape.OpenPushWorld directOracle := ⟨ρ,x,d,v,[],[],rfl,hd,hxd,by simp⟩
  let U : DirectOracleReshape.OpenPushWorld directOracle := ⟨ρ',x,d',v,[],[],rfl,hd',hxd',by simp⟩
  have h₁ := rawPresentation_openPush c W hxc
  have h₃ := rawPresentation_openPush c' U hxc'
  have hm : RawTypePresentation directOracle (ValTy.openVar x d c) (ValTy.openVar x d' c')
      W.namedWorld U.namedWorld := hbody v
  have h₂ := (h₁.symm directOracle _ _ _ _).trans directOracle _ _ _ _ _ _ hm
  have h₄ := h₂.trans directOracle _ _ _ _ _ _ h₃
  simpa only [W,U,DirectOracleReshape.OpenPushWorld.pushedWorld,
    DirectOracleReshape.OpenPushWorld.pushedRho,DirectOracleReshape.OpenPushWorld.pushedG,
    DirectOracleReshape.OpenPushWorld.pushedD,List.nil_append,World.rawPush] using h₄

/-- A fresh named update preserves every raw fibre, even when arbitrary
callbacks/arrays are stored at the intervening dependent binders. -/
theorem RawTypePresentation.fresh {orc : FFSOracleSem} (hirr : OracleFvIrrel orc)
    (τ : ValTy) (w : World) (x : VName) (v : ValValSem)
    (hΓ : ValTyCtxFresh x w.types) (hx : x ∉ ValTy.fv τ) :
    RawTypePresentation orc τ τ w (w.update x v) := by
  cases τ with
  | space s =>
    exact (leafAgreement_shapes _ _ s (SpaceOracleAgreement.fresh hirr w x v hΓ s hx)).2
  | piTy d c =>
    simp only [ValTy.fv, Finset.mem_union, not_or] at hx
    refine ⟨RawTypePresentation.fresh hirr d w x v hΓ hx.1, ?_⟩
    intro arg
    exact RawTypePresentation.fresh hirr c (w.rawPush d arg) x v
      (ValTyCtxFresh.cons hx.1 hΓ) hx.2
termination_by sizeOf τ

end GLang.PaperValueDomains
