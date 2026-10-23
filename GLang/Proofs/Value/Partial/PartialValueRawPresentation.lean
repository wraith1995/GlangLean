import GLang.Proofs.Value.Presentation.PaperValueFreshCoherence
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectAssembly
import GLang.Proofs.Value.Binding.ValueWorldRawPush

namespace GLang.PartialDirectOpenPush.World

def namedWorld (W : World orc) : PaperValueDomains.World :=
  ⟨W.namedRho,W.namedG,W.namedD⟩
def pushedWorld (W : World orc) : PaperValueDomains.World :=
  ⟨W.pushedRho,W.pushedG,W.pushedD⟩
end GLang.PartialDirectOpenPush.World

namespace GLang.PartialValueSubstitution
open PaperValueDomains ValSoundOfDenot

/-- A type-only condition: corresponding base dimensions, and corresponding
codomains after any identical raw argument is stored on both sides. -/
def RawPresentation (orc : PartialFFSOracleSem) : ValTy → ValTy → World → World → Prop
  | .space s, .space t, w, u =>
      ValSpace.dofPartial (orc w.env w.types w.values) s = ValSpace.dofPartial (orc u.env u.types u.values) t
  | .piTy d c, .piTy d' c', w, u =>
      RawPresentation orc d d' w u ∧
        ∀ v, RawPresentation orc c c' (w.rawPush d v) (u.rawPush d' v)
  | _, _, _, _ => False

/-- Every type has the same runtime presentation as itself in the same world. -/
theorem RawPresentation.refl (orc : PartialFFSOracleSem) (t : ValTy)
    (w : World) : RawPresentation orc t t w w := by
  cases t with
  | space s => rfl
  | piTy d c => exact ⟨RawPresentation.refl orc d w,
      fun v => RawPresentation.refl orc c (w.rawPush d v)⟩
termination_by sizeOf t

theorem RawPresentation.sameShape (orc : PartialFFSOracleSem) (τ υ : ValTy)
    (w u : World) (hp : RawPresentation orc τ υ w u) : ValTy.SameShape τ υ := by
  cases τ <;> cases υ
  case space.space => trivial
  case space.piTy => exact hp.elim
  case piTy.space => exact hp.elim
  case piTy.piTy d c d' c' =>
    exact ⟨RawPresentation.sameShape orc d d' w u hp.1,
      RawPresentation.sameShape orc c c' _ _ (hp.2 ValValSem.default)⟩
termination_by sizeOf τ

/-- Exact raw presentation determines the full partial dependent type,
including suspended failures in all canonical fibers. -/
theorem RawPresentation.type_heq (orc : PartialFFSOracleSem) :
    ∀ (t s : ValTy) (w u : World), RawPresentation orc t s w u →
      HEq (denotValTyPartial orc w.env w.types w.values t)
        (denotValTyPartial orc u.env u.types u.values s)
  | .space t, .space s, w, u, h => by
      simp only [RawPresentation] at h
      simp only [denotValTyPartial, h]
      rfl
  | .space _, .piTy _ _, _, _, h => h.elim
  | .piTy _ _, .space _, _, _, h => h.elim
  | .piTy d c, .piTy d' c', w, u, h => by
      have hd := h.1.sameShape orc d d' w u
      have hc := (h.2 ValValSem.default).sameShape orc c c' _ _
      have hdt := PartialValueTransport.type_eq hd
      have hct := PartialValueTransport.type_eq hc
      have hdc := ValTy.SameShape.carrierEl_eq hd
      have hp := PartialValueTransport.type_eq (show ValTy.SameShape (.piTy d c) (.piTy d' c') from ⟨hd,hc⟩)
      simp only [PartialValueTransport.denot_pi]
      apply PartialValueTransport.bind_heq hdt hp _ _ (h.1.type_heq orc d d' w u)
      intro D D' hD
      apply except_ok_heq hp
      apply PartialValueTransport.pair_heq hdt (by rw [hdc,hct]) _ _ _ _ hD
      apply Function.hfunext hdc
      intro a b hab
      have hreify := carrierToVal_SameShape d d' hd a b hab
      rw [hreify]
      exact (h.2 (d'.carrierToVal b)).type_heq orc c c' _ _
termination_by t _ _ _ _ => sizeOf t

 theorem RawPresentation.symm (orc : PartialFFSOracleSem) (τ υ : ValTy)
    (w u : World) (hp : RawPresentation orc τ υ w u) :
    RawPresentation orc υ τ u w := by
  cases τ <;> cases υ
  case space.space => exact Eq.symm hp
  case space.piTy => exact hp.elim
  case piTy.space => exact hp.elim
  case piTy.piTy d c d' c' =>
    exact ⟨hp.1.symm orc d d' w u, fun v => (hp.2 v).symm orc c c' _ _⟩
termination_by sizeOf τ

 theorem RawPresentation.trans (orc : PartialFFSOracleSem) (τ υ ζ : ValTy)
    (w u z : World) (hp : RawPresentation orc τ υ w u)
    (hq : RawPresentation orc υ ζ u z) : RawPresentation orc τ ζ w z := by
  cases τ <;> cases υ <;> cases ζ
  case space.space.space => exact Eq.trans hp hq
  case piTy.piTy.piTy d c d' c' d'' c'' =>
    exact ⟨hp.1.trans orc d d' d'' w u z hq.1,
      fun v => (hp.2 v).trans orc c c' c'' _ _ _ (hq.2 v)⟩
  all_goals first | exact hp.elim | exact hq.elim
termination_by sizeOf τ

/-- Exact raw presentation also survives the actual fresh-name/stack bridge. -/
theorem rawPresentation_openPush (τ : ValTy)
    (W : PartialDirectOpenPush.World PartialDirectOracle.oracle) (hy : W.y ∉ ValTy.fv τ) :
    RawPresentation PartialDirectOracle.oracle (ValTy.openRec W.G.length W.u τ) τ
      W.namedWorld W.pushedWorld := by
  cases τ with
  | space s =>
    exact (PartialDirectOpenPush.observations PartialDirectOpenPush.oracle_openPush W s hy).1
  | piTy d c =>
    simp only [ValTy.fv, Finset.mem_union, not_or] at hy
    refine ⟨rawPresentation_openPush d W hy.1, ?_⟩
    intro v
    have h := rawPresentation_openPush c (W.extend d v hy.1) hy.2
    simpa only [PartialDirectOpenPush.World.namedWorld,
      PartialDirectOpenPush.World.pushedWorld, PartialDirectOpenPush.World.namedRho,
      PartialDirectOpenPush.World.namedG, PartialDirectOpenPush.World.namedD,
      PartialDirectOpenPush.World.pushedRho, PartialDirectOpenPush.World.pushedG,
      PartialDirectOpenPush.World.pushedD, PartialDirectOpenPush.World.extend,
      PartialDirectOpenPush.World.u, ValTy.closePrefix, List.length_cons,
      List.cons_append, World.rawPush] using h
termination_by sizeOf τ

/-- The original cofinite type IH, for arbitrary raw bindings, closes the exact
raw presentation of a dependent function type. -/
theorem rawPresentation_pi_open (ρ ρ' : ValEnvSem) (x : VName)
    (d c d' c' : ValTy)
    (hp : RawPresentation PartialDirectOracle.oracle d d' ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩)
    (hd : ValTy.lc d) (hd' : ValTy.lc d')
    (hxd : x ∉ ValTy.fv d) (hxd' : x ∉ ValTy.fv d')
    (hxc : x ∉ ValTy.fv c) (hxc' : x ∉ ValTy.fv c')
    (hbody : ∀ v, RawPresentation PartialDirectOracle.oracle (ValTy.openVar x d c) (ValTy.openVar x d' c')
      ⟨ρ.update x v,[],[]⟩ ⟨ρ'.update x v,[],[]⟩) :
    RawPresentation PartialDirectOracle.oracle (.piTy d c) (.piTy d' c') ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ := by
  refine ⟨hp, ?_⟩
  intro v
  let W : PartialDirectOpenPush.World PartialDirectOracle.oracle := ⟨ρ,x,d,v,[],[],rfl,hd,hxd,by simp⟩
  let U : PartialDirectOpenPush.World PartialDirectOracle.oracle := ⟨ρ',x,d',v,[],[],rfl,hd',hxd',by simp⟩
  have h₁ := rawPresentation_openPush c W hxc
  have h₃ := rawPresentation_openPush c' U hxc'
  have hm : RawPresentation PartialDirectOracle.oracle (ValTy.openVar x d c) (ValTy.openVar x d' c')
      W.namedWorld U.namedWorld := hbody v
  have h₂ := (h₁.symm PartialDirectOracle.oracle _ _ _ _).trans PartialDirectOracle.oracle _ _ _ _ _ _ hm
  have h₄ := h₂.trans PartialDirectOracle.oracle _ _ _ _ _ _ h₃
  simpa only [W,U,PartialDirectOpenPush.World.pushedWorld,
    PartialDirectOpenPush.World.pushedRho,PartialDirectOpenPush.World.pushedG,
    PartialDirectOpenPush.World.pushedD,List.nil_append,World.rawPush] using h₄

/-- A fresh named update preserves every raw fibre, even when arbitrary
callbacks/arrays are stored at the intervening dependent binders. -/
theorem RawPresentation.fresh {orc : PartialFFSOracleSem} (hirr : PartialDirectFv.OracleFresh orc)
    (τ : ValTy) (w : World) (x : VName) (v : ValValSem)
    (hΓ : ValTyCtxFresh x w.types) (hx : x ∉ ValTy.fv τ) :
    RawPresentation orc τ τ w (w.update x v) := by
  cases τ with
  | space s =>
    exact ((PartialDirectFv.observations hirr w.env x v w.types w.values hΓ s hx).1).symm
  | piTy d c =>
    simp only [ValTy.fv, Finset.mem_union, not_or] at hx
    refine ⟨RawPresentation.fresh hirr d w x v hΓ hx.1, ?_⟩
    intro arg
    exact RawPresentation.fresh hirr c (w.rawPush d arg) x v
      (ValTyCtxFresh.cons hx.1 hΓ) hx.2
termination_by sizeOf τ

end GLang.PartialValueSubstitution
