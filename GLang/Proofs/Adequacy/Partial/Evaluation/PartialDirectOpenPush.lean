import GLang.Proofs.Value.Partial.PartialValueTransport
import GLang.Proofs.Adequacy.Total.DirectOracleOpenPush

/-! Named-variable/bound-slot transport for partial semantics. -/
namespace GLang.PartialDirectOpenPush
open DirectOracleOpenPush

def OracleOpenPush (orc : PartialFFSOracleSem) : Prop :=
  forall {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
      {G : List ValTy} {D : List ValValSem} {p : ValFFSProp}
      {s : ValSpace} {e : ValExpr},
    G.length = D.length ->
    ValTy.lc sigmaV ->
    y ∉ ValTy.fv sigmaV ->
    (forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) ->
    y ∉ ValSpace.fv s -> y ∉ ValExpr.fv e ->
    orc (rho.update y w) (ValTy.closePrefix (.var y sigmaV) G) D p
        (ValSpace.openRec G.length (.var y sigmaV) s)
        (ValExpr.openRec G.length (.var y sigmaV) e) =
      orc rho (G ++ [sigmaV]) (D ++ [w]) p s e

structure World (orc : PartialFFSOracleSem) where
  rho : ValEnvSem
  y : VName
  sigmaV : ValTy
  w : ValValSem
  G : List ValTy
  D : List ValValSem
  length_eq : G.length = D.length
  sigma_lc : ValTy.lc sigmaV
  y_sigma : y ∉ ValTy.fv sigmaV
  y_G : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV

namespace World

def u (W : World orc) : ValExpr := .var W.y W.sigmaV
def namedG (W : World orc) : List ValTy := ValTy.closePrefix W.u W.G
def pushedG (W : World orc) : List ValTy := W.G ++ [W.sigmaV]
def namedD (W : World orc) : List ValValSem := W.D
def pushedD (W : World orc) : List ValValSem := W.D ++ [W.w]
def namedRho (W : World orc) : ValEnvSem := W.rho.update W.y W.w
def pushedRho (W : World orc) : ValEnvSem := W.rho

def extend (W : World orc) (tau : ValTy) (v : ValValSem)
    (hy : W.y ∉ ValTy.fv tau) : World orc where
  rho := W.rho
  y := W.y
  sigmaV := W.sigmaV
  w := W.w
  G := tau :: W.G
  D := v :: W.D
  length_eq := by simp [W.length_eq]
  sigma_lc := W.sigma_lc
  y_sigma := W.y_sigma
  y_G := by
    intro tau' htau'
    rcases List.mem_cons.mp htau' with rfl | htau'
    · exact hy
    · exact W.y_G tau' htau'

@[simp] theorem extend_u (W : World orc) (tau : ValTy)
    (v : ValValSem) (hy) : (W.extend tau v hy).u = W.u := rfl

@[simp] theorem extend_namedG (W : World orc) (tau : ValTy)
    (v : ValValSem) (hy) :
    (W.extend tau v hy).namedG =
      ValTy.openRec W.G.length W.u tau :: W.namedG := by
  simp [extend, namedG, u, ValTy.closePrefix]

@[simp] theorem extend_pushedG (W : World orc) (tau : ValTy)
    (v : ValValSem) (hy) :
    (W.extend tau v hy).pushedG = tau :: W.pushedG := by
  simp [extend, pushedG]

@[simp] theorem extend_namedD (W : World orc) (tau : ValTy)
    (v : ValValSem) (hy) :
    (W.extend tau v hy).namedD = v :: W.namedD := rfl

@[simp] theorem extend_pushedD (W : World orc) (tau : ValTy)
    (v : ValValSem) (hy) :
    (W.extend tau v hy).pushedD = v :: W.pushedD := by
  simp [extend, pushedD]

@[simp] theorem extend_depth (W : World orc) (tau : ValTy)
    (v : ValValSem) (hy) : (W.extend tau v hy).G.length = W.G.length + 1 := by
  simp [extend]

end World

theorem observations {orc : PartialFFSOracleSem} (h : OracleOpenPush orc)
    (W : World orc) : ∀ (s : ValSpace), W.y ∉ s.fv →
      (ValSpace.openRec W.G.length W.u s).dofPartial (orc W.namedRho W.namedG W.namedD) =
        s.dofPartial (orc W.pushedRho W.pushedG W.pushedD) ∧
      (ValSpace.openRec W.G.length W.u s).shpOfPartial (orc W.namedRho W.namedG W.namedD) =
        s.shpOfPartial (orc W.pushedRho W.pushedG W.pushedD)
  | .empty, _ => by simp [ValSpace.openRec, ValSpace.dofPartial, ValSpace.shpOfPartial]
  | .real, _ => by simp [ValSpace.openRec, ValSpace.dofPartial, ValSpace.shpOfPartial]
  | .dsum a b, hs => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hs
      have ha := (observations h W a hs.1).1
      have hb := (observations h W b hs.2).1
      have he : (ValSpace.openRec W.G.length W.u (.dsum a b)).shpOfPartial
          (orc W.namedRho W.namedG W.namedD) =
          (ValSpace.dsum a b).shpOfPartial (orc W.pushedRho W.pushedG W.pushedD) := by
        simp only [ValSpace.openRec, ValSpace.shpOfPartial, ha, hb]
      exact ⟨by simp only [ValSpace.dofPartial, he], he⟩
  | .tprod a b, hs => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hs
      have ha := (observations h W a hs.1).1
      have hb := (observations h W b hs.2).1
      have he : (ValSpace.openRec W.G.length W.u (.tprod a b)).shpOfPartial
          (orc W.namedRho W.namedG W.namedD) =
          (ValSpace.tprod a b).shpOfPartial (orc W.pushedRho W.pushedG W.pushedD) := by
        simp only [ValSpace.openRec, ValSpace.shpOfPartial, ha, hb]
      exact ⟨by simp only [ValSpace.dofPartial, he], he⟩
  | .ffs p s e, hs => by
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hs
      have he := h (rho := W.rho) (w := W.w) (p := p) W.length_eq W.sigma_lc
        W.y_sigma W.y_G hs.1 hs.2
      change orc W.namedRho W.namedG W.namedD p
        (ValSpace.openRec W.G.length W.u s) (ValExpr.openRec W.G.length W.u e) =
        orc W.pushedRho W.pushedG W.pushedD p s e at he
      constructor <;> simp only [ValSpace.openRec, ValSpace.dofPartial, ValSpace.shpOfPartial, he]
termination_by s => sizeOf s

/-- Partial dependent types retain the same fibers across the binder bridge,
including fibers that fail only after a higher-order argument is supplied. -/
theorem type_heq {orc : PartialFFSOracleSem} (h : OracleOpenPush orc) :
    ∀ (t : ValTy) (W : World orc), W.y ∉ t.fv →
      HEq (denotValTyPartial orc W.namedRho W.namedG W.namedD
        (ValTy.openRec W.G.length W.u t))
        (denotValTyPartial orc W.pushedRho W.pushedG W.pushedD t)
  | .space s, W, hs => by
      simp only [ValTy.openRec, denotValTyPartial, (observations h W s hs).1]
      rfl
  | .piTy d c, W, ht => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at ht
      have hd := ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u d
      have hc := ValSoundOfDenot.ValTy.SameShape_openRec (W.G.length + 1) W.u c
      have hdt := PartialValueTransport.type_eq hd
      have hct := PartialValueTransport.type_eq hc
      have hdc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hd
      have hp := PartialValueTransport.type_eq (ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u (.piTy d c))
      simp only [ValTy.openRec, PartialValueTransport.denot_pi]
      change HEq
        ((denotValTyPartial orc W.namedRho W.namedG W.namedD
          (ValTy.openRec W.G.length W.u d)).bind (fun domain =>
            .ok (PartialValType.piTy domain (fun a =>
              denotValTyPartial orc W.namedRho
                (ValTy.openRec W.G.length W.u d :: W.namedG)
                ((ValTy.openRec W.G.length W.u d).carrierToVal a :: W.namedD)
                (ValTy.openRec (W.G.length + 1) W.u c)))))
        ((denotValTyPartial orc W.pushedRho W.pushedG W.pushedD d).bind (fun domain =>
            .ok (PartialValType.piTy domain (fun a =>
              denotValTyPartial orc W.pushedRho (d :: W.pushedG)
                (d.carrierToVal a :: W.pushedD) c))))
      apply PartialValueTransport.bind_heq hdt hp _ _ (type_heq h d W ht.1)
      intro D D' hD
      apply except_ok_heq hp
      apply PartialValueTransport.pair_heq hdt (by rw [hdc, hct]) _ _ _ _ hD
      apply Function.hfunext hdc
      intro a b hab
      have hreify := carrierToVal_SameShape _ _ hd a b hab
      rw [hreify]
      have ih := type_heq h c (W.extend d (d.carrierToVal b) ht.1) ht.2
      simpa only [World.extend_namedG, World.extend_namedD, World.extend_pushedG,
        World.extend_pushedD, World.extend_depth, World.extend_u,
        World.namedRho, World.pushedRho, World.extend] using ih

end GLang.PartialDirectOpenPush
