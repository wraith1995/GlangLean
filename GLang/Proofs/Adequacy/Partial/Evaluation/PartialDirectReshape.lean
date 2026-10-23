import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectOpenPush
import GLang.Proofs.Value.DenotationChecks

namespace GLang.PartialDirectOpenPush
open PartialValueTransport

private theorem applyTyped_heq {A B : Type} (hAB : A = B) (v : ValValSem)
    (a : A) (b : B) (hab : HEq a b) : v.applyTyped a = v.applyTyped b := by
  cases hAB
  rw [eq_of_heq hab]

/-- Explicit eliminator form of the higher-order reshape equation. -/
theorem reshape_pi (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γt : List ValTy) (Δt : List ValValSem) (Γs : List ValTy) (Δs : List ValValSem)
    (v : ValValSem) (dt ct ds cs : ValTy) :
    PartialValueEval.reshapeBetween orc ρ Γt Δt Γs Δs v (.piTy dt ct) (.piTy ds cs) =
      bindAcross (denotValTyPartial orc ρ Γt Δt dt) (fun target =>
      bindAcross (denotValTyPartial orc ρ Γs Δs ds) (fun _ =>
        .ok (.fn dt.carrierEl (fun a =>
          bindAcross (target.check a) (fun checked =>
          bindAcross (PartialValueEval.reshapeBetween orc ρ Γs Δs Γt Δt
              (dt.carrierToVal checked) ds dt) (fun argS =>
          bindAcross (ds.carrierFromVal argS) (fun source =>
          bindAcross (v.applyTyped source) (fun result =>
            PartialValueEval.reshapeBetween orc ρ (dt :: Γt)
              (dt.carrierToVal checked :: Δt) (ds :: Γs) (argS :: Δs) result ct cs)))))))) := by
  rw [PartialValueEval.reshapeBetween]
  cases ht : denotValTyPartial orc ρ Γt Δt dt with
  | error e => rfl
  | ok target =>
    cases hs : denotValTyPartial orc ρ Γs Δs ds with
    | error e => rfl
    | ok source =>
      apply congrArg Except.ok
      apply congrArg (ValValSem.fn dt.carrierEl)
      funext a
      cases hc : target.check a with
      | error e => rfl
      | ok checked =>
        simp only [bindAcross]
        cases hr : PartialValueEval.reshapeBetween orc ρ Γs Δs Γt Δt (dt.carrierToVal checked) ds dt with
        | error e => rfl
        | ok argS =>
          simp only [bindAcross]
          cases hd : ds.carrierFromVal argS with
          | error e => rfl
          | ok source =>
            simp only [bindAcross]
            cases hv : v.applyTyped source <;> rfl

/-- Two prefix worlds share the variable represented by their distinguished
slot. Their inner type/value prefixes can differ during contravariant reshape. -/
structure SameSlot {orc : PartialFFSOracleSem} (Wt Ws : World orc) : Prop where
  rho : Wt.rho = Ws.rho
  name : Wt.y = Ws.y
  ty : Wt.sigmaV = Ws.sigmaV
  value : Wt.w = Ws.w

namespace SameSlot

theorem named {orc : PartialFFSOracleSem} {Wt Ws : World orc} (h : SameSlot Wt Ws) :
    Wt.namedRho = Ws.namedRho := by simp only [World.namedRho, h.rho, h.name, h.value]

theorem pushed {orc : PartialFFSOracleSem} {Wt Ws : World orc} (h : SameSlot Wt Ws) :
    Wt.pushedRho = Ws.pushedRho := h.rho

theorem symm {orc : PartialFFSOracleSem} {Wt Ws : World orc} (h : SameSlot Wt Ws) :
    SameSlot Ws Wt := ⟨h.rho.symm, h.name.symm, h.ty.symm, h.value.symm⟩

theorem extend {orc : PartialFFSOracleSem} {Wt Ws : World orc} (h : SameSlot Wt Ws)
    (t s : ValTy) (a b : ValValSem) (ht : Wt.y ∉ t.fv) (hs : Ws.y ∉ s.fv) :
    SameSlot (Wt.extend t a ht) (Ws.extend s b hs) := ⟨h.rho, h.name, h.ty, h.value⟩

end SameSlot

/-- Higher-order reshape commutes with the named/bound presentation change,
including separate source fibers indexed by the reshaped argument. -/
theorem reshape_eq {orc : PartialFFSOracleSem} (h : OracleOpenPush orc) :
    ∀ (v : ValValSem) (t s : ValTy) (Wt Ws : World orc),
      SameSlot Wt Ws → Wt.y ∉ t.fv → Ws.y ∉ s.fv →
      PartialValueEval.reshapeBetween orc Wt.namedRho Wt.namedG Wt.namedD Ws.namedG Ws.namedD
        v (ValTy.openRec Wt.G.length Wt.u t) (ValTy.openRec Ws.G.length Ws.u s) =
      PartialValueEval.reshapeBetween orc Wt.pushedRho Wt.pushedG Wt.pushedD Ws.pushedG Ws.pushedD v t s
  | .array a, .space t, .space s, Wt, Ws, hw, ht, hs => by
      simp only [ValTy.openRec, PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray]
      rw [(observations h Wt t ht).1]
      have hsource := (observations h Ws s hs).1
      rw [← hw.named, ← hw.pushed] at hsource
      rw [hsource]
  | .fn _ _, .space _, _, _, _, _, _, _ => by
      simp only [ValTy.openRec, PartialValueEval.reshapeBetween]
  | .array _, .space _, .piTy _ _, _, _, _, _, _ => by
      simp only [ValTy.openRec, PartialValueEval.reshapeBetween]
  | v, .piTy dt ct, .piTy ds cs, Wt, Ws, hw, ht, hs => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at ht hs
      simp only [ValTy.openRec, reshape_pi]
      have hdt := ValSoundOfDenot.ValTy.SameShape_openRec Wt.G.length Wt.u dt
      have hds := ValSoundOfDenot.ValTy.SameShape_openRec Ws.G.length Ws.u ds
      have htc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hdt
      have hsc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hds
      apply eq_of_heq
      apply bindAcross_heq (type_eq hdt) rfl _ _ (type_heq h dt Wt ht.1)
      intro target target' htarget
      have hsource := type_heq h ds Ws hs.1
      rw [← hw.named, ← hw.pushed] at hsource
      apply bindAcross_heq (type_eq hds) rfl _ _ hsource
      intro source source' _hsource
      apply heq_of_eq
      apply congrArg Except.ok
      apply ValValSem.fn_partial_congr _ _ htc
      intro a
      let b := htc ▸ a
      have hab : HEq a b := (cast_heq htc a).symm
      apply eq_of_heq
      apply bindAcross_heq htc rfl _ _ (check_heq hdt target target' htarget a b hab)
      intro arg arg' harg
      have hraw := carrierToVal_SameShape _ _ hdt arg arg' harg
      rw [hraw]
      have hdomain := reshape_eq h (dt.carrierToVal arg') ds dt Ws Wt hw.symm hs.1 ht.1
      rw [← hw.named, ← hw.pushed] at hdomain
      apply bindAcross_heq rfl rfl _ _ (heq_of_eq hdomain)
      intro argS argS' hargS
      have hargS' := eq_of_heq hargS
      subst argS'
      apply bindAcross_heq hsc rfl _ _ (carrierFromVal_SameShape _ _ hds argS)
      intro decoded decoded' hdecoded
      have happ : v.applyTyped decoded = v.applyTyped decoded' := by
        exact applyTyped_heq hsc v decoded decoded' hdecoded
      apply bindAcross_heq rfl rfl _ _ (heq_of_eq happ)
      intro result result' hresult
      have hr := eq_of_heq hresult
      subst result'
      apply heq_of_eq
      have ih := reshape_eq h result ct cs
        (Wt.extend dt (dt.carrierToVal arg') ht.1) (Ws.extend ds argS hs.1)
        (hw.extend _ _ _ _ ht.1 hs.1) ht.2 hs.2
      simpa only [World.extend_namedG, World.extend_namedD, World.extend_pushedG,
        World.extend_pushedD, World.extend_depth, World.extend_u,
        World.namedRho, World.pushedRho, World.extend] using ih
  | _, .piTy _ _, .space _, _, _, _, _, _ => by
      simp only [ValTy.openRec, PartialValueEval.reshapeBetween]
termination_by _ t s _ _ _ _ _ => t.kindSize + s.kindSize
decreasing_by all_goals (simp only [ValTy.kindSize_piTy]; omega)

end GLang.PartialDirectOpenPush
