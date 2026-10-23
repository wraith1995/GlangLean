import GLang.Proofs.Value.Partial.PartialValueApplicationRuntime
import GLang.Proofs.Value.Partial.PartialValueTransport

namespace GLang.PartialValueEval
open PartialValueTransport

theorem checkResult_bind (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy) (v : ValValSem) :
    checkResult orc ρ Γ Δ t (.ok v) =
      bindAcross (t.carrierFromVal v) (fun a => checkValTyPartial orc ρ Γ Δ t a) := by
  cases h : t.carrierFromVal v <;> simp [checkResult, h, bindAcross]

theorem checkValTy_bind (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy) (a : t.carrierEl) :
    checkValTyPartial orc ρ Γ Δ t a =
      bindAcross (denotValTyPartial orc ρ Γ Δ t) (fun T => T.check a) := by
  unfold checkValTyPartial
  cases denotValTyPartial orc ρ Γ Δ t <;> rfl

theorem checkRuntime_bind (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy) (r : Except DimError ValValSem) :
    checkRuntime orc ρ Γ Δ t r =
      bindAcross (checkResult orc ρ Γ Δ t r) (fun a => .ok (t.carrierToVal a)) := by
  unfold checkRuntime
  cases checkResult orc ρ Γ Δ t r <;> rfl

theorem applyChecked_bind (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (d t : ValTy) (f : ValValSem)
    (a : Except DimError ValValSem) :
    applyChecked orc ρ Γ Δ d t (.ok f) a =
      bindAcross (checkResult orc ρ Γ Δ d a)
        (fun x => checkRuntime orc ρ Γ Δ t (f.applyTyped x)) := by
  cases h : checkResult orc ρ Γ Δ d a <;> simp [applyChecked, h, bindAcross]

/-- Runtime checking commutes with a change of type presentation that preserves
both structural carriers and the actual partial type interpretation. -/
theorem checkResult_heq
    (orc orc' : PartialFFSOracleSem) (ρ ρ' : ValEnvSem)
    (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem) (t t' : ValTy)
    (hs : ValSoundOfDenot.ValTy.SameShape t t')
    (ht : HEq (denotValTyPartial orc ρ Γ Δ t) (denotValTyPartial orc' ρ' Γ' Δ' t'))
    (r : Except DimError ValValSem) :
    HEq (checkResult orc ρ Γ Δ t r) (checkResult orc' ρ' Γ' Δ' t' r) := by
  cases r with
  | error e => exact except_error_heq (ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hs) e
  | ok v =>
    rw [checkResult_bind, checkResult_bind]
    have hc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hs
    apply bindAcross_heq hc hc _ _ (carrierFromVal_SameShape t t' hs v)
    intro a b hab
    rw [checkValTy_bind, checkValTy_bind]
    apply bindAcross_heq (type_eq hs) hc _ _ ht
    intro T U hTU
    exact check_heq hs T U hTU a b hab

theorem checkRuntime_eq
    (orc orc' : PartialFFSOracleSem) (ρ ρ' : ValEnvSem)
    (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem) (t t' : ValTy)
    (hs : ValSoundOfDenot.ValTy.SameShape t t')
    (ht : HEq (denotValTyPartial orc ρ Γ Δ t) (denotValTyPartial orc' ρ' Γ' Δ' t'))
    (r : Except DimError ValValSem) :
    checkRuntime orc ρ Γ Δ t r = checkRuntime orc' ρ' Γ' Δ' t' r := by
  apply eq_of_heq
  rw [checkRuntime_bind, checkRuntime_bind]
  apply bindAcross_heq (ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hs) rfl _ _
    (checkResult_heq orc orc' ρ ρ' Γ Γ' Δ Δ' t t' hs ht r)
  intro a b hab
  exact heq_of_eq (congrArg Except.ok (carrierToVal_SameShape t t' hs a b hab))

private theorem applyTyped_heq {A B : Type} (h : A = B) (v : ValValSem)
    (a : A) (b : B) (hab : HEq a b) : v.applyTyped a = v.applyTyped b := by
  cases h
  rw [eq_of_heq hab]

theorem applyDomainChecked_bind (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (d : ValTy) (f : ValValSem)
    (a : Except DimError ValValSem) :
    applyDomainChecked orc ρ Γ Δ d (.ok f) a =
      bindAcross (checkResult orc ρ Γ Δ d a) (fun x => f.applyTyped x) := by
  cases h : checkResult orc ρ Γ Δ d a <;> simp [applyDomainChecked, h, bindAcross, Except.bind]

/-- Binary application depends only on the function domain's interpretation. -/
theorem applyDomainChecked_congr
    (orc orc' : PartialFFSOracleSem) (ρ ρ' : ValEnvSem)
    (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem) (d d' : ValTy)
    (hd : ValSoundOfDenot.ValTy.SameShape d d')
    (hD : HEq (denotValTyPartial orc ρ Γ Δ d) (denotValTyPartial orc' ρ' Γ' Δ' d'))
    (f a : Except DimError ValValSem) :
    applyDomainChecked orc ρ Γ Δ d f a = applyDomainChecked orc' ρ' Γ' Δ' d' f a := by
  cases f with
  | error e => rfl
  | ok f =>
    rw [applyDomainChecked_bind, applyDomainChecked_bind]
    apply eq_of_heq
    have hc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hd
    apply bindAcross_heq hc rfl _ _ (checkResult_heq orc orc' ρ ρ' Γ Γ' Δ Δ' d d' hd hD a)
    intro x y hxy
    exact heq_of_eq (applyTyped_heq hc f x y hxy)

theorem applyChecked_eq
    (orc orc' : PartialFFSOracleSem) (ρ ρ' : ValEnvSem)
    (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem) (d d' t t' : ValTy)
    (hd : ValSoundOfDenot.ValTy.SameShape d d')
    (ht : ValSoundOfDenot.ValTy.SameShape t t')
    (hD : HEq (denotValTyPartial orc ρ Γ Δ d) (denotValTyPartial orc' ρ' Γ' Δ' d'))
    (hT : HEq (denotValTyPartial orc ρ Γ Δ t) (denotValTyPartial orc' ρ' Γ' Δ' t'))
    (f a : Except DimError ValValSem) :
    applyChecked orc ρ Γ Δ d t f a = applyChecked orc' ρ' Γ' Δ' d' t' f a := by
  cases f with
  | error e => rfl
  | ok f =>
    apply eq_of_heq
    rw [applyChecked_bind, applyChecked_bind]
    have hc := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hd
    apply bindAcross_heq hc rfl _ _ (checkResult_heq orc orc' ρ ρ' Γ Γ' Δ Δ' d d' hd hD a)
    intro x y hxy
    have happ := applyTyped_heq hc f x y hxy
    rw [happ]
    exact heq_of_eq (checkRuntime_eq orc orc' ρ ρ' Γ Γ' Δ Δ' t t' ht hT _)

 theorem applyBetween_bind (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (d c a t : ValTy) (f v : ValValSem) :
    applyBetween orc ρ Γ Δ d c a t (.ok f) (.ok v) =
      bindAcross (reshapeBetween orc ρ Γ Δ Γ Δ v d a) (fun arg =>
        bindAcross (d.carrierFromVal arg) (fun x =>
          bindAcross (f.applyTyped x) (fun r =>
            reshapeBetween orc ρ Γ Δ (d :: Γ) (d.carrierToVal x :: Δ) r t c))) := by
  cases h : reshapeBetween orc ρ Γ Δ Γ Δ v d a <;> simp only [applyBetween, h, bindAcross]
  rename_i arg
  cases h' : d.carrierFromVal arg <;> simp only [h', bindAcross]
  rename_i x
  cases f.applyTyped x <;> rfl

/-- Congruence for application transport, with the codomain compared at the
actual decoded argument in the function's local context. -/
theorem applyBetween_congr
    (orc orc' : PartialFFSOracleSem) (ρ ρ' : ValEnvSem)
    (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem)
    (d d' c c' a a' t t' : ValTy)
    (hd : ValSoundOfDenot.ValTy.SameShape d d')
    (harg : ∀ v, reshapeBetween orc ρ Γ Δ Γ Δ v d a =
      reshapeBetween orc' ρ' Γ' Δ' Γ' Δ' v d' a')
    (hout : ∀ (x : d.carrierEl) (y : d'.carrierEl), HEq x y → ∀ r,
      reshapeBetween orc ρ Γ Δ (d :: Γ) (d.carrierToVal x :: Δ) r t c =
      reshapeBetween orc' ρ' Γ' Δ' (d' :: Γ') (d'.carrierToVal y :: Δ') r t' c')
    (f v : Except DimError ValValSem) :
    applyBetween orc ρ Γ Δ d c a t f v =
      applyBetween orc' ρ' Γ' Δ' d' c' a' t' f v := by
  cases f with
  | error e => rfl
  | ok f =>
    cases v with
    | error e => rfl
    | ok v =>
      rw [applyBetween_bind, applyBetween_bind, harg]
      apply eq_of_heq
      apply bindAcross_heq rfl rfl _ _ HEq.rfl
      intro arg arg' ha
      cases ha
      have hcarrier := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hd
      apply bindAcross_heq hcarrier rfl _ _ (carrierFromVal_SameShape d d' hd arg)
      intro x y hxy
      rw [applyTyped_heq hcarrier f x y hxy]
      apply bindAcross_heq rfl rfl _ _ HEq.rfl
      intro r r' hr
      cases hr
      exact heq_of_eq (hout x y hxy r)

end GLang.PartialValueEval
