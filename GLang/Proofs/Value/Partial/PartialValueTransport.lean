import GLang.Value.TypeInterpretation
import GLang.Proofs.Value.Soundness.ValueSoundnessSem

/-! Structural transport of partial type descriptions and result checks. -/
namespace GLang.PartialValueTransport
universe u v
open ValSoundOfDenot

theorem type_eq : ∀ {t s : ValTy}, ValTy.SameShape t s →
    PartialValType t = PartialValType s
  | .space _, .space _, _ => rfl
  | .piTy d c, .piTy d' c', h => by
      simp only [PartialValType, type_eq h.1, type_eq h.2,
        ValTy.SameShape.carrierEl_eq h.1]
  | .space _, .piTy _ _, h => h.elim
  | .piTy _ _, .space _, h => h.elim

/-- Universe-polymorphic elimination for raw semantic values, whose function
carrier packages live one universe above structural argument carriers. -/
def bindAcross {A : Type u} {B : Type v} (r : Except DimError A)
    (f : A → Except DimError B) : Except DimError B :=
  match r with
  | .error e => .error e
  | .ok a => f a

theorem bindAcross_heq {A A' : Type u} {B B' : Type v} (ha : A = A') (hb : B = B')
    (r : Except DimError A) (r' : Except DimError A') (hr : HEq r r')
    (f : A → Except DimError B) (f' : A' → Except DimError B')
    (hf : ∀ a a', HEq a a' → HEq (f a) (f' a')) :
    HEq (bindAcross r f) (bindAcross r' f') := by
  cases ha; cases hb
  have he := eq_of_heq hr
  subst r'
  cases r with
  | error e => rfl
  | ok a => exact hf a a HEq.rfl

/-- Partial bind transports both the failure and success branches. -/
theorem bind_heq {A A' B B' : Type} (ha : A = A') (hb : B = B')
    (r : Except DimError A) (r' : Except DimError A') (hr : HEq r r')
    (f : A → Except DimError B) (f' : A' → Except DimError B')
    (hf : ∀ a a', HEq a a' → HEq (f a) (f' a')) :
    HEq (r.bind f) (r'.bind f') := by
  cases ha; cases hb
  have he := eq_of_heq hr
  subst r'
  cases r with
  | error e => rfl
  | ok a => exact hf a a HEq.rfl

theorem pair_heq {A A' B B' : Type} (ha : A = A') (hb : B = B')
    (a : A) (a' : A') (b : B) (b' : B') (haa : HEq a a') (hbb : HEq b b') :
    HEq (a, b) (a', b') := by
  cases ha; cases hb
  rw [eq_of_heq haa, eq_of_heq hbb]

theorem pair_parts_heq {A A' B B' : Type} (ha : A = A') (hb : B = B')
    (a : A) (a' : A') (b : B) (b' : B') (h : HEq (a, b) (a', b')) :
    HEq a a' ∧ HEq b b' := by
  cases ha; cases hb
  have he := eq_of_heq h
  cases he
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem check_pi (d c : ValTy) (D : PartialValType d)
    (F : d.carrierEl → Except DimError (PartialValType c))
    (f : (ValTy.piTy d c).carrierEl) :
    PartialValType.check (τ := .piTy d c) (D, F) f =
      .ok (fun a => (F a).bind (fun C => (f a).bind
        (fun b => PartialValType.check (τ := c) C b))) := by
  simp only [PartialValType.check]
  apply congrArg Except.ok
  funext a
  cases hF : F a with
  | error e => rfl
  | ok C =>
      simp only [Except.bind]
      cases hf : f a <;> rfl

/-- The recursive checker respects an unchanged partial interpretation under
same-shaped syntax. No dimension equality is inferred from shape alone. -/
theorem check_heq : ∀ {t s : ValTy} (h : ValTy.SameShape t s)
    (T : PartialValType t) (S : PartialValType s) (ht : HEq T S)
    (v : t.carrierEl) (w : s.carrierEl) (hv : HEq v w),
    HEq (T.check v) (S.check w)
  | .space _, .space _, _, T, S, ht, v, w, hv => by
      have ht' := eq_of_heq ht
      have hv' := eq_of_heq hv
      subst S; subst w
      rfl
  | .piTy d c, .piTy d' c', h, (D, F), (D', F'), ht, v, w, hv => by
      have hd := ValTy.SameShape.carrierEl_eq h.1
      have hc := ValTy.SameShape.carrierEl_eq h.2
      have hF : (d.carrierEl → Except DimError (PartialValType c)) =
          (d'.carrierEl → Except DimError (PartialValType c')) := by
        rw [hd, type_eq h.2]
      have parts := pair_parts_heq (type_eq h.1) hF D D' F F' ht
      rw [check_pi, check_pi]
      apply except_ok_heq (ValTy.SameShape.carrierEl_eq h)
      apply Function.hfunext hd
      intro a a' ha
      have hfa := heq_app hd (congrArg (Except DimError) (type_eq h.2)) parts.2 ha
      have hva := heq_app hd (congrArg (Except DimError) hc) hv ha
      change HEq ((F a).bind (fun target => (v a).bind (fun b => PartialValType.check (τ := c) target b)))
        ((F' a').bind (fun target => (w a').bind (fun b => PartialValType.check (τ := c') target b)))
      apply bind_heq (type_eq h.2) hc _ _ hfa
      intro C C' hC
      apply bind_heq hc hc _ _ hva
      intro b b' hb
      exact check_heq h.2 C C' hC b b' hb
  | .space _, .piTy _ _, h, _, _, _, _, _, _ => h.elim
  | .piTy _ _, .space _, h, _, _, _, _, _, _ => h.elim

/-- Bind-form equation avoids dependent generated matchers in transport proofs. -/
theorem denot_pi (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (d c : ValTy) :
    denotValTyPartial orc ρ Γ Δ (.piTy d c) =
      (denotValTyPartial orc ρ Γ Δ d).bind (fun D =>
        .ok (PartialValType.piTy D (fun a =>
          denotValTyPartial orc ρ (d :: Γ) (d.carrierToVal a :: Δ) c))) := by
  rw [denotValTyPartial]
  cases hd : denotValTyPartial orc ρ Γ Δ d <;> rfl

end GLang.PartialValueTransport
