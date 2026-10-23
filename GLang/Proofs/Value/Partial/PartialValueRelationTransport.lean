import GLang.Proofs.Value.Partial.PartialValueRuntimeRelation
import GLang.Proofs.Value.Partial.PartialValueTransport

/-! Changing locally nameless type presentation preserves the partial logical
relation when the actual partial type interpretations are transported exactly.
No type coherence or evaluator-invariance premise is hidden in this bridge. -/
namespace GLang.PartialValueDomains
open PaperValueDomains ValSoundOfDenot PartialValueTransport

private theorem except_iff {A B : Type} (hAB : A = B)
    (T : Except DimError A) (U : Except DimError B) (hTU : HEq T U)
    (P : Except DimError A → Prop) (Q : Except DimError B → Prop)
    (he : ∀ e, P (.error e) ↔ Q (.error e))
    (ho : ∀ a b, HEq a b → (P (.ok a) ↔ Q (.ok b))) : P T ↔ Q U := by
  cases hAB
  obtain rfl := eq_of_heq hTU
  cases T with
  | error e => exact he e
  | ok a => exact ho a a HEq.rfl

private theorem forall_iff {A B : Type} (hAB : A = B)
    (P : A → Prop) (Q : B → Prop) (h : ∀ a b, HEq a b → (P a ↔ Q b)) :
    (∀ a, P a) ↔ ∀ b, Q b := by
  cases hAB
  exact forall_congr' (fun a => h a a HEq.rfl)

private theorem result_iff {A B : Type} (hAB : A = B)
    (R : A → A → Prop) (S : B → B → Prop)
    (h : ∀ a b a' b', HEq a a' → HEq b b' → (R a b ↔ S a' b'))
    (r s : Except DimError A) (r' s' : Except DimError B)
    (hr : HEq r r') (hs : HEq s s') : PartialRel R r s ↔ PartialRel S r' s' := by
  cases hAB
  obtain rfl := eq_of_heq hr
  obtain rfl := eq_of_heq hs
  cases r <;> cases s <;> simp only [PartialRel]
  exact h _ _ _ _ HEq.rfl HEq.rfl

/-- Transport the complete higher-order relation across equal partial type
interpretations and unchanged structural-carrier values. -/
theorem partialRelated_heq : ∀ {t s : ValTy} (h : ValTy.SameShape t s)
    (T U : Except DimError (PartialValType t))
    (T' U' : Except DimError (PartialValType s)), HEq T T' → HEq U U' →
    ∀ a b a' b', HEq a a' → HEq b b' →
      (PartialRelated t T U a b ↔ PartialRelated s T' U' a' b')
  | .space _, .space _, h, T, U, T', U', ht, hu, a, b, a', b', ha, hb => by
      obtain rfl := eq_of_heq ht
      obtain rfl := eq_of_heq hu
      obtain rfl := eq_of_heq ha
      obtain rfl := eq_of_heq hb
      cases T <;> cases U <;> rfl
  | .piTy d c, .piTy d' c', h, T, U, T', U', ht, hu, a, b, a', b', ha, hb => by
      apply except_iff (type_eq h) T T' ht
        (fun T => PartialRelated (.piTy d c) T U a b)
        (fun T' => PartialRelated (.piTy d' c') T' U' a' b')
      · intro e
        cases U <;> cases U' <;> rfl
      · intro t t' htt
        apply except_iff (type_eq h) U U' hu
          (fun U => PartialRelated (.piTy d c) (.ok t) U a b)
          (fun U' => PartialRelated (.piTy d' c') (.ok t') U' a' b')
        · intro e; rfl
        · intro u u' huu
          rcases t with ⟨D,F⟩
          rcases t' with ⟨D',F'⟩
          rcases u with ⟨E,G⟩
          rcases u' with ⟨E',G'⟩
          have hd := ValTy.SameShape.carrierEl_eq h.1
          have hc := ValTy.SameShape.carrierEl_eq h.2
          have hF : (d.carrierEl → Except DimError (PartialValType c)) =
              (d'.carrierEl → Except DimError (PartialValType c')) := by rw [hd,type_eq h.2]
          have hp := pair_parts_heq (type_eq h.1) hF D D' F F' htt
          have hq := pair_parts_heq (type_eq h.1) hF E E' G G' huu
          apply forall_iff hd
          intro x x' hx
          apply forall_iff hd
          intro y y' hy
          apply imp_congr
          · exact partialRelated_heq h.1 _ _ _ _
              (except_ok_heq (type_eq h.1) hp.1)
              (except_ok_heq (type_eq h.1) hq.1) x y x' y' hx hy
          · exact result_iff hc _ _
              (fun r v r' v' hr hv => partialRelated_heq h.2 _ _ _ _
                (heq_app hd (congrArg (Except DimError) (type_eq h.2)) hp.2 hx)
                (heq_app hd (congrArg (Except DimError) (type_eq h.2)) hq.2 hy)
                r v r' v' hr hv) _ _ _ _
              (heq_app hd (congrArg (Except DimError) hc) ha hx)
              (heq_app hd (congrArg (Except DimError) hc) hb hy)
  | .space _, .piTy _ _, h, _, _, _, _, _, _, _, _, _, _, _, _ => h.elim
  | .piTy _ _, .space _, h, _, _, _, _, _, _, _, _, _, _, _, _ => h.elim

/-- Coherence is preserved under the same exact change of presentation. -/
theorem partialCoherent_heq : ∀ {t s : ValTy} (h : ValTy.SameShape t s)
    (T U : Except DimError (PartialValType t))
    (T' U' : Except DimError (PartialValType s)), HEq T T' → HEq U U' →
      (PartialCoherent t T U ↔ PartialCoherent s T' U')
  | .space _, .space _, h, T, U, T', U', ht, hu => by
      obtain rfl := eq_of_heq ht
      obtain rfl := eq_of_heq hu
      cases T <;> cases U <;> rfl
  | .piTy d c, .piTy d' c', h, T, U, T', U', ht, hu => by
      apply except_iff (type_eq h) T T' ht
        (fun T => PartialCoherent (.piTy d c) T U)
        (fun T' => PartialCoherent (.piTy d' c') T' U')
      · intro e
        apply except_iff (type_eq h) U U' hu
          (fun U => PartialCoherent (.piTy d c) (.error e) U)
          (fun U' => PartialCoherent (.piTy d' c') (.error e) U')
        · intro e'; rfl
        · intro a b hab; rfl
      · intro t t' htt
        apply except_iff (type_eq h) U U' hu
          (fun U => PartialCoherent (.piTy d c) (.ok t) U)
          (fun U' => PartialCoherent (.piTy d' c') (.ok t') U')
        · intro e; rfl
        · intro u u' huu
          rcases t with ⟨D,F⟩
          rcases t' with ⟨D',F'⟩
          rcases u with ⟨E,G⟩
          rcases u' with ⟨E',G'⟩
          have hd := ValTy.SameShape.carrierEl_eq h.1
          have hF : (d.carrierEl → Except DimError (PartialValType c)) =
              (d'.carrierEl → Except DimError (PartialValType c')) := by rw [hd,type_eq h.2]
          have hp := pair_parts_heq (type_eq h.1) hF D D' F F' htt
          have hq := pair_parts_heq (type_eq h.1) hF E E' G G' huu
          apply and_congr
          · exact partialCoherent_heq h.1 _ _ _ _
              (except_ok_heq (type_eq h.1) hp.1) (except_ok_heq (type_eq h.1) hq.1)
          · apply forall_iff hd
            intro x x' hx
            apply forall_iff hd
            intro y y' hy
            apply imp_congr
            · exact partialRelated_heq h.1 _ _ _ _
                (except_ok_heq (type_eq h.1) hp.1)
                (except_ok_heq (type_eq h.1) hq.1) x y x' y' hx hy
            · exact partialCoherent_heq h.2 _ _ _ _
                (heq_app hd (congrArg (Except DimError) (type_eq h.2)) hp.2 hx)
                (heq_app hd (congrArg (Except DimError) (type_eq h.2)) hq.2 hy)
  | .space _, .piTy _ _, h, _, _, _, _, _, _ => h.elim
  | .piTy _ _, .space _, h, _, _, _, _, _, _ => h.elim

private theorem raw_result_iff (R S : ValValSem → ValValSem → Prop)
    (h : ∀ a b, R a b ↔ S a b) (r s : Except DimError ValValSem) :
    PartialRel R r s ↔ PartialRel S r s := by
  cases r <;> cases s <;> simp only [PartialRel]
  exact h _ _

/-- Raw callback results admit the same exact change of type presentation. -/
theorem partialRuntimeRelated_heq : ∀ {t s : ValTy} (h : ValTy.SameShape t s)
    (T U : Except DimError (PartialValType t))
    (T' U' : Except DimError (PartialValType s)), HEq T T' → HEq U U' →
    ∀ v w, PartialRuntimeRelated t T U v w ↔ PartialRuntimeRelated s T' U' v w
  | .space _, .space _, h, T, U, T', U', ht, hu, v, w => by
      cases v <;> cases w <;> try rfl
      exact partialRelated_heq h T U T' U' ht hu _ _ _ _ HEq.rfl HEq.rfl
  | .piTy d c, .piTy d' c', h, T, U, T', U', ht, hu, v, w => by
      apply except_iff (type_eq h) T T' ht
        (fun T => PartialRuntimeRelated (.piTy d c) T U v w)
        (fun T' => PartialRuntimeRelated (.piTy d' c') T' U' v w)
      · intro e
        cases U <;> cases U' <;> cases v <;> cases w <;> rfl
      · intro t t' htt
        apply except_iff (type_eq h) U U' hu
          (fun U => PartialRuntimeRelated (.piTy d c) (.ok t) U v w)
          (fun U' => PartialRuntimeRelated (.piTy d' c') (.ok t') U' v w)
        · intro e; cases v <;> cases w <;> rfl
        · intro u u' huu
          rcases t with ⟨D,F⟩
          rcases t' with ⟨D',F'⟩
          rcases u with ⟨E,G⟩
          rcases u' with ⟨E',G'⟩
          cases v <;> cases w <;> try rfl
          rename_i A f B g
          have hd := ValTy.SameShape.carrierEl_eq h.1
          have hF : (d.carrierEl → Except DimError (PartialValType c)) =
              (d'.carrierEl → Except DimError (PartialValType c')) := by rw [hd,type_eq h.2]
          have hp := pair_parts_heq (type_eq h.1) hF D D' F F' htt
          have hq := pair_parts_heq (type_eq h.1) hF E E' G G' huu
          constructor
          · rintro ⟨hA,hB,hfg⟩
            refine ⟨hA.trans hd,hB.trans hd,?_⟩
            intro a b hab
            have ha : HEq (hA ▸ a) ((hA.trans hd) ▸ a) :=
              (cast_heq hA a).trans (cast_heq (hA.trans hd) a).symm
            have hb : HEq (hB ▸ b) ((hB.trans hd) ▸ b) :=
              (cast_heq hB b).trans (cast_heq (hB.trans hd) b).symm
            have hab0 := (partialRelated_heq h.1 _ _ _ _
              (except_ok_heq (type_eq h.1) hp.1) (except_ok_heq (type_eq h.1) hq.1)
              _ _ _ _ ha hb).2 hab
            exact (raw_result_iff _ _ (fun x y => partialRuntimeRelated_heq h.2 _ _ _ _
              (heq_app hd (congrArg (Except DimError) (type_eq h.2)) hp.2 ha)
              (heq_app hd (congrArg (Except DimError) (type_eq h.2)) hq.2 hb) x y)
              _ _).1 (hfg a b hab0)
          · rintro ⟨hA,hB,hfg⟩
            refine ⟨hA.trans hd.symm,hB.trans hd.symm,?_⟩
            intro a b hab
            have ha : HEq ((hA.trans hd.symm) ▸ a) (hA ▸ a) :=
              (cast_heq (hA.trans hd.symm) a).trans (cast_heq hA a).symm
            have hb : HEq ((hB.trans hd.symm) ▸ b) (hB ▸ b) :=
              (cast_heq (hB.trans hd.symm) b).trans (cast_heq hB b).symm
            have hab0 := (partialRelated_heq h.1 _ _ _ _
              (except_ok_heq (type_eq h.1) hp.1) (except_ok_heq (type_eq h.1) hq.1)
              _ _ _ _ ha hb).1 hab
            exact (raw_result_iff _ _ (fun x y => partialRuntimeRelated_heq h.2 _ _ _ _
              (heq_app hd (congrArg (Except DimError) (type_eq h.2)) hp.2 ha)
              (heq_app hd (congrArg (Except DimError) (type_eq h.2)) hq.2 hb) x y)
              _ _).2 (hfg a b hab0)
  | .space _, .piTy _ _, h, _, _, _, _, _, _, _, _ => h.elim
  | .piTy _ _, .space _, h, _, _, _, _, _, _, _, _ => h.elim

end GLang.PartialValueDomains
