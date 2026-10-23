import GLang.Proofs.Value.Queries.ValueQueryDependencies
import GLang.Proofs.Value.Partial.PartialValuePrimitiveLocality
import GLang.Proofs.Value.Partial.PartialValueRuntimeTransport

/-! Oracle congruence on the dependency graph, using finite certificates derived from typing. -/
namespace GLang.ValueQueryDependencies
open PartialValueDomains PaperValueDomains

inductive Reach (root : Node) : Node → Prop
  | refl : Reach root root
  | child {parent node} : Reach root parent → node ∈ children parent → Reach root node

theorem Reach.trans {a b c : Node} (hab : Reach a b) (hbc : Reach b c) : Reach a c := by
  induction hbc with
  | refl => exact hab
  | child _ hm ih => exact .child ih hm

theorem Reach.finite {root node : Node} (h : Reach root node) (hr : Finite root) :
    Finite node := by
  induction h with
  | refl => exact hr
  | child _ hm ih => exact ih.child hm

theorem Reach.rank_le {root node : Node} (h : Reach root node) (hr : Finite root) :
    rank node ≤ rank root := by
  induction h with
  | refl => exact le_rfl
  | child h hm ih => exact le_trans (Nat.le_of_lt (rank_child_lt (h.finite hr) hm)) ih

def OracleAgreement (left right : PartialFFSOracleSem) (root : Node) : Prop :=
  ∀ Γ p s e, Reach root (.space Γ (.ffs p s e)) →
    ∀ ρ Δ, left ρ Γ Δ p s e = right ρ Γ Δ p s e

theorem OracleAgreement.restrict {left right : PartialFFSOracleSem} {root node : Node}
    (h : OracleAgreement left right root) (hn : Reach root node) :
    OracleAgreement left right node :=
  fun Γ p s e he => h Γ p s e (hn.trans he)

theorem OracleAgreement.child {left right : PartialFFSOracleSem} {root node : Node}
    (h : OracleAgreement left right root) (hn : node ∈ children root) :
    OracleAgreement left right node := h.restrict (.child .refl hn)

theorem OracleAgreement.inferSpace {left right : PartialFFSOracleSem}
    {Γ : List ValTy} {e : ValExpr} (h : OracleAgreement left right (.expr Γ e)) :
    OracleAgreement left right (.space Γ (ValExpr.inferSpaceCtx Γ e)) :=
  h.child (by simp [children])

theorem OracleAgreement.inferType {left right : PartialFFSOracleSem}
    {Γ : List ValTy} {e : ValExpr} (h : OracleAgreement left right (.expr Γ e)) :
    OracleAgreement left right (.type Γ (ValExpr.inferTypeCtx Γ e)) :=
  h.child (by simp [children])

theorem OracleAgreement.space {left right : PartialFFSOracleSem}
    {Γ : List ValTy} {s : ValSpace} (h : OracleAgreement left right (.space Γ s))
    (ρ : ValEnvSem) (Δ : List ValValSem) :
    PartialSpaceAgreement (left ρ Γ Δ) (right ρ Γ Δ) s := by
  cases s with
  | empty | real => trivial
  | dsum a b | tprod a b =>
    exact ⟨(h.child (node := .space Γ a) (by simp [children])).space ρ Δ,
      (h.child (node := .space Γ b) (by simp [children])).space ρ Δ⟩
  | ffs p s e => exact h Γ p s e .refl ρ Δ
termination_by sizeOf s

theorem OracleAgreement.type {left right : PartialFFSOracleSem}
    (ρ : ValEnvSem) : ∀ (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy),
    OracleAgreement left right (.type Γ t) →
    denotValTyPartial left ρ Γ Δ t = denotValTyPartial right ρ Γ Δ t
  | Γ, Δ, .space s, h => by
    simp only [denotValTyPartial,
      (PartialSpaceAgreement.observations _ _ s
        ((h.child (node := .space Γ s) (by simp [children])).space ρ Δ)).2]
  | Γ, Δ, .piTy d c, h => by
    have hd := h.child (node := .type Γ d) (by simp [children])
    have hc := h.child (node := .type (d :: Γ) c) (by simp [children])
    rw [denotValTyPartial, denotValTyPartial, hd.type ρ Γ Δ d]
    cases ht : denotValTyPartial right ρ Γ Δ d with
    | error e => rfl
    | ok domain =>
      apply congrArg Except.ok
      apply congrArg (PartialValType.piTy domain)
      funext a
      exact hc.type ρ (d :: Γ) (d.carrierToVal a :: Δ) c

theorem OracleAgreement.reshape {left right : PartialFFSOracleSem}
    (ρ : ValEnvSem) : ∀ (v : ValValSem) (t s : ValTy)
      (Γt : List ValTy) (Δt : List ValValSem) (Γs : List ValTy) (Δs : List ValValSem),
    OracleAgreement left right (.type Γt t) →
    OracleAgreement left right (.type Γs s) →
    PartialValueEval.reshapeBetween left ρ Γt Δt Γs Δs v t s =
      PartialValueEval.reshapeBetween right ρ Γt Δt Γs Δs v t s
  | .array a, .space t, .space s, Γt, Δt, Γs, Δs, ht, hs => by
    have hdt := PartialSpaceAgreement.observations _ _ t
      ((ht.child (node := .space Γt t) (by simp [children])).space ρ Δt)
    have hds := PartialSpaceAgreement.observations _ _ s
      ((hs.child (node := .space Γs s) (by simp [children])).space ρ Δs)
    simp only [PartialValueEval.reshapeBetween, PartialValueEval.reshapeArray, hdt.2, hds.2]
  | .fn _ _, .space _, _, _, _, _, _, _, _ => by simp only [PartialValueEval.reshapeBetween]
  | .array _, .space _, .piTy _ _, _, _, _, _, _, _ => by simp only [PartialValueEval.reshapeBetween]
  | v, .piTy _ _, .space _, _, _, _, _, _, _ => by simp only [PartialValueEval.reshapeBetween]
  | v, .piTy dt ct, .piTy ds cs, Γt, Δt, Γs, Δs, ht, hs => by
    have hdt := ht.child (node := .type Γt dt) (by simp [children])
    have hds := hs.child (node := .type Γs ds) (by simp [children])
    have hct := ht.child (node := .type (dt :: Γt) ct) (by simp [children])
    have hcs := hs.child (node := .type (ds :: Γs) cs) (by simp [children])
    rw [PartialValueEval.reshapeBetween, PartialValueEval.reshapeBetween,
      hdt.type ρ Γt Δt dt, hds.type ρ Γs Δs ds]
    cases hdtv : denotValTyPartial right ρ Γt Δt dt with
    | error e => rfl
    | ok target =>
      cases hdsv : denotValTyPartial right ρ Γs Δs ds with
      | error e => rfl
      | ok source =>
        apply congrArg Except.ok
        apply congrArg (ValValSem.fn dt.carrierEl)
        funext a
        cases hc : target.check a with
        | error e => rfl
        | ok checked =>
          simp only []
          rw [OracleAgreement.reshape ρ (dt.carrierToVal checked) ds dt Γs Δs Γt Δt hds hdt]
          cases ha : PartialValueEval.reshapeBetween right ρ Γs Δs Γt Δt
              (dt.carrierToVal checked) ds dt with
          | error e => rfl
          | ok argS =>
            simp only []
            cases hb : ds.carrierFromVal argS with
            | error e => rfl
            | ok arg =>
              simp only []
              cases hr : v.applyTyped arg with
              | error e => rfl
              | ok result =>
                exact OracleAgreement.reshape ρ result ct cs
                  (dt :: Γt) (dt.carrierToVal checked :: Δt)
                  (ds :: Γs) (argS :: Δs) hct hcs
termination_by _ t s _ _ _ _ _ _ => ValTy.kindSize t + ValTy.kindSize s
decreasing_by all_goals (simp only [ValTy.kindSize_piTy]; omega)

private theorem primitive_operand_child {Γ : List ValTy} {e a : ValExpr}
    (ha : a ∈ primitiveOperands e) : .expr Γ a ∈ children (.expr Γ e) := by
  cases e <;> simp_all [primitiveOperands, children, exprChildren, List.mem_map]

private theorem primitive_operand_smaller {e a : ValExpr}
    (ha : a ∈ primitiveOperands e) : a.size < e.size := by
  cases e <;> simp only [primitiveOperands, List.mem_cons, List.not_mem_nil, or_false] at ha
  all_goals first
    | contradiction
    | (have h := ValExpr.size_le_sizeList ha; simp only [ValExpr.size]; omega)
    | (rcases ha with rfl | rfl | rfl <;> simp only [ValExpr.size] <;> omega)

theorem OracleAgreement.operand {left right : PartialFFSOracleSem} {Γ : List ValTy}
    {e a : ValExpr} (h : OracleAgreement left right (.expr Γ e))
    (ha : a ∈ primitiveOperands e) : OracleAgreement left right (.expr Γ a) :=
  h.child (primitive_operand_child ha)

private theorem OracleAgreement.primitiveInput {left right : PartialFFSOracleSem}
    {Γ : List ValTy} {e : ValExpr} (h : OracleAgreement left right (.expr Γ e))
    {s : ValSpace} (hs : s ∈ primitiveInputSpaces Γ e) :
    OracleAgreement left right (.space Γ s) := by
  cases e <;> simp only [primitiveInputSpaces, List.mem_cons, List.not_mem_nil, or_false] at hs
  all_goals first
    | contradiction
    | (rcases hs with rfl | rfl | rfl)
  all_goals solve
    | (apply h.child; simp [children, exprChildren])
    | (apply OracleAgreement.inferSpace; apply h.operand; simp [primitiveOperands])

theorem OracleAgreement.primitiveSpaces {left right : PartialFFSOracleSem}
    {Γ : List ValTy} {e : ValExpr} (h : OracleAgreement left right (.expr Γ e))
    {s : ValSpace} (hs : s ∈ partialPrimitiveQuerySpaces Γ e) :
    OracleAgreement left right (.space Γ s) := by
  simp only [partialPrimitiveQuerySpaces, primitiveQuerySpaces, List.mem_append,
    List.mem_cons] at hs
  rcases hs with (rfl | hs) | hs
  · exact h.inferSpace
  · exact h.primitiveInput hs
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hs
    exact (h.operand ha).inferSpace

/-- The complete evaluator depends only on reachable oracle observations.
This congruence statement is valid even for raw syntax with cycles; it does
not assert that those observations are strictly smaller. -/
theorem OracleAgreement.eval {left right : PartialFFSOracleSem}
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem) (e : ValExpr)
    (h : OracleAgreement left right (.expr Γ e)) :
    denotValB_partial left ρ Γ Δ e = denotValB_partial right ρ Γ Δ e := by
  by_cases hp : ArrayPrimitive e
  · apply partial_arrayPrimitive_eval_congr_oracles left right e
      ⟨ρ, Γ, Δ⟩ ⟨ρ, Γ, Δ⟩ hp rfl
    · intro s hs
      exact (h.primitiveSpaces hs).space ρ Δ
    · intro a ha
      exact (h.operand ha).eval ρ Γ Δ a
  · cases he : e with
    | bvar i => simp only [denotValB_partial]
    | var x t => simp only [denotValB_partial]
    | vlam d c body =>
      rw [he] at h
      have hd := h.child (node := .type Γ d) (by simp [children, exprChildren])
      have hb := h.child (node := .expr (d :: Γ) body) (by simp [children, exprChildren])
      rw [denotValB_partial, denotValB_partial, hd.type ρ Γ Δ d]
      cases hdv : denotValTyPartial right ρ Γ Δ d with
      | error err => rfl
      | ok domain =>
        apply congrArg Except.ok
        apply congrArg (ValValSem.fn d.carrierEl)
        funext a
        exact hb.eval ρ (d :: Γ) (d.carrierToVal a :: Δ) body
    | appV f a =>
      rw [he] at h
      have hf := h.child (node := .expr Γ f) (by simp [children, exprChildren])
      have ha := h.child (node := .expr Γ a) (by simp [children, exprChildren])
      rw [denotValB_partial, denotValB_partial]
      cases hft : ValExpr.inferTypeCtx Γ f with
      | space s => rfl
      | piTy d c =>
        rw [hf.eval ρ Γ Δ f, ha.eval ρ Γ Δ a]
        have hfi := hf.inferType
        rw [hft] at hfi
        have hd := hfi.child (node := .type Γ d) (by simp [children])
        exact PartialValueEval.applyDomainChecked_congr left right ρ ρ Γ Γ Δ Δ d d
          (ValSoundOfDenot.ValTy.SameShape.refl d) (heq_of_eq (hd.type ρ Γ Δ d)) _ _
    | reshap a t s =>
      rw [he] at h
      have ha := h.child (node := .expr Γ a) (by simp [children, exprChildren])
      have ht := h.child (node := .type Γ t) (by simp [children, exprChildren])
      have hs := h.child (node := .type Γ s) (by simp [children, exprChildren])
      rw [denotValB_partial, denotValB_partial, ha.eval ρ Γ Δ a]
      cases hv : denotValB_partial right ρ Γ Δ a with
      | error err => rfl
      | ok v =>
        cases s with
        | space s => exact OracleAgreement.reshape ρ v t (.space s) Γ Δ Γ Δ ht hs
        | piTy d c =>
          cases hi : ValExpr.inferTypeCtx Γ a with
          | space sa => simp only [PartialValueEval.reshapeInferred, hi]
          | piTy da ca =>
            have hai := ha.inferType
            rw [hi] at hai
            exact OracleAgreement.reshape ρ v t (.piTy da ca) Γ Δ Γ Δ ht hai
    | _ => exact False.elim (hp (by simp only [he, ArrayPrimitive]))
termination_by e.size
decreasing_by
  all_goals first
    | exact primitive_operand_smaller ha
    | (simp_all only [ValExpr.size]; omega)

end GLang.ValueQueryDependencies
