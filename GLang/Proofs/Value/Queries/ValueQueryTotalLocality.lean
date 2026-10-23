import GLang.Proofs.Adequacy.Foundations.FvIrrel
import GLang.Proofs.Value.Queries.ValueQueryLocality
import GLang.Proofs.Value.Queries.ValuePrimitiveOracleLocality

namespace GLang.TotalQueryLocality
open ValueQueryDependencies PaperValueDomains

def OracleAgreement (left right : FFSOracleSem) (root : Node) : Prop :=
  ∀ Γ p s e, Reach root (.space Γ (.ffs p s e)) →
    ∀ ρ Δ, left ρ Γ Δ p s e = right ρ Γ Δ p s e

theorem OracleAgreement.restrict {left right : FFSOracleSem} {root node : Node}
    (h : OracleAgreement left right root) (hn : Reach root node) :
    OracleAgreement left right node :=
  fun Γ p s e he => h Γ p s e (hn.trans he)

theorem OracleAgreement.child {left right : FFSOracleSem} {root node : Node}
    (h : OracleAgreement left right root) (hn : node ∈ children root) :
    OracleAgreement left right node := h.restrict (.child .refl hn)

theorem OracleAgreement.inferSpace {left right : FFSOracleSem}
    {Γ : List ValTy} {e : ValExpr} (h : OracleAgreement left right (.expr Γ e)) :
    OracleAgreement left right (.space Γ (ValExpr.inferSpaceCtx Γ e)) :=
  h.child (by simp [children])

theorem OracleAgreement.inferType {left right : FFSOracleSem}
    {Γ : List ValTy} {e : ValExpr} (h : OracleAgreement left right (.expr Γ e)) :
    OracleAgreement left right (.type Γ (ValExpr.inferTypeCtx Γ e)) :=
  h.child (by simp [children])

theorem OracleAgreement.space {left right : FFSOracleSem}
    {Γ : List ValTy} {s : ValSpace} (h : OracleAgreement left right (.space Γ s))
    (ρ : ValEnvSem) (Δ : List ValValSem) :
    PaperValueDomains.SpaceOracleAgreement (left ρ Γ Δ) (right ρ Γ Δ) s := by
  cases s with
  | empty | real => trivial
  | dsum a b | tprod a b =>
    exact ⟨(h.child (node := .space Γ a) (by simp [children])).space ρ Δ,
      (h.child (node := .space Γ b) (by simp [children])).space ρ Δ⟩
  | ffs p s e => exact h Γ p s e .refl ρ Δ
termination_by sizeOf s

theorem OracleAgreement.type {left right : FFSOracleSem}
    (ρ : ValEnvSem) : ∀ (Γ : List ValTy) (Δ : List ValValSem) (t : ValTy),
    OracleAgreement left right (.type Γ t) →
    denotValTyS left ρ Γ Δ t = denotValTyS right ρ Γ Δ t
  | Γ, Δ, .space s, h => by
    have hs := (h.child (node := .space Γ s) (by simp [children])).space ρ Δ
    rw [denotValTyS_space,denotValTyS_space,(leafAgreement_shapes _ _ s hs).2]
  | Γ, Δ, .piTy d c, h => by
    have hd := h.child (node := .type Γ d) (by simp [children])
    have hc := h.child (node := .type (d :: Γ) c) (by simp [children])
    rw [denotValTyS,denotValTyS,hd.type ρ Γ Δ d]
    apply congrArg (ValTypeSem.piTy (denotValTyS right ρ Γ Δ d).El)
    funext a
    exact hc.type ρ (d :: Γ) (ValValSem.fromEl (denotValTyS right ρ Γ Δ d) a :: Δ) c

theorem OracleAgreement.reshape {left right : FFSOracleSem}
    (ρ : ValEnvSem) : ∀ (v : ValValSem) (t s : ValTy)
      (Γt : List ValTy) (Δt : List ValValSem) (Γs : List ValTy) (Δs : List ValValSem),
    OracleAgreement left right (.type Γt t) →
    OracleAgreement left right (.type Γs s) →
    reshapDenotSemBetweenS left ρ Γt Δt Γs Δs v t s =
      reshapDenotSemBetweenS right ρ Γt Δt Γs Δs v t s
  | .array a, .space t, .space s, Γt, Δt, Γs, Δs, ht, hs => by
    have hdt := leafAgreement_shapes _ _ t
      ((ht.child (node := .space Γt t) (by simp [children])).space ρ Δt)
    have hds := leafAgreement_shapes _ _ s
      ((hs.child (node := .space Γs s) (by simp [children])).space ρ Δs)
    simp only [reshapDenotSemBetweenS,reshapArrayBetweenS,hdt.2,hds.2]
  | .fn _ _, .space _, _, _, _, _, _, _, _ => by simp only [reshapDenotSemBetweenS]
  | .array _, .space _, .piTy _ _, _, _, _, _, _, _ => by simp only [reshapDenotSemBetweenS,reshapArrayBetweenS]
  | v, .piTy _ _, .space _, _, _, _, _, _, _ => by simp only [reshapDenotSemBetweenS]
  | v, .piTy dt ct, .piTy ds cs, Γt, Δt, Γs, Δs, ht, hs => by
    have hdt := ht.child (node := .type Γt dt) (by simp [children])
    have hds := hs.child (node := .type Γs ds) (by simp [children])
    have hct := ht.child (node := .type (dt :: Γt) ct) (by simp [children])
    have hcs := hs.child (node := .type (ds :: Γs) cs) (by simp [children])
    rw [reshapDenotSemBetweenS,reshapDenotSemBetweenS,
      hdt.type ρ Γt Δt dt,hds.type ρ Γs Δs ds]
    apply congrArg Except.ok
    apply congrArg _
    funext a
    dsimp only
    generalize he : ValValSem.fromElChecked (denotValTyS right ρ Γt Δt dt) a = checked
    cases checked with
    | error err => simp [he]
    | ok argT =>
      simp only [he]
      rw [OracleAgreement.reshape ρ argT ds dt Γs Δs Γt Δt hds hdt]
      generalize hr : reshapDenotSemBetweenS right ρ Γs Δs Γt Δt argT ds dt = converted
      cases converted with
      | error err => simp
      | ok argS =>
        generalize hd : ValValSem.toEl (denotValTyS right ρ Γs Δs ds) argS = decoded
        cases decoded with
        | error err => simp [hd]
        | ok source =>
          generalize hv : v.applyTyped source = applied
          cases applied with
          | error err => simp [hd,hv]
          | ok result =>
            simp only [hd,hv]
            exact OracleAgreement.reshape ρ result ct cs (dt::Γt) (argT::Δt)
              (ds::Γs) (argS::Δs) hct hcs
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

theorem OracleAgreement.operand {left right : FFSOracleSem} {Γ : List ValTy}
    {e a : ValExpr} (h : OracleAgreement left right (.expr Γ e))
    (ha : a ∈ primitiveOperands e) : OracleAgreement left right (.expr Γ a) :=
  h.child (primitive_operand_child ha)

private theorem OracleAgreement.primitiveInput {left right : FFSOracleSem}
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

theorem OracleAgreement.primitiveSpaces {left right : FFSOracleSem}
    {Γ : List ValTy} {e : ValExpr} (h : OracleAgreement left right (.expr Γ e))
    {s : ValSpace} (hs : s ∈ primitiveQuerySpaces Γ e) :
    OracleAgreement left right (.space Γ s) := by
  simp only [primitiveQuerySpaces,
    List.mem_cons] at hs
  rcases hs with rfl | hs
  · exact h.inferSpace
  · exact h.primitiveInput hs

theorem OracleAgreement.eval {left right : FFSOracleSem}
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem) (e : ValExpr)
    (h : OracleAgreement left right (.expr Γ e)) :
    denotValB_semS left ρ Γ Δ e = denotValB_semS right ρ Γ Δ e := by
  by_cases hp : ArrayPrimitive e
  · apply arrayPrimitive_eval_congr_oracles left right e ⟨ρ,Γ,Δ⟩ ⟨ρ,Γ,Δ⟩ hp rfl
    · intro s hs
      exact (h.primitiveSpaces hs).space ρ Δ
    · intro a ha
      exact (h.operand ha).eval ρ Γ Δ a
  · cases he : e with
    | bvar i => simp only [denotValB_semS]
    | var x t => simp only [denotValB_semS]
    | vlam d c body =>
      rw [he] at h
      have hd := h.child (node := .type Γ d) (by simp [children,exprChildren])
      have hb := h.child (node := .expr (d::Γ) body) (by simp [children,exprChildren])
      rw [denotValB_semS,denotValB_semS,hd.type ρ Γ Δ d]
      apply congrArg Except.ok
      apply congrArg (ValValSem.fn (denotValTyS right ρ Γ Δ d).El)
      funext a
      exact hb.eval ρ (d::Γ) (ValValSem.fromEl (denotValTyS right ρ Γ Δ d) a :: Δ) body
    | appV f a =>
      rw [he] at h
      have hf := h.child (node := .expr Γ f) (by simp [children,exprChildren])
      have ha := h.child (node := .expr Γ a) (by simp [children,exprChildren])
      have hfi := hf.inferType
      have hd : OracleAgreement left right (.type Γ (ValExpr.inferTypeCtx Γ f).domain) := by
        cases ht : ValExpr.inferTypeCtx Γ f with
        | space s => simpa only [ht,ValTy.domain] using hfi
        | piTy d c =>
          rw [ht] at hfi
          exact hfi.child (by simp [ht,ValTy.domain,children])
      rw [denotValB_semS,denotValB_semS,hf.eval ρ Γ Δ f,ha.eval ρ Γ Δ a]
      cases hfun : denotValB_semS right ρ Γ Δ f with
      | error err => rfl
      | ok value =>
        cases value with
        | array ar => rfl
        | fn A funValue =>
          cases harg : denotValB_semS right ρ Γ Δ a with
          | error err => rfl
          | ok arg =>
            exact appV_match_congr (.fn A funValue) arg
              (hd.type ρ Γ Δ (ValExpr.inferTypeCtx Γ f).domain)
    | reshap a t s =>
      rw [he] at h
      have ha := h.child (node := .expr Γ a) (by simp [children,exprChildren])
      have ht := h.child (node := .type Γ t) (by simp [children,exprChildren])
      have hs := h.child (node := .type Γ s) (by simp [children,exprChildren])
      rw [denotValB_semS,denotValB_semS,ha.eval ρ Γ Δ a]
      cases hv : denotValB_semS right ρ Γ Δ a with
      | error err => rfl
      | ok v =>
        dsimp only
        rw [reshapDenotSemS_eq_between,reshapDenotSemS_eq_between]
        exact OracleAgreement.reshape ρ v t s Γ Δ Γ Δ ht hs
    | _ => exact False.elim (hp (by simp only [he,ArrayPrimitive]))
termination_by e.size
decreasing_by
  all_goals first
    | exact primitive_operand_smaller ha
    | (simp_all only [ValExpr.size]; omega)

end GLang.TotalQueryLocality
