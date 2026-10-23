import GLang.Proofs.Value.Runtime.RuntimeValueDeclaredAnnotations
import GLang.Proofs.Value.Runtime.RuntimeValueMatchedClosure
import GLang.Proofs.Value.Binding.ValueBetaAnnotations

set_option maxHeartbeats 3000000
namespace GLang.RuntimeValue
open ValueDependency

/-- The result type uses only variable annotations already present in the
expression. In the application case this is proved through substitution. -/
theorem ValHasType.resultAnnotations {ε : ValCtx} (hc : ValCtxValid ε) :
    ∀ {e : ValExpr} {t : ValTy}, ValHasType ε e t →
      typeAnnotations t ⊆ exprAnnotations e
  | _, _, .var hl => by
    intro q hq
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .zero hs => by
    intro q hq
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .rlit r => by
    intro q hq
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .scale h0 h1 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h1 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .vadd h0 h1 hs => by
    intro q hq
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .dsumE h0 h1 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    have ih1 := @ValHasType.resultAnnotations ε hc _ _ h1 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .tprodE h0 h1 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    have ih1 := @ValHasType.resultAnnotations ε hc _ _ h1 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .delta hs => by
    intro q hq
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .idelta hs => by
    intro q hq
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .ttv_space hs h0 h1 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .ttv_real hs h0 h1 hn => by
    intro q hq
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .mtm hs ht h0 h1 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    have ih1 := @ValHasType.resultAnnotations ε hc _ _ h1 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .vkrn h0 h1 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    have ih1 := @ValHasType.resultAnnotations ε hc _ _ h1 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .vblk h0 h1 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    have ih1 := @ValHasType.resultAnnotations ε hc _ _ h1 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .reshap he hs ht => by
    intro q hq
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .vtrans h0 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .pinv_tensor h0 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .pinv_raw h0 hn => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .inv_tensor h0 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .inv_raw h0 hn => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .rrefRep h0 h1 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h1 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .svds h0 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .gsvdS h0 h1 h2 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .gsvdU h0 h1 h2 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .gsvdUI h0 h1 h2 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .gsvdV h0 h1 h2 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .gsvdVI h0 h1 h2 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, .gpinv h0 h1 h2 => by
    intro q hq
    have ih0 := @ValHasType.resultAnnotations ε hc _ _ h0 q
    simp only [typeAnnotations, spaceAnnotations, exprAnnotations,
      List.mem_append, List.mem_cons, List.not_mem_nil] at *
    all_goals tauto
  | _, _, @ValHasType.vlam ε d c kd kc body L ht hb => by
    intro q hq
    exact List.mem_append_left _ hq
  | _, _, @ValHasType.vsum ε s0 s es hs hb ht hdet => by
    cases es with
    | nil =>
      have hz := hdet rfl
      subst s
      simp [typeAnnotations, spaceAnnotations]
    | cons e es =>
      intro q hq
      have he := ValHasType.resultAnnotations hc (hb e (by simp)) hq
      simp only [exprAnnotations, listAnnotations, List.mem_append]
      exact Or.inr (Or.inl he)
  | _, _, @ValHasType.appV ε f a d c out k hf ha heq ht => by
    subst out
    have hfAnn := ValHasType.resultAnnotations hc hf
    have hpi := (hf.regular hc).2.declared
    have hb := typeDeclared_beta_annotations ε (validContext_lc hc) a
      (validExpr_lc hc ha).1 c 0 hpi.2
    intro q hq
    rcases List.mem_append.mp (hb hq) with hcod | harg
    · exact List.mem_append_left _ (hfAnn (List.mem_append_right _ hcod))
    · exact List.mem_append_right _ harg
end GLang.RuntimeValue
