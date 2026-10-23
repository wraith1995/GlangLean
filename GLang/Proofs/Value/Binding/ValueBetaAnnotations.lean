import GLang.Proofs.Value.Typing.ValueDeclaredAnnotations

set_option maxHeartbeats 3000000
namespace GLang.ValueDependency
mutual
  theorem spaceDeclared_beta_annotations (ε : ValCtx)
      (hc : ∀ x t, ε.lookup x = some t → t.lc)
      (u : ValExpr) (hu : u.lc) :
      ∀ (v : ValSpace) (k : Nat), spaceDeclared ε v →
      spaceAnnotations (ValSpace.substBound k u v) ⊆ spaceAnnotations v ++ exprAnnotations u
    | .empty, k, h => by
      intro q hq
      simp only [ValSpace.substBound, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .real, k, h => by
      intro q hq
      simp only [ValSpace.substBound, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .dsum s0 s1, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s0 k h.1 q
      have h1 := @spaceDeclared_beta_annotations ε hc u hu s1 k h.2 q
      simp only [ValSpace.substBound, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .tprod s0 s1, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s0 k h.1 q
      have h1 := @spaceDeclared_beta_annotations ε hc u hu s1 k h.2 q
      simp only [ValSpace.substBound, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .ffs p s e, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e k h.2 q
      simp only [ValSpace.substBound, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
  theorem typeDeclared_beta_annotations (ε : ValCtx)
      (hc : ∀ x t, ε.lookup x = some t → t.lc)
      (u : ValExpr) (hu : u.lc) :
      ∀ (v : ValTy) (k : Nat), typeDeclared ε v →
      typeAnnotations (ValTy.substBound k u v) ⊆ typeAnnotations v ++ exprAnnotations u
    | .space s, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s k h q
      simp only [ValTy.substBound, typeAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .piTy t0 t1, k, h => by
      intro q hq
      have h0 := @typeDeclared_beta_annotations ε hc u hu t0 k h.1 q
      have h1 := @typeDeclared_beta_annotations ε hc u hu t1 (k + 1) h.2 q
      simp only [ValTy.substBound, typeAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
  theorem exprDeclared_beta_annotations (ε : ValCtx)
      (hc : ∀ x t, ε.lookup x = some t → t.lc)
      (u : ValExpr) (hu : u.lc) :
      ∀ (v : ValExpr) (k : Nat), exprDeclared ε v →
      exprAnnotations (ValExpr.substBound k u v) ⊆ exprAnnotations v ++ exprAnnotations u
    | .bvar i, k, h => by
      by_cases hi : i = k
      · simp [ValExpr.substBound, hi, DirectOracleOpenPush.raiseExpr_lc hu, exprAnnotations]
      · by_cases hk : k < i <;> simp [ValExpr.substBound, hi, hk, exprAnnotations]
    | .var y t, k, h => by
      have ht := hc y t h
      have ht' := ValTy.substBound_eq_of_raise k u t (DirectOracleOpenPush.raiseTy_lc ht 1 k)
      simp only [ValExpr.substBound, ht']
      intro q hq
      exact List.mem_append_left _ hq
    | .vlam t0 t1 e, k, h => by
      intro q hq
      have h0 := @typeDeclared_beta_annotations ε hc u hu t0 k h.1 q
      have h1 := @typeDeclared_beta_annotations ε hc u hu t1 (k + 1) h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu e (k + 1) h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .zero s, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s k h q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .rlit r, k, h => by
      intro q hq
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .scale e0 e1, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e0 k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .dsumE e0 e1, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e0 k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .tprodE e0 e1, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e0 k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .appV e0 e1, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e0 k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .vkrn e0 e1, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e0 k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .vblk e0 e1, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e0 k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .rrefRep e0 e1, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e0 k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .vadd s e0 e1, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e0 k h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .delta i s, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s k h q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .idelta s, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s k h q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .vsum s es, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s k h.1 q
      have h1 := @listDeclared_beta_annotations ε hc u hu es k h.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .ttv s e0 e1, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu e0 k h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .mtm i j s0 s1 e0 e1, k, h => by
      intro q hq
      have h0 := @spaceDeclared_beta_annotations ε hc u hu s0 k h.1 q
      have h1 := @spaceDeclared_beta_annotations ε hc u hu s1 k h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu e0 k h.2.2.1 q
      have h3 := @exprDeclared_beta_annotations ε hc u hu e1 k h.2.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .reshap e t t0, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h.1 q
      have h1 := @typeDeclared_beta_annotations ε hc u hu t k h.2.1 q
      have h2 := @typeDeclared_beta_annotations ε hc u hu t0 k h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .vtrans e, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .pinv e, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .inv e, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .svds e, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .gsvdS e a b, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu a k h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu b k h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .gsvdU e a b, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu a k h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu b k h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .gsvdUI e a b, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu a k h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu b k h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .gsvdV e a b, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu a k h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu b k h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .gsvdVI e a b, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu a k h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu b k h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | .gpinv e a b, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h.1 q
      have h1 := @exprDeclared_beta_annotations ε hc u hu a k h.2.1 q
      have h2 := @exprDeclared_beta_annotations ε hc u hu b k h.2.2 q
      simp only [ValExpr.substBound, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
  theorem listDeclared_beta_annotations (ε : ValCtx)
      (hc : ∀ x t, ε.lookup x = some t → t.lc)
      (u : ValExpr) (hu : u.lc) :
      ∀ (v : List ValExpr) (k : Nat), listDeclared ε v →
      listAnnotations (ValExpr.substBoundList k u v) ⊆ listAnnotations v ++ exprAnnotations u
    | [], k, h => by
      intro q hq
      simp only [ValExpr.substBoundList, listAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
    | e :: es, k, h => by
      intro q hq
      have h0 := @exprDeclared_beta_annotations ε hc u hu e k h.1 q
      have h1 := @listDeclared_beta_annotations ε hc u hu es k h.2 q
      simp only [ValExpr.substBoundList, listAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at *
      all_goals tauto
end
end GLang.ValueDependency
