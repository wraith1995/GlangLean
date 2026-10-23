import GLang.Proofs.Value.Queries.ValueDependencyRank
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace GLang.ValueDependency

/-! Reverse occurrence tracking for binder rank arguments. -/
mutual
  theorem spaceAnnotations_open_inverse (z : ValSpace) (x : VName) (a : ValTy)
      (k : Nat) (u : ValExpr)
      (h : (x, a) ∈ spaceAnnotations (ValSpace.openRec k u z)) :
      (∃ b j, (x, b) ∈ spaceAnnotations z ∧ a = ValTy.openRec j u b) ∨
        (x, a) ∈ exprAnnotations u := by
    cases z with
    | empty =>
      simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | real =>
      simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | dsum a₁ b₁ =>
      simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases spaceAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [spaceAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases spaceAnnotations_open_inverse b₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [spaceAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | tprod a₁ b₁ =>
      simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases spaceAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [spaceAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases spaceAnnotations_open_inverse b₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [spaceAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | ffs p₁ s₁ e₁ =>
      simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases spaceAnnotations_open_inverse s₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [spaceAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse e₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [spaceAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu

  theorem typeAnnotations_open_inverse (z : ValTy) (x : VName) (a : ValTy)
      (k : Nat) (u : ValExpr)
      (h : (x, a) ∈ typeAnnotations (ValTy.openRec k u z)) :
      (∃ b j, (x, b) ∈ typeAnnotations z ∧ a = ValTy.openRec j u b) ∨
        (x, a) ∈ exprAnnotations u := by
    cases z with
    | space s₁ =>
      simp only [ValTy.openRec, typeAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases spaceAnnotations_open_inverse s₁ x a k u h with ⟨b, j, hb, heq⟩ | hu
      · refine Or.inl ⟨b, j, ?_, heq⟩
        simp only [typeAnnotations, List.mem_append, List.mem_cons]
        exact hb
      · exact Or.inr hu
    | piTy a₁ b₁ =>
      simp only [ValTy.openRec, typeAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases typeAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [typeAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases typeAnnotations_open_inverse b₁ x a (k + 1) u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [typeAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu

  theorem exprAnnotations_open_inverse (z : ValExpr) (x : VName) (a : ValTy)
      (k : Nat) (u : ValExpr)
      (h : (x, a) ∈ exprAnnotations (ValExpr.openRec k u z)) :
      (∃ b j, (x, b) ∈ exprAnnotations z ∧ a = ValTy.openRec j u b) ∨
        (x, a) ∈ exprAnnotations u := by
    cases z with
    | zero s₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases spaceAnnotations_open_inverse s₁ x a k u h with ⟨b, j, hb, heq⟩ | hu
      · refine Or.inl ⟨b, j, ?_, heq⟩
        simp only [exprAnnotations, List.mem_append, List.mem_cons]
        exact hb
      · exact Or.inr hu
    | rlit r₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | scale a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases exprAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | vadd s₁ a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases spaceAnnotations_open_inverse s₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse a₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | dsumE a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases exprAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | tprodE a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases exprAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | delta n₁ s₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases spaceAnnotations_open_inverse s₁ x a k u h with ⟨b, j, hb, heq⟩ | hu
      · refine Or.inl ⟨b, j, ?_, heq⟩
        simp only [exprAnnotations, List.mem_append, List.mem_cons]
        exact hb
      · exact Or.inr hu
    | idelta s₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases spaceAnnotations_open_inverse s₁ x a k u h with ⟨b, j, hb, heq⟩ | hu
      · refine Or.inl ⟨b, j, ?_, heq⟩
        simp only [exprAnnotations, List.mem_append, List.mem_cons]
        exact hb
      · exact Or.inr hu
    | vsum s₁ es₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases spaceAnnotations_open_inverse s₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases listAnnotations_open_inverse es₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | vlam a₁ b₁ e₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases typeAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases typeAnnotations_open_inverse b₁ x a (k + 1) u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse e₁ x a (k + 1) u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | bvar n₁ =>
      by_cases hn : n₁ = k
      · simp only [ValExpr.openRec, hn, if_true] at h
        exact Or.inr h
      · simp only [ValExpr.openRec, hn, if_false, exprAnnotations, List.not_mem_nil] at h
    | var x₁ t₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · cases h0
        exact Or.inl ⟨t₁, k, by simp [exprAnnotations], rfl⟩
      · rcases typeAnnotations_open_inverse t₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | ttv s₁ a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases spaceAnnotations_open_inverse s₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse a₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | mtm n₁ m₁ s₁ t₁ a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with ((h0 | h1) | h2) | h3
      · rcases spaceAnnotations_open_inverse s₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl (Or.inl hb))
        · exact Or.inr hu
      · rcases spaceAnnotations_open_inverse t₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl (Or.inr hb))
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse a₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h3 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | appV a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases exprAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | vkrn a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases exprAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | vblk a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases exprAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | reshap e₁ t₁ u₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases exprAnnotations_open_inverse e₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases typeAnnotations_open_inverse t₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases typeAnnotations_open_inverse u₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | vtrans e₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases exprAnnotations_open_inverse e₁ x a k u h with ⟨b, j, hb, heq⟩ | hu
      · refine Or.inl ⟨b, j, ?_, heq⟩
        simp only [exprAnnotations, List.mem_append, List.mem_cons]
        exact hb
      · exact Or.inr hu
    | gsvdS e₁ a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases exprAnnotations_open_inverse e₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse a₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | gsvdU e₁ a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases exprAnnotations_open_inverse e₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse a₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | gsvdUI e₁ a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases exprAnnotations_open_inverse e₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse a₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | gsvdV e₁ a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases exprAnnotations_open_inverse e₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse a₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | gsvdVI e₁ a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases exprAnnotations_open_inverse e₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse a₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | gpinv e₁ a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · rcases exprAnnotations_open_inverse e₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inl hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse a₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr hb)
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h2 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu
    | pinv e₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases exprAnnotations_open_inverse e₁ x a k u h with ⟨b, j, hb, heq⟩ | hu
      · refine Or.inl ⟨b, j, ?_, heq⟩
        simp only [exprAnnotations, List.mem_append, List.mem_cons]
        exact hb
      · exact Or.inr hu
    | inv e₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases exprAnnotations_open_inverse e₁ x a k u h with ⟨b, j, hb, heq⟩ | hu
      · refine Or.inl ⟨b, j, ?_, heq⟩
        simp only [exprAnnotations, List.mem_append, List.mem_cons]
        exact hb
      · exact Or.inr hu
    | svds e₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases exprAnnotations_open_inverse e₁ x a k u h with ⟨b, j, hb, heq⟩ | hu
      · refine Or.inl ⟨b, j, ?_, heq⟩
        simp only [exprAnnotations, List.mem_append, List.mem_cons]
        exact hb
      · exact Or.inr hu
    | rrefRep a₁ b₁ =>
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases exprAnnotations_open_inverse a₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases exprAnnotations_open_inverse b₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [exprAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu

  theorem listAnnotations_open_inverse (z : List ValExpr) (x : VName) (a : ValTy)
      (k : Nat) (u : ValExpr)
      (h : (x, a) ∈ listAnnotations (ValExpr.openRecList k u z)) :
      (∃ b j, (x, b) ∈ listAnnotations z ∧ a = ValTy.openRec j u b) ∨
        (x, a) ∈ exprAnnotations u := by
    cases z with
    | nil =>
      simp only [ValExpr.openRecList, listAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | cons e₁ es₁ =>
      simp only [ValExpr.openRecList, listAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · rcases exprAnnotations_open_inverse e₁ x a k u h0 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [listAnnotations, List.mem_append, List.mem_cons]
          exact Or.inl hb
        · exact Or.inr hu
      · rcases listAnnotations_open_inverse es₁ x a k u h1 with ⟨b, j, hb, heq⟩ | hu
        · refine Or.inl ⟨b, j, ?_, heq⟩
          simp only [listAnnotations, List.mem_append, List.mem_cons]
          exact Or.inr hb
        · exact Or.inr hu

end
end GLang.ValueDependency
