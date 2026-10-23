import GLang.Value.Supporting.StrictTyping

/-! Finite syntactic annotation dependencies, including annotations nested inside annotations. -/
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace GLang.ValueDependency

mutual
  def spaceAnnotations : ValSpace → List (VName × ValTy)
    | .empty => []
    | .real => []
    | .dsum a b => spaceAnnotations a ++ spaceAnnotations b
    | .tprod a b => spaceAnnotations a ++ spaceAnnotations b
    | .ffs p s e => spaceAnnotations s ++ exprAnnotations e
  def typeAnnotations : ValTy → List (VName × ValTy)
    | .space s => spaceAnnotations s
    | .piTy a b => typeAnnotations a ++ typeAnnotations b
  def exprAnnotations : ValExpr → List (VName × ValTy)
    | .zero s => spaceAnnotations s
    | .rlit r => []
    | .scale a b => exprAnnotations a ++ exprAnnotations b
    | .vadd s a b => spaceAnnotations s ++ exprAnnotations a ++ exprAnnotations b
    | .dsumE a b => exprAnnotations a ++ exprAnnotations b
    | .tprodE a b => exprAnnotations a ++ exprAnnotations b
    | .delta n s => spaceAnnotations s
    | .idelta s => spaceAnnotations s
    | .vsum s es => spaceAnnotations s ++ listAnnotations es
    | .vlam a b e => typeAnnotations a ++ typeAnnotations b ++ exprAnnotations e
    | .bvar n => []
    | .var x t => (x, t) :: typeAnnotations t
    | .ttv s a b => spaceAnnotations s ++ exprAnnotations a ++ exprAnnotations b
    | .mtm n m s t a b => spaceAnnotations s ++ spaceAnnotations t ++ exprAnnotations a ++ exprAnnotations b
    | .appV a b => exprAnnotations a ++ exprAnnotations b
    | .vkrn a b => exprAnnotations a ++ exprAnnotations b
    | .vblk a b => exprAnnotations a ++ exprAnnotations b
    | .reshap e t u => exprAnnotations e ++ typeAnnotations t ++ typeAnnotations u
    | .vtrans e => exprAnnotations e
    | .gsvdS e a b => exprAnnotations e ++ exprAnnotations a ++ exprAnnotations b
    | .gsvdU e a b => exprAnnotations e ++ exprAnnotations a ++ exprAnnotations b
    | .gsvdUI e a b => exprAnnotations e ++ exprAnnotations a ++ exprAnnotations b
    | .gsvdV e a b => exprAnnotations e ++ exprAnnotations a ++ exprAnnotations b
    | .gsvdVI e a b => exprAnnotations e ++ exprAnnotations a ++ exprAnnotations b
    | .gpinv e a b => exprAnnotations e ++ exprAnnotations a ++ exprAnnotations b
    | .pinv e => exprAnnotations e
    | .inv e => exprAnnotations e
    | .svds e => exprAnnotations e
    | .rrefRep a b => exprAnnotations a ++ exprAnnotations b
  def listAnnotations : List ValExpr → List (VName × ValTy)
    | .nil => []
    | .cons e es => exprAnnotations e ++ listAnnotations es
end

mutual
  theorem spaceAnnotations_rank (z : ValSpace) (x : VName) (σ : ValTy)
      (h : (x, σ) ∈ spaceAnnotations z) : σ.size < ValSpace.size z := by
    cases z with
    | empty =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | real =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | dsum a b =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := spaceAnnotations_rank a x σ h0
        simp only [ValSpace.size]
        omega
      · have hh := spaceAnnotations_rank b x σ h1
        simp only [ValSpace.size]
        omega
    | tprod a b =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := spaceAnnotations_rank a x σ h0
        simp only [ValSpace.size]
        omega
      · have hh := spaceAnnotations_rank b x σ h1
        simp only [ValSpace.size]
        omega
    | ffs p s e =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := spaceAnnotations_rank s x σ h0
        simp only [ValSpace.size]
        omega
      · have hh := exprAnnotations_rank e x σ h1
        simp only [ValSpace.size]
        omega

  theorem typeAnnotations_rank (z : ValTy) (x : VName) (σ : ValTy)
      (h : (x, σ) ∈ typeAnnotations z) : σ.size < ValTy.size z := by
    cases z with
    | space s =>
      simp only [typeAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      have hh := spaceAnnotations_rank s x σ h
      simp only [ValTy.size]
      omega
    | piTy a b =>
      simp only [typeAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := typeAnnotations_rank a x σ h0
        simp only [ValTy.size]
        omega
      · have hh := typeAnnotations_rank b x σ h1
        simp only [ValTy.size]
        omega

  theorem exprAnnotations_rank (z : ValExpr) (x : VName) (σ : ValTy)
      (h : (x, σ) ∈ exprAnnotations z) : σ.size < ValExpr.size z := by
    cases z with
    | zero s =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      have hh := spaceAnnotations_rank s x σ h
      simp only [ValExpr.size]
      omega
    | rlit r =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | scale a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := exprAnnotations_rank a x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h1
        simp only [ValExpr.size]
        omega
    | vadd s a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := spaceAnnotations_rank s x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank a x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h2
        simp only [ValExpr.size]
        omega
    | dsumE a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := exprAnnotations_rank a x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h1
        simp only [ValExpr.size]
        omega
    | tprodE a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := exprAnnotations_rank a x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h1
        simp only [ValExpr.size]
        omega
    | delta n s =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      have hh := spaceAnnotations_rank s x σ h
      simp only [ValExpr.size]
      omega
    | idelta s =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      have hh := spaceAnnotations_rank s x σ h
      simp only [ValExpr.size]
      omega
    | vsum s es =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := spaceAnnotations_rank s x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := listAnnotations_rank es x σ h1
        simp only [ValExpr.size]
        omega
    | vlam a b e =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := typeAnnotations_rank a x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := typeAnnotations_rank b x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank e x σ h2
        simp only [ValExpr.size]
        omega
    | bvar n =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | var y u =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · cases h0
        simp only [ValExpr.size]
        omega
      · have hh := typeAnnotations_rank u x σ h1
        simp only [ValExpr.size]
        omega
    | ttv s a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := spaceAnnotations_rank s x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank a x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h2
        simp only [ValExpr.size]
        omega
    | mtm n m s t a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with ((h0 | h1) | h2) | h3
      · have hh := spaceAnnotations_rank s x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := spaceAnnotations_rank t x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank a x σ h2
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h3
        simp only [ValExpr.size]
        omega
    | appV a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := exprAnnotations_rank a x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h1
        simp only [ValExpr.size]
        omega
    | vkrn a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := exprAnnotations_rank a x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h1
        simp only [ValExpr.size]
        omega
    | vblk a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := exprAnnotations_rank a x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h1
        simp only [ValExpr.size]
        omega
    | reshap e t u =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := exprAnnotations_rank e x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := typeAnnotations_rank t x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := typeAnnotations_rank u x σ h2
        simp only [ValExpr.size]
        omega
    | vtrans e =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      have hh := exprAnnotations_rank e x σ h
      simp only [ValExpr.size]
      omega
    | gsvdS e a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := exprAnnotations_rank e x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank a x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h2
        simp only [ValExpr.size]
        omega
    | gsvdU e a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := exprAnnotations_rank e x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank a x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h2
        simp only [ValExpr.size]
        omega
    | gsvdUI e a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := exprAnnotations_rank e x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank a x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h2
        simp only [ValExpr.size]
        omega
    | gsvdV e a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := exprAnnotations_rank e x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank a x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h2
        simp only [ValExpr.size]
        omega
    | gsvdVI e a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := exprAnnotations_rank e x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank a x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h2
        simp only [ValExpr.size]
        omega
    | gpinv e a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · have hh := exprAnnotations_rank e x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank a x σ h1
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h2
        simp only [ValExpr.size]
        omega
    | pinv e =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      have hh := exprAnnotations_rank e x σ h
      simp only [ValExpr.size]
      omega
    | inv e =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      have hh := exprAnnotations_rank e x σ h
      simp only [ValExpr.size]
      omega
    | svds e =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      have hh := exprAnnotations_rank e x σ h
      simp only [ValExpr.size]
      omega
    | rrefRep a b =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := exprAnnotations_rank a x σ h0
        simp only [ValExpr.size]
        omega
      · have hh := exprAnnotations_rank b x σ h1
        simp only [ValExpr.size]
        omega

  theorem listAnnotations_rank (z : List ValExpr) (x : VName) (σ : ValTy)
      (h : (x, σ) ∈ listAnnotations z) : σ.size < ValExpr.sizeList z := by
    cases z with
    | nil =>
      simp only [listAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | cons e es =>
      simp only [listAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · have hh := exprAnnotations_rank e x σ h0
        simp only [ValExpr.sizeList]
        omega
      · have hh := listAnnotations_rank es x σ h1
        simp only [ValExpr.sizeList]
        omega

end

mutual
  theorem spaceAnnotations_fv (z : ValSpace) : ValSpace.fv z = ((spaceAnnotations z).map Prod.fst).toFinset := by
    cases z with
    | empty =>
      simp only [ValSpace.fv, spaceAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst]
    | real =>
      simp only [ValSpace.fv, spaceAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst]
    | dsum a b =>
      simp only [ValSpace.fv, spaceAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv a, spaceAnnotations_fv b]
    | tprod a b =>
      simp only [ValSpace.fv, spaceAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv a, spaceAnnotations_fv b]
    | ffs p s e =>
      simp only [ValSpace.fv, spaceAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv s, exprAnnotations_fv e]

  theorem typeAnnotations_fv (z : ValTy) : ValTy.fv z = ((typeAnnotations z).map Prod.fst).toFinset := by
    cases z with
    | space s =>
      simp only [ValTy.fv, typeAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv s]
    | piTy a b =>
      simp only [ValTy.fv, typeAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, typeAnnotations_fv a, typeAnnotations_fv b]

  theorem exprAnnotations_fv (z : ValExpr) : ValExpr.fv z = ((exprAnnotations z).map Prod.fst).toFinset := by
    cases z with
    | zero s =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv s]
    | rlit r =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst]
    | scale a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv a, exprAnnotations_fv b]
    | vadd s a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv s, exprAnnotations_fv a, exprAnnotations_fv b]
    | dsumE a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv a, exprAnnotations_fv b]
    | tprodE a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv a, exprAnnotations_fv b]
    | delta n s =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv s]
    | idelta s =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv s]
    | vsum s es =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv s, listAnnotations_fv es]
    | vlam a b e =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, typeAnnotations_fv a, typeAnnotations_fv b, exprAnnotations_fv e]
    | bvar n =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst]
    | var x t =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, typeAnnotations_fv t]
    | ttv s a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv s, exprAnnotations_fv a, exprAnnotations_fv b]
    | mtm n m s t a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, spaceAnnotations_fv s, spaceAnnotations_fv t, exprAnnotations_fv a, exprAnnotations_fv b]
    | appV a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv a, exprAnnotations_fv b]
    | vkrn a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv a, exprAnnotations_fv b]
    | vblk a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv a, exprAnnotations_fv b]
    | reshap e t u =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e, typeAnnotations_fv t, typeAnnotations_fv u]
    | vtrans e =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e]
    | gsvdS e a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e, exprAnnotations_fv a, exprAnnotations_fv b]
    | gsvdU e a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e, exprAnnotations_fv a, exprAnnotations_fv b]
    | gsvdUI e a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e, exprAnnotations_fv a, exprAnnotations_fv b]
    | gsvdV e a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e, exprAnnotations_fv a, exprAnnotations_fv b]
    | gsvdVI e a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e, exprAnnotations_fv a, exprAnnotations_fv b]
    | gpinv e a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e, exprAnnotations_fv a, exprAnnotations_fv b]
    | pinv e =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e]
    | inv e =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e]
    | svds e =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e]
    | rrefRep a b =>
      simp only [ValExpr.fv, exprAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv a, exprAnnotations_fv b]

  theorem listAnnotations_fv (z : List ValExpr) : ValExpr.fvList z = ((listAnnotations z).map Prod.fst).toFinset := by
    cases z with
    | nil =>
      simp only [ValExpr.fvList, listAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst]
    | cons e es =>
      simp only [ValExpr.fvList, listAnnotations, List.map_append, List.toFinset_append, List.map_cons, List.toFinset_cons, List.map_nil, List.toFinset_nil, Prod.fst, exprAnnotations_fv e, listAnnotations_fv es]

end

mutual
  theorem spaceAnnotations_close_fresh (z : ValSpace) (x : VName) (k : Nat)
      (h : x ∉ ValSpace.fv z) : ValSpace.closeRec k x z = z := by
    cases z with
    | empty =>
      rfl
    | real =>
      rfl
    | dsum a b =>
      simp only [ValSpace.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValSpace.closeRec, spaceAnnotations_close_fresh a x k h.1, spaceAnnotations_close_fresh b x k h.2]
    | tprod a b =>
      simp only [ValSpace.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValSpace.closeRec, spaceAnnotations_close_fresh a x k h.1, spaceAnnotations_close_fresh b x k h.2]
    | ffs p s e =>
      simp only [ValSpace.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValSpace.closeRec, spaceAnnotations_close_fresh s x k h.1, exprAnnotations_close_fresh e x k h.2]

  theorem typeAnnotations_close_fresh (z : ValTy) (x : VName) (k : Nat)
      (h : x ∉ ValTy.fv z) : ValTy.closeRec k x z = z := by
    cases z with
    | space s =>
      simp only [ValTy.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValTy.closeRec, spaceAnnotations_close_fresh s x k h]
    | piTy a b =>
      simp only [ValTy.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValTy.closeRec, typeAnnotations_close_fresh a x k h.1, typeAnnotations_close_fresh b x (k + 1) h.2]

  theorem exprAnnotations_close_fresh (z : ValExpr) (x : VName) (k : Nat)
      (h : x ∉ ValExpr.fv z) : ValExpr.closeRec k x z = z := by
    cases z with
    | zero s =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, spaceAnnotations_close_fresh s x k h]
    | rlit r =>
      rfl
    | scale a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh a x k h.1, exprAnnotations_close_fresh b x k h.2]
    | vadd s a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, spaceAnnotations_close_fresh s x k h.1.1, exprAnnotations_close_fresh a x k h.1.2, exprAnnotations_close_fresh b x k h.2]
    | dsumE a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh a x k h.1, exprAnnotations_close_fresh b x k h.2]
    | tprodE a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh a x k h.1, exprAnnotations_close_fresh b x k h.2]
    | delta n s =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, spaceAnnotations_close_fresh s x k h]
    | idelta s =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, spaceAnnotations_close_fresh s x k h]
    | vsum s es =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, spaceAnnotations_close_fresh s x k h.1, listAnnotations_close_fresh es x k h.2]
    | vlam a b e =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, typeAnnotations_close_fresh a x k h.1.1, typeAnnotations_close_fresh b x (k + 1) h.1.2, exprAnnotations_close_fresh e x (k + 1) h.2]
    | bvar n =>
      rfl
    | var y t =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, typeAnnotations_close_fresh t x k h.2, if_neg (Ne.symm h.1)]
    | ttv s a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, spaceAnnotations_close_fresh s x k h.1.1, exprAnnotations_close_fresh a x k h.1.2, exprAnnotations_close_fresh b x k h.2]
    | mtm n m s t a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, spaceAnnotations_close_fresh s x k h.1.1.1, spaceAnnotations_close_fresh t x k h.1.1.2, exprAnnotations_close_fresh a x k h.1.2, exprAnnotations_close_fresh b x k h.2]
    | appV a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh a x k h.1, exprAnnotations_close_fresh b x k h.2]
    | vkrn a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh a x k h.1, exprAnnotations_close_fresh b x k h.2]
    | vblk a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh a x k h.1, exprAnnotations_close_fresh b x k h.2]
    | reshap e t u =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h.1.1, typeAnnotations_close_fresh t x k h.1.2, typeAnnotations_close_fresh u x k h.2]
    | vtrans e =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h]
    | gsvdS e a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h.1.1, exprAnnotations_close_fresh a x k h.1.2, exprAnnotations_close_fresh b x k h.2]
    | gsvdU e a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h.1.1, exprAnnotations_close_fresh a x k h.1.2, exprAnnotations_close_fresh b x k h.2]
    | gsvdUI e a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h.1.1, exprAnnotations_close_fresh a x k h.1.2, exprAnnotations_close_fresh b x k h.2]
    | gsvdV e a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h.1.1, exprAnnotations_close_fresh a x k h.1.2, exprAnnotations_close_fresh b x k h.2]
    | gsvdVI e a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h.1.1, exprAnnotations_close_fresh a x k h.1.2, exprAnnotations_close_fresh b x k h.2]
    | gpinv e a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h.1.1, exprAnnotations_close_fresh a x k h.1.2, exprAnnotations_close_fresh b x k h.2]
    | pinv e =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h]
    | inv e =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h]
    | svds e =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh e x k h]
    | rrefRep a b =>
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRec, exprAnnotations_close_fresh a x k h.1, exprAnnotations_close_fresh b x k h.2]

  theorem listAnnotations_close_fresh (z : List ValExpr) (x : VName) (k : Nat)
      (h : x ∉ ValExpr.fvList z) : ValExpr.closeRecList k x z = z := by
    cases z with
    | nil =>
      rfl
    | cons e es =>
      simp only [ValExpr.fvList, Finset.mem_union, Finset.mem_insert, not_or] at h
      simp only [ValExpr.closeRecList, exprAnnotations_close_fresh e x k h.1, listAnnotations_close_fresh es x k h.2]

end

/-- Opening cannot inflate an external declaration annotation when both the
body annotation and the stored annotation omit the chosen fresh name. -/
theorem opened_annotation_eq (x : VName) (d a stored : ValTy) (k : Nat)
    (ha : x ∉ a.fv) (hs : x ∉ stored.fv)
    (h : ValTy.openRec k (.var x d) a = stored) : a = stored := by
  have hc := congrArg (ValTy.closeRec k x) h
  rw [ValTy.close_openVar x d a ha k, typeAnnotations_close_fresh stored x k hs] at hc
  exact hc

mutual
  theorem spaceAnnotations_open_occurrence (z : ValSpace) (x : VName) (a : ValTy)
      (h : (x, a) ∈ spaceAnnotations z) (k : Nat) (u : ValExpr) :
      ∃ j, (x, ValTy.openRec j u a) ∈ spaceAnnotations (ValSpace.openRec k u z) := by
    cases z with
    | empty =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | real =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | dsum a₁ b₁ =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence b₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | tprod a₁ b₁ =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence b₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | ffs p₁ s₁ e₁ =>
      simp only [spaceAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence s₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValSpace.openRec, spaceAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj

  theorem typeAnnotations_open_occurrence (z : ValTy) (x : VName) (a : ValTy)
      (h : (x, a) ∈ typeAnnotations z) (k : Nat) (u : ValExpr) :
      ∃ j, (x, ValTy.openRec j u a) ∈ typeAnnotations (ValTy.openRec k u z) := by
    cases z with
    | space s₁ =>
      simp only [typeAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence s₁ x a h k u
      refine ⟨j, ?_⟩
      simp only [ValTy.openRec, typeAnnotations, List.mem_append, List.mem_cons]
      exact hj
    | piTy a₁ b₁ =>
      simp only [typeAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := typeAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValTy.openRec, typeAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := typeAnnotations_open_occurrence b₁ x a h1 (k + 1) u
        refine ⟨j, ?_⟩
        simp only [ValTy.openRec, typeAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj

  theorem exprAnnotations_open_occurrence (z : ValExpr) (x : VName) (a : ValTy)
      (h : (x, a) ∈ exprAnnotations z) (k : Nat) (u : ValExpr) :
      ∃ j, (x, ValTy.openRec j u a) ∈ exprAnnotations (ValExpr.openRec k u z) := by
    cases z with
    | zero s₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence s₁ x a h k u
      refine ⟨j, ?_⟩
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
      exact hj
    | rlit r₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | scale a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | vadd s₁ a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence s₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | dsumE a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | tprodE a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | delta n₁ s₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence s₁ x a h k u
      refine ⟨j, ?_⟩
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
      exact hj
    | idelta s₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence s₁ x a h k u
      refine ⟨j, ?_⟩
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
      exact hj
    | vsum s₁ es₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence s₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := listAnnotations_open_occurrence es₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | vlam a₁ b₁ e₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := typeAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := typeAnnotations_open_occurrence b₁ x a h1 (k + 1) u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h2 (k + 1) u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | bvar n₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | var x₁ t₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · cases h0
        exact ⟨k, by simp [ValExpr.openRec, exprAnnotations]⟩
      · obtain ⟨j, hj⟩ := typeAnnotations_open_occurrence t₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | ttv s₁ a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence s₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | mtm n₁ m₁ s₁ t₁ a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with ((h0 | h1) | h2) | h3
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence s₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl (Or.inl hj))
      · obtain ⟨j, hj⟩ := spaceAnnotations_open_occurrence t₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl (Or.inr hj))
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h3 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | appV a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | vkrn a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | vblk a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | reshap e₁ t₁ u₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := typeAnnotations_open_occurrence t₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := typeAnnotations_open_occurrence u₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | vtrans e₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h k u
      refine ⟨j, ?_⟩
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
      exact hj
    | gsvdS e₁ a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | gsvdU e₁ a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | gsvdUI e₁ a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | gsvdV e₁ a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | gsvdVI e₁ a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | gpinv e₁ a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with (h0 | h1) | h2
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inl hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hj)
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h2 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj
    | pinv e₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h k u
      refine ⟨j, ?_⟩
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
      exact hj
    | inv e₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h k u
      refine ⟨j, ?_⟩
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
      exact hj
    | svds e₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h k u
      refine ⟨j, ?_⟩
      simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
      exact hj
    | rrefRep a₁ b₁ =>
      simp only [exprAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence a₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence b₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRec, exprAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj

  theorem listAnnotations_open_occurrence (z : List ValExpr) (x : VName) (a : ValTy)
      (h : (x, a) ∈ listAnnotations z) (k : Nat) (u : ValExpr) :
      ∃ j, (x, ValTy.openRec j u a) ∈ listAnnotations (ValExpr.openRecList k u z) := by
    cases z with
    | nil =>
      simp only [listAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
    | cons e₁ es₁ =>
      simp only [listAnnotations, List.mem_append, List.mem_cons, List.not_mem_nil] at h
      rcases h with h0 | h1
      · obtain ⟨j, hj⟩ := exprAnnotations_open_occurrence e₁ x a h0 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRecList, listAnnotations, List.mem_append, List.mem_cons]
        exact Or.inl hj
      · obtain ⟨j, hj⟩ := listAnnotations_open_occurrence es₁ x a h1 k u
        refine ⟨j, ?_⟩
        simp only [ValExpr.openRecList, listAnnotations, List.mem_append, List.mem_cons]
        exact Or.inr hj

end

/-- Every free name, including one nested in another annotation, has a
strictly smaller syntactic annotation within the enclosing type. -/
theorem fv_has_smaller_annotation (t : ValTy) (x : VName) (hx : x ∈ t.fv) :
    ∃ a, (x, a) ∈ typeAnnotations t ∧ a.size < t.size := by
  rw [typeAnnotations_fv] at hx
  obtain ⟨⟨y, a⟩, ha, hxy⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  simp only [Prod.fst] at hxy
  subst y
  exact ⟨a, ha, typeAnnotations_rank t x a ha⟩

/-- At an actual typed free-variable occurrence the syntactic annotation is
exactly the context declaration, not merely a shape-compatible type. -/
theorem typed_var_annotation_lookup {ε : ValCtx} {x : VName} {a t : ValTy}
    (h : ValHasType ε (.var x a) t) : ε.lookup x = some a := by
  cases h with
  | var h => exact h

theorem annotation_agreement_of_opening (ε : ValCtx) (t d : ValTy)
    (x : VName) (k : Nat) (hfresh : x ∉ t.fv)
    (hannotations : ∀ y a, (y, a) ∈ typeAnnotations t → x ∉ a.fv)
    (hstored : ∀ y a, ε.lookup y = some a → x ∉ a.fv)
    (hopened : ∀ y a, (y, a) ∈ typeAnnotations (ValTy.openRec k (.var x d) t) →
      (Finmap.insert x d ε).lookup y = some a) :
    ∀ y a, (y, a) ∈ typeAnnotations t → ε.lookup y = some a := by
  intro y a ha
  have hy : y ∈ t.fv := by
    rw [typeAnnotations_fv]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(y, a), ha, rfl⟩)
  have hyx : y ≠ x := by intro heq; subst y; exact hfresh hy
  obtain ⟨j, hj⟩ := typeAnnotations_open_occurrence t y a ha k (.var x d)
  have hl := hopened y (ValTy.openRec j (.var x d) a) hj
  rw [Finmap.lookup_insert_of_ne _ hyx] at hl
  have hae := opened_annotation_eq x d a (ValTy.openRec j (.var x d) a) j
    (hannotations y a ha) (hstored _ _ hl) rfl
  rw [← hae] at hl
  exact hl

/-- The exact syntactic occurrence argument reduces context dependency rank
to typed annotation agreement. No semantic premise is involved. -/
theorem context_dependency_rank_of_annotation_agreement (ε : ValCtx) (t : ValTy)
    (h : ∀ x a, (x, a) ∈ typeAnnotations t → ε.lookup x = some a)
    (x : VName) (hx : x ∈ t.fv) :
    ∃ a, ε.lookup x = some a ∧ a.size < t.size := by
  obtain ⟨a, ha, hrank⟩ := fv_has_smaller_annotation t x hx
  exact ⟨a, h x a ha, hrank⟩

end GLang.ValueDependency
