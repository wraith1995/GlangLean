import GLang.Proofs.Value.Typing.ValueContextSupport
import GLang.Proofs.Value.Queries.ValueDependencyRank
import GLang.Proofs.Value.Binding.ValueBeta

set_option maxHeartbeats 3000000
namespace GLang.ValueDependency

/- Free variable annotations agree with the named context. Bound variables
are handled by binders; a free variable annotation is checked as a whole. -/
mutual
  def spaceDeclared (ε : ValCtx) : ValSpace → Prop
    | .empty => True
    | .real => True
    | .dsum s0 s1 => spaceDeclared ε s0 ∧ spaceDeclared ε s1
    | .tprod s0 s1 => spaceDeclared ε s0 ∧ spaceDeclared ε s1
    | .ffs p s e => spaceDeclared ε s ∧ exprDeclared ε e
  def typeDeclared (ε : ValCtx) : ValTy → Prop
    | .space s => spaceDeclared ε s
    | .piTy t0 t1 => typeDeclared ε t0 ∧ typeDeclared ε t1
  def exprDeclared (ε : ValCtx) : ValExpr → Prop
    | .bvar i => True
    | .var y t => ε.lookup y = some t
    | .vlam t0 t1 e => typeDeclared ε t0 ∧ typeDeclared ε t1 ∧ exprDeclared ε e
    | .zero s => spaceDeclared ε s
    | .rlit r => True
    | .scale e0 e1 => exprDeclared ε e0 ∧ exprDeclared ε e1
    | .dsumE e0 e1 => exprDeclared ε e0 ∧ exprDeclared ε e1
    | .tprodE e0 e1 => exprDeclared ε e0 ∧ exprDeclared ε e1
    | .appV e0 e1 => exprDeclared ε e0 ∧ exprDeclared ε e1
    | .vkrn e0 e1 => exprDeclared ε e0 ∧ exprDeclared ε e1
    | .vblk e0 e1 => exprDeclared ε e0 ∧ exprDeclared ε e1
    | .rrefRep e0 e1 => exprDeclared ε e0 ∧ exprDeclared ε e1
    | .vadd s e0 e1 => spaceDeclared ε s ∧ exprDeclared ε e0 ∧ exprDeclared ε e1
    | .delta i s => spaceDeclared ε s
    | .idelta s => spaceDeclared ε s
    | .vsum s es => spaceDeclared ε s ∧ listDeclared ε es
    | .ttv s e0 e1 => spaceDeclared ε s ∧ exprDeclared ε e0 ∧ exprDeclared ε e1
    | .mtm i j s0 s1 e0 e1 => spaceDeclared ε s0 ∧ spaceDeclared ε s1 ∧ exprDeclared ε e0 ∧ exprDeclared ε e1
    | .reshap e t t0 => exprDeclared ε e ∧ typeDeclared ε t ∧ typeDeclared ε t0
    | .vtrans e => exprDeclared ε e
    | .pinv e => exprDeclared ε e
    | .inv e => exprDeclared ε e
    | .svds e => exprDeclared ε e
    | .gsvdS e a b => exprDeclared ε e ∧ exprDeclared ε a ∧ exprDeclared ε b
    | .gsvdU e a b => exprDeclared ε e ∧ exprDeclared ε a ∧ exprDeclared ε b
    | .gsvdUI e a b => exprDeclared ε e ∧ exprDeclared ε a ∧ exprDeclared ε b
    | .gsvdV e a b => exprDeclared ε e ∧ exprDeclared ε a ∧ exprDeclared ε b
    | .gsvdVI e a b => exprDeclared ε e ∧ exprDeclared ε a ∧ exprDeclared ε b
    | .gpinv e a b => exprDeclared ε e ∧ exprDeclared ε a ∧ exprDeclared ε b
  def listDeclared (ε : ValCtx) : List ValExpr → Prop
    | [] => True
    | e :: es => exprDeclared ε e ∧ listDeclared ε es
end

mutual
  theorem spaceDeclared_open_inv (ε : ValCtx) (x : VName) (d : ValTy)
      (hctx : x ∉ ε.fvSupport) :
      ∀ (v : ValSpace) (k : Nat), x ∉ ValSpace.fv v →
      spaceDeclared (Finmap.insert x d ε) (ValSpace.openRec k (.var x d) v) → spaceDeclared ε v
    | .empty, k, hf, h => by
      trivial
    | .real, k, hf, h => by
      trivial
    | .dsum s0 s1, k, hf, h => by
      simp only [ValSpace.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValSpace.openRec, spaceDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s0 := by tauto
      have hf1 : x ∉ ValSpace.fv s1 := by tauto
      exact ⟨spaceDeclared_open_inv ε x d hctx s0 k hf0 h.1, spaceDeclared_open_inv ε x d hctx s1 k hf1 h.2⟩
    | .tprod s0 s1, k, hf, h => by
      simp only [ValSpace.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValSpace.openRec, spaceDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s0 := by tauto
      have hf1 : x ∉ ValSpace.fv s1 := by tauto
      exact ⟨spaceDeclared_open_inv ε x d hctx s0 k hf0 h.1, spaceDeclared_open_inv ε x d hctx s1 k hf1 h.2⟩
    | .ffs p s e, k, hf, h => by
      simp only [ValSpace.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValSpace.openRec, spaceDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s := by tauto
      have hf1 : x ∉ ValExpr.fv e := by tauto
      exact ⟨spaceDeclared_open_inv ε x d hctx s k hf0 h.1, exprDeclared_open_inv ε x d hctx e k hf1 h.2⟩
  theorem typeDeclared_open_inv (ε : ValCtx) (x : VName) (d : ValTy)
      (hctx : x ∉ ε.fvSupport) :
      ∀ (v : ValTy) (k : Nat), x ∉ ValTy.fv v →
      typeDeclared (Finmap.insert x d ε) (ValTy.openRec k (.var x d) v) → typeDeclared ε v
    | .space s, k, hf, h => by
      simp only [ValTy.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValTy.openRec, typeDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s := by tauto
      exact spaceDeclared_open_inv ε x d hctx s k hf0 h
    | .piTy t0 t1, k, hf, h => by
      simp only [ValTy.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValTy.openRec, typeDeclared] at h ⊢
      have hf0 : x ∉ ValTy.fv t0 := by tauto
      have hf1 : x ∉ ValTy.fv t1 := by tauto
      exact ⟨typeDeclared_open_inv ε x d hctx t0 k hf0 h.1, typeDeclared_open_inv ε x d hctx t1 (k + 1) hf1 h.2⟩
  theorem exprDeclared_open_inv (ε : ValCtx) (x : VName) (d : ValTy)
      (hctx : x ∉ ε.fvSupport) :
      ∀ (v : ValExpr) (k : Nat), x ∉ ValExpr.fv v →
      exprDeclared (Finmap.insert x d ε) (ValExpr.openRec k (.var x d) v) → exprDeclared ε v
    | .bvar i, k, hf, h => by
      trivial
    | .var y t, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h
      have hyx : y ≠ x := Ne.symm hf.1
      rw [Finmap.lookup_insert_of_ne _ hyx] at h
      have heq := opened_annotation_eq x d t (ValTy.openRec k (.var x d) t) k hf.2
        (ValCtx.not_mem_fv_of_not_mem_support hctx h) rfl
      exact heq ▸ h
    | .vlam t0 t1 e, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValTy.fv t0 := by tauto
      have hf1 : x ∉ ValTy.fv t1 := by tauto
      have hf2 : x ∉ ValExpr.fv e := by tauto
      exact ⟨typeDeclared_open_inv ε x d hctx t0 k hf0 h.1, typeDeclared_open_inv ε x d hctx t1 (k + 1) hf1 h.2.1, exprDeclared_open_inv ε x d hctx e (k + 1) hf2 h.2.2⟩
    | .zero s, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s := by tauto
      exact spaceDeclared_open_inv ε x d hctx s k hf0 h
    | .rlit r, k, hf, h => by
      trivial
    | .scale e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e0 := by tauto
      have hf1 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e0 k hf0 h.1, exprDeclared_open_inv ε x d hctx e1 k hf1 h.2⟩
    | .dsumE e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e0 := by tauto
      have hf1 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e0 k hf0 h.1, exprDeclared_open_inv ε x d hctx e1 k hf1 h.2⟩
    | .tprodE e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e0 := by tauto
      have hf1 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e0 k hf0 h.1, exprDeclared_open_inv ε x d hctx e1 k hf1 h.2⟩
    | .appV e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e0 := by tauto
      have hf1 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e0 k hf0 h.1, exprDeclared_open_inv ε x d hctx e1 k hf1 h.2⟩
    | .vkrn e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e0 := by tauto
      have hf1 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e0 k hf0 h.1, exprDeclared_open_inv ε x d hctx e1 k hf1 h.2⟩
    | .vblk e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e0 := by tauto
      have hf1 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e0 k hf0 h.1, exprDeclared_open_inv ε x d hctx e1 k hf1 h.2⟩
    | .rrefRep e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e0 := by tauto
      have hf1 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e0 k hf0 h.1, exprDeclared_open_inv ε x d hctx e1 k hf1 h.2⟩
    | .vadd s e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s := by tauto
      have hf1 : x ∉ ValExpr.fv e0 := by tauto
      have hf2 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨spaceDeclared_open_inv ε x d hctx s k hf0 h.1, exprDeclared_open_inv ε x d hctx e0 k hf1 h.2.1, exprDeclared_open_inv ε x d hctx e1 k hf2 h.2.2⟩
    | .delta i s, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s := by tauto
      exact spaceDeclared_open_inv ε x d hctx s k hf0 h
    | .idelta s, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s := by tauto
      exact spaceDeclared_open_inv ε x d hctx s k hf0 h
    | .vsum s es, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s := by tauto
      have hf1 : x ∉ ValExpr.fvList es := by tauto
      exact ⟨spaceDeclared_open_inv ε x d hctx s k hf0 h.1, listDeclared_open_inv ε x d hctx es k hf1 h.2⟩
    | .ttv s e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s := by tauto
      have hf1 : x ∉ ValExpr.fv e0 := by tauto
      have hf2 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨spaceDeclared_open_inv ε x d hctx s k hf0 h.1, exprDeclared_open_inv ε x d hctx e0 k hf1 h.2.1, exprDeclared_open_inv ε x d hctx e1 k hf2 h.2.2⟩
    | .mtm i j s0 s1 e0 e1, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValSpace.fv s0 := by tauto
      have hf1 : x ∉ ValSpace.fv s1 := by tauto
      have hf2 : x ∉ ValExpr.fv e0 := by tauto
      have hf3 : x ∉ ValExpr.fv e1 := by tauto
      exact ⟨spaceDeclared_open_inv ε x d hctx s0 k hf0 h.1, spaceDeclared_open_inv ε x d hctx s1 k hf1 h.2.1, exprDeclared_open_inv ε x d hctx e0 k hf2 h.2.2.1, exprDeclared_open_inv ε x d hctx e1 k hf3 h.2.2.2⟩
    | .reshap e t t0, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      have hf1 : x ∉ ValTy.fv t := by tauto
      have hf2 : x ∉ ValTy.fv t0 := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e k hf0 h.1, typeDeclared_open_inv ε x d hctx t k hf1 h.2.1, typeDeclared_open_inv ε x d hctx t0 k hf2 h.2.2⟩
    | .vtrans e, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      exact exprDeclared_open_inv ε x d hctx e k hf0 h
    | .pinv e, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      exact exprDeclared_open_inv ε x d hctx e k hf0 h
    | .inv e, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      exact exprDeclared_open_inv ε x d hctx e k hf0 h
    | .svds e, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      exact exprDeclared_open_inv ε x d hctx e k hf0 h
    | .gsvdS e a b, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      have hf1 : x ∉ ValExpr.fv a := by tauto
      have hf2 : x ∉ ValExpr.fv b := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e k hf0 h.1, exprDeclared_open_inv ε x d hctx a k hf1 h.2.1, exprDeclared_open_inv ε x d hctx b k hf2 h.2.2⟩
    | .gsvdU e a b, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      have hf1 : x ∉ ValExpr.fv a := by tauto
      have hf2 : x ∉ ValExpr.fv b := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e k hf0 h.1, exprDeclared_open_inv ε x d hctx a k hf1 h.2.1, exprDeclared_open_inv ε x d hctx b k hf2 h.2.2⟩
    | .gsvdUI e a b, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      have hf1 : x ∉ ValExpr.fv a := by tauto
      have hf2 : x ∉ ValExpr.fv b := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e k hf0 h.1, exprDeclared_open_inv ε x d hctx a k hf1 h.2.1, exprDeclared_open_inv ε x d hctx b k hf2 h.2.2⟩
    | .gsvdV e a b, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      have hf1 : x ∉ ValExpr.fv a := by tauto
      have hf2 : x ∉ ValExpr.fv b := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e k hf0 h.1, exprDeclared_open_inv ε x d hctx a k hf1 h.2.1, exprDeclared_open_inv ε x d hctx b k hf2 h.2.2⟩
    | .gsvdVI e a b, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      have hf1 : x ∉ ValExpr.fv a := by tauto
      have hf2 : x ∉ ValExpr.fv b := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e k hf0 h.1, exprDeclared_open_inv ε x d hctx a k hf1 h.2.1, exprDeclared_open_inv ε x d hctx b k hf2 h.2.2⟩
    | .gpinv e a b, k, hf, h => by
      simp only [ValExpr.fv, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRec, exprDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      have hf1 : x ∉ ValExpr.fv a := by tauto
      have hf2 : x ∉ ValExpr.fv b := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e k hf0 h.1, exprDeclared_open_inv ε x d hctx a k hf1 h.2.1, exprDeclared_open_inv ε x d hctx b k hf2 h.2.2⟩
  theorem listDeclared_open_inv (ε : ValCtx) (x : VName) (d : ValTy)
      (hctx : x ∉ ε.fvSupport) :
      ∀ (v : List ValExpr) (k : Nat), x ∉ ValExpr.fvList v →
      listDeclared (Finmap.insert x d ε) (ValExpr.openRecList k (.var x d) v) → listDeclared ε v
    | [], k, hf, h => by
      trivial
    | e :: es, k, hf, h => by
      simp only [ValExpr.fvList, Finset.mem_union, Finset.mem_insert, not_or] at hf
      simp only [ValExpr.openRecList, listDeclared] at h ⊢
      have hf0 : x ∉ ValExpr.fv e := by tauto
      have hf1 : x ∉ ValExpr.fvList es := by tauto
      exact ⟨exprDeclared_open_inv ε x d hctx e k hf0 h.1, listDeclared_open_inv ε x d hctx es k hf1 h.2⟩
end
end GLang.ValueDependency
