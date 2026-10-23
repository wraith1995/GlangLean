import GLang.Value.Context

/-! Value kinding and typing for error-capable evaluation. Array kinds are
static; the evaluator checks dimensions and dependent function compatibility. -/
namespace GLang.RuntimeValue

mutual

  inductive ValSValid : ValCtx → ValSpace → Type
    | real {ε} : ValSValid ε .real
    | empty {ε} : ValSValid ε .empty
    | dsum {ε s₀ s₁} :
        ValSValid ε s₀ → ValSValid ε s₁ → ValSValid ε (.dsum s₀ s₁)
    | tprod {ε s₀ s₁} :
        ValSValid ε s₀ → ValSValid ε s₁ → ValSValid ε (.tprod s₀ s₁)
    | ffs {ε p s₀ s₁ leev}
        : ValSValid ε s₀
        → ValSValid ε s₁
        → ValHasType ε leev (.space (.tprod s₀ s₁))
        → ValSValid ε (.ffs p (.tprod s₀ s₁) leev)

  inductive ValTValid : ValCtx → ValTy → ValKind → Type
    | space {ε s} : ValSValid ε s → ValTValid ε (.space s) .base
    | piTy {ε τ₀ τ₁ k₀ k₁} (L : Finset VName)
        : ValTValid ε τ₀ k₀
        → (∀ x, x ∉ L →
            ValTValid (Finmap.insert x τ₀ ε) (ValTy.openVar x τ₀ τ₁) k₁)
        → ValTValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁)

  inductive ValHasType : ValCtx → ValExpr → ValTy → Type
    | var {ε x τ} : ε.lookup x = some τ → ValHasType ε (.var x τ) τ
    | zero {ε s} : ValSValid ε s → ValHasType ε (.zero s) (.space s)
    | rlit {ε} (r : ℝ) : ValHasType ε (.rlit r) (.space .real)
    | scale {ε e₀ e₁ τ}
        : ValHasType ε e₀ (.space .real)
        → ValHasType ε e₁ τ
        → ValHasType ε (.scale e₀ e₁) τ
    | vadd {ε e₀ e₁ s s₀ s₁}
        : ValHasType ε e₀ (.space s₀)
        → ValHasType ε e₁ (.space s₁)
        → ValSValid ε s
        → ValHasType ε (.vadd s e₀ e₁) (.space s)
    | dsumE {ε e₀ e₁ s₀ s₁}
        : ValHasType ε e₀ (.space s₀)
        → ValHasType ε e₁ (.space s₁)
        → ValHasType ε (.dsumE e₀ e₁) (.space (.dsum s₀ s₁))
    | tprodE {ε e₀ e₁ s₀ s₁}
        : ValHasType ε e₀ (.space s₀)
        → ValHasType ε e₁ (.space s₁)
        → ValHasType ε (.tprodE e₀ e₁) (.space (.tprod s₀ s₁))
    | delta {ε n s} : ValSValid ε s → ValHasType ε (.delta n s) (.space s)
    | idelta {ε s}
        : ValSValid ε s
        → ValHasType ε (.idelta s) (.space (.tprod s s))
    | ttv_space {ε s0p s0pp s1 τarg e₀ e₁}
        : ValSValid ε s0pp
        → ValHasType ε e₀ (.space (.tprod s0p s1))
        → ValHasType ε e₁ τarg
        → ValHasType ε (.ttv s0pp e₀ e₁) (.space s1)
    | ttv_real {ε s0p s0pp τarg e₀ e₁}
        : ValSValid ε s0pp
        → ValHasType ε e₀ (.space s0p)
        → ValHasType ε e₁ τarg
        → (∀ a b, s0p ≠ .tprod a b)
        → ValHasType ε (.ttv s0pp e₀ e₁) (.space .real)
    | mtm {ε n₀ n₁ s0 s1 s1p s1pp s2 e₀ e₁}
        : ValSValid ε s1pp
        → ValSValid ε s1
        → ValHasType ε e₀ (.space (.tprod s1p s0))
        → ValHasType ε e₁ (.space (.tprod s2 s1))
        → ValHasType ε (.mtm n₀ n₁ s1pp s1 e₀ e₁)
                       (.space (.tprod s2 s0))
    | vsum {ε s0 s es}
        : ValSValid ε s0
        → (∀ e ∈ es, ValHasType ε e (.space s))
        → ValSValid ε s
        → (es = [] → s = .empty)
        → ValHasType ε (.vsum s0 es) (.space s)
    | vlam {ε τ₀ τ₁ k₀ k₁ e} (L : Finset VName)
        : ValTValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁)
        → (∀ x, x ∉ L →
            ValHasType (Finmap.insert x τ₀ ε) (ValExpr.openVar x τ₀ e) (ValTy.openVar x τ₀ τ₁))
        → ValHasType ε (.vlam τ₀ τ₁ e) (.piTy τ₀ τ₁)
    | appV {ε e₀ e₁ τ₀ τ₁ τ_out k_out}
        : ValHasType ε e₀ (.piTy τ₀ τ₁)
        → ValHasType ε e₁ τ₀
        → τ_out = ValTy.applyCodomain e₁ τ₁
        → ValTValid ε τ_out k_out
        → ValHasType ε (.appV e₀ e₁) τ_out
    | vkrn {ε e e' s0 s1 s2 s3}
        : ValHasType ε e  (.space (.tprod s0 s2))
        → ValHasType ε e' (.space (.tprod s1 s3))
        → ValHasType ε (.vkrn e e')
              (.space (.tprod (.tprod s0 s1) (.tprod s2 s3)))
    | vblk {ε e e' s0 s1 s2 s3}
        : ValHasType ε e  (.space (.tprod s0 s2))
        → ValHasType ε e' (.space (.tprod s1 s3))
        → ValHasType ε (.vblk e e')
              (.space (.tprod (.dsum s0 s1) (.dsum s2 s3)))
    | reshap {ε e τ_in τ₀ τ k}
        : ValHasType ε e τ_in
        → ValTValid ε τ₀ k
        → ValTValid ε τ k
        → ValHasType ε (.reshap e τ τ₀) τ
    | vtrans {ε e s₀ s₁}
        : ValHasType ε e (.space (.tprod s₀ s₁))
        → ValHasType ε (.vtrans e) (.space (.tprod s₁ s₀))
    | gsvdS {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdS e a b)
            (.space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                            (.ffs .image    (.tprod s0 s1) e)))

    | gsvdU {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdU e a b)
            (.space (.tprod s0 (.ffs .cokernel (.tprod s0 s1) e)))

    | gsvdUI {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdUI e a b)
            (.space (.tprod s0 (.ffs .kernel (.tprod s0 s1) e)))
    | gsvdV {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdV e a b)
            (.space (.tprod s1 (.ffs .image (.tprod s0 s1) e)))

    | gsvdVI {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdVI e a b)
            (.space (.tprod s1 (.ffs .coimage (.tprod s0 s1) e)))
    | pinv_tensor {ε e s₀ s₁}
        : ValHasType ε e (.space (.tprod s₀ s₁))
        → ValHasType ε (.pinv e) (.space (.tprod s₁ s₀))
    | pinv_raw {ε e s₀}
        : ValHasType ε e (.space s₀)
        → (∀ a b, s₀ ≠ .tprod a b)
        → ValHasType ε (.pinv e) (.space (.tprod .real s₀))
    | gpinv {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gpinv e a b) (.space (.tprod s1 s0))
    | rrefRep {ε e₀ e₁ s p0 p1}
        : ValHasType ε e₀ (.space s)
        → ValHasType ε e₁ (.space (.tprod p0 p1))
        → ValHasType ε (.rrefRep e₀ e₁) (.space (.tprod p1 p0))
    | inv_tensor {ε e s₀ s₁}
        : ValHasType ε e (.space (.tprod s₀ s₁))
        → ValHasType ε (.inv e) (.space (.tprod s₁ s₀))
    | inv_raw {ε e s₀}
        : ValHasType ε e (.space s₀)
        → (∀ a b, s₀ ≠ .tprod a b)
        → ValHasType ε (.inv e) (.space (.tprod .real s₀))
    | svds {ε e s0 s1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε (.svds e)
            (.space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                            (.ffs .image    (.tprod s0 s1) e)))

end

def ValHasType.canonicalFSV {which ε e a b s0 s1 a0 a1 b0 b1}
    (he : ValHasType ε e (.space (.tprod s0 s1)))
    (ha : ValHasType ε a (.space (.tprod a0 a1)))
    (hb : ValHasType ε b (.space (.tprod b0 b1))) :
    ValHasType ε (.canonicalFSV which e a b)
      (.space (.tprod (which.ambient s0 s1) (.ffs which (.tprod s0 s1) e))) := by
  cases which with
  | kernel => exact .gsvdUI he ha hb
  | cokernel => exact .gsvdU he ha hb
  | image => exact .gsvdV he ha hb
  | coimage => exact .gsvdVI he ha hb

namespace ValHasType

def rlit_typed {ε : ValCtx} (r : ℝ) :
    ValHasType ε (.rlit r) (.space .real) :=
  ValHasType.rlit r

end ValHasType

end GLang.RuntimeValue
