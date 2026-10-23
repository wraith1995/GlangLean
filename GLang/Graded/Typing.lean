import GLang.Graded.Ctx

namespace GLang.Graded

open GLang

def resurrect (f : Name → Option Ty) : GCtx :=
  fun x => (f x).map (fun τ => (GGrade.omega, τ))

/-- Every binding has grade other than one. This is the context condition
for the empty-linear-context leaf rules. -/
def NoLin (Γ : GCtx) : Prop := ∀ y τy, Γ y ≠ some (GGrade.one, τy)

mutual

  inductive GSValid : (Name → Option Ty) → Space → Type
    | empty {f} : GSValid f .empty
    | real  {f} : GSValid f .real
    | dual  {f s} : GSValid f s → GSValid f (.dual s)
    | dsum  {f s₀ s₁} : GSValid f s₀ → GSValid f s₁ → GSValid f (.dsum s₀ s₁)
    | tprod {f s₀ s₁} : GSValid f s₀ → GSValid f s₁ → GSValid f (.tprod s₀ s₁)
    -- FFS type formation: the witness term `e : s₀*⊗s₁` is typed at the
    -- grade-0 resurrection of the type-context `f` (source: `HasType ∅ ε e …`).
    | ker   {f e s₀ s₁} : GSValid f s₀ → GSValid f s₁
                       → GHasType (resurrect f) e (.space (.tprod (.dual s₀) s₁))
                       → GSValid f (.ker s₀ s₁ e)
    | coker {f e s₀ s₁} : GSValid f s₀ → GSValid f s₁
                       → GHasType (resurrect f) e (.space (.tprod (.dual s₀) s₁))
                       → GSValid f (.coker s₀ s₁ e)
    | img   {f e s₀ s₁} : GSValid f s₀ → GSValid f s₁
                       → GHasType (resurrect f) e (.space (.tprod (.dual s₀) s₁))
                       → GSValid f (.img s₀ s₁ e)
    | coimg {f e s₀ s₁} : GSValid f s₀ → GSValid f s₁
                       → GHasType (resurrect f) e (.space (.tprod (.dual s₀) s₁))
                       → GSValid f (.coimg s₀ s₁ e)

  /-- `f ⊢ τ : tvalid` — well-formed types with kind (source `TValid`). -/
  inductive GTValid : (Name → Option Ty) → Ty → Kind → Type
    | space {f s} : GSValid f s → GTValid f (.space s) .base
    -- Cofinite piTy: the codomain `τ₁` binds `bvar 0`, opened at fresh `y ∉ L`
    -- in the type-context extended by `y : τ₀` (at ω, i.e. type-visible).
    | piTy {f τ₀ τ₁ k₀ k₁} (L : Finset Name)
        : GTValid f τ₀ k₀
        → (∀ y, y ∉ L → GTValid (Function.update f y (some τ₀)) (Ty.openVar y τ₁) k₁)
        → GTValid f (.piTy τ₀ τ₁) (.arrow k₀ k₁)

  inductive GSubType : (Name → Option Ty) → Space → Space → Type
    | sub_ker   {f e s₀ s₁} : GSValid f s₀ → GSValid f s₁
                           → GHasType (resurrect f) e (.space (.tprod (.dual s₀) s₁))
                           → GSubType f (.ker s₀ s₁ e) s₀
    | sub_coker {f e s₀ s₁} : GSValid f s₀ → GSValid f s₁
                           → GHasType (resurrect f) e (.space (.tprod (.dual s₀) s₁))
                           → GSubType f (.coker s₀ s₁ e) s₀
    | sub_img   {f e s₀ s₁} : GSValid f s₀ → GSValid f s₁
                           → GHasType (resurrect f) e (.space (.tprod (.dual s₀) s₁))
                           → GSubType f (.img s₀ s₁ e) s₁
    | sub_coimg {f e s₀ s₁} : GSValid f s₀ → GSValid f s₁
                           → GHasType (resurrect f) e (.space (.tprod (.dual s₀) s₁))
                           → GSubType f (.coimg s₀ s₁ e) s₁

  inductive GHasType : GCtx → Term → Ty → Type

    -- `zero` (affine): types at ANY `Γ`, consuming nothing.
    | gzero {Γ s} : GSValid (typeCtxOmega Γ) s → GHasType Γ (.zero s) (.space s)

    -- `smul` (Δ-split): the operand contexts add to the conclusion's.
    | gsmul {Γ Γ₀ Γ₁ e₀ e₁ s}
        : GSValid (typeCtxOmega Γ) s
        → (∀ x, Γ x = gadd (Γ₀ x) (Γ₁ x))
        → TypeAgree Γ₀ Γ₁
        → GHasType Γ₀ e₀ (.space .real)
        → GHasType Γ₁ e₁ (.space s)
        → GHasType Γ (.smul e₀ e₁) (.space s)

    -- `add` (single-Δ): both operands share the same `Γ`.
    | gadd {Γ e₀ e₁ s}
        : GSValid (typeCtxOmega Γ) s
        → GHasType Γ e₀ (.space s)
        → GHasType Γ e₁ (.space s)
        → GHasType Γ (.add e₀ e₁) (.space s)

    -- `inner` (∅-Δ): `Γ` threaded, no linearity added.
    | ginner {Γ s}
        : GSValid (typeCtxOmega Γ) s
        → NoLin Γ
        → GHasType Γ (.inner s) (.space (.tprod (.dual s) (.dual s)))

    -- `real_lit` (∅-Δ).
    | greal_lit {Γ} (r : ℝ) : NoLin Γ → GHasType Γ (.real r) (.space .real)

    -- `app_linear` (Δ-split).
    | gapp_linear {Γ Γ₀ Γ₁ e₀ e₁ s₀ s₁}
        : GSValid (typeCtxOmega Γ) s₀
        → GSValid (typeCtxOmega Γ) s₁
        → (∀ x, Γ x = gadd (Γ₀ x) (Γ₁ x))
        → TypeAgree Γ₀ Γ₁
        → GHasType Γ₀ e₀ (.space (.tprod (.dual s₀) s₁))
        → GHasType Γ₁ e₁ (.space s₀)
        → GHasType Γ (.appL s₀ s₁ e₀ e₁) (.space s₁)

    -- `app_inner` (Δ-split).
    | gapp_inner {Γ Γ₀ Γ₁ e₀ e₁ s}
        : GSValid (typeCtxOmega Γ) s
        → (∀ x, Γ x = gadd (Γ₀ x) (Γ₁ x))
        → TypeAgree Γ₀ Γ₁
        → GHasType Γ₀ e₀ (.space (.dual s))
        → GHasType Γ₁ e₁ (.space s)
        → GHasType Γ (.appI s e₀ e₁) (.space .real)

    -- `app_nonlinear` (∅-Δ): result type is `τ₁` with `bvar 0` instantiated by `e₁`.
    | gapp_nonlinear {Γ e₀ e₁ τ₀ τ₁}
        : NoLin Γ
        → GHasType Γ e₀ (.piTy τ₀ τ₁)
        → GHasType Γ e₁ τ₀
        → GHasType Γ (.appN e₀ e₁) (Ty.instantiate e₁ τ₁)

    -- `gvar` (var_lin + var_nlin unified): `x` usable at its grade `g`, and NO
    -- OTHER linear (grade-`1`) resource left — the affine leaf discipline.
    | gvar {Γ x g τ}
        : Γ x = some (g, τ)
        → g ≠ GGrade.zero

        → (∀ y, y ≠ x → ∀ τy, Γ y ≠ some (GGrade.one, τy))
        → GHasType Γ (.var x) τ

    -- `pinv_tensor` (∅-Δ).
    | gpinv_tensor {Γ e s₀ s₁}
        : GSValid (typeCtxOmega Γ) s₀
        → GSValid (typeCtxOmega Γ) s₁
        → NoLin Γ
        → GHasType Γ e (.space (.tprod (.dual s₀) s₁))
        → GHasType Γ (.pinvT s₀ s₁ e) (.space (.tprod (.dual s₁) s₀))

    -- `pinv_dual` (∅-Δ).
    | gpinv_dual {Γ e s}
        : GSValid (typeCtxOmega Γ) s
        → NoLin Γ
        → GHasType Γ e (.space (.dual s))
        → GHasType Γ (.pinvD s e) (.space (.tprod (.dual .real) s))

    -- `dsumE` (single-Δ).
    | gdsumE {Γ e₀ e₁ s₀ s₁}
        : GSValid (typeCtxOmega Γ) s₀
        → GSValid (typeCtxOmega Γ) s₁
        → GHasType Γ e₀ (.space s₀)
        → GHasType Γ e₁ (.space s₁)
        → GHasType Γ (.dsumE e₀ e₁) (.space (.dsum s₀ s₁))

    -- `tprodE` (Δ-split).
    | gtprodE {Γ Γ₀ Γ₁ e₀ e₁ s₀ s₁}
        : GSValid (typeCtxOmega Γ) s₀
        → GSValid (typeCtxOmega Γ) s₁
        → (∀ x, Γ x = gadd (Γ₀ x) (Γ₁ x))
        → TypeAgree Γ₀ Γ₁
        → GHasType Γ₀ e₀ (.space s₀)
        → GHasType Γ₁ e₁ (.space s₁)
        → GHasType Γ (.tprodE e₀ e₁) (.space (.tprod s₀ s₁))

    -- `llam_real` (binder): extend the LINEAR context by a fresh var at grade `1`
    -- (a linear vector `y : s`, stored in `GCtx` as `some (one, .space s)`).
    | gllam_real {Γ s e} (L : Finset Name)
        : GSValid (typeCtxOmega Γ) s
        → (∀ y, y ∉ L →
            GHasType (Function.update Γ y (some (GGrade.one, .space s)))
                     (Term.openVar y e) (.space .real))
        → GHasType Γ (.llam s .real e) (.space (.dual s))

    -- `llam_tensor` (binder): non-ℝ codomain.
    | gllam_tensor {Γ s₀ s e} (L : Finset Name)
        : s ≠ .real
        → GSValid (typeCtxOmega Γ) s₀
        → GSValid (typeCtxOmega Γ) s
        → (∀ y, y ∉ L →
            GHasType (Function.update Γ y (some (GGrade.one, .space s₀)))
                     (Term.openVar y e) (.space s))
        → GHasType Γ (.llam s₀ s e) (.space (.tprod (.dual s₀) s))

    -- `embed` (∅-Δ): subspace inclusion.
    | gembed {Γ s₀ s₁}
        : GSubType (typeCtxOmega Γ) s₀ s₁
        → NoLin Γ
        → GHasType Γ (.embed s₀) (.space (.tprod (.dual s₀) s₁))

    -- `nllam` (binder): extend the TYPE/ω context by a fresh var at grade `ω`.
    | gnllam {Γ τ₀ τ₁ k₀ k₁ e} (L : Finset Name)
        : GTValid (typeCtxOmega Γ) (.piTy τ₀ τ₁) (.arrow k₀ k₁)
        → NoLin Γ
        → (∀ y, y ∉ L →
            GHasType (Function.update Γ y (some (GGrade.omega, τ₀)))
                     (Term.openVar y e) (Ty.openVar y τ₁))
        → GHasType Γ (.nllam τ₀ e) (.piTy τ₀ τ₁)

end

end GLang.Graded
