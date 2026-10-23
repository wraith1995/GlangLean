import GLang.Surface.Binding
import Mathlib.Data.Finmap

namespace GLang.Surface

abbrev LCtx  := @Finmap Name (fun _ => Space)
abbrev NLCtx := @Finmap Name (fun _ => Ty)

def LCtx.toNL (lin : LCtx) : NLCtx where
  entries := lin.entries.map (fun e : Σ _ : Name, Space =>
    (⟨e.1, Ty.space e.2⟩ : Σ _ : Name, Ty))
  nodupKeys := by
    have h : (lin.entries.map (fun e : Σ _ : Name, Space =>
              (⟨e.1, Ty.space e.2⟩ : Σ _ : Name, Ty))).keys = lin.entries.keys := by
      show (lin.entries.map _).map Sigma.fst = lin.entries.map Sigma.fst
      rw [Multiset.map_map]; rfl
    rw [← Multiset.nodup_keys, h]
    exact Multiset.nodup_keys.mpr lin.nodupKeys

structure PromoteFresh (lin : LCtx) (Δ : LCtx) (ε : NLCtx) : Prop where
  fresh_Δ   : ∀ y, y ∈ lin →
              ∀ x s, Δ.lookup x = some s → y ∉ Space.fv s
  fresh_lin : ∀ y, y ∈ lin →
              ∀ x s, lin.lookup x = some s → y ∉ Space.fv s

  fresh_ε   : ∀ y, y ∈ lin →
              ∀ x τ, ε.lookup x = some τ → y ∉ Ty.fv τ

mutual

  inductive SValid : NLCtx → Space → Type

    | empty {ε} : SValid ε .empty

    | real {ε} : SValid ε .real

    | dual {ε s} : SValid ε s → SValid ε (.dual s)

    | dsum {ε s₀ s₁} : SValid ε s₀ → SValid ε s₁ → SValid ε (.dsum s₀ s₁)

    | tprod {ε s₀ s₁} : SValid ε s₀ → SValid ε s₁ → SValid ε (.tprod s₀ s₁)

    | ker   {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                       → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                       → SValid ε (.ker e)
    | coker {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                       → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                       → SValid ε (.coker e)
    | img   {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                       → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                       → SValid ε (.img e)
    | coimg {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                       → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                       → SValid ε (.coimg e)

  inductive TValid : NLCtx → Ty → Kind → Type

    | space {ε s}              : SValid ε s → TValid ε (.space s) .base

    | piTy  {ε τ₀ τ₁ k₀ k₁} (L : Finset Name)
        : TValid ε τ₀ k₀
        → (∀ y, y ∉ L → TValid (Finmap.insert y τ₀ ε) (Ty.openVar y τ₁) k₁)
        → TValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁)

  inductive SubType : NLCtx → Space → Space → Type

    | sub_ker   {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                           → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                           → SubType ε (.ker e) s₀
    | sub_coker {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                           → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                           → SubType ε (.coker e) s₀
    | sub_img   {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                           → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                           → SubType ε (.img e) s₁
    | sub_coimg {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                           → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                           → SubType ε (.coimg e) s₁

  inductive HasType : LCtx → NLCtx → Term → Ty → Type

    | zero {Δ ε s} : SValid ε s → HasType Δ ε (.zero s) (.space s)

    | smul {Δ₀ Δ₁ ε e₀ e₁ s}
        : SValid ε s
        → Finmap.Disjoint Δ₀ Δ₁
        → HasType Δ₀ ε e₀ (.space .real)
        → HasType Δ₁ ε e₁ (.space s)
        → HasType (Δ₀ ∪ Δ₁) ε (.smul e₀ e₁) (.space s)

    | add {Δ ε e₀ e₁ s}
        : SValid ε s
        → HasType Δ ε e₀ (.space s)
        → HasType Δ ε e₁ (.space s)
        → HasType Δ ε (.add e₀ e₁) (.space s)

    | inner {ε s}
        : SValid ε s
        → HasType ∅ ε (.inner s) (.space (.tprod (.dual s) (.dual s)))

    | real_lit {ε} (r : ℝ) : HasType ∅ ε (.real r) (.space .real)

    | app_linear {Δ₀ Δ₁ ε e₀ e₁ s₀ s₁}
        : SValid ε s₀
        → SValid ε s₁
        → Finmap.Disjoint Δ₀ Δ₁
        → HasType Δ₀ ε e₀ (.space (.tprod (.dual s₀) s₁))
        → HasType Δ₁ ε e₁ (.space s₀)
        → HasType (Δ₀ ∪ Δ₁) ε (.app e₀ e₁) (.space s₁)

    | app_inner {Δ₀ Δ₁ ε e₀ e₁ s}
        : SValid ε s
        → Finmap.Disjoint Δ₀ Δ₁
        → HasType Δ₀ ε e₀ (.space (.dual s))
        → HasType Δ₁ ε e₁ (.space s)
        → HasType (Δ₀ ∪ Δ₁) ε (.app e₀ e₁) (.space .real)

    | app_nonlinear {ε e₀ e₁ τ₀ τ₁}
        : HasType ∅ ε e₀ (.piTy τ₀ τ₁)
        → HasType ∅ ε e₁ τ₀
        → HasType ∅ ε (.app e₀ e₁) (Ty.instantiate e₁ τ₁)

    | var_lin {ε x s}
        : HasType (Finmap.singleton x s) ε (.var x) (.space s)

    | var_nlin {ε x τ}
        : ε.lookup x = some τ
        → HasType ∅ ε (.var x) τ

    | pinv_tensor {ε e s₀ s₁}
        : SValid ε s₀
        → SValid ε s₁
        → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
        → HasType ∅ ε (.pinv e) (.space (.tprod (.dual s₁) s₀))

    | pinv_dual {ε e s}
        : SValid ε s
        → HasType ∅ ε e (.space (.dual s))
        → HasType ∅ ε (.pinv e) (.space (.tprod (.dual .real) s))

    | promote {Δ ε' e τ} (lin : LCtx)
        (_h_disjΔ : Finmap.Disjoint lin Δ)
        (_h_disjε : Finmap.Disjoint lin.toNL ε')
        (_h_fresh : PromoteFresh lin Δ ε')

        : HasType (lin ∪ Δ) ε' e τ
        → HasType Δ (lin.toNL ∪ ε') e τ

    | dsumE {Δ ε e₀ e₁ s₀ s₁}
        : SValid ε s₀
        → SValid ε s₁
        → HasType Δ ε e₀ (.space s₀)
        → HasType Δ ε e₁ (.space s₁)
        → HasType Δ ε (.dsumE e₀ e₁) (.space (.dsum s₀ s₁))

    | tprodE {Δ₀ Δ₁ ε e₀ e₁ s₀ s₁}
        : SValid ε s₀
        → SValid ε s₁
        → Finmap.Disjoint Δ₀ Δ₁
        → HasType Δ₀ ε e₀ (.space s₀)
        → HasType Δ₁ ε e₁ (.space s₁)
        → HasType (Δ₀ ∪ Δ₁) ε (.tprodE e₀ e₁) (.space (.tprod s₀ s₁))

    | llam_real {Δ ε s e} (L : Finset Name)
        : SValid ε s
        → (∀ y, y ∉ L → HasType (Finmap.insert y s Δ) ε (Term.openVar y e) (.space .real))
        → HasType Δ ε (.llam s e) (.space (.dual s))

    | llam_tensor {Δ ε s₀ s e} (L : Finset Name)
        : s ≠ .real
        → SValid ε s₀
        → SValid ε s
        → (∀ y, y ∉ L → HasType (Finmap.insert y s₀ Δ) ε (Term.openVar y e) (.space s))
        → HasType Δ ε (.llam s₀ e) (.space (.tprod (.dual s₀) s))

    | embed {ε s₀ s₁}
        : SubType ε s₀ s₁
        → HasType ∅ ε (.embed s₀) (.space (.tprod (.dual s₀) s₁))

    | nllam {ε τ₀ τ₁ k₀ k₁ e} (L : Finset Name)
        : TValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁)
        → (∀ y, y ∉ L → HasType ∅ (Finmap.insert y τ₀ ε) (Term.openVar y e) (Ty.openVar y τ₁))
        → HasType ∅ ε (.nllam τ₀ e) (.piTy τ₀ τ₁)

end

inductive Basis.BasisValid : NLCtx → Basis → Prop
  | empty {ε} : Basis.BasisValid ε .empty
  | one   {ε} : Basis.BasisValid ε .one
  | dual  {ε b} : Basis.BasisValid ε b →
      Basis.tof b = .space (Basis.sof b) →
      Basis.BasisValid ε (.dual b)
  | dsum  {ε b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space (Basis.sof b₀) →
      Basis.tof b₁ = .space (Basis.sof b₁) →
      Basis.BasisValid ε (.dsum b₀ b₁)
  | tprod {ε b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space (Basis.sof b₀) →
      Basis.tof b₁ = .space (Basis.sof b₁) →
      Basis.BasisValid ε (.tprod b₀ b₁)
  | proj_ker {ε s₀ s₁ e b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space s₀ → Basis.tof b₁ = .space s₁ →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.proj (.ker e) b₀ b₁)
  | proj_coker {ε s₀ s₁ e b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space s₀ → Basis.tof b₁ = .space s₁ →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.proj (.coker e) b₀ b₁)
  | proj_img {ε s₀ s₁ e b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space s₀ → Basis.tof b₁ = .space s₁ →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.proj (.img e) b₀ b₁)
  | proj_coimg {ε s₀ s₁ e b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space s₀ → Basis.tof b₁ = .space s₁ →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.proj (.coimg e) b₀ b₁)
  | image {ε b s₀ s₁ e} : Basis.BasisValid ε b → Basis.sof b = .coker e →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.image b)
  | terms {ε s es b} : Basis.BasisValid ε b → Basis.tof b = .space s →
      Nonempty (SValid ε s) →
      (∀ e ∈ es, Nonempty (HasType ∅ ε e (.space s))) →
      es ≠ [] →
      Basis.BasisValid ε (.terms es b)
  | frame {ε b₀ b₁} (L : Finset Name) :
      Basis.BasisValid ε b₀ →
      (∀ y, y ∉ L →
        Basis.BasisValid (Finmap.insert y (Basis.tof b₀) ε) (Basis.openVar y b₁)) →
      Basis.BasisValid ε (.frame b₀ b₁)

end GLang.Surface
