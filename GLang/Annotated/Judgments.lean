/- Source space formation, kinding, typing, and subspace judgments.
Linear and nonlinear contexts are finite maps. -/

import GLang.Annotated.Binding
import GLang.Proofs.Source.SourceLN
import Mathlib.Data.Finmap

namespace GLang

abbrev LCtx  := @Finmap Name (fun _ => Space)
abbrev NLCtx := @Finmap Name (fun _ => Ty)

/-- Inclusion of nonlinear typing contexts, preserving both names and their
    source types.  This relation is foundational: operational certificates use
    it to record that a derivation formed in an earlier source context remains
    available in a later context. -/
def NLCtxIncl (Γ Γ' : NLCtx) : Prop :=
  ∀ x τ, Γ.lookup x = some τ → Γ'.lookup x = some τ

namespace NLCtxIncl

theorem refl (Γ : NLCtx) : NLCtxIncl Γ Γ := fun _ _ h => h

theorem trans {Γ₀ Γ₁ Γ₂ : NLCtx} (h01 : NLCtxIncl Γ₀ Γ₁)
    (h12 : NLCtxIncl Γ₁ Γ₂) : NLCtxIncl Γ₀ Γ₂ :=
  fun x τ hx => h12 x τ (h01 x τ hx)

theorem insert_right {Γ₀ Γ : NLCtx} (h : NLCtxIncl Γ₀ Γ) {x : Name}
    (hx : x ∉ Γ) (τ : Ty) : NLCtxIncl Γ₀ (Finmap.insert x τ Γ) := by
  intro y υ hy
  by_cases hyx : y = x
  · have hm : y ∈ Γ := Finmap.mem_of_lookup_eq_some (h y υ hy)
    exact absurd (hyx ▸ hm) hx
  · simpa [Finmap.lookup_insert_of_ne _ hyx] using h y υ hy

/-- Membership transports along an inclusion. -/
theorem mem_of {Γ Γ' : NLCtx} (h : NLCtxIncl Γ Γ') {x : Name} (hx : x ∈ Γ) : x ∈ Γ' := by
  obtain ⟨τ, hτ⟩ := Finmap.mem_iff.mp hx
  exact Finmap.mem_of_lookup_eq_some (h x τ hτ)

/-- Disjointness from a larger right operand restricts to a smaller one. -/
theorem disjoint_right_of {A Γ Γ' : NLCtx} (hd : Finmap.Disjoint A Γ')
    (h : NLCtxIncl Γ Γ') : Finmap.Disjoint A Γ :=
  fun x hxA hxΓ => hd x hxA (h.mem_of hxΓ)

end NLCtxIncl

/-- Promote a linear context fragment to a non-linear one by wrapping each
    space `s` as a type `.space s`. Used by the `.promote` typing rule. -/
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

/-- `LCtx.toNL` preserves the underlying multiset of keys. -/
theorem LCtx.toNL_entries_keys (lin : LCtx) :
    lin.toNL.entries.keys = lin.entries.keys := by
  show (lin.entries.map _).map Sigma.fst = lin.entries.map Sigma.fst
  rw [Multiset.map_map]; rfl

/-- `LCtx.toNL` preserves the (finset of) keys. -/
@[simp] theorem LCtx.toNL_keys (lin : LCtx) :
    lin.toNL.keys = lin.keys := by
  unfold Finmap.keys
  congr 1
  exact LCtx.toNL_entries_keys lin

/-- `LCtx.toNL` lookup: if `lin.lookup x = some s`, then
    `lin.toNL.lookup x = some (.space s)`. -/
theorem LCtx.toNL_lookup (lin : LCtx) (x : Name) (s : Space)
    (h : lin.lookup x = some s) : lin.toNL.lookup x = some (.space s) := by
  rw [Finmap.lookup_eq_some_iff] at h ⊢
  show (⟨x, .space s⟩ : Σ _ : Name, Ty) ∈
        lin.entries.map (fun e : Σ _ : Name, Space => ⟨e.1, Ty.space e.2⟩)
  rw [Multiset.mem_map]
  exact ⟨⟨x, s⟩, h, rfl⟩

/-- Membership in `LCtx.toNL` ≡ membership in the underlying `LCtx`. -/
theorem LCtx.mem_toNL_iff (lin : LCtx) (x : Name) :
    x ∈ lin.toNL ↔ x ∈ lin := by
  rw [← Finmap.mem_keys, ← Finmap.mem_keys, LCtx.toNL_keys]

def LCtx.IsDisjUnion (Δ₀ Δ₁ Δ : LCtx) : Prop :=
  Δ = Δ₀ ∪ Δ₁ ∧ Finmap.Disjoint Δ₀ Δ₁

/-- Barendregt-style freshness premise for `.promote`: names in `lin`
    don't appear free in any type mentioned by the surrounding context
    (Δ, lin's own spaces, ε'). Required to make the inner `CtxWF`
    derivable for the linearity meta-theorem. -/
structure PromoteFresh (lin : LCtx) (Δ : LCtx) (ε : NLCtx) : Prop where
  fresh_Δ   : ∀ y, y ∈ lin →
              ∀ x s, Δ.lookup x = some s → y ∉ Space.fv s
  fresh_lin : ∀ y, y ∈ lin →
              ∀ x s, lin.lookup x = some s → y ∉ Space.fv s
  /-- Strengthened from "only `.space s` entries" to "all entries":
      lin's names don't appear in any type bound in ε. Needed for
      `nl_fv_in_ε` of the inner context to inherit from the outer ε
      (which is `lin.toNL ∪ ε'`). -/
  fresh_ε   : ∀ y, y ∈ lin →
              ∀ x τ, ε.lookup x = some τ → y ∉ Ty.fv τ

mutual

  inductive SValid : NLCtx → Space → Type
    -- `⊥ : svalid`
    | empty {ε} : SValid ε .empty
    -- `ℝ : svalid`
    | real {ε} : SValid ε .real
    -- `s* : svalid`
    | dual {ε s} : SValid ε s → SValid ε (.dual s)
    -- `s₀ ⊕ s₁ : svalid`
    | dsum {ε s₀ s₁} : SValid ε s₀ → SValid ε s₁ → SValid ε (.dsum s₀ s₁)
    -- `s₀ ⊗ s₁ : svalid`
    | tprod {ε s₀ s₁} : SValid ε s₀ → SValid ε s₁ → SValid ε (.tprod s₀ s₁)

    | ker   {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                       → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                       → SValid ε (.ker s₀ s₁ e)
    | coker {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                       → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                       → SValid ε (.coker s₀ s₁ e)
    | img   {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                       → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                       → SValid ε (.img s₀ s₁ e)
    | coimg {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                       → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                       → SValid ε (.coimg s₀ s₁ e)

  inductive TValid : NLCtx → Ty → Kind → Type
    -- `s : tvalid` of kind `*` from `s : svalid`.
    | space {ε s}              : SValid ε s → TValid ε (.space s) .base

    | piTy  {ε τ₀ τ₁ k₀ k₁} (L : Finset Name)
        : TValid ε τ₀ k₀
        → (∀ y, y ∉ L → TValid (Finmap.insert y τ₀ ε) (Ty.openVar y τ₁) k₁)
        → TValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁)

  inductive SubType : NLCtx → Space → Space → Type
    -- SValid premises on s₀ and s₁ added for the same reason as in
    -- `SValid.ker` etc. — redundant but pragmatic.
    | sub_ker   {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                           → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                           → SubType ε (.ker s₀ s₁ e) s₀
    | sub_coker {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                           → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                           → SubType ε (.coker s₀ s₁ e) s₀
    | sub_img   {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                           → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                           → SubType ε (.img s₀ s₁ e) s₁
    | sub_coimg {ε e s₀ s₁} : SValid ε s₀ → SValid ε s₁
                           → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
                           → SubType ε (.coimg s₀ s₁ e) s₁

  inductive HasType : LCtx → NLCtx → Term → Ty → Type

    -- `(∅,ε) ⊢ s : svalid` ⊢ `(Δ,ε) ⊢ 0_s : s`
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

    -- `(∅,ε) ⊢ s : svalid` ⊢ `(∅,ε) ⊢ inner_s : s*⊗s*`
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
        → HasType (Δ₀ ∪ Δ₁) ε (.appL s₀ s₁ e₀ e₁) (.space s₁)

    | app_inner {Δ₀ Δ₁ ε e₀ e₁ s}
        : SValid ε s
        → Finmap.Disjoint Δ₀ Δ₁
        → HasType Δ₀ ε e₀ (.space (.dual s))
        → HasType Δ₁ ε e₁ (.space s)
        → HasType (Δ₀ ∪ Δ₁) ε (.appI s e₀ e₁) (.space .real)

    | app_nonlinear {ε e₀ e₁ τ₀ τ₁}
        : HasType ∅ ε e₀ (.piTy τ₀ τ₁)
        → HasType ∅ ε e₁ τ₀
        → HasType ∅ ε (.appN e₀ e₁) (Ty.instantiate e₁ τ₁)

    -- Linear variable: `Δ = {(x,s)}` (a singleton Finmap) ⊢ `(Δ,ε) ⊢ x : s`.
    -- ε arbitrary.
    | var_lin {ε x s}
        : HasType (Finmap.singleton x s) ε (.var x) (.space s)

    | var_nlin {ε x τ}
        : ε.lookup x = some τ
        → HasType ∅ ε (.var x) τ

    | pinv_tensor {ε e s₀ s₁}
        : SValid ε s₀
        → SValid ε s₁
        → HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))
        → HasType ∅ ε (.pinvT s₀ s₁ e) (.space (.tprod (.dual s₁) s₀))

    -- Pseudo-inverse on a dual: e : s* ⊢ e† : ℝ*⊗s. Empty Δ.
    | pinv_dual {ε e s}
        : SValid ε s
        → HasType ∅ ε e (.space (.dual s))
        → HasType ∅ ε (.pinvD s e) (.space (.tprod (.dual .real) s))

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
        → HasType Δ ε (.llam s .real e) (.space (.dual s))

    -- Linear λ to a non-ℝ codomain. Cofinite, opening into the linear Δ.
    -- The `s ≠ .real` premise keeps this disjoint from `llam_real`.
    | llam_tensor {Δ ε s₀ s e} (L : Finset Name)
        : s ≠ .real
        → SValid ε s₀
        → SValid ε s
        → (∀ y, y ∉ L → HasType (Finmap.insert y s₀ Δ) ε (Term.openVar y e) (.space s))
        → HasType Δ ε (.llam s₀ s e) (.space (.tprod (.dual s₀) s))

    -- Subspace inclusion: `s₀ ≤ s₁` ⊢ `embed_s₀ : s₀*⊗s₁`. Empty Δ.
    | embed {ε s₀ s₁}
        : SubType ε s₀ s₁
        → HasType ∅ ε (.embed s₀) (.space (.tprod (.dual s₀) s₁))

    | nllam {ε τ₀ τ₁ k₀ k₁ e} (L : Finset Name)
        : TValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁)
        → (∀ y, y ∉ L → HasType ∅ (Finmap.insert y τ₀ ε) (Term.openVar y e) (Ty.openVar y τ₁))
        → HasType ∅ ε (.nllam τ₀ e) (.piTy τ₀ τ₁)

end

/-! ## Linear-lambda result inversion

The nonlinear evaluator works at frame bases, whose source type is a dependent
function type.  The following small inversion records the typing boundary
between that route and source linear lambdas: even through `promote`, a
`Term.llam` can only have a space type.
-/

/-- Every well-typed source linear lambda has a space result type. -/
def HasType.llam_isSpace
    {Δ : LCtx} {ε : NLCtx} {s₀ s₁ : Space} {body : Term} {τ : Ty}
    (h : HasType Δ ε (.llam s₀ s₁ body) τ) : ∃ s, τ = .space s :=
  match h with
  | .llam_real _ _ _ => ⟨_, rfl⟩
  | .llam_tensor _ _ _ _ _ => ⟨_, rfl⟩
  | .promote _ _ _ _ h' => HasType.llam_isSpace h'

/-- Consequently, a source linear lambda cannot inhabit a nonlinear function type. -/
theorem HasType.llam_not_pi
    {Δ : LCtx} {ε : NLCtx} {s₀ s₁ : Space} {body : Term} {τ₀ τ₁ : Ty}
    (h : HasType Δ ε (.llam s₀ s₁ body) (.piTy τ₀ τ₁)) : False := by
  obtain ⟨s, hs⟩ := h.llam_isSpace
  cases hs

/-! ## Typing of the derived term helpers (`Term.lembd` / `Term.lproj`).

`Term.lembd`/`Term.lproj` are `@[reducible]` abbreviations
(`Syntax.lean`), so these lemmas are the underlying `.embed` / `.pinvT∘.embed`
rules at the helper's (defeq) type. -/

def HasType.lembd {ε : NLCtx} {s₀ s₁ : Space} (h : SubType ε s₀ s₁) :
    HasType ∅ ε (Term.lembd s₀) (.space (.tprod (.dual s₀) s₁)) :=
  HasType.embed h

def HasType.lproj {ε : NLCtx} {s_sub s_amb : Space}
    (h₀ : SValid ε s_sub) (h₁ : SValid ε s_amb) (hsub : SubType ε s_sub s_amb) :
    HasType ∅ ε (Term.lproj s_sub s_amb)
      (.space (.tprod (.dual s_amb) s_sub)) :=
  HasType.pinv_tensor h₀ h₁ (HasType.embed hsub)

end GLang
