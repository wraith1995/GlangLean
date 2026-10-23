

import GLang.Annotated.Binding
import GLang.Annotated.Judgments
import GLang.Annotated.Denotation
import GLang.Proofs.Source.Wellformed
import GLang.Proofs.Source.Soundness
import GLang.Numerics.Pseudoinverse.MoorePenroseChar
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

namespace GLang

open scoped TensorProduct

/-- Helper: if `x ∉ ε` and `SValid ε s`, then `x ∉ Space.fv s`.
    Captures the chain `h_fresh ∘ Finmap.mem_keys.mp ∘ SValid.fv_closure`
    that appears repeatedly throughout this file's FV-irrelevance setups. -/
private lemma SValid.notMem_fv_of_notMem_ε {ε : NLCtx} {s : Space} {x : Name}
    (sv : SValid ε s) (h_fresh : x ∉ ε) : x ∉ Space.fv s :=
  fun hin => h_fresh (Finmap.mem_keys.mp (sv.fv_closure hin))

/-! Derived source term constructors for inner-product operations. -/

namespace Term

/-- Reserved binder names for derived-term definitions. Prefixed with `$`
    to keep them syntactically distinct from user-chosen names; capture-
    naive substitution at `.appN` won't alias them. -/
private def x0 : Name := "$x0"
private def x1 : Name := "$x1"

def kembed0 (s₀ s₁ : Space) : Term :=
  .llam s₀ (.dsum s₀ s₁) (.dsumE (.bvar 0) (.zero s₁))

def kembed1 (s₀ s₁ : Space) : Term :=
  .llam s₁ (.dsum s₀ s₁) (.dsumE (.zero s₀) (.bvar 0))

def kproj0 (s₀ s₁ : Space) : Term :=
  .pinvT s₀ (.dsum s₀ s₁) (kembed0 s₀ s₁)

def kproj1 (s₀ s₁ : Space) : Term :=
  .pinvT s₁ (.dsum s₀ s₁) (kembed1 s₀ s₁)

def flat (s : Space) : Term :=
  .llam s (.dual s) (.appL s (.dual s) (.inner s) (.bvar 0))

def sharp (s : Space) : Term :=
  .pinvT s (.dual s) (flat s)

@[reducible] def projSubspace (s_sub s_amb : Space) : Term :=
  Term.lproj s_sub s_amb

/-- Apply `inner_s` as a bilinear form: returns `⟨e₀, e₁⟩_s` of type
    `.real`. Decoded as `appI s (appL s s* inner_s e₀) e₁`. -/
def innerApp (s : Space) (e₀ e₁ : Term) : Term :=
  .appI s (.appL s (.dual s) (.inner s) e₀) e₁

/-- `openRec` pushes through `innerApp` keeping it folded (LN convenience
    for the cofinite typing/denotation proofs). -/
theorem openRec_innerApp (k : Nat) (u : Term) (s : Space) (e₀ e₁ : Term) :
    Term.openRec k u (innerApp s e₀ e₁) =
      innerApp (Space.openRec k u s) (Term.openRec k u e₀) (Term.openRec k u e₁) := rfl

private def g_name : Name := "$g"
private def a_name : Name := "$a"
private def b_name : Name := "$b"
private def p_name : Name := "$p"

def curry2NonReal (sA sB sRest : Space) : Term :=
  let g_ty : Space := .tprod (.dual (.tprod sA sB)) sRest
  let body_ty_outer : Space := .tprod (.dual sA) (.tprod (.dual sB) sRest)
  let body_ty_mid : Space := .tprod (.dual sB) sRest
  .llam g_ty body_ty_outer
    (.llam sA body_ty_mid
      (.llam sB sRest
        (.appL (.tprod sA sB) sRest
          (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0)))))

def curry2Real (sA sB : Space) : Term :=
  let g_ty : Space := .dual (.tprod sA sB)
  let body_ty_outer : Space := .tprod (.dual sA) (.dual sB)
  .llam g_ty body_ty_outer
    (.llam sA (.dual sB)
      (.llam sB .real
        (.appI (.tprod sA sB)
          (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0)))))

def uncurry2NonReal (sA sB sRest : Space) : Term :=
  let curried_ty : Space := .tprod (.dual sA) (.tprod (.dual sB) sRest)
  let uncurried_ty : Space := .tprod (.dual (.tprod sA sB)) sRest
  .pinvT uncurried_ty curried_ty (curry2NonReal sA sB sRest)

def uncurry2Real (sA sB : Space) : Term :=
  let curried_ty : Space := .tprod (.dual sA) (.dual sB)
  let uncurried_ty : Space := .dual (.tprod sA sB)
  .pinvT uncurried_ty curried_ty (curry2Real sA sB)

/-- Apply the non-real uncurry to a Term `f : sA*⊗sB*⊗sRest`, producing
    a Term of type `(sA⊗sB)*⊗sRest`. -/
def applyUncurry2NonReal (sA sB sRest : Space) (f : Term) : Term :=
  let curried_ty : Space := .tprod (.dual sA) (.tprod (.dual sB) sRest)
  let uncurried_ty : Space := .tprod (.dual (.tprod sA sB)) sRest
  .appL curried_ty uncurried_ty (uncurry2NonReal sA sB sRest) f

/-- Apply the real uncurry to a Term `f : sA*⊗sB*`, producing a Term of
    type `(sA⊗sB)*`. -/
def applyUncurry2Real (sA sB : Space) (f : Term) : Term :=
  let curried_ty : Space := .tprod (.dual sA) (.dual sB)
  let uncurried_ty : Space := .dual (.tprod sA sB)
  .appL curried_ty uncurried_ty (uncurry2Real sA sB) f

end Term

@[reducible] def Space.iofSubBody (sub s_amb : Space) : Term :=
  .llam sub (.dual sub)
    (.llam sub .real
      (Term.innerApp s_amb
        (Term.embedApp sub s_amb (.bvar 1))
        (Term.embedApp sub s_amb (.bvar 0))))

noncomputable def Space.iof : Space → Term

  | .empty =>
      .zero (.tprod (.dual .empty) (.dual .empty))
  -- `\iof{ℝ} = λ(x₀, x₁) → x₀ · x₁`. Two nested linear lambdas;
  -- inner uses `llam_real`, outer uses `llam_tensor`.
  | .real =>
      .llam .real (.dual .real)
        (.llam .real .real
          (.smul (.bvar 1) (.bvar 0)))
  -- `\iof{s₀ ⊕ s₁} = λ(x₀, x₁) → ⟨π₀ x₀, π₀ x₁⟩ + ⟨π₁ x₀, π₁ x₁⟩`.
  | .dsum s₀ s₁ =>
      let pi0 := Term.kproj0 s₀ s₁
      let pi1 := Term.kproj1 s₀ s₁
      .llam (.dsum s₀ s₁) (.dual (.dsum s₀ s₁))
        (.llam (.dsum s₀ s₁) .real
          (.add
            (Term.innerApp s₀
              (.appL (.dsum s₀ s₁) s₀ pi0 (.bvar 1))
              (.appL (.dsum s₀ s₁) s₀ pi0 (.bvar 0)))
            (Term.innerApp s₁
              (.appL (.dsum s₀ s₁) s₁ pi1 (.bvar 1))
              (.appL (.dsum s₀ s₁) s₁ pi1 (.bvar 0)))))

  | .tprod s₀ s₁ =>
      -- F: the 4-arg inner lambda. Codomain annotations track the body
      -- type at each level (not the encoded tensor — `.llam x s₀ s e`
      -- annotates `s = type of body`, distinct from the lambda's own
      -- encoded type `s₀*⊗s`):
      --   innermost: body : ℝ        → codomain `.real`
      --   middle:    body : s₁*       → codomain `.dual s₁`
      --   outer-mid: body : s₀*⊗s₁*   → codomain `.tprod (.dual s₀) (.dual s₁)`
      --   outermost: body : s₁*⊗s₀*⊗s₁* → codomain `.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁))`
      let F : Term :=
        .llam s₀
          (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁)))
          (.llam s₁
            (.tprod (.dual s₀) (.dual s₁))
            (.llam s₀ (.dual s₁)
              (.llam s₁ .real
                (.smul
                  (Term.innerApp s₀ (.bvar 3) (.bvar 1))
                  (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))
      -- step1: fuse first two args of F. Type (s₀⊗s₁)*⊗s₀*⊗s₁*.
      let step1 : Term :=
        Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁)) F
      -- Outer eta: λ p. uncurry-Real (step1 applied to p).
      .llam (.tprod s₀ s₁) (.dual (.tprod s₀ s₁))
        (Term.applyUncurry2Real s₀ s₁
          (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
            step1
            (.bvar 0)))
  -- `\iof{s*} = λ(x₀, x₁) → ⟨♯ x₀, ♯ x₁⟩_s`. Sharp encodes `s* → s` as
  -- `s** ⊗ s`; .appL with s₀ := s*, s₁ := s takes input s* and gives s.
  | .dual s =>
      let sharp_s := Term.sharp s
      .llam (.dual s) (.dual (.dual s))
        (.llam (.dual s) .real
          (Term.innerApp s
            (.appL (.dual s) s sharp_s (.bvar 1))
            (.appL (.dual s) s sharp_s (.bvar 0))))
  -- `\iof{Ker(e)} = λ(x₀, x₁) → ⟨embed x₀, embed x₁⟩_{s₀}`. The
  -- subspace inclusion is `embed_{Ker(e)} : Ker(e)* ⊗ s₀`; appL with
  -- s₀_app := Ker(e), s₁_app := s₀ applies it.
  -- `\iof{Ker(e)} = λ(x₀, x₁) → ⟨embed x₀, embed x₁⟩_{s₀}`: the ambient
  -- inner product pulled back along `embed_{Ker(e)} : Ker(e)* ⊗ s₀`.
  -- Ker/CoKer embed into the domain ambient `s₀`; Img/CoImg into `s₁`.
  | .ker s₀ s₁ e   => Space.iofSubBody (Space.ker s₀ s₁ e) s₀
  | .coker s₀ s₁ e => Space.iofSubBody (Space.coker s₀ s₁ e) s₀
  | .img s₀ s₁ e   => Space.iofSubBody (Space.img s₀ s₁ e) s₁
  | .coimg s₀ s₁ e => Space.iofSubBody (Space.coimg s₀ s₁ e) s₁

/-- Binder names used anywhere in `Space.iof` or its derived-term
    dependencies. Required fresh against ε for typing to succeed. -/
structure IofFresh (ε : NLCtx) : Prop where
  fresh_x0 : Term.x0 ∉ ε
  fresh_x1 : Term.x1 ∉ ε
  fresh_y00 : ("$y00" : Name) ∉ ε
  fresh_y01 : ("$y01" : Name) ∉ ε
  fresh_y10 : ("$y10" : Name) ∉ ε
  fresh_y11 : ("$y11" : Name) ∉ ε
  fresh_g : Term.g_name ∉ ε
  fresh_a : Term.a_name ∉ ε
  fresh_b : Term.b_name ∉ ε
  fresh_p : Term.p_name ∉ ε

/-! ## Step 1 — typing lemmas. -/

namespace Term

/-- `Finmap.insert x s ∅ = Finmap.singleton x s` (LN: a singleton linear
    context arising from opening a 1-binder lambda). -/
theorem insert_empty_eq_singleton (x : Name) (s : Space) :
    (Finmap.insert x s ∅ : LCtx) = Finmap.singleton x s := by
  apply Finmap.ext_lookup
  intro a
  by_cases ha : a = x
  · subst ha; rw [Finmap.lookup_insert, Finmap.lookup_singleton_eq]
  · rw [Finmap.lookup_insert_of_ne _ ha, Finmap.lookup_empty]
    have h_not_mem : a ∉ (Finmap.singleton x s : LCtx) := by
      rw [Finmap.mem_singleton]; exact ha
    exact (Finmap.lookup_eq_none.mpr h_not_mem).symm

/-- `(∅, ε) ⊢ kembed0 s₀ s₁ : s₀* ⊗ (s₀ ⊕ s₁)`. Note `def` (not `theorem`)
    since `HasType` is `Type`, not `Prop` — a typing "proof" is the
    underlying typing derivation, which is data.  -/
noncomputable def kembed0_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType ∅ ε (kembed0 s₀ s₁)
      (.space (.tprod (.dual s₀) (.dsum s₀ s₁))) :=
  HasType.llam_tensor ∅
    (by intro h; cases h) sv₀ (SValid.dsum sv₀ sv₁)
    (fun y _ => by
      simp only [Term.openVar, Term.openRec,
        Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
      rw [Term.insert_empty_eq_singleton y s₀]
      exact HasType.dsumE sv₀ sv₁ HasType.var_lin (HasType.zero sv₁))

/-- `(∅, ε) ⊢ kembed1 s₀ s₁ : s₁* ⊗ (s₀ ⊕ s₁)`. -/
noncomputable def kembed1_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType ∅ ε (kembed1 s₀ s₁)
      (.space (.tprod (.dual s₁) (.dsum s₀ s₁))) :=
  HasType.llam_tensor ∅
    (by intro h; cases h) sv₁ (SValid.dsum sv₀ sv₁)
    (fun y _ => by
      simp only [Term.openVar, Term.openRec,
        Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
      rw [Term.insert_empty_eq_singleton y s₁]
      exact HasType.dsumE sv₀ sv₁ (HasType.zero sv₀) HasType.var_lin)

/-- `(∅, ε) ⊢ kproj0 s₀ s₁ : (s₀ ⊕ s₁)* ⊗ s₀`. -/
noncomputable def kproj0_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType ∅ ε (kproj0 s₀ s₁)
      (.space (.tprod (.dual (.dsum s₀ s₁)) s₀)) :=
  HasType.pinv_tensor sv₀ (SValid.dsum sv₀ sv₁)
    (kembed0_hasType sv₀ sv₁)

/-- `(∅, ε) ⊢ kproj1 s₀ s₁ : (s₀ ⊕ s₁)* ⊗ s₁`. -/
noncomputable def kproj1_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType ∅ ε (kproj1 s₀ s₁)
      (.space (.tprod (.dual (.dsum s₀ s₁)) s₁)) :=
  HasType.pinv_tensor sv₁ (SValid.dsum sv₀ sv₁)
    (kembed1_hasType sv₀ sv₁)

/-- Helper: `Finmap.insert x s ∅ = ∅ ∪ Finmap.singleton x s`. -/
private theorem insert_empty_eq_union_singleton (x : Name) (s : Space) :
    (Finmap.insert x s ∅ : LCtx) = ∅ ∪ Finmap.singleton x s := by
  rw [Finmap.empty_union]
  apply Finmap.ext_lookup
  intro a
  by_cases ha : a = x
  · subst ha; rw [Finmap.lookup_insert, Finmap.lookup_singleton_eq]
  · rw [Finmap.lookup_insert_of_ne _ ha, Finmap.lookup_empty,
        Finmap.lookup_eq_none.mpr (by rw [Finmap.mem_singleton]; exact ha)]

/-- `(∅, ε) ⊢ flat s : s* ⊗ s*`. Represents the Riesz map `s → s*`. -/
noncomputable def flat_hasType {ε : NLCtx} {s : Space}
    (sv : SValid ε s) :
    HasType ∅ ε (flat s)
      (.space (.tprod (.dual s) (.dual s))) :=
  -- Codomain (.dual s) ≠ .real (constructor mismatch). Use llam_tensor.
  HasType.llam_tensor ∅
    (by intro h; cases h) sv (SValid.dual sv)
    (fun y _ => by
      simp only [Term.openVar, Term.openRec, Space.openRec_lc (SValid.lc sv),
        Space.openRec_lc (SValid.lc (SValid.dual sv)), if_true]
      rw [insert_empty_eq_union_singleton y s]
      exact HasType.app_linear sv (SValid.dual sv)
        (by intro k hk₀ _; exact absurd hk₀ Finmap.notMem_empty)
        (HasType.inner sv)
        HasType.var_lin)

/-- `(∅, ε) ⊢ sharp s : (s*)* ⊗ s`. Represents the inverse Riesz `s* → s`. -/
noncomputable def sharp_hasType {ε : NLCtx} {s : Space}
    (sv : SValid ε s) :
    HasType ∅ ε (sharp s)
      (.space (.tprod (.dual (.dual s)) s)) :=
  HasType.pinv_tensor sv (SValid.dual sv) (flat_hasType sv)

/-- `innerApp s e₀ e₁` types at `Δ₀ ⊎ Δ₁ ⊢ .space .real` when
    `e₀ : s` at Δ₀ and `e₁ : s` at Δ₁ with Δ₀ ⊥ Δ₁. -/
noncomputable def innerApp_hasType {Δ₀ Δ₁ : LCtx} {ε : NLCtx} {s : Space}
    {e₀ e₁ : Term}
    (sv : SValid ε s)
    (disj : Finmap.Disjoint Δ₀ Δ₁)
    (he₀ : HasType Δ₀ ε e₀ (.space s))
    (he₁ : HasType Δ₁ ε e₁ (.space s)) :
    HasType (Δ₀ ∪ Δ₁) ε (innerApp s e₀ e₁) (.space .real) :=
  -- innerApp s e₀ e₁ = .appI s (.appL s s* (.inner s) e₀) e₁.
  -- Outer .appI: Δ = Δ_innerAppL ⊎ Δ_e1.
  -- Inner .appL: Δ_innerAppL = ∅ (for .inner) ⊎ Δ₀ (for e₀), so = Δ₀.
  -- Need (∅ ∪ Δ₀) = Δ₀ for inner appL.
  have h_eq : Δ₀ = ∅ ∪ Δ₀ := by rw [Finmap.empty_union]
  have inner_appL : HasType Δ₀ ε (.appL s (.dual s) (.inner s) e₀)
      (.space (.dual s)) :=
    h_eq ▸ HasType.app_linear sv (SValid.dual sv)
      (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty)
      (HasType.inner sv) he₀
  HasType.app_inner sv disj inner_appL he₁

end Term

/-! ## Finmap helpers for typing nested lambdas. -/

private theorem insert_empty_eq_singleton (x : Name) (s : Space) :
    (Finmap.insert x s ∅ : LCtx) = Finmap.singleton x s := by
  apply Finmap.ext_lookup
  intro a
  by_cases ha : a = x
  · subst ha; rw [Finmap.lookup_insert, Finmap.lookup_singleton_eq]
  · rw [Finmap.lookup_insert_of_ne _ ha, Finmap.lookup_empty]
    have h_not_mem : a ∉ (Finmap.singleton x s : LCtx) := by
      rw [Finmap.mem_singleton]; exact ha
    exact (Finmap.lookup_eq_none.mpr h_not_mem).symm

/-- Two singletons with distinct keys are disjoint. -/
private theorem disjoint_singletons {x y : Name} {s t : Space} (h : x ≠ y) :
    Finmap.Disjoint (Finmap.singleton x s : LCtx) (Finmap.singleton y t : LCtx) := by
  intro k hk₀ hk₁
  rw [Finmap.mem_singleton] at hk₀ hk₁
  -- hk₀ : k = x, hk₁ : k = y
  exact h (hk₀.symm.trans hk₁)

/-- `Finmap.insert x s (Finmap.singleton y t) = Finmap.singleton x s ∪ Finmap.singleton y t`
    when `x ≠ y`. -/
private theorem insert_singleton_eq_union_singletons (x y : Name) (s t : Space) (h : x ≠ y) :
    (Finmap.insert x s (Finmap.singleton y t) : LCtx) =
      Finmap.singleton x s ∪ Finmap.singleton y t := by
  apply Finmap.ext_lookup
  intro a
  by_cases ha : a = x
  · subst ha
    rw [Finmap.lookup_insert]
    rw [Finmap.lookup_union_left (by rw [Finmap.mem_singleton])]
    rw [Finmap.lookup_singleton_eq]
  · by_cases hb : a = y
    · subst hb
      rw [Finmap.lookup_insert_of_ne _ ha,
          Finmap.lookup_union_right (by rw [Finmap.mem_singleton]; exact ha),
          Finmap.lookup_singleton_eq]
    · rw [Finmap.lookup_insert_of_ne _ ha]
      have hn_x : a ∉ (Finmap.singleton x s : LCtx) := by
        rw [Finmap.mem_singleton]; exact ha
      have hn_y : a ∉ (Finmap.singleton y t : LCtx) := by
        rw [Finmap.mem_singleton]; exact hb
      rw [Finmap.lookup_eq_none.mpr hn_y]
      rw [Finmap.lookup_eq_none.mpr (by
        intro hmem
        rw [Finmap.mem_union] at hmem
        cases hmem with
        | inl h => exact hn_x h
        | inr h => exact hn_y h)]

/-- `(∅, ε) ⊢ Space.iof .empty : ⊥* ⊗ ⊥*`. -/
noncomputable def Space.iof_hasType_empty {ε : NLCtx} :
    HasType ∅ ε (Space.iof .empty)
      (.space (.tprod (.dual .empty) (.dual .empty))) :=
  HasType.zero (SValid.tprod (SValid.dual SValid.empty) (SValid.dual SValid.empty))

/-- `(∅, ε) ⊢ Space.iof .real : ℝ* ⊗ ℝ*`. -/
noncomputable def Space.iof_hasType_real {ε : NLCtx} :
    HasType ∅ ε (Space.iof .real)
      (.space (.tprod (.dual .real) (.dual .real))) := by
  -- Outer .llam_tensor opens body at a fresh y0:ℝ, codomain .dual .real.
  refine HasType.llam_tensor ∅
    (by intro h; cases h) SValid.real (SValid.dual SValid.real) (fun y0 _ => ?_)
  -- Body context: insert y0 ℝ ∅ = singleton y0 ℝ.
  simp only [Term.openVar, Term.openRec]
  rw [insert_empty_eq_singleton]
  -- Inner .llam_real opens at a fresh y1:ℝ (≠ y0 via L := {y0}), body type .real.
  refine HasType.llam_real {y0} SValid.real (fun y1 hy1 => ?_)
  have h_ne : y1 ≠ y0 := fun h => hy1 (by simp [h])
  simp only [Term.openVar, Term.openRec]
  -- Body: .smul (.var y0) (.var y1) at Δ = insert y1 ℝ (singleton y0 ℝ).
  rw [insert_singleton_eq_union_singletons _ _ _ _ h_ne]
  rw [Finmap.union_comm_of_disjoint (disjoint_singletons h_ne)]
  exact HasType.smul SValid.real (disjoint_singletons h_ne.symm)
    HasType.var_lin HasType.var_lin

/-- Apply `sharp s` to `.var x` at Δ = `singleton x (.dual s)`. -/
private noncomputable def sharpVar_hasType {ε : NLCtx} {s : Space} (x : Name)
    (sv : SValid ε s) :
    HasType (Finmap.singleton x (.dual s)) ε
      (.appL (.dual s) s (Term.sharp s) (.var x)) (.space s) := by
  have h_eq : (Finmap.singleton x (.dual s) : LCtx) =
      ∅ ∪ Finmap.singleton x (.dual s) := by rw [Finmap.empty_union]
  rw [h_eq]
  exact HasType.app_linear (SValid.dual sv) sv
    (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty)
    (Term.sharp_hasType sv) HasType.var_lin

/-- `(∅, ε) ⊢ Space.iof (.dual s) : (s*)* ⊗ (s*)*`. -/
noncomputable def Space.iof_hasType_dual {ε : NLCtx} {s : Space}
    (sv : SValid ε s) :
    HasType ∅ ε (Space.iof (.dual s))
      (.space (.tprod (.dual (.dual s)) (.dual (.dual s)))) := by
  refine HasType.llam_tensor ∅
    (by intro h; cases h) (SValid.dual sv) (SValid.dual (SValid.dual sv))
    (fun y0 _ => ?_)
  simp only [Term.openVar, Term.openRec, Term.openRec_innerApp,
    Term.openRec_lc (HasType.lc (Term.sharp_hasType sv)),
    Space.openRec_lc (SValid.lc sv), Space.openRec_lc (SValid.lc (SValid.dual sv))]
  rw [insert_empty_eq_singleton]
  refine HasType.llam_real {y0} (SValid.dual sv) (fun y1 hy1 => ?_)
  have h_ne : y1 ≠ y0 := fun h => hy1 (by simp [h])
  simp only [Term.openVar, Term.openRec, Term.openRec_innerApp,
    Term.openRec_lc (HasType.lc (Term.sharp_hasType sv)),
    Space.openRec_lc (SValid.lc sv), Space.openRec_lc (SValid.lc (SValid.dual sv))]
  rw [insert_singleton_eq_union_singletons _ _ _ _ h_ne]
  rw [Finmap.union_comm_of_disjoint (disjoint_singletons h_ne)]
  exact Term.innerApp_hasType (Δ₀ := Finmap.singleton y0 (.dual s))
    (Δ₁ := Finmap.singleton y1 (.dual s))
    sv (disjoint_singletons h_ne.symm)
    (sharpVar_hasType _ sv)
    (sharpVar_hasType _ sv)

/-- `(∅, ε) ⊢ Space.iof (.dsum s₀ s₁) : (s₀⊕s₁)* ⊗ (s₀⊕s₁)*`. -/
noncomputable def Space.iof_hasType_dsum {ε : NLCtx} {s₀ s₁ : Space}
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType ∅ ε (Space.iof (.dsum s₀ s₁))
      (.space (.tprod (.dual (.dsum s₀ s₁)) (.dual (.dsum s₀ s₁)))) := by
  have h_sv : SValid ε (.dsum s₀ s₁) := SValid.dsum sv₀ sv₁
  -- Outer .llam_tensor opens at fresh y0 : (.dsum s₀ s₁), codomain .dual (.dsum s₀ s₁).
  refine HasType.llam_tensor ∅
    (by intro h; cases h) h_sv (SValid.dual h_sv) (fun y0 _ => ?_)
  simp only [Term.openVar, Term.openRec, Term.openRec_innerApp,
    Term.openRec_lc (HasType.lc (Term.kproj0_hasType sv₀ sv₁)),
    Term.openRec_lc (HasType.lc (Term.kproj1_hasType sv₀ sv₁)),
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁),
    Space.openRec_lc (SValid.lc h_sv)]
  rw [insert_empty_eq_singleton]
  -- Inner .llam_real opens at fresh y1 : (.dsum s₀ s₁) (≠ y0 via L := {y0}), body .real.
  refine HasType.llam_real {y0} h_sv (fun y1 hy1 => ?_)
  have h_ne : y1 ≠ y0 := fun h => hy1 (by simp [h])
  simp only [Term.openVar, Term.openRec, Term.openRec_innerApp,
    Term.openRec_lc (HasType.lc (Term.kproj0_hasType sv₀ sv₁)),
    Term.openRec_lc (HasType.lc (Term.kproj1_hasType sv₀ sv₁)),
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁),
    Space.openRec_lc (SValid.lc h_sv)]
  -- Body context: insert y1 (.dsum s₀ s₁) (singleton y0 (.dsum s₀ s₁)) = {y1} ∪ {y0} → commute → {y0} ∪ {y1}.
  rw [insert_singleton_eq_union_singletons _ _ _ _ h_ne]
  rw [Finmap.union_comm_of_disjoint (disjoint_singletons h_ne)]
  refine HasType.add SValid.real ?_ ?_
  all_goals {
    apply Term.innerApp_hasType (Δ₀ := Finmap.singleton y0 (.dsum s₀ s₁))
      (Δ₁ := Finmap.singleton y1 (.dsum s₀ s₁))
    · first | exact sv₀ | exact sv₁
    · exact disjoint_singletons h_ne.symm
    · have h_eq : (Finmap.singleton y0 (.dsum s₀ s₁) : LCtx) =
          ∅ ∪ Finmap.singleton y0 (.dsum s₀ s₁) := by rw [Finmap.empty_union]
      rw [h_eq]
      first
      | exact HasType.app_linear h_sv sv₀
          (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty)
          (Term.kproj0_hasType sv₀ sv₁) HasType.var_lin
      | exact HasType.app_linear h_sv sv₁
          (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty)
          (Term.kproj1_hasType sv₀ sv₁) HasType.var_lin
    · have h_eq : (Finmap.singleton y1 (.dsum s₀ s₁) : LCtx) =
          ∅ ∪ Finmap.singleton y1 (.dsum s₀ s₁) := by rw [Finmap.empty_union]
      rw [h_eq]
      first
      | exact HasType.app_linear h_sv sv₀
          (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty)
          (Term.kproj0_hasType sv₀ sv₁) HasType.var_lin
      | exact HasType.app_linear h_sv sv₁
          (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty)
          (Term.kproj1_hasType sv₀ sv₁) HasType.var_lin
  }

/-! ### Four fundamental subspaces.

Each is `λ(x₀, x₁) → ⟨embed x₀, embed x₁⟩_{ambient}`. We package one
generic helper parametric in the subspace constructor + its SubType
derivation. -/

/-- Apply `.embed sub` to `.var x` at Δ = `singleton x sub`, producing a
    value in the ambient space. -/
private noncomputable def embedVar_hasType {ε : NLCtx} {sub s_amb : Space}
    (sub_sub : SubType ε sub s_amb)
    (x : Name) :
    HasType (Finmap.singleton x sub) ε
      (.appL sub s_amb (.embed sub) (.var x)) (.space s_amb) := by
  -- Extract SValid ε sub and SValid ε s_amb from the SubType derivation.
  -- All four SubType constructors carry these (as `SValid ε s₀` and `SValid ε s₁`
  -- premises in `sub_ker / sub_coker / sub_img / sub_coimg`).
  have ⟨sv_sub, sv_amb⟩ : SValid ε sub × SValid ε s_amb := match sub_sub with
    | .sub_ker   sv₀ sv₁ he => ⟨.ker sv₀ sv₁ he, sv₀⟩
    | .sub_coker sv₀ sv₁ he => ⟨.coker sv₀ sv₁ he, sv₀⟩
    | .sub_img   sv₀ sv₁ he => ⟨.img sv₀ sv₁ he, sv₁⟩
    | .sub_coimg sv₀ sv₁ he => ⟨.coimg sv₀ sv₁ he, sv₁⟩
  have h_eq : (Finmap.singleton x sub : LCtx) =
      ∅ ∪ Finmap.singleton x sub := by rw [Finmap.empty_union]
  rw [h_eq]
  exact HasType.app_linear sv_sub sv_amb
    (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty)
    (HasType.embed sub_sub) HasType.var_lin

/-- Generic typing for `Space.iof` on any fundamental subspace.
    Given a subspace `sub ≤ s_amb` (witnessed by `SubType`), the body
    structure is `λ x₀, x₁. ⟨embed x₀, embed x₁⟩_{s_amb}`. -/
private noncomputable def iof_hasType_fundamental_subspace_body
    {ε : NLCtx} {sub s_amb : Space}
    (sv_sub : SValid ε sub) (sv_amb : SValid ε s_amb)
    (sub_sub : SubType ε sub s_amb) :
    HasType ∅ ε
      (Space.iofSubBody sub s_amb)
      (.space (.tprod (.dual sub) (.dual sub))) := by
  refine HasType.llam_tensor ∅
    (by intro h; cases h) sv_sub (SValid.dual sv_sub) (fun y0 _ => ?_)
  simp only [Space.iofSubBody, Term.openVar, Term.openRec, Term.openRec_innerApp,
    Term.embedApp, Space.openRec_lc (SValid.lc sv_sub),
    Space.openRec_lc (SValid.lc sv_amb)]
  rw [insert_empty_eq_singleton]
  refine HasType.llam_real {y0} sv_sub (fun y1 hy1 => ?_)
  have h_ne : y1 ≠ y0 := fun h => hy1 (by simp [h])
  simp only [Term.openVar, Term.openRec, Term.openRec_innerApp,
    Term.embedApp, Space.openRec_lc (SValid.lc sv_sub),
    Space.openRec_lc (SValid.lc sv_amb)]
  rw [insert_singleton_eq_union_singletons _ _ _ _ h_ne]
  rw [Finmap.union_comm_of_disjoint (disjoint_singletons h_ne)]
  exact Term.innerApp_hasType (Δ₀ := Finmap.singleton y0 sub)
    (Δ₁ := Finmap.singleton y1 sub)
    sv_amb (disjoint_singletons h_ne.symm)
    (embedVar_hasType sub_sub _)
    (embedVar_hasType sub_sub _)

/-- `(∅, ε) ⊢ Space.iof (.ker s₀ s₁ e) : Ker(e)* ⊗ Ker(e)*`. -/
noncomputable def Space.iof_hasType_ker {ε : NLCtx} {s₀ s₁ : Space} {e : Term}
    (h_fresh_x0 : Term.x0 ∉ ε) (h_fresh_x1 : Term.x1 ∉ ε)
    (h_x0_ne_x1 : Term.x0 ≠ Term.x1)
    (sv : SValid ε (.ker s₀ s₁ e)) :
    HasType ∅ ε (Space.iof (.ker s₀ s₁ e))
      (.space (.tprod (.dual (.ker s₀ s₁ e)) (.dual (.ker s₀ s₁ e)))) := by
  -- Extract sub_ker from sv to get the SubType + ambient SValid.
  cases sv with
  | ker sv₀ sv₁ he =>
    exact iof_hasType_fundamental_subspace_body
      (SValid.ker sv₀ sv₁ he) sv₀
      (SubType.sub_ker sv₀ sv₁ he)

/-- `(∅, ε) ⊢ Space.iof (.coker s₀ s₁ e) : CoKer(e)* ⊗ CoKer(e)*`. -/
noncomputable def Space.iof_hasType_coker {ε : NLCtx} {s₀ s₁ : Space} {e : Term}
    (h_fresh_x0 : Term.x0 ∉ ε) (h_fresh_x1 : Term.x1 ∉ ε)
    (h_x0_ne_x1 : Term.x0 ≠ Term.x1)
    (sv : SValid ε (.coker s₀ s₁ e)) :
    HasType ∅ ε (Space.iof (.coker s₀ s₁ e))
      (.space (.tprod (.dual (.coker s₀ s₁ e)) (.dual (.coker s₀ s₁ e)))) := by
  cases sv with
  | coker sv₀ sv₁ he =>
    exact iof_hasType_fundamental_subspace_body
      (SValid.coker sv₀ sv₁ he) sv₀
      (SubType.sub_coker sv₀ sv₁ he)

/-- `(∅, ε) ⊢ Space.iof (.img s₀ s₁ e) : Img(e)* ⊗ Img(e)*`. -/
noncomputable def Space.iof_hasType_img {ε : NLCtx} {s₀ s₁ : Space} {e : Term}
    (h_fresh_x0 : Term.x0 ∉ ε) (h_fresh_x1 : Term.x1 ∉ ε)
    (h_x0_ne_x1 : Term.x0 ≠ Term.x1)
    (sv : SValid ε (.img s₀ s₁ e)) :
    HasType ∅ ε (Space.iof (.img s₀ s₁ e))
      (.space (.tprod (.dual (.img s₀ s₁ e)) (.dual (.img s₀ s₁ e)))) := by
  cases sv with
  | img sv₀ sv₁ he =>
    exact iof_hasType_fundamental_subspace_body
      (SValid.img sv₀ sv₁ he) sv₁
      (SubType.sub_img sv₀ sv₁ he)

/-- `(∅, ε) ⊢ Space.iof (.coimg s₀ s₁ e) : CoImg(e)* ⊗ CoImg(e)*`. -/
noncomputable def Space.iof_hasType_coimg {ε : NLCtx} {s₀ s₁ : Space} {e : Term}
    (h_fresh_x0 : Term.x0 ∉ ε) (h_fresh_x1 : Term.x1 ∉ ε)
    (h_x0_ne_x1 : Term.x0 ≠ Term.x1)
    (sv : SValid ε (.coimg s₀ s₁ e)) :
    HasType ∅ ε (Space.iof (.coimg s₀ s₁ e))
      (.space (.tprod (.dual (.coimg s₀ s₁ e)) (.dual (.coimg s₀ s₁ e)))) := by
  cases sv with
  | coimg sv₀ sv₁ he =>
    exact iof_hasType_fundamental_subspace_body
      (SValid.coimg sv₀ sv₁ he) sv₁
      (SubType.sub_coimg sv₀ sv₁ he)

/-! ### Tprod case.

`Space.iof (.tprod s₀ s₁)` unfolds to:
```
let F := λ y00 y01 y10 y11. (innerApp s₀ y00 y10) · (innerApp s₁ y01 y11)
let step1 := applyUncurry2NonReal s₀ s₁ (s₀*⊗s₁*) F
λ p:(s₀⊗s₁) ⊸ applyUncurry2Real s₀ s₁ (.appL ... step1 (.var p))
```

We need typing lemmas for the curry/uncurry chain and for F's 4-binder
body. We build them up. -/

/-- Multi-key Finmap normalization: `insert d (insert c (insert b (insert a ∅)))`
    expressed via `Finmap.union`. Used for `Space.iof .tprod`'s 4-binder body. -/
private theorem Finmap.lookup_singleton_eq_none_of_ne {x k : Name} {s : Space}
    (h : k ≠ x) : (Finmap.singleton x s : LCtx).lookup k = none := by
  rw [Finmap.lookup_eq_none, Finmap.mem_singleton]; exact h

/-- Curry's body context: after the 3 nested lambdas of curry2NonReal/Real,
    Δ_body = insert b sB (insert a sA (insert g g_ty ∅)). We need this to
    equal `singleton g g_ty ∪ (singleton a sA ∪ singleton b sB)` for the
    body's .appL split.  -/
private theorem insert_three_eq_union_curry
    (g a b : Name) (sg sa sb : Space)
    (h_ga : g ≠ a) (h_gb : g ≠ b) (h_ab : a ≠ b) :
    (Finmap.insert b sb (Finmap.insert a sa (Finmap.insert g sg ∅)) : LCtx) =
      Finmap.singleton g sg ∪
        (Finmap.singleton a sa ∪ Finmap.singleton b sb) := by
  apply Finmap.ext_lookup
  intro k
  by_cases hkg : k = g
  · subst hkg
    rw [Finmap.lookup_insert_of_ne _ h_gb,
        Finmap.lookup_insert_of_ne _ h_ga, Finmap.lookup_insert]
    rw [Finmap.lookup_union_left (by rw [Finmap.mem_singleton]),
        Finmap.lookup_singleton_eq]
  · by_cases hka : k = a
    · subst hka
      rw [Finmap.lookup_insert_of_ne _ h_ab, Finmap.lookup_insert]
      rw [Finmap.lookup_union_right (by rw [Finmap.mem_singleton]; exact h_ga.symm),
          Finmap.lookup_union_left (by rw [Finmap.mem_singleton]),
          Finmap.lookup_singleton_eq]
    · by_cases hkb : k = b
      · subst hkb
        rw [Finmap.lookup_insert]
        rw [Finmap.lookup_union_right (by rw [Finmap.mem_singleton]; exact h_gb.symm),
            Finmap.lookup_union_right
              (by rw [Finmap.mem_singleton]; exact fun h => h_ab h.symm),
            Finmap.lookup_singleton_eq]
      · rw [Finmap.lookup_insert_of_ne _ hkb,
            Finmap.lookup_insert_of_ne _ hka,
            Finmap.lookup_insert_of_ne _ hkg, Finmap.lookup_empty]
        rw [Finmap.lookup_union_right
              (by rw [Finmap.mem_singleton]; exact hkg)]
        rw [Finmap.lookup_union_right
              (by rw [Finmap.mem_singleton]; exact hka)]
        rw [Finmap.lookup_singleton_eq_none_of_ne hkb]

namespace Term

/-- Helper: `.tprodE (.var a) (.var b)` typed at `singleton a sA ∪ singleton b sB`. -/
private noncomputable def tprodE_var_var_hasType {ε : NLCtx} {sA sB : Space}
    (svA : SValid ε sA) (svB : SValid ε sB) (a b : Name) (h_ab : a ≠ b) :
    HasType (Finmap.singleton a sA ∪ Finmap.singleton b sB) ε
      (.tprodE (.var a) (.var b)) (.space (.tprod sA sB)) :=
  HasType.tprodE svA svB (disjoint_singletons h_ab) HasType.var_lin HasType.var_lin

/-- `(∅, ε) ⊢ curry2NonReal sA sB sRest : ((sA⊗sB)*⊗sRest)* ⊗ sA*⊗sB*⊗sRest`. -/
noncomputable def curry2NonReal_hasType {ε : NLCtx} {sA sB sRest : Space}
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest) :
    HasType ∅ ε (curry2NonReal sA sB sRest)
      (.space
        (.tprod (.dual (.tprod (.dual (.tprod sA sB)) sRest))
          (.tprod (.dual sA) (.tprod (.dual sB) sRest)))) := by
  -- Outer llam_tensor opens at fresh y_g. Codomain = sA*⊗sB*⊗sRest ≠ .real.
  refine HasType.llam_tensor ∅
    (by intro h; cases h)
    (SValid.tprod (SValid.dual (SValid.tprod svA svB)) svR)
    (SValid.tprod (SValid.dual svA) (SValid.tprod (SValid.dual svB) svR))
    (fun yg _ => ?_)
  simp only [curry2NonReal, Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc svR),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  rw [insert_empty_eq_singleton]
  -- Middle llam_tensor opens at fresh y_a (≠ y_g via L := {y_g}).
  refine HasType.llam_tensor {yg}
    (by intro h; cases h) svA (SValid.tprod (SValid.dual svB) svR)
    (fun ya hya => ?_)
  have h_ag : ya ≠ yg := fun h => hya (by simp [h])
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc svR),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  -- Inner llam_tensor opens at fresh y_b (≠ y_g, y_a via L := {y_g, y_a}).
  refine HasType.llam_tensor {yg, ya} h_sRest_ne_real svB svR (fun yb hyb => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyb
  obtain ⟨h_bg', h_ba'⟩ := hyb
  have h_bg : yb ≠ yg := h_bg'
  have h_ba : yb ≠ ya := h_ba'
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc svR),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  -- Body context: insert y_b sB (insert y_a sA (singleton y_g g_ty)).
  rw [← insert_empty_eq_singleton]
  rw [insert_three_eq_union_curry _ _ _ _ _ _ h_ag.symm h_bg.symm h_ba.symm]
  refine HasType.app_linear (SValid.tprod svA svB) svR ?_ HasType.var_lin
    (tprodE_var_var_hasType svA svB _ _ h_ba.symm)
  intro k hk_g hk_ab
  rw [Finmap.mem_singleton] at hk_g
  rw [Finmap.mem_union] at hk_ab
  cases hk_ab with
  | inl hk_a => rw [Finmap.mem_singleton] at hk_a; exact h_ag.symm (hk_g.symm.trans hk_a)
  | inr hk_b => rw [Finmap.mem_singleton] at hk_b; exact h_bg.symm (hk_g.symm.trans hk_b)

/-- Body of `curry2NonReal sA sB sRest` is well-typed under
    `Finmap.insert g_name g_ty ∅`. Used to apply `denot_llam_body_isLinear`
    to extract body linearity for the bijectivity proof. -/
noncomputable def curry2NonReal_body_hasType {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : g_name ∉ ε) (h_fresh_a : a_name ∉ ε) (h_fresh_b : b_name ∉ ε)
    (h_ga : g_name ≠ a_name) (h_gb : g_name ≠ b_name) (h_ab : a_name ≠ b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest) :
    HasType
      (Finmap.insert g_name (.tprod (.dual (.tprod sA sB)) sRest) ∅) ε
      (.llam sA (.tprod (.dual sB) sRest)
        (.llam sB sRest
          (.appL (.tprod sA sB) sRest
            (.var g_name)
            (.tprodE (.bvar 1) (.bvar 0)))))
      (.space (.tprod (.dual sA) (.tprod (.dual sB) sRest))) := by
  -- Reuse the inner structure of curry2NonReal_hasType, but skip the outermost llam.
  rw [insert_empty_eq_singleton]
  refine HasType.llam_tensor {g_name}
    (by intro h; cases h)
    svA (SValid.tprod (SValid.dual svB) svR) (fun ya hya => ?_)
  have h_ag : ya ≠ g_name := fun h => hya (by simp [h])
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc svR),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  refine HasType.llam_tensor {g_name, ya} h_sRest_ne_real svB svR (fun yb hyb => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyb
  obtain ⟨h_bg', h_ba'⟩ := hyb
  have h_bg : yb ≠ g_name := h_bg'
  have h_ba : yb ≠ ya := h_ba'
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc svR),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  rw [← insert_empty_eq_singleton]
  rw [insert_three_eq_union_curry _ _ _ _ _ _ h_ag.symm h_bg.symm h_ba.symm]
  refine HasType.app_linear (SValid.tprod svA svB) svR ?_ HasType.var_lin
    (tprodE_var_var_hasType svA svB _ _ h_ba.symm)
  intro k hk_g hk_ab
  rw [Finmap.mem_singleton] at hk_g
  rw [Finmap.mem_union] at hk_ab
  cases hk_ab with
  | inl hk_a => rw [Finmap.mem_singleton] at hk_a; exact h_ag.symm (hk_g.symm.trans hk_a)
  | inr hk_b => rw [Finmap.mem_singleton] at hk_b; exact h_bg.symm (hk_g.symm.trans hk_b)

/-- `(∅, ε) ⊢ curry2Real sA sB : ((sA⊗sB)*)* ⊗ sA*⊗sB*`. -/
noncomputable def curry2Real_hasType {ε : NLCtx} {sA sB : Space}
    (svA : SValid ε sA) (svB : SValid ε sB) :
    HasType ∅ ε (curry2Real sA sB)
      (.space
        (.tprod (.dual (.dual (.tprod sA sB)))
          (.tprod (.dual sA) (.dual sB)))) := by
  refine HasType.llam_tensor ∅
    (by intro h; cases h)
    (SValid.dual (SValid.tprod svA svB))
    (SValid.tprod (SValid.dual svA) (SValid.dual svB))
    (fun yg _ => ?_)
  simp only [curry2Real, Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  rw [insert_empty_eq_singleton]
  refine HasType.llam_tensor {yg}
    (by intro h; cases h) svA (SValid.dual svB) (fun ya hya => ?_)
  have h_ag : ya ≠ yg := fun h => hya (by simp [h])
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  refine HasType.llam_real {yg, ya} svB (fun yb hyb => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyb
  obtain ⟨h_bg', h_ba'⟩ := hyb
  have h_bg : yb ≠ yg := h_bg'
  have h_ba : yb ≠ ya := h_ba'
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  rw [← insert_empty_eq_singleton]
  rw [insert_three_eq_union_curry _ _ _ _ _ _ h_ag.symm h_bg.symm h_ba.symm]
  refine HasType.app_inner (SValid.tprod svA svB) ?_ HasType.var_lin
    (tprodE_var_var_hasType svA svB _ _ h_ba.symm)
  intro k hk_g hk_ab
  rw [Finmap.mem_singleton] at hk_g
  rw [Finmap.mem_union] at hk_ab
  cases hk_ab with
  | inl hk_a => rw [Finmap.mem_singleton] at hk_a; exact h_ag.symm (hk_g.symm.trans hk_a)
  | inr hk_b => rw [Finmap.mem_singleton] at hk_b; exact h_bg.symm (hk_g.symm.trans hk_b)

/-- Mid-level body of curry2NonReal (inside the middle .llam). Used to
    extract linearity in `a_name`. -/
noncomputable def curry2NonReal_mid_hasType {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_a : a_name ∉ ε) (h_fresh_b : b_name ∉ ε)
    (h_ga : g_name ≠ a_name) (h_gb : g_name ≠ b_name) (h_ab : a_name ≠ b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest) :
    HasType
      (Finmap.insert a_name sA (Finmap.insert g_name
        (.tprod (.dual (.tprod sA sB)) sRest) ∅)) ε
      (.llam sB sRest
        (.appL (.tprod sA sB) sRest
          (.var g_name)
          (.tprodE (.var a_name) (.bvar 0))))
      (.space (.tprod (.dual sB) sRest)) := by
  refine HasType.llam_tensor {g_name, a_name} h_sRest_ne_real svB svR (fun yb hyb => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyb
  obtain ⟨h_bg', h_ba'⟩ := hyb
  have h_bg : yb ≠ g_name := h_bg'
  have h_ba : yb ≠ a_name := h_ba'
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc svR),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  -- Body: .appL (.tprod sA sB) sRest (.var g) (.tprodE (.var a) (.var yb))
  -- under context insert yb sB (insert a sA (insert g g_ty ∅))
  rw [insert_three_eq_union_curry _ _ _ _ _ _ h_ga h_bg.symm h_ba.symm]
  refine HasType.app_linear (SValid.tprod svA svB) svR ?_ HasType.var_lin
    (tprodE_var_var_hasType svA svB _ _ h_ba.symm)
  intro k hk_g hk_ab
  rw [Finmap.mem_singleton] at hk_g
  rw [Finmap.mem_union] at hk_ab
  cases hk_ab with
  | inl hk_a => rw [Finmap.mem_singleton] at hk_a; exact h_ga (hk_g.symm.trans hk_a)
  | inr hk_b => rw [Finmap.mem_singleton] at hk_b; exact h_bg.symm (hk_g.symm.trans hk_b)

/-- Innermost body of curry2NonReal (the `.appL` at the bottom).
    Used to extract linearity in `b_name`. -/
noncomputable def curry2NonReal_innermost_hasType {ε : NLCtx} {sA sB sRest : Space}
    (h_ga : g_name ≠ a_name) (h_gb : g_name ≠ b_name) (h_ab : a_name ≠ b_name)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest) :
    HasType
      (Finmap.insert b_name sB (Finmap.insert a_name sA (Finmap.insert g_name
        (.tprod (.dual (.tprod sA sB)) sRest) ∅))) ε
      (.appL (.tprod sA sB) sRest
        (.var g_name)
        (.tprodE (.var a_name) (.var b_name)))
      (.space sRest) := by
  rw [insert_three_eq_union_curry _ _ _ _ _ _ h_ga h_gb h_ab]
  refine HasType.app_linear (SValid.tprod svA svB) svR ?_ HasType.var_lin
    (tprodE_var_var_hasType svA svB _ _ h_ab)
  intro k hk_g hk_ab
  rw [Finmap.mem_singleton] at hk_g
  rw [Finmap.mem_union] at hk_ab
  cases hk_ab with
  | inl hk_a => rw [Finmap.mem_singleton] at hk_a; exact h_ga (hk_g.symm.trans hk_a)
  | inr hk_b => rw [Finmap.mem_singleton] at hk_b; exact h_gb (hk_g.symm.trans hk_b)

/-- Body of `curry2Real sA sB` is well-typed under `Finmap.insert g_name g_ty ∅`. -/
noncomputable def curry2Real_body_hasType {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : g_name ∉ ε) (h_fresh_a : a_name ∉ ε) (h_fresh_b : b_name ∉ ε)
    (h_ga : g_name ≠ a_name) (h_gb : g_name ≠ b_name) (h_ab : a_name ≠ b_name)
    (svA : SValid ε sA) (svB : SValid ε sB) :
    HasType
      (Finmap.insert g_name (.dual (.tprod sA sB)) ∅) ε
      (.llam sA (.dual sB)
        (.llam sB .real
          (.appI (.tprod sA sB)
            (.var g_name)
            (.tprodE (.bvar 1) (.bvar 0)))))
      (.space (.tprod (.dual sA) (.dual sB))) := by
  rw [insert_empty_eq_singleton]
  refine HasType.llam_tensor {g_name}
    (by intro h; cases h)
    svA (SValid.dual svB) (fun ya hya => ?_)
  have h_ag : ya ≠ g_name := fun h => hya (by simp [h])
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  refine HasType.llam_real {g_name, ya} svB (fun yb hyb => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyb
  obtain ⟨h_bg', h_ba'⟩ := hyb
  have h_bg : yb ≠ g_name := h_bg'
  have h_ba : yb ≠ ya := h_ba'
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  rw [← insert_empty_eq_singleton]
  rw [insert_three_eq_union_curry _ _ _ _ _ _ h_ag.symm h_bg.symm h_ba.symm]
  refine HasType.app_inner (SValid.tprod svA svB) ?_ HasType.var_lin
    (tprodE_var_var_hasType svA svB _ _ h_ba.symm)
  intro k hk_g hk_ab
  rw [Finmap.mem_singleton] at hk_g
  rw [Finmap.mem_union] at hk_ab
  cases hk_ab with
  | inl hk_a => rw [Finmap.mem_singleton] at hk_a; exact h_ag.symm (hk_g.symm.trans hk_a)
  | inr hk_b => rw [Finmap.mem_singleton] at hk_b; exact h_bg.symm (hk_g.symm.trans hk_b)

/-- Mid-level body of curry2Real (inside the middle .llam). -/
noncomputable def curry2Real_mid_hasType {ε : NLCtx} {sA sB : Space}
    (h_fresh_a : a_name ∉ ε) (h_fresh_b : b_name ∉ ε)
    (h_ga : g_name ≠ a_name) (h_gb : g_name ≠ b_name) (h_ab : a_name ≠ b_name)
    (svA : SValid ε sA) (svB : SValid ε sB) :
    HasType
      (Finmap.insert a_name sA (Finmap.insert g_name (.dual (.tprod sA sB)) ∅)) ε
      (.llam sB .real
        (.appI (.tprod sA sB)
          (.var g_name)
          (.tprodE (.var a_name) (.bvar 0))))
      (.space (.dual sB)) := by
  refine HasType.llam_real {g_name, a_name} svB (fun yb hyb => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyb
  obtain ⟨h_bg', h_ba'⟩ := hyb
  have h_bg : yb ≠ g_name := h_bg'
  have h_ba : yb ≠ a_name := h_ba'
  simp only [Term.openVar, Term.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
    Space.openRec_lc (SValid.lc (SValid.tprod svA svB))]
  rw [insert_three_eq_union_curry _ _ _ _ _ _ h_ga h_bg.symm h_ba.symm]
  refine HasType.app_inner (SValid.tprod svA svB) ?_ HasType.var_lin
    (tprodE_var_var_hasType svA svB _ _ h_ba.symm)
  intro k hk_g hk_ab
  rw [Finmap.mem_singleton] at hk_g
  rw [Finmap.mem_union] at hk_ab
  cases hk_ab with
  | inl hk_a => rw [Finmap.mem_singleton] at hk_a; exact h_ga (hk_g.symm.trans hk_a)
  | inr hk_b => rw [Finmap.mem_singleton] at hk_b; exact h_bg.symm (hk_g.symm.trans hk_b)

/-- Innermost body of curry2Real (the .appI at the bottom). -/
noncomputable def curry2Real_innermost_hasType {ε : NLCtx} {sA sB : Space}
    (h_ga : g_name ≠ a_name) (h_gb : g_name ≠ b_name) (h_ab : a_name ≠ b_name)
    (svA : SValid ε sA) (svB : SValid ε sB) :
    HasType
      (Finmap.insert b_name sB (Finmap.insert a_name sA (Finmap.insert g_name
        (.dual (.tprod sA sB)) ∅))) ε
      (.appI (.tprod sA sB)
        (.var g_name)
        (.tprodE (.var a_name) (.var b_name)))
      (.space .real) := by
  rw [insert_three_eq_union_curry _ _ _ _ _ _ h_ga h_gb h_ab]
  refine HasType.app_inner (SValid.tprod svA svB) ?_ HasType.var_lin
    (tprodE_var_var_hasType svA svB _ _ h_ab)
  intro k hk_g hk_ab
  rw [Finmap.mem_singleton] at hk_g
  rw [Finmap.mem_union] at hk_ab
  cases hk_ab with
  | inl hk_a => rw [Finmap.mem_singleton] at hk_a; exact h_ga (hk_g.symm.trans hk_a)
  | inr hk_b => rw [Finmap.mem_singleton] at hk_b; exact h_gb (hk_g.symm.trans hk_b)

/-- `(∅, ε) ⊢ uncurry2NonReal sA sB sRest : (sA*⊗sB*⊗sRest)* ⊗ ((sA⊗sB)*⊗sRest)`. -/
noncomputable def uncurry2NonReal_hasType {ε : NLCtx} {sA sB sRest : Space}
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest) :
    HasType ∅ ε (uncurry2NonReal sA sB sRest)
      (.space
        (.tprod (.dual (.tprod (.dual sA) (.tprod (.dual sB) sRest)))
          (.tprod (.dual (.tprod sA sB)) sRest))) :=
  HasType.pinv_tensor
    (SValid.tprod (SValid.dual (SValid.tprod svA svB)) svR)
    (SValid.tprod (SValid.dual svA) (SValid.tprod (SValid.dual svB) svR))
    (curry2NonReal_hasType h_sRest_ne_real svA svB svR)

/-- `(∅, ε) ⊢ uncurry2Real sA sB : (sA*⊗sB*)* ⊗ (sA⊗sB)*`. -/
noncomputable def uncurry2Real_hasType {ε : NLCtx} {sA sB : Space}
    (svA : SValid ε sA) (svB : SValid ε sB) :
    HasType ∅ ε (uncurry2Real sA sB)
      (.space
        (.tprod (.dual (.tprod (.dual sA) (.dual sB)))
          (.dual (.tprod sA sB)))) :=
  HasType.pinv_tensor
    (SValid.dual (SValid.tprod svA svB))
    (SValid.tprod (SValid.dual svA) (SValid.dual svB))
    (curry2Real_hasType svA svB)

/-- Applying uncurry to a curried function: typed via `.app_linear`
    with the uncurry term at Δ=∅ and the function at Δ_f. -/
noncomputable def applyUncurry2NonReal_hasType {Δ_f : LCtx} {ε : NLCtx}
    {sA sB sRest : Space} {f : Term}
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (hf : HasType Δ_f ε f (.space (.tprod (.dual sA) (.tprod (.dual sB) sRest)))) :
    HasType Δ_f ε (applyUncurry2NonReal sA sB sRest f)
      (.space (.tprod (.dual (.tprod sA sB)) sRest)) := by
  have h_eq : Δ_f = ∅ ∪ Δ_f := by rw [Finmap.empty_union]
  rw [h_eq]
  exact HasType.app_linear
    (SValid.tprod (SValid.dual svA) (SValid.tprod (SValid.dual svB) svR))
    (SValid.tprod (SValid.dual (SValid.tprod svA svB)) svR)
    (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty)
    (uncurry2NonReal_hasType h_sRest_ne_real svA svB svR)
    hf

noncomputable def applyUncurry2Real_hasType {Δ_f : LCtx} {ε : NLCtx}
    {sA sB : Space} {f : Term}
    (svA : SValid ε sA) (svB : SValid ε sB)
    (hf : HasType Δ_f ε f (.space (.tprod (.dual sA) (.dual sB)))) :
    HasType Δ_f ε (applyUncurry2Real sA sB f)
      (.space (.dual (.tprod sA sB))) := by
  have h_eq : Δ_f = ∅ ∪ Δ_f := by rw [Finmap.empty_union]
  rw [h_eq]
  exact HasType.app_linear
    (SValid.tprod (SValid.dual svA) (SValid.dual svB))
    (SValid.dual (SValid.tprod svA svB))
    (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty)
    (uncurry2Real_hasType svA svB)
    hf

end Term

/-! ### F's 4-binder body — Finmap equality + typing. -/

/-- `Finmap.insert d (insert c (insert b (insert a ∅)))` viewed as a smul
    split: `(singleton a ∪ singleton c) ∪ (singleton b ∪ singleton d)`.
    Used by F's body to split Δ for .smul. -/
private theorem insert_four_eq_smul_split
    {a b c d : Name} {sa sb sc sd : Space}
    (h_ab : a ≠ b) (h_ac : a ≠ c) (h_ad : a ≠ d)
    (h_bc : b ≠ c) (h_bd : b ≠ d) (h_cd : c ≠ d) :
    (Finmap.insert d sd (Finmap.insert c sc
        (Finmap.insert b sb (Finmap.insert a sa ∅))) : LCtx) =
      (Finmap.singleton a sa ∪ Finmap.singleton c sc) ∪
      (Finmap.singleton b sb ∪ Finmap.singleton d sd) := by
  apply Finmap.ext_lookup
  intro k
  by_cases hka : k = a
  · subst hka
    rw [Finmap.lookup_insert_of_ne _ h_ad,
        Finmap.lookup_insert_of_ne _ h_ac,
        Finmap.lookup_insert_of_ne _ h_ab,
        Finmap.lookup_insert]
    rw [Finmap.lookup_union_left
          (by rw [Finmap.mem_union]; left; rw [Finmap.mem_singleton])]
    rw [Finmap.lookup_union_left (by rw [Finmap.mem_singleton]),
        Finmap.lookup_singleton_eq]
  · by_cases hkb : k = b
    · subst hkb
      rw [Finmap.lookup_insert_of_ne _ h_bd,
          Finmap.lookup_insert_of_ne _ h_bc,
          Finmap.lookup_insert]
      rw [Finmap.lookup_union_right (by
            intro hmem
            rw [Finmap.mem_union, Finmap.mem_singleton, Finmap.mem_singleton] at hmem
            rcases hmem with h | h
            · exact h_ab h.symm
            · exact h_bc h)]
      rw [Finmap.lookup_union_left (by rw [Finmap.mem_singleton]),
          Finmap.lookup_singleton_eq]
    · by_cases hkc : k = c
      · subst hkc
        rw [Finmap.lookup_insert_of_ne _ h_cd, Finmap.lookup_insert]
        rw [Finmap.lookup_union_left
              (by rw [Finmap.mem_union]; right; rw [Finmap.mem_singleton])]
        rw [Finmap.lookup_union_right (by rw [Finmap.mem_singleton]; exact h_ac.symm),
            Finmap.lookup_singleton_eq]
      · by_cases hkd : k = d
        · subst hkd
          rw [Finmap.lookup_insert]
          rw [Finmap.lookup_union_right (by
                intro hmem
                rw [Finmap.mem_union, Finmap.mem_singleton, Finmap.mem_singleton] at hmem
                rcases hmem with h | h
                · exact h_ad h.symm
                · exact h_cd h.symm)]
          rw [Finmap.lookup_union_right (by rw [Finmap.mem_singleton]; exact h_bd.symm),
              Finmap.lookup_singleton_eq]
        · rw [Finmap.lookup_insert_of_ne _ hkd,
              Finmap.lookup_insert_of_ne _ hkc,
              Finmap.lookup_insert_of_ne _ hkb,
              Finmap.lookup_insert_of_ne _ hka,
              Finmap.lookup_empty]
          -- RHS: lookup k ((singleton a ∪ singleton c) ∪ (singleton b ∪ singleton d)).
          -- k ∉ (singleton a ∪ singleton c) (since k ≠ a, k ≠ c). Skip left.
          rw [Finmap.lookup_union_right (by
                intro hmem
                rw [Finmap.mem_union, Finmap.mem_singleton, Finmap.mem_singleton] at hmem
                rcases hmem with h | h
                · exact hka h
                · exact hkc h)]

          rw [Finmap.lookup_union_right (by rw [Finmap.mem_singleton]; exact hkb)]

          exact (Finmap.lookup_singleton_eq_none_of_ne hkd).symm

/-- Disjointness of the two 2-element unions in the smul split. -/
private theorem disjoint_smul_split
    {a b c d : Name} {sa sb sc sd : Space}
    (h_ab : a ≠ b) (h_ad : a ≠ d) (h_bc : b ≠ c) (h_cd : c ≠ d) :
    Finmap.Disjoint
      (Finmap.singleton a sa ∪ Finmap.singleton c sc : LCtx)
      (Finmap.singleton b sb ∪ Finmap.singleton d sd : LCtx) := by
  intro k hk_ac hk_bd
  rw [Finmap.mem_union, Finmap.mem_singleton, Finmap.mem_singleton] at hk_ac hk_bd
  rcases hk_ac with hk_a | hk_c
  · subst hk_a
    rcases hk_bd with hk_b | hk_d
    · exact h_ab hk_b
    · exact h_ad hk_d
  · subst hk_c
    rcases hk_bd with hk_b | hk_d
    · exact h_bc hk_b.symm
    · exact h_cd hk_d

/-- Distinctness of `Space.iof`'s y-binder names — all `decide`-able. -/
theorem Term.y_pairwise_distinct :
    (("$y00" : Name) ≠ "$y01") ∧
    (("$y00" : Name) ≠ "$y10") ∧
    (("$y00" : Name) ≠ "$y11") ∧
    (("$y01" : Name) ≠ "$y10") ∧
    (("$y01" : Name) ≠ "$y11") ∧
    (("$y10" : Name) ≠ "$y11") := by decide

/-- The 4-binder F lambda inside `Space.iof (.tprod s₀ s₁)` (LN form). -/
@[reducible] def tprod_F (s₀ s₁ : Space) : Term :=
  .llam s₀
    (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁)))
    (.llam s₁
      (.tprod (.dual s₀) (.dual s₁))
      (.llam s₀ (.dual s₁)
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.bvar 3) (.bvar 1))
            (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))

/-- The inner body of the outer `.llam` in `Space.iof (.tprod s₀ s₁)` (LN
    form; the bound vector is `.bvar 0`). -/
@[reducible] def Space.iofTprodBody (s₀ s₁ : Space) : Term :=
  Term.applyUncurry2Real s₀ s₁
    (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
      (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁)) (tprod_F s₀ s₁))
      (.bvar 0))

/-- F's typing — the 4-binder lambda inside `Space.iof (.tprod s₀ s₁)`. -/
private noncomputable def tprod_F_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType ∅ ε (tprod_F s₀ s₁)
      (.space (.tprod (.dual s₀) (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁))))) := by
  -- Outer llam_tensor opens at fresh y00.
  refine HasType.llam_tensor ∅ (by intro h; cases h) sv₀
    (SValid.tprod (SValid.dual sv₁) (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)))
    (fun y00 _ => ?_)
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  rw [insert_empty_eq_singleton]
  -- Second llam_tensor opens at fresh y01 (≠ y00).
  refine HasType.llam_tensor {y00} (by intro h; cases h) sv₁
    (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)) (fun y01 hy01 => ?_)
  have h_01_00 : y01 ≠ y00 := fun h => hy01 (by simp [h])
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  -- Third llam_tensor opens at fresh y10 (≠ y00, y01).
  refine HasType.llam_tensor {y00, y01} (by intro h; cases h) sv₀ (SValid.dual sv₁)
    (fun y10 hy10 => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy10
  obtain ⟨h_10_00', h_10_01'⟩ := hy10
  have h_10_00 : y10 ≠ y00 := h_10_00'
  have h_10_01 : y10 ≠ y01 := h_10_01'
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  -- Innermost llam_real opens at fresh y11 (≠ y00, y01, y10).
  refine HasType.llam_real {y00, y01, y10} sv₁ (fun y11 hy11 => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy11
  obtain ⟨h_11_00', h_11_01', h_11_10'⟩ := hy11
  have h_11_00 : y11 ≠ y00 := h_11_00'
  have h_11_01 : y11 ≠ y01 := h_11_01'
  have h_11_10 : y11 ≠ y10 := h_11_10'
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  -- Body context: insert y11 s₁ (insert y10 s₀ (insert y01 s₁ (singleton y00 s₀))).
  rw [← insert_empty_eq_singleton]
  rw [insert_four_eq_smul_split h_01_00.symm h_10_00.symm h_11_00.symm
    h_10_01.symm h_11_01.symm h_11_10.symm]
  exact HasType.smul SValid.real
    (disjoint_smul_split h_01_00.symm h_11_00.symm h_10_01.symm h_11_10.symm)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton y00 s₀)
      (Δ₁ := Finmap.singleton y10 s₀) sv₀
      (disjoint_singletons h_10_00.symm) HasType.var_lin HasType.var_lin)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton y01 s₁)
      (Δ₁ := Finmap.singleton y11 s₁) sv₁
      (disjoint_singletons h_11_01.symm) HasType.var_lin HasType.var_lin)

private noncomputable def F_y00_body_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (h_fy00 : ("$y00" : Name) ∉ ε) (h_fy01 : ("$y01" : Name) ∉ ε)
    (h_fy10 : ("$y10" : Name) ∉ ε) (h_fy11 : ("$y11" : Name) ∉ ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType (Finmap.insert ("$y00" : Name) s₀ ∅) ε
      (.llam s₁
        (.tprod (.dual s₀) (.dual s₁))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))
      (.space (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁)))) := by
  rw [insert_empty_eq_singleton]
  refine HasType.llam_tensor {("$y00" : Name)} (by intro h; cases h) sv₁
    (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)) (fun y01 hy01 => ?_)
  have h_01_00 : y01 ≠ "$y00" := fun h => hy01 (by simp [h])
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  refine HasType.llam_tensor {("$y00" : Name), y01} (by intro h; cases h) sv₀ (SValid.dual sv₁)
    (fun y10 hy10 => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy10
  obtain ⟨h_10_00', h_10_01'⟩ := hy10
  have h_10_00 : y10 ≠ "$y00" := h_10_00'
  have h_10_01 : y10 ≠ y01 := h_10_01'
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  refine HasType.llam_real {("$y00" : Name), y01, y10} sv₁ (fun y11 hy11 => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy11
  obtain ⟨h_11_00', h_11_01', h_11_10'⟩ := hy11
  have h_11_00 : y11 ≠ "$y00" := h_11_00'
  have h_11_01 : y11 ≠ y01 := h_11_01'
  have h_11_10 : y11 ≠ y10 := h_11_10'
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  rw [← insert_empty_eq_singleton]
  rw [insert_four_eq_smul_split h_01_00.symm h_10_00.symm h_11_00.symm
    h_10_01.symm h_11_01.symm h_11_10.symm]
  exact HasType.smul SValid.real
    (disjoint_smul_split h_01_00.symm h_11_00.symm h_10_01.symm h_11_10.symm)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton "$y00" s₀)
      (Δ₁ := Finmap.singleton y10 s₀) sv₀
      (disjoint_singletons h_10_00.symm) HasType.var_lin HasType.var_lin)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton y01 s₁)
      (Δ₁ := Finmap.singleton y11 s₁) sv₁
      (disjoint_singletons h_11_01.symm) HasType.var_lin HasType.var_lin)

private noncomputable def F_y01_body_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (h_fy00 : ("$y00" : Name) ∉ ε) (h_fy01 : ("$y01" : Name) ∉ ε)
    (h_fy10 : ("$y10" : Name) ∉ ε) (h_fy11 : ("$y11" : Name) ∉ ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType
      (Finmap.insert ("$y01" : Name) s₁ (Finmap.singleton ("$y00" : Name) s₀)) ε
      (.llam s₀ (.dual s₁)
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.var "$y01") (.bvar 0)))))
      (.space (.tprod (.dual s₀) (.dual s₁))) := by
  obtain ⟨h_00_01, h_00_10, _, h_01_10, _, _⟩ := Term.y_pairwise_distinct
  refine HasType.llam_tensor {("$y00" : Name), "$y01"} (by intro h; cases h) sv₀
    (SValid.dual sv₁) (fun y10 hy10 => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy10
  obtain ⟨h_10_00', h_10_01'⟩ := hy10
  have h_10_00 : y10 ≠ "$y00" := h_10_00'
  have h_10_01 : y10 ≠ "$y01" := h_10_01'
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  refine HasType.llam_real {("$y00" : Name), "$y01", y10} sv₁ (fun y11 hy11 => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy11
  obtain ⟨h_11_00', h_11_01', h_11_10'⟩ := hy11
  have h_11_00 : y11 ≠ "$y00" := h_11_00'
  have h_11_01 : y11 ≠ "$y01" := h_11_01'
  have h_11_10 : y11 ≠ y10 := h_11_10'
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  rw [← insert_empty_eq_singleton]
  rw [insert_four_eq_smul_split h_00_01 h_10_00.symm h_11_00.symm
    h_10_01.symm h_11_01.symm h_11_10.symm]
  exact HasType.smul SValid.real
    (disjoint_smul_split h_00_01 h_11_00.symm h_10_01.symm h_11_10.symm)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton "$y00" s₀)
      (Δ₁ := Finmap.singleton y10 s₀) sv₀
      (disjoint_singletons h_10_00.symm) HasType.var_lin HasType.var_lin)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton "$y01" s₁)
      (Δ₁ := Finmap.singleton y11 s₁) sv₁
      (disjoint_singletons h_11_01.symm) HasType.var_lin HasType.var_lin)

private noncomputable def F_y10_body_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (h_fy11 : ("$y11" : Name) ∉ ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType
      (Finmap.insert ("$y10" : Name) s₀
        (Finmap.insert ("$y01" : Name) s₁
          (Finmap.singleton ("$y00" : Name) s₀))) ε
      (.llam s₁ .real
        (.smul
          (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
          (Term.innerApp s₁ (.var "$y01") (.bvar 0))))
      (.space (.dual s₁)) := by
  obtain ⟨h_00_01, h_00_10, _, h_01_10, _, _⟩ := Term.y_pairwise_distinct
  refine HasType.llam_real {("$y00" : Name), "$y01", "$y10"} sv₁ (fun y11 hy11 => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy11
  obtain ⟨h_11_00', h_11_01', h_11_10'⟩ := hy11
  have h_11_00 : y11 ≠ "$y00" := h_11_00'
  have h_11_01 : y11 ≠ "$y01" := h_11_01'
  have h_11_10 : y11 ≠ "$y10" := h_11_10'
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  rw [← insert_empty_eq_singleton]
  rw [insert_four_eq_smul_split h_00_01 h_00_10 h_11_00.symm
    h_01_10 h_11_01.symm h_11_10.symm]
  exact HasType.smul SValid.real
    (disjoint_smul_split h_00_01 h_11_00.symm h_01_10 h_11_10.symm)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton "$y00" s₀)
      (Δ₁ := Finmap.singleton "$y10" s₀) sv₀
      (disjoint_singletons h_00_10) HasType.var_lin HasType.var_lin)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton "$y01" s₁)
      (Δ₁ := Finmap.singleton y11 s₁) sv₁
      (disjoint_singletons h_11_01.symm) HasType.var_lin HasType.var_lin)

private noncomputable def F_smul_body_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType
      (Finmap.insert ("$y11" : Name) s₁
        (Finmap.insert ("$y10" : Name) s₀
          (Finmap.insert ("$y01" : Name) s₁
            (Finmap.singleton ("$y00" : Name) s₀)))) ε
      (.smul
        (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
        (Term.innerApp s₁ (.var "$y01") (.var "$y11")))
      (.space .real) := by
  obtain ⟨h_00_01, h_00_10, h_00_11, h_01_10, h_01_11, h_10_11⟩ :=
    Term.y_pairwise_distinct
  rw [← insert_empty_eq_singleton]
  rw [insert_four_eq_smul_split h_00_01 h_00_10 h_00_11 h_01_10 h_01_11 h_10_11]
  exact HasType.smul SValid.real
    (disjoint_smul_split h_00_01 h_00_11 h_01_10 h_10_11)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton "$y00" s₀)
      (Δ₁ := Finmap.singleton "$y10" s₀) sv₀
      (disjoint_singletons h_00_10) HasType.var_lin HasType.var_lin)
    (Term.innerApp_hasType (Δ₀ := Finmap.singleton "$y01" s₁)
      (Δ₁ := Finmap.singleton "$y11" s₁) sv₁
      (disjoint_singletons h_01_11) HasType.var_lin HasType.var_lin)

/-- `(∅, ε) ⊢ Space.iof (.tprod s₀ s₁) : (s₀⊗s₁)* ⊗ (s₀⊗s₁)*`. -/
noncomputable def Space.iof_hasType_tprod {ε : NLCtx} {s₀ s₁ : Space}
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType ∅ ε (Space.iof (.tprod s₀ s₁))
      (.space (.tprod (.dual (.tprod s₀ s₁)) (.dual (.tprod s₀ s₁)))) := by
  -- Outer .llam_tensor opens at fresh y_p:(s₀⊗s₁). Codomain (s₀⊗s₁)* ≠ .real.
  refine HasType.llam_tensor ∅
    (by intro h; cases h)
    (SValid.tprod sv₀ sv₁) (SValid.dual (SValid.tprod sv₀ sv₁)) (fun yp _ => ?_)
  -- The body: applyUncurry2Real s₀ s₁ (step1 applied to .bvar 0 → .var yp).
  -- step1 = applyUncurry2NonReal s₀ s₁ (s₀*⊗s₁*) F. F and step1 are closed,
  -- so openVar only touches the trailing `.bvar 0` argument.
  have h_uR_lc : Term.lc (Term.uncurry2Real s₀ s₁) :=
    HasType.lc (Term.uncurry2Real_hasType sv₀ sv₁)
  have h_step1_lc : Term.lc (Term.applyUncurry2NonReal s₀ s₁
      (.tprod (.dual s₀) (.dual s₁)) (tprod_F s₀ s₁)) :=
    HasType.lc (Term.applyUncurry2NonReal_hasType (by intro h; cases h) sv₀ sv₁
      (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)) (tprod_F_hasType sv₀ sv₁))
  have hbody : Term.openVar yp (Space.iofTprodBody s₀ s₁) =
      Term.applyUncurry2Real s₀ s₁
        (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁))
          (.var yp)) := by
    simp only [Space.iofTprodBody, Term.applyUncurry2Real,
      Term.openVar, Term.openRec, Space.openRec, if_true,
      Term.openRec_lc h_uR_lc, Term.openRec_lc h_step1_lc,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  show HasType _ ε (Term.openVar yp (Space.iofTprodBody s₀ s₁)) _
  rw [hbody]
  rw [insert_empty_eq_singleton]
  refine Term.applyUncurry2Real_hasType sv₀ sv₁ ?_
  have h_eq : (Finmap.singleton yp (.tprod s₀ s₁) : LCtx) =
      ∅ ∪ Finmap.singleton yp (.tprod s₀ s₁) := by rw [Finmap.empty_union]
  rw [h_eq]
  refine HasType.app_linear
    (SValid.tprod sv₀ sv₁)
    (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁))
    (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty) ?_ HasType.var_lin
  exact Term.applyUncurry2NonReal_hasType
    (by intro h; cases h) sv₀ sv₁
    (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁))
    (tprod_F_hasType sv₀ sv₁)

noncomputable def iof_tprod_body_hasType {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁) :
    HasType (Finmap.insert Term.p_name (.tprod s₀ s₁) ∅) ε
      (Term.applyUncurry2Real s₀ s₁
        (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁))
          (.var Term.p_name)))
      (.space (.dual (.tprod s₀ s₁))) := by
  rw [insert_empty_eq_singleton]
  refine Term.applyUncurry2Real_hasType sv₀ sv₁ ?_
  have h_eq : (Finmap.singleton Term.p_name (.tprod s₀ s₁) : LCtx) =
      ∅ ∪ Finmap.singleton Term.p_name (.tprod s₀ s₁) := by rw [Finmap.empty_union]
  rw [h_eq]
  refine HasType.app_linear
    (SValid.tprod sv₀ sv₁)
    (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁))
    (fun k hk₀ _ => absurd hk₀ Finmap.notMem_empty) ?_ HasType.var_lin
  exact Term.applyUncurry2NonReal_hasType
    (by intro h; cases h) sv₀ sv₁
    (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁))
    (tprod_F_hasType sv₀ sv₁)

/-! ## Main typing theorem. -/

/-- Distinctness of `Space.iof`'s reserved binder names. Used inside
    `Space.iof_hasType` to discharge `x ∉ Δ` premises on nested lambdas. -/
theorem Term.x0_ne_x1 : (Term.x0 : Name) ≠ Term.x1 := by decide

noncomputable def Space.iof_hasType {ε : NLCtx} (fresh : IofFresh ε) :
    (s : Space) → SValid ε s →
      HasType ∅ ε (Space.iof s) (.space (.tprod (.dual s) (.dual s)))
  | .empty,       _ => Space.iof_hasType_empty
  | .real,        _ => Space.iof_hasType_real
  | .dual _,      .dual sv' => Space.iof_hasType_dual sv'
  | .dsum _ _,    .dsum sv₀ sv₁ => Space.iof_hasType_dsum sv₀ sv₁
  | .tprod _ _,   .tprod sv₀ sv₁ => Space.iof_hasType_tprod sv₀ sv₁
  | .ker _ _ _,   sv =>
      Space.iof_hasType_ker
        fresh.fresh_x0 fresh.fresh_x1 Term.x0_ne_x1 sv
  | .coker _ _ _, sv =>
      Space.iof_hasType_coker
        fresh.fresh_x0 fresh.fresh_x1 Term.x0_ne_x1 sv
  | .img _ _ _,   sv =>
      Space.iof_hasType_img
        fresh.fresh_x0 fresh.fresh_x1 Term.x0_ne_x1 sv
  | .coimg _ _ _, sv =>
      Space.iof_hasType_coimg
        fresh.fresh_x0 fresh.fresh_x1 Term.x0_ne_x1 sv

/-! ## Bilinear-form builders (for use in the IP proof, not as semantics).

These re-package canonical builders on `V →ₗ V →ₗ ℝ` so that we can
state intermediate equalities like
`(denotTerm σ (Space.iof (.dsum s₀ s₁))).asLinMap _ _ = bilinDsum (subform_0) (subform_1)`
during the IP proof's structural recursion. -/

/-- Direct-sum bilinear form: `B (p) (q) = B₀ p.1 q.1 + B₁ p.2 q.2`. -/
noncomputable def bilinDsum {V₀ V₁ : Type*}
    [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    (B₀ : V₀ →ₗ[ℝ] V₀ →ₗ[ℝ] ℝ) (B₁ : V₁ →ₗ[ℝ] V₁ →ₗ[ℝ] ℝ) :
    (V₀ × V₁) →ₗ[ℝ] (V₀ × V₁) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun p q => B₀ p.1 q.1 + B₁ p.2 q.2)
    (by intro p₁ p₂ q; simp; ring)
    (by intro c p q; simp; ring)
    (by intro p q₁ q₂; simp; ring)
    (by intro c p q; simp; ring)

@[simp] lemma bilinDsum_apply {V₀ V₁ : Type*}
    [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    (B₀ : V₀ →ₗ[ℝ] V₀ →ₗ[ℝ] ℝ) (B₁ : V₁ →ₗ[ℝ] V₁ →ₗ[ℝ] ℝ)
    (p q : V₀ × V₁) :
    bilinDsum B₀ B₁ p q = B₀ p.1 q.1 + B₁ p.2 q.2 := rfl

/-- Tensor-product bilinear form (Mathlib `BilinForm.tmul`). -/
noncomputable def bilinTprod {V₀ V₁ : Type*}
    [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    (B₀ : V₀ →ₗ[ℝ] V₀ →ₗ[ℝ] ℝ) (B₁ : V₁ →ₗ[ℝ] V₁ →ₗ[ℝ] ℝ) :
    (V₀ ⊗[ℝ] V₁) →ₗ[ℝ] (V₀ ⊗[ℝ] V₁) →ₗ[ℝ] ℝ :=
  LinearMap.BilinForm.tmul (A := ℝ) (R := ℝ) B₀ B₁

/-- Restrict a bilinear form to a submodule. -/
noncomputable def bilinRestrict {V : Type*}
    [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : Submodule ℝ V) :
    K →ₗ[ℝ] K →ₗ[ℝ] ℝ :=
  LinearMap.BilinForm.restrict B K

@[simp] lemma bilinRestrict_apply {V : Type*}
    [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : Submodule ℝ V)
    (x y : K) : bilinRestrict B K x y = B x y := rfl

/-- Riesz-pullback bilinear form: `B' φ ψ = B (♯ φ) (♯ ψ)` where ♯ is
    the Riesz inverse V* → V (parameter — caller supplies the right ♯). -/
noncomputable def bilinDual {V : Type}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (sharp : (V →ₗ[ℝ] ℝ) →ₗ[ℝ] V) :
    (V →ₗ[ℝ] ℝ) →ₗ[ℝ] (V →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun φ ψ => B (sharp φ) (sharp ψ))
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)
    (by intros; simp)

/-- IsInnerProduct of 0 on PUnit — vacuously, since PUnit has only one element. -/
lemma isInnerProduct_zero_punit :
    IsInnerProduct (0 : PUnit →ₗ[ℝ] PUnit →ₗ[ℝ] ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y; simp
  · intro x; simp
  · intro x _; rfl

/-- Direct-sum preserves IsInnerProduct. -/
lemma bilinDsum_isInnerProduct {V₀ V₁ : Type*}
    [AddCommGroup V₀] [Module ℝ V₀] [AddCommGroup V₁] [Module ℝ V₁]
    {B₀ : V₀ →ₗ[ℝ] V₀ →ₗ[ℝ] ℝ} {B₁ : V₁ →ₗ[ℝ] V₁ →ₗ[ℝ] ℝ}
    (h₀ : IsInnerProduct B₀) (h₁ : IsInnerProduct B₁) :
    IsInnerProduct (bilinDsum B₀ B₁) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q; simp [bilinDsum_apply, h₀.1, h₁.1]
  · intro p; simp [bilinDsum_apply]; exact add_nonneg (h₀.2.1 p.1) (h₁.2.1 p.2)
  · intro p hp
    simp [bilinDsum_apply] at hp
    have h_eq : B₀ p.1 p.1 = 0 ∧ B₁ p.2 p.2 = 0 := by
      have h_nn₀ := h₀.2.1 p.1
      have h_nn₁ := h₁.2.1 p.2
      constructor <;> linarith
    exact Prod.ext (h₀.2.2 p.1 h_eq.1) (h₁.2.2 p.2 h_eq.2)

/-- Submodule restriction preserves IsInnerProduct. -/
lemma bilinRestrict_isInnerProduct {V : Type*}
    [AddCommGroup V] [Module ℝ V] {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ}
    (h : IsInnerProduct B) (K : Submodule ℝ V) :
    IsInnerProduct (bilinRestrict B K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y; simpa using h.1 x y
  · intro x; simpa using h.2.1 x
  · intro x hx
    simp [bilinRestrict_apply] at hx
    exact Subtype.ext (h.2.2 _ hx)

/-! ## Denotation-reduction lemmas for the IP proof.

The IP proof needs to compute `asLinMap V V* (denotTerm σ (Space.iof s))`
and recognize it as a specific bilinear form. The key reduction:
`asLinMap` of `innerTensor` recovers the original bilinear form, because
`innerTensor B := dualTensorHomEquiv.symm B`-wrapped-as-DVal and `asLinMap`
applies `dualTensorHom` (which is the equivalence-inverse). -/

/-- `DVal.asLinMap` of `innerTensor B` returns `B` (up to the carrier
    check inside `asLinMap`). -/
lemma asLinMap_innerTensor (V : HSpace)
    (B : V.carrier →ₗ[ℝ] V.carrier →ₗ[ℝ] ℝ) :
    DVal.asLinMap V (HSpace.dual V) (V.innerTensor B) = B := by
  unfold DVal.asLinMap DVal.asHil HSpace.innerTensor
  simp only [dif_pos]
  exact LinearEquiv.apply_symm_apply (dualTensorHomEquiv ℝ V.carrier _) B

/-- `DVal.asLinMap V₀ V₁` of `llamTensorDVal V₀ V₁ f` recovers
    `LinearMap.ofFun (fun y => (f (.hil ⟨V₀, y⟩)).atSpace V₁)`. -/
lemma asLinMap_llamTensorDVal (V₀ V₁ : HSpace) (f : DVal → DVal) :
    DVal.asLinMap V₀ V₁ (llamTensorDVal V₀ V₁ f)
      = LinearMap.ofFun (fun y : V₀.carrier => (f (.hil ⟨V₀, y⟩)).atSpace V₁) := by
  unfold DVal.asLinMap DVal.asHil llamTensorDVal
  simp only [dif_pos]
  exact LinearEquiv.apply_symm_apply
    (dualTensorHomEquiv ℝ V₀.carrier V₁.carrier) _

/-- `.atSpace V` on a `.hil ⟨V, v⟩` reduces to `v` (carriers match). -/
@[simp] lemma atSpace_hil_self (V : HSpace) (v : V.carrier) :
    DVal.atSpace V (.hil ⟨V, v⟩) = v := by
  unfold DVal.atSpace DVal.asHil
  simp only [dif_pos]

/-- `LinearMap.ofFun f = g` when `f` agrees pointwise with the LinearMap
    `g`. Derives `IsLinearMap` of `f` from `g`'s linearity automatically. -/
lemma linearMap_ofFun_eq_of_pt {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V → W) (g : V →ₗ[ℝ] W) (hg : ∀ x, f x = g x) :
    LinearMap.ofFun f = g := by
  have h_lin : IsLinearMap ℝ f := by
    constructor
    · intros y₁ y₂; rw [hg, hg, hg]; exact g.map_add y₁ y₂
    · intros c y; rw [hg, hg]; exact g.map_smul c y
  apply LinearMap.ext
  intro x
  rw [LinearMap.ofFun_apply_of_isLinearMap h_lin]
  exact hg x

/-- `atSpace (HSpace.dual V₀)` on `llamRealDVal V₀ f` returns the ofFun. -/
lemma atSpace_llamRealDVal (V₀ : HSpace) (f : DVal → ℝ) :
    (llamRealDVal V₀ f).atSpace (HSpace.dual V₀)
      = LinearMap.ofFun (fun y' : V₀.carrier => f (.hil ⟨V₀, y'⟩)) := by
  unfold llamRealDVal DVal.atSpace DVal.asHil
  simp only [dif_pos]

/-- `σ.bind x v` lookup of `x` gives `v`. -/
@[simp] lemma denotTerm_var_bind_self (σ : DEnv) (x : Name) (v : DVal) :
    denotTerm (σ.bind x v) (.var x) = v := by
  show ((σ.bind x v).vars.lookup x).getD DVal.default = v
  unfold DEnv.bind
  simp [Finmap.lookup_insert]

/-- `(σ.bind x v).bind x' v').vars.lookup x = some v` when `x ≠ x'`. -/
@[simp] lemma denotTerm_var_bind_other_bind_self {σ : DEnv} {x x' : Name}
    (v v' : DVal) (h : x ≠ x') :
    denotTerm ((σ.bind x v).bind x' v') (.var x) = v := by
  show (((σ.bind x v).bind x' v').vars.lookup x).getD DVal.default = v
  unfold DEnv.bind
  simp [Finmap.lookup_insert_of_ne _ h, Finmap.lookup_insert]

/-- `.hil ⟨HSpace.real, y⟩.asReal = y`. -/
@[simp] lemma DVal.asReal_hil_real (y : ℝ) :
    DVal.asReal (.hil ⟨HSpace.real, y⟩) = y := by
  unfold DVal.asReal DVal.asHil
  simp only [dif_pos]

/-- `.hil ⟨V, v⟩.asHil = ⟨V, v⟩` directly. -/
@[simp] lemma DVal.asHil_hil (V : HSpace) (v : V.carrier) :
    DVal.asHil (.hil ⟨V, v⟩) = ⟨V, v⟩ := rfl

/-- Smul denotation when both args denote at HSpace.real. -/
lemma denotTerm_smul_real (σ : DEnv) (e₀ e₁ : Term) (y : ℝ)
    (h₁ : denotTerm σ e₁ = .hil ⟨HSpace.real, y⟩) :
    denotTerm σ (.smul e₀ e₁) = .hil ⟨HSpace.real, (denotTerm σ e₀).asReal * y⟩ := by
  show (let ⟨V₁, v₁⟩ := (denotTerm σ e₁).asHil
        DVal.hil ⟨V₁, (denotTerm σ e₀).asReal • v₁⟩) = _
  rw [h₁]
  show DVal.hil ⟨HSpace.real, (denotTerm σ e₀).asReal • y⟩ = _
  rfl

/-- `.addAt` of two `.hil` values at the same HSpace. -/
@[simp] lemma DVal.addAt_hil_hil (V : HSpace) (v₀ v₁ : V.carrier) :
    DVal.addAt (.hil ⟨V, v₀⟩) (.hil ⟨V, v₁⟩) = .hil ⟨V, v₀ + v₁⟩ := by
  unfold DVal.addAt DVal.asHil
  simp

/-- denot of `.add` when both args denote at the same HSpace.real value. -/
lemma denotTerm_add_real (σ : DEnv) (e₀ e₁ : Term) (a b : ℝ)
    (h₀ : denotTerm σ e₀ = .hil ⟨HSpace.real, a⟩)
    (h₁ : denotTerm σ e₁ = .hil ⟨HSpace.real, b⟩) :
    denotTerm σ (.add e₀ e₁) = .hil ⟨HSpace.real, a + b⟩ := by
  show (denotTerm σ e₀).addAt (denotTerm σ e₁) = _
  rw [h₀, h₁]
  exact DVal.addAt_hil_hil _ _ _

/-- `asLinMap` of `embedDVal V_sub V_amb incl` returns `incl`. -/
lemma asLinMap_embedDVal (V_sub V_amb : HSpace)
    (incl : V_sub.carrier →ₗ[ℝ] V_amb.carrier) :
    DVal.asLinMap V_sub V_amb (embedDVal V_sub V_amb incl) = incl := by
  unfold embedDVal DVal.asLinMap DVal.asHil
  simp only [dif_pos]
  exact LinearEquiv.apply_symm_apply
    (dualTensorHomEquiv ℝ V_sub.carrier V_amb.carrier) _

/-- `asLinFunctional V` of `.hil ⟨HSpace.dual V, φ⟩` returns `φ`. -/
lemma asLinFunctional_hil_dual (V : HSpace) (φ : V.carrier →ₗ[ℝ] ℝ) :
    DVal.asLinFunctional V
      (.hil ⟨HSpace.dual V, φ⟩) = φ := by
  unfold DVal.asLinFunctional DVal.asHil
  simp only [dif_pos]

/-- Denot of `.embed (.ker s₀ s₁ e)` at any σ, parameterized by σ's `e`-denot.
    Reduces to embedDVal with K.subtype, given that the inner f's matches. -/
lemma denot_embed_ker (σ : DEnv) (s₀ s₁ : Space) (e : Term) :
    let V₀ := denotSpace σ s₀
    let V₁ := denotSpace σ s₁
    let f := (denotTerm σ e).asLinMap V₀ V₁
    let V_sub := HSpace.ofSubmodule V₀ (LinearMap.ker f)
    denotTerm σ (.embed (.ker s₀ s₁ e)) = embedDVal V_sub V₀ (LinearMap.ker f).subtype := rfl

/-! ## `IsCanonical` — σ.innerAssign matches the canonical IP construction.

We provide two equivalent (under appropriate hypotheses) views:

  • `DEnv.IsCanonical σ` — the *direct* equation: `σ.innerAssign` of any
    `denotSpace σ s` equals the inner product that `Space.iof s` denotes
    to (viewed via `asLinMap`).

  • `DEnv.IsCanonicalStructured σ` — the *structural* per-constructor
    constraints: σ.innerAssign on each canonical HSpace constructor
    (`.real`, `.empty`, `.dsum V₀ V₁`, `.tprod V₀ V₁`,
    `.ofSubmodule V K`) equals the corresponding `bilin*` builder
    applied to σ.innerAssign on the sub-spaces.

Under both, `lem:innerLemap` is trivial — `IsInnerProduct` of the iof
denotation is just `σ.innerIsIP` of the corresponding HSpace.

The "later we prove this is literally the case" — existence of a
canonical σ — is a separate theorem (see `exists_canonical_DEnv`,
TBD). -/
def DEnv.IsCanonical (σ : DEnv) (ε : NLCtx) : Prop :=
  ∀ s : Space, SValid ε s →
    (denotSpace σ s).innerProduct =
      (denotTerm σ (Space.iof s)).asLinMap
        (denotSpace σ s) (HSpace.dual (denotSpace σ s))

theorem Space.iof_denot_isInnerProduct_canonical
    {σ : DEnv} {ε : NLCtx} (h_can : σ.IsCanonical ε)
    {s : Space} (sv : SValid ε s) :
    IsInnerProduct
      ((denotTerm σ (Space.iof s)).asLinMap
        (denotSpace σ s) (HSpace.dual (denotSpace σ s))) := by
  rw [← h_can s sv]
  exact (denotSpace σ s).innerIsIP

/-- Forward direction (just `IsCanonical` restated): under the canonical
    inner-product assignment, `Space.iof s` denotationally **IS** the
    σ-chosen inner product on `denotSpace σ s`.

    This is the conditional statement: *given* canonical σ, iof's
    denotation equals the inner product. -/
theorem Space.iof_denot_eq_innerAssign
    {σ : DEnv} {ε : NLCtx} (h_can : σ.IsCanonical ε)
    {s : Space} (sv : SValid ε s) :
    (denotTerm σ (Space.iof s)).asLinMap
      (denotSpace σ s) (HSpace.dual (denotSpace σ s)) =
        (denotSpace σ s).innerProduct :=
  (h_can s sv).symm

/-! ## Existence of canonical DEnv. -/

/-- For any HSpace V, a positive-definite bilinear form exists. -/
lemma exists_isInnerProduct (V : HSpace) :
    ∃ B : V.carrier →ₗ[ℝ] V.carrier →ₗ[ℝ] ℝ, IsInnerProduct B :=
  ⟨V.innerProduct, V.innerIsIP⟩

/-- `DVal.asLinMap V₁ V₀` of `pinvTensorDVal V₀ V₁ d` returns the
    Moore-Penrose pseudo-inverse of `d.asLinMap V₀ V₁`. -/
lemma asLinMap_pinvTensorDVal (V₀ V₁ : HSpace) (d : DVal) :
    DVal.asLinMap V₁ V₀ (pinvTensorDVal V₀ V₁ d)
      = LinearMap.mooreInv V₀.innerIsIP V₁.innerIsIP
          (DVal.asLinMap V₀ V₁ d) := by
  unfold pinvTensorDVal DVal.asLinMap DVal.asHil
  simp only [dif_pos]
  exact LinearEquiv.apply_symm_apply
    (dualTensorHomEquiv ℝ V₁.carrier V₀.carrier) _

/-- **Bridge sub-lemma**: `mooreInv` of the curry of `V.innerProduct`
    equals `rieszInv`. Both are the inverse of `V.IP : V → V*` (bijective
    for PD on fin-dim V); equality follows by `V.IP`-injectivity once we
    show both compose with `V.IP` to give the identity.

    Right inverse via `mooreInv_image_eq_starProjection` + `range V.IP = ⊤`. -/
private lemma mooreInv_innerProduct_eq_rieszInv (V : HSpace) :
    LinearMap.mooreInv V.innerIsIP (HSpace.dual V).innerIsIP V.innerProduct
      = V.innerIsIP.rieszInv := by
  have h_V_inj : Function.Injective
      (V.innerProduct : V.carrier → (V.carrier →ₗ[ℝ] ℝ)) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx' : V.innerProduct x = 0 := LinearMap.mem_ker.mp hx
    have hxx : V.innerProduct x x = 0 := by rw [hx']; rfl
    exact V.innerIsIP.2.2 x hxx
  have h_dim : Module.finrank ℝ V.carrier =
      Module.finrank ℝ (V.carrier →ₗ[ℝ] ℝ) := Subspace.dual_finrank_eq.symm
  have h_V_surj : Function.Surjective
      (V.innerProduct : V.carrier → (V.carrier →ₗ[ℝ] ℝ)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_dim).mp h_V_inj
  have h_range_eq_top : LinearMap.range V.innerProduct = ⊤ :=
    LinearMap.range_eq_top.mpr h_V_surj
  apply LinearMap.ext
  intro φ
  apply h_V_inj
  -- Goal: V.IP (mooreInv φ) = V.IP (rieszInv φ).
  -- LHS = (range V.IP).starProjection φ via mooreInv_image_eq_starProjection
  --     = ⊤.starProjection φ = φ.
  -- RHS = φ via LinearEquiv.apply_symm_apply.
  letI _ := V.innerIsIP.toIPSCore
  letI _ := (HSpace.dual V).innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V.carrier :=
    (V.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : NormedAddCommGroup (V.carrier →ₗ[ℝ] ℝ) :=
    ((HSpace.dual V).innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  letI _ : InnerProductSpace ℝ (V.carrier →ₗ[ℝ] ℝ) :=
    InnerProductSpace.ofCore inferInstance
  rw [LinearMap.mooreInv_image_eq_starProjection V.innerIsIP
    (HSpace.dual V).innerIsIP V.innerProduct φ]
  -- Use the starProjection_eq_self_iff route to avoid motive issues.
  have h_proj : (LinearMap.range V.innerProduct).starProjection φ = φ :=
    Submodule.starProjection_eq_self_iff.mpr (h_range_eq_top ▸ Submodule.mem_top)
  rw [h_proj]
  -- Goal: φ = V.IP (rieszInv φ).
  symm
  unfold IsInnerProduct.rieszInv
  exact (LinearMap.linearEquivOfInjective _ _ _).apply_symm_apply φ

/-- Bridge: under freshness of `x0` against `FV(s)`, the denotation of
    `Term.flat s` decoded as `LinearMap V → V*` equals `V.innerProduct`. -/
private lemma asLinMap_denotTerm_flat
    {ε : NLCtx} (σ : DEnv) (s : Space) (sv : SValid ε s)
    (h_fresh : Term.x0 ∉ Space.fv s) :
    DVal.asLinMap (denotSpace σ s) (HSpace.dual (denotSpace σ s))
        (denotTerm σ (Term.flat s))
      = (denotSpace σ s).innerProduct := by
  set V := denotSpace σ s with hV
  show DVal.asLinMap V (HSpace.dual V) (denotTerm σ
    (.llam s (.dual s) (.appL s (.dual s) (.inner s) (.bvar 0))))
    = V.innerProduct
  rw [denotTerm_llam_non_real (by intro h; cases h)]
  -- Under σ.bind x0 v, denotSpace σ.bind x0 v s = denotSpace σ s = V (by FV-irrelev).
  have h_denot_s : ∀ v : DVal, denotSpace (σ.bind Term.x0 v) s = V := fun v =>
    denotSpace_agree s (DEnv.AgreeOn.bind_left_of_not_mem h_fresh)
  -- denotSpace s.dual = HSpace.dual (denotSpace s).
  have h_denot_s_dual : ∀ v : DVal,
      denotSpace (σ.bind Term.x0 v) (.dual s) = HSpace.dual V := fun v => by
    rw [show denotSpace (σ.bind Term.x0 v) (.dual s)
          = HSpace.dual (denotSpace (σ.bind Term.x0 v) s) from rfl, h_denot_s v]
  -- D1 bridge: denotTermAux σ [v] body = denotTerm (σ.bind x0 v) (openVar x0 body).
  have h_aux_bridge : ∀ v : DVal,
      denotTermAux σ [v] (.appL s (.dual s) (.inner s) (.bvar 0))
        = denotTerm (σ.bind Term.x0 v)
            (.appL s (.dual s) (.inner s) (.var Term.x0)) := by
    intro v
    rw [show (.appL s (.dual s) (.inner s) (.var Term.x0) : Term)
          = Term.openVar Term.x0 (.appL s (.dual s) (.inner s) (.bvar 0)) from by
        simp [Term.openVar, Term.openRec, Space.openRec_lc sv.lc,
          Space.openRec_lc (SValid.dual sv).lc]]
    rw [denotTerm_openVar_bind]
    · simp only [Term.openVar, Term.openRec, Space.openRec_lc sv.lc,
        Space.openRec_lc (SValid.dual sv).lc]
      exact Term.lc.appL sv.lc (SValid.dual sv).lc (Term.lc.inner sv.lc) Term.lc.var
    · simp only [Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty, or_false]
      intro h
      rcases h with (h | h) | h <;> exact h_fresh h
  rw [show llamTensorDVal (denotSpace σ s) (denotSpace σ (.dual s))
        (fun v => denotTermAux σ [v]
          (.appL s (.dual s) (.inner s) (.bvar 0)))
      = llamTensorDVal V (HSpace.dual V)
        (fun v => denotTerm (σ.bind Term.x0 v)
          (.appL s (.dual s) (.inner s) (.var Term.x0))) from by
        simp only [hV]; congr 1; funext v; exact h_aux_bridge v]
  rw [asLinMap_llamTensorDVal]
  apply linearMap_ofFun_eq_of_pt _ V.innerProduct
  intro y
  -- Body under σ' := σ.bind x0 ⟨V, y⟩: appL s (.dual s) (inner s) (var x0).
  -- denot appL: .hil ⟨V*, asLinMap V V* (inner_denot) (atSpace V (var_denot))⟩.
  -- inner denot = V.innerTensor V.IP; asLinMap → V.IP; var_x0 denot under σ' = .hil ⟨V, y⟩;
  -- atSpace V = y. So body denot.atSpace V* = V.IP y.
  let σ' := σ.bind Term.x0 (.hil ⟨V, y⟩)
  have h_inner_eq : denotSpace σ' s = V := h_denot_s _
  -- denot σ' (appL s s.dual (inner s) (var x0)) reduces with σ'-context denotSpaces = V, V*.
  -- Use show to align types — denotSpace σ' s = V, denotSpace σ' s.dual = V*.
  show (denotTerm σ' (.appL s (.dual s) (.inner s) (.var Term.x0))).atSpace
        (HSpace.dual V) = V.innerProduct y
  -- Compute denot of appL using FV-irrelevance to switch σ' denotSpaces back to V, V*.
  have h_appL : denotTerm σ' (.appL s (.dual s) (.inner s) (.var Term.x0))
      = .hil ⟨HSpace.dual V,
              ((denotTerm σ' (.inner s)).asLinMap V (HSpace.dual V))
                ((denotTerm σ' (.var Term.x0)).atSpace V)⟩ := by
    show (let V₀ := denotSpace σ' s
          let V₁ := denotSpace σ' (.dual s)
          let f := (denotTerm σ' (.inner s)).asLinMap V₀ V₁
          let v : V₀.carrier := (denotTerm σ' (.var Term.x0)).atSpace V₀
          DVal.hil ⟨V₁, f v⟩) = _
    -- Substitute denotSpace σ' s = V and denotSpace σ' s.dual = V*
    rw [h_denot_s, h_denot_s_dual]
  rw [h_appL, atSpace_hil_self]
  -- Goal: asLinMap V V* (denot σ' inner_s) (atSpace V (var_x0 denot)) = V.IP y.
  -- denot σ' (.inner s) = (denotSpace σ' s).innerTensor (denotSpace σ' s).innerProduct.
  -- After h_denot_s: = V.innerTensor V.innerProduct.
  have h_inner_denot : denotTerm σ' (.inner s)
      = HSpace.innerTensor V V.innerProduct := by
    show (denotSpace σ' s).innerTensor (denotSpace σ' s).innerProduct = _
    rw [h_denot_s]
  rw [h_inner_denot, asLinMap_innerTensor]
  rw [denotTerm_var_bind_self]
  rw [atSpace_hil_self]

private lemma asLinMap_denotTerm_sharp_eq_rieszInv
    {ε : NLCtx} (σ : DEnv) (s : Space) (sv : SValid ε s)
    (h_fresh : Term.x0 ∉ Space.fv s) :
    DVal.asLinMap (HSpace.dual (denotSpace σ s)) (denotSpace σ s)
        (denotTerm σ (Term.sharp s))
      = (denotSpace σ s).innerIsIP.rieszInv := by
  set V := denotSpace σ s with hV
  show DVal.asLinMap (HSpace.dual V) V
      (pinvTensorDVal V (HSpace.dual V) (denotTerm σ (Term.flat s)))
      = V.innerIsIP.rieszInv
  rw [asLinMap_pinvTensorDVal V (HSpace.dual V) (denotTerm σ (Term.flat s))]
  rw [asLinMap_denotTerm_flat σ s sv h_fresh]
  exact mooreInv_innerProduct_eq_rieszInv V

/-- Any LinearMap from PUnit to anything is the zero map (PUnit is a
    subsingleton, and linear maps preserve 0). -/
private lemma linearMap_from_punit_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f g : PUnit →ₗ[ℝ] V) : f = g := by
  apply LinearMap.ext
  intro x
  have hx : x = (0 : PUnit) := rfl
  rw [hx, LinearMap.map_zero, LinearMap.map_zero]

/-- Any bilinear form on PUnit is the zero form. -/
private lemma bilin_punit_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    (f g : PUnit →ₗ[ℝ] PUnit →ₗ[ℝ] V) : f = g :=
  linearMap_from_punit_eq f g

/-- Bridge: under freshness, `(denot σ kembed0).asLinMap V₀ V_sum = inl`. -/
private lemma asLinMap_denotTerm_kembed0
    {ε : NLCtx} (σ : DEnv) (s₀ s₁ : Space)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (h_fresh_s₀ : Term.x0 ∉ Space.fv s₀) (h_fresh_s₁ : Term.x0 ∉ Space.fv s₁) :
    DVal.asLinMap (denotSpace σ s₀) (HSpace.dsum (denotSpace σ s₀) (denotSpace σ s₁))
        (denotTerm σ (Term.kembed0 s₀ s₁))
      = LinearMap.inl ℝ (denotSpace σ s₀).carrier (denotSpace σ s₁).carrier := by
  set V₀ := denotSpace σ s₀
  set V₁ := denotSpace σ s₁
  show DVal.asLinMap V₀ (HSpace.dsum V₀ V₁) (denotTerm σ
    (.llam s₀ (.dsum s₀ s₁) (.dsumE (.bvar 0) (.zero s₁))))
    = LinearMap.inl ℝ V₀.carrier V₁.carrier
  rw [denotTerm_llam_non_real (by intro h; cases h)]
  have h_bridge : ∀ v : DVal,
      denotTermAux σ [v] (.dsumE (.bvar 0) (.zero s₁))
        = denotTerm (σ.bind Term.x0 v) (.dsumE (.var Term.x0) (.zero s₁)) := by
    intro v
    rw [show (.dsumE (.var Term.x0) (.zero s₁) : Term)
          = Term.openVar Term.x0 (.dsumE (.bvar 0) (.zero s₁)) from by
        simp [Term.openVar, Term.openRec, Space.openRec_lc sv₁.lc]]
    rw [denotTerm_openVar_bind]
    · simp only [Term.openVar, Term.openRec, Space.openRec_lc sv₁.lc]
      exact Term.lc.dsumE Term.lc.var (Term.lc.zero sv₁.lc)
    · simp only [Term.fv, Finset.mem_union, Finset.notMem_empty, false_or]
      exact h_fresh_s₁
  show DVal.asLinMap V₀ (HSpace.dsum V₀ V₁)
    (llamTensorDVal V₀ (HSpace.dsum V₀ V₁)
      (fun v => denotTermAux σ [v] (.dsumE (.bvar 0) (.zero s₁))))
    = LinearMap.inl ℝ V₀.carrier V₁.carrier
  rw [show (fun v => denotTermAux σ [v] (.dsumE (.bvar 0) (.zero s₁)))
        = (fun v => denotTerm (σ.bind Term.x0 v) (.dsumE (.var Term.x0) (.zero s₁)))
      from funext h_bridge]
  rw [asLinMap_llamTensorDVal]
  apply linearMap_ofFun_eq_of_pt _ (LinearMap.inl ℝ V₀.carrier V₁.carrier)
  intro y
  -- Body under σ.bind x0 ⟨V₀, y⟩: dsumE (var x0) (zero s₁).
  set σ' := σ.bind Term.x0 (.hil ⟨V₀, y⟩)
  have h_dV₁ : denotSpace σ' s₁ = V₁ :=
    denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_s₁)
  -- denot σ' (.var x0) = .hil ⟨V₀, y⟩.
  -- denot σ' (.zero s₁) = .hil ⟨V₁, 0⟩.
  -- .dsumE = .hil ⟨HSpace.dsum V₀ V₁, (y, 0)⟩.
  -- atSpace HSpace.dsum V₀ V₁ = (y, 0) = inl y.
  show ((denotTerm σ' (.dsumE (.var Term.x0) (.zero s₁)))).atSpace
        (HSpace.dsum V₀ V₁) = LinearMap.inl ℝ V₀.carrier V₁.carrier y
  show (let ⟨V₀', v₀'⟩ := (denotTerm σ' (.var Term.x0)).asHil
        let ⟨V₁', v₁'⟩ := (denotTerm σ' (.zero s₁)).asHil
        DVal.hil ⟨HSpace.dsum V₀' V₁', (v₀', v₁')⟩).atSpace
          (HSpace.dsum V₀ V₁) = _
  rw [denotTerm_var_bind_self]
  show (let ⟨V₁', v₁'⟩ := (denotTerm σ' (.zero s₁)).asHil
        DVal.hil ⟨HSpace.dsum V₀ V₁', (y, v₁')⟩).atSpace
          (HSpace.dsum V₀ V₁) = _
  show (DVal.hil ⟨HSpace.dsum V₀ (denotSpace σ' s₁),
        (y, (0 : (denotSpace σ' s₁).carrier))⟩).atSpace
          (HSpace.dsum V₀ V₁) = _
  rw [h_dV₁]
  rw [atSpace_hil_self]
  rfl

/-- Bridge: `(denot σ kembed1).asLinMap V₁ V_sum = inr`. Symmetric. -/
private lemma asLinMap_denotTerm_kembed1
    {ε : NLCtx} (σ : DEnv) (s₀ s₁ : Space)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (h_fresh_s₀ : Term.x0 ∉ Space.fv s₀) :
    DVal.asLinMap (denotSpace σ s₁) (HSpace.dsum (denotSpace σ s₀) (denotSpace σ s₁))
        (denotTerm σ (Term.kembed1 s₀ s₁))
      = LinearMap.inr ℝ (denotSpace σ s₀).carrier (denotSpace σ s₁).carrier := by
  set V₀ := denotSpace σ s₀
  set V₁ := denotSpace σ s₁
  show DVal.asLinMap V₁ (HSpace.dsum V₀ V₁) (denotTerm σ
    (.llam s₁ (.dsum s₀ s₁) (.dsumE (.zero s₀) (.bvar 0))))
    = LinearMap.inr ℝ V₀.carrier V₁.carrier
  rw [denotTerm_llam_non_real (by intro h; cases h)]
  have h_bridge : ∀ v : DVal,
      denotTermAux σ [v] (.dsumE (.zero s₀) (.bvar 0))
        = denotTerm (σ.bind Term.x0 v) (.dsumE (.zero s₀) (.var Term.x0)) := by
    intro v
    rw [show (.dsumE (.zero s₀) (.var Term.x0) : Term)
          = Term.openVar Term.x0 (.dsumE (.zero s₀) (.bvar 0)) from by
        simp [Term.openVar, Term.openRec, Space.openRec_lc sv₀.lc]]
    rw [denotTerm_openVar_bind]
    · simp only [Term.openVar, Term.openRec, Space.openRec_lc sv₀.lc]
      exact Term.lc.dsumE (Term.lc.zero sv₀.lc) Term.lc.var
    · simp only [Term.fv, Finset.mem_union, Finset.notMem_empty, or_false]
      exact h_fresh_s₀
  show DVal.asLinMap V₁ (HSpace.dsum V₀ V₁)
    (llamTensorDVal V₁ (HSpace.dsum V₀ V₁)
      (fun v => denotTermAux σ [v] (.dsumE (.zero s₀) (.bvar 0))))
    = LinearMap.inr ℝ V₀.carrier V₁.carrier
  rw [show (fun v => denotTermAux σ [v] (.dsumE (.zero s₀) (.bvar 0)))
        = (fun v => denotTerm (σ.bind Term.x0 v) (.dsumE (.zero s₀) (.var Term.x0)))
      from funext h_bridge]
  rw [asLinMap_llamTensorDVal]
  apply linearMap_ofFun_eq_of_pt _ (LinearMap.inr ℝ V₀.carrier V₁.carrier)
  intro y
  set σ' := σ.bind Term.x0 (.hil ⟨V₁, y⟩)
  have h_dV₀ : denotSpace σ' s₀ = V₀ :=
    denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_s₀)
  show ((denotTerm σ' (.dsumE (.zero s₀) (.var Term.x0)))).atSpace
        (HSpace.dsum V₀ V₁) = LinearMap.inr ℝ V₀.carrier V₁.carrier y
  show (let ⟨V₀', v₀'⟩ := (denotTerm σ' (.zero s₀)).asHil
        let ⟨V₁', v₁'⟩ := (denotTerm σ' (.var Term.x0)).asHil
        DVal.hil ⟨HSpace.dsum V₀' V₁', (v₀', v₁')⟩).atSpace
          (HSpace.dsum V₀ V₁) = _
  rw [denotTerm_var_bind_self]
  show (DVal.hil ⟨HSpace.dsum (denotSpace σ' s₀) V₁,
        ((0 : (denotSpace σ' s₀).carrier), y)⟩).atSpace
          (HSpace.dsum V₀ V₁) = _
  rw [h_dV₀]
  rw [atSpace_hil_self]
  rfl

/-- **Bridge for `.dsum`**: under the canonical direct-sum IP on V₀ × V₁,
    the Moore-Penrose pseudo-inverse of the canonical injection
    `LinearMap.inl : V₀ →ₗ V₀ × V₁` is the canonical projection `LinearMap.fst`.

    Proof: `LinearMap.inl` is injective, with range `V₀ × {0}` (= `ker snd`).
    The orth complement of `V₀ × {0}` is `{0} × V₁` (= `ker fst`) under the
    dsum IP. So `starProjection (range inl) (a, b) = (a, 0) = inl a`. Combined
    with `mooreInv_image_eq_starProjection` + inl-injectivity, mooreInv inl = fst. -/
private lemma mooreInv_inl_eq_fst (V₀ V₁ : HSpace) :
    LinearMap.mooreInv V₀.innerIsIP (HSpace.dsum V₀ V₁).innerIsIP
        (LinearMap.inl ℝ V₀.carrier V₁.carrier)
      = LinearMap.fst ℝ V₀.carrier V₁.carrier := by
  set V_sum := HSpace.dsum V₀ V₁ with hV_sum
  have h_inj : Function.Injective (LinearMap.inl ℝ V₀.carrier V₁.carrier) := by
    intro a b hab
    have := (Prod.mk_inj.mp hab).1
    exact this
  letI _ := V₀.innerIsIP.toIPSCore
  letI _ := V_sum.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V₀.carrier :=
    (V₀.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : NormedAddCommGroup V_sum.carrier :=
    (V_sum.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V₀.carrier := InnerProductSpace.ofCore inferInstance
  letI _ : InnerProductSpace ℝ V_sum.carrier := InnerProductSpace.ofCore inferInstance
  apply LinearMap.ext
  intro y
  apply h_inj
  rw [LinearMap.mooreInv_image_eq_starProjection]
  -- Goal: starProjection (range inl) y = inl (fst y) = (y.1, 0).
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · -- inl (fst y) ∈ range inl.
    exact ⟨y.1, rfl⟩
  · -- ∀ w ∈ range inl, ⟨y - inl (fst y), w⟩ = 0.
    intro w hw
    obtain ⟨v, hv⟩ := hw
    subst hv
    -- Goal: ⟨y - inl y.1, inl v⟩ = 0.
    -- y - inl y.1 = (y.1, y.2) - (y.1, 0) = (0, y.2).
    -- inl v = (v, 0).
    -- ⟨(0, y.2), (v, 0)⟩ = V₀.IP 0 v + V₁.IP y.2 0 = 0.
    show V_sum.innerProduct (y - LinearMap.inl ℝ V₀.carrier V₁.carrier y.1)
            (LinearMap.inl ℝ V₀.carrier V₁.carrier v) = 0
    show V₀.innerProduct (y.1 - y.1) v + V₁.innerProduct (y.2 - 0) 0 = 0
    simp

/-- **Bridge for `.dsum`** (right side): mooreInv of `LinearMap.inr` is
    `LinearMap.snd`. Symmetric to `mooreInv_inl_eq_fst`. -/
private lemma mooreInv_inr_eq_snd (V₀ V₁ : HSpace) :
    LinearMap.mooreInv V₁.innerIsIP (HSpace.dsum V₀ V₁).innerIsIP
        (LinearMap.inr ℝ V₀.carrier V₁.carrier)
      = LinearMap.snd ℝ V₀.carrier V₁.carrier := by
  set V_sum := HSpace.dsum V₀ V₁ with hV_sum
  have h_inj : Function.Injective (LinearMap.inr ℝ V₀.carrier V₁.carrier) := by
    intro a b hab
    have := (Prod.mk_inj.mp hab).2
    exact this
  letI _ := V₁.innerIsIP.toIPSCore
  letI _ := V_sum.innerIsIP.toIPSCore
  letI _ : NormedAddCommGroup V₁.carrier :=
    (V₁.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : NormedAddCommGroup V_sum.carrier :=
    (V_sum.innerIsIP.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V₁.carrier := InnerProductSpace.ofCore inferInstance
  letI _ : InnerProductSpace ℝ V_sum.carrier := InnerProductSpace.ofCore inferInstance
  apply LinearMap.ext
  intro y
  apply h_inj
  rw [LinearMap.mooreInv_image_eq_starProjection]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨y.2, rfl⟩
  · intro w hw
    obtain ⟨v, hv⟩ := hw
    subst hv
    show V_sum.innerProduct (y - LinearMap.inr ℝ V₀.carrier V₁.carrier y.2)
            (LinearMap.inr ℝ V₀.carrier V₁.carrier v) = 0
    show V₀.innerProduct (y.1 - 0) 0 + V₁.innerProduct (y.2 - y.2) v = 0
    simp

private theorem denot_llam_body_isLinear
    {Δ : LCtx} {ε : NLCtx} {x : Name} {s_in s_τ : Space} {body : Term}
    (h_xΔ : x ∉ Δ) (h_xε : x ∉ ε)
    (d_s_in : SValid ε s_in) (d_s_τ : SValid ε s_τ)
    (d_body : HasType (Finmap.insert x s_in Δ) ε body (.space s_τ))
    (ctx : CtxWF Δ ε)
    {σ : DEnv} (wf : EnvWF σ Δ ε) :
    IsLinearMap ℝ (fun y : (denotSpace σ s_in).carrier =>
      (denotTerm (σ.bind x (.hil ⟨denotSpace σ s_in, y⟩)) body).atSpace
        (denotSpace σ s_τ)) := by
  have h_x_not_fv_s_in : x ∉ Space.fv s_in := d_s_in.notMem_fv_of_notMem_ε h_xε
  have h_x_not_fv_s_τ : x ∉ Space.fv s_τ := d_s_τ.notMem_fv_of_notMem_ε h_xε
  have ctx_ext : CtxWF (Finmap.insert x s_in Δ) ε := {
    disjoint := fun x'' hx'' hx''_ε => by
      rcases Finmap.mem_insert.mp hx'' with rfl | hx_in_Δ
      · exact h_xε hx''_ε
      · exact ctx.disjoint x'' hx_in_Δ hx''_ε
    lin_fv_in_ε := fun x'' s'' hx'' z hz => by
      by_cases h_eq : x'' = x
      · subst x''
        rw [Finmap.lookup_insert] at hx''
        have h_eq_s : s'' = s_in := (Option.some.inj hx'').symm
        rw [h_eq_s] at hz
        exact Finmap.mem_keys.mp (SValid.fv_closure d_s_in hz)
      · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
        exact ctx.lin_fv_in_ε x'' s'' hx'' z hz
    nl_fv_in_ε := ctx.nl_fv_in_ε
  }
  set V_s_in_loc := denotSpace σ s_in with hV_s_in_loc
  let v_default : DVal := .hil ⟨V_s_in_loc, 0⟩
  let σ_test : DEnv := σ.bind x v_default
  have h_v_default : v_default.matchesShape (HType.hil V_s_in_loc) :=
    DVal.matchesShape_hil_rfl _ _
  have h_denot_s_in_test : denotSpace σ_test s_in = V_s_in_loc :=
    denotSpace_agree s_in (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s_in)
  have h_denot_s_τ_test : denotSpace σ_test s_τ = denotSpace σ s_τ :=
    denotSpace_agree s_τ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s_τ)
  have wf_test : EnvWF σ_test (Finmap.insert x s_in Δ) ε := {
    lin_match := fun x'' s'' hx'' => by
      by_cases h_eq : x'' = x
      · subst x''
        rw [Finmap.lookup_insert] at hx''
        have h_eq_s : s'' = s_in := (Option.some.inj hx'').symm
        subst h_eq_s
        refine ⟨v_default, ?_, ?_⟩
        · show σ_test.vars.lookup x = some v_default
          simp [σ_test, DEnv.bind, Finmap.lookup_insert]
        · rw [h_denot_s_in_test]; exact h_v_default
      · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
        obtain ⟨w, h_lookup, h_match⟩ := wf.lin_match x'' s'' hx''
        refine ⟨w, ?_, ?_⟩
        · show σ_test.vars.lookup x'' = some w
          simp [σ_test, DEnv.bind, Finmap.lookup_insert_of_ne _ h_eq, h_lookup]
        · have h_x_not_fv : x ∉ Space.fv s'' := fun hin =>
            h_xε (ctx.lin_fv_in_ε x'' s'' hx'' x hin)
          have hd : denotSpace σ_test s'' = denotSpace σ s'' :=
            denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv)
          rw [hd]; exact h_match
    nl_match := fun x'' τ'' hx'' => by
      have h_x_in_ε : x'' ∈ ε := Finmap.mem_iff.mpr ⟨_, hx''⟩
      have h_xne : x ≠ x'' := fun heq => by subst heq; exact h_xε h_x_in_ε
      obtain ⟨w, h_lookup, h_match⟩ := wf.nl_match x'' τ'' hx''
      refine ⟨w, ?_, ?_⟩
      · show σ_test.vars.lookup x'' = some w
        simp [σ_test, DEnv.bind, Finmap.lookup_insert_of_ne _ h_xne.symm, h_lookup]
      · have h_x_not_fv : x ∉ Ty.fv τ'' := fun hin =>
          h_xε (ctx.nl_fv_in_ε x'' τ'' hx'' x hin)
        have hd : denotTy σ_test τ'' = denotTy σ τ'' :=
          denotTy_agree τ'' (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv)
        rw [hd]; exact h_match
  }
  have h_sound := soundness d_body ctx_ext wf_test
  have h_lin_test : LinearAtVar σ_test x s_in body (.space s_τ) :=
    h_sound.2 x s_in (Finmap.lookup_insert Δ)
  simp only [LinearAtVar] at h_lin_test
  -- Bind-overwrite: σ_test.bind x v = σ.bind x v (same DEnv since x overwrites x).
  have h_bind_overwrite : ∀ v : DVal, σ_test.bind x v = σ.bind x v := by
    intro v
    show (DEnv.mk _ : DEnv) = DEnv.mk _
    congr 1
    exact Finmap.insert_insert σ.vars
  -- Rewrite the test hypothesis to use σ-version's denotSpace.
  rw [h_denot_s_in_test, h_denot_s_τ_test] at h_lin_test

  apply IsLinearMap.congr h_lin_test
  intro y
  rw [h_bind_overwrite]

/-- **General bridge**: for a bijective LinearMap between PD inner-product
    spaces, the Moore-Penrose pseudo-inverse equals the linear-equivalence
    inverse. Specializes both the `.dual` (rieszInv-of-V.IP) and `.dsum`
    (mooreInv-of-injection = projection) bridges, and will be the key for
    the .tprod uncurry chain.

    Proof: `f` bijective ⇒ range f = ⊤ ⇒ starProjection (range f) = id ⇒
    f (mooreInv f y) = y = f (f⁻¹ y). By f-injectivity, mooreInv f = f⁻¹. -/
private lemma mooreInv_bijective {V₀ V₁ : Type}
    [AddCommGroup V₀] [Module ℝ V₀] [FiniteDimensional ℝ V₀]
    [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    {B₀ : V₀ →ₗ[ℝ] V₀ →ₗ[ℝ] ℝ} (h₀ : IsInnerProduct B₀)
    {B₁ : V₁ →ₗ[ℝ] V₁ →ₗ[ℝ] ℝ} (h₁ : IsInnerProduct B₁)
    {f : V₀ →ₗ[ℝ] V₁} (h_bij : Function.Bijective f) :
    LinearMap.mooreInv h₀ h₁ f =
      ((LinearEquiv.ofBijective f h_bij).symm : V₁ →ₗ[ℝ] V₀) := by
  have h_range : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr h_bij.2
  letI _ := h₀.toIPSCore
  letI _ := h₁.toIPSCore
  letI _ : NormedAddCommGroup V₀ := (h₀.toIPSCore).toNormedAddCommGroup
  letI _ : NormedAddCommGroup V₁ := (h₁.toIPSCore).toNormedAddCommGroup
  letI _ : InnerProductSpace ℝ V₀ := InnerProductSpace.ofCore inferInstance
  letI _ : InnerProductSpace ℝ V₁ := InnerProductSpace.ofCore inferInstance
  apply LinearMap.ext
  intro y
  apply h_bij.1
  rw [LinearMap.mooreInv_image_eq_starProjection h₀ h₁ f y]
  rw [Submodule.starProjection_eq_self_iff.mpr (h_range ▸ Submodule.mem_top)]
  exact (LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective f h_bij) y).symm

private lemma curry2NonReal_denoted_midFn_isLinear
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (g_val : (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)).carrier) :
    let σ_g := σ.bind Term.g_name (.hil ⟨denotSpace σ
                  (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩)
    IsLinearMap ℝ (fun a_val : (denotSpace σ_g sA).carrier =>
      (denotTerm (σ_g.bind Term.a_name
          (.hil ⟨denotSpace σ_g sA, a_val⟩))
        (.llam sB sRest
          (.appL (.tprod sA sB) sRest
            (.var Term.g_name)
            (.tprodE (.var Term.a_name) (.bvar 0))))).atSpace
        (denotSpace σ_g (.tprod (.dual sB) sRest))) := by
  -- Use FV-transport helpers for the 1-binder Δ = {g}.
  have d_sA : SValid ε sA := svA
  have d_body_ty_mid : SValid ε (.tprod (.dual sB) sRest) :=
    SValid.tprod (SValid.dual svB) svR
  have d_body := Term.curry2NonReal_mid_hasType h_fresh_a h_fresh_b
    h_ga h_gb h_ab h_sRest_ne_real svA svB svR
  have d_g_ty : SValid ε (.tprod (.dual (.tprod sA sB)) sRest) :=
    SValid.tprod (SValid.dual (SValid.tprod svA svB)) svR
  have ctx_g := ctx_ε.extend_lin h_fresh_g d_g_ty
  have wf_g := env_wf.extend_lin ctx_ε h_fresh_g d_g_ty g_val
  have h_a_notin : Term.a_name ∉ (Finmap.insert Term.g_name
        (Space.tprod (Space.dual (Space.tprod sA sB)) sRest) ∅ : LCtx) := by
    rw [Finmap.mem_insert]; push_neg
    exact ⟨h_ga.symm, Finmap.notMem_empty⟩
  exact denot_llam_body_isLinear h_a_notin h_fresh_a
    d_sA d_body_ty_mid d_body ctx_g wf_g

private lemma curry2NonReal_denoted_innermostFn_isLinear
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (g_val : (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)).carrier)
    (a_val : (denotSpace σ sA).carrier) :
    let σ_g := σ.bind Term.g_name (.hil ⟨denotSpace σ
                  (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩)
    let σ_g_a := σ_g.bind Term.a_name (.hil ⟨denotSpace σ sA, a_val⟩)
    IsLinearMap ℝ (fun b_val : (denotSpace σ_g_a sB).carrier =>
      (denotTerm (σ_g_a.bind Term.b_name (.hil ⟨denotSpace σ_g_a sB, b_val⟩))
        (.appL (.tprod sA sB) sRest
          (.var Term.g_name)
          (.tprodE (.var Term.a_name) (.var Term.b_name)))).atSpace
        (denotSpace σ_g_a sRest)) := by
  -- 2-binder Δ = {a, g}: chain extend_lin + extend_lin_at.
  have d_sB : SValid ε sB := svB
  have d_sRest : SValid ε sRest := svR
  have d_body := Term.curry2NonReal_innermost_hasType h_ga h_gb h_ab svA svB svR
  have d_g_ty : SValid ε (.tprod (.dual (.tprod sA sB)) sRest) :=
    SValid.tprod (SValid.dual (SValid.tprod svA svB)) svR
  have h_g_not_fv_sA : Term.g_name ∉ Space.fv sA :=
    svA.notMem_fv_of_notMem_ε h_fresh_g
  have ctx_g := ctx_ε.extend_lin h_fresh_g d_g_ty
  have wf_g := env_wf.extend_lin ctx_ε h_fresh_g d_g_ty g_val
  have h_denot_sA_g :
      denotSpace σ sA = denotSpace (σ.bind Term.g_name
        (.hil ⟨denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩)) sA :=
    (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sA)).symm
  have ctx_ga := ctx_g.extend_lin h_fresh_a svA
  have wf_ga := wf_g.extend_lin_at ctx_g h_fresh_a svA h_denot_sA_g a_val
  have h_b_notin : Term.b_name ∉ (Finmap.insert Term.a_name sA (Finmap.insert Term.g_name
        (Space.tprod (Space.dual (Space.tprod sA sB)) sRest) ∅) : LCtx) := by
    rw [Finmap.mem_insert]; push_neg
    refine ⟨h_ab.symm, ?_⟩
    rw [Finmap.mem_insert]; push_neg
    exact ⟨h_gb.symm, Finmap.notMem_empty⟩
  exact denot_llam_body_isLinear h_b_notin h_fresh_b
    d_sB d_sRest d_body ctx_ga wf_ga

private lemma curry2Real_denoted_innerFn_isLinear
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    IsLinearMap ℝ (fun g_val : (denotSpace σ (.dual (.tprod sA sB))).carrier =>
      (denotTerm (σ.bind Term.g_name
          (.hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩))
        (.llam sA (.dual sB)
          (.llam sB .real
            (.appI (.tprod sA sB)
              (.var Term.g_name)
              (.tprodE (.bvar 1) (.bvar 0)))))).atSpace
        (denotSpace σ (.tprod (.dual sA) (.dual sB)))) := by
  have d_g_ty : SValid ε (.dual (.tprod sA sB)) :=
    SValid.dual (SValid.tprod svA svB)
  have d_body_ty : SValid ε (.tprod (.dual sA) (.dual sB)) :=
    SValid.tprod (SValid.dual svA) (SValid.dual svB)
  have d_body := Term.curry2Real_body_hasType h_fresh_g h_fresh_a h_fresh_b
    h_ga h_gb h_ab svA svB
  exact denot_llam_body_isLinear Finmap.notMem_empty h_fresh_g
    d_g_ty d_body_ty d_body ctx_ε env_wf

private lemma curry2NonReal_denoted_innerFn_isLinear
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    IsLinearMap ℝ (fun g_val :
        (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)).carrier =>
      (denotTermAux σ
          [.hil ⟨denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩]
        (.llam sA (.tprod (.dual sB) sRest)
          (.llam sB sRest
            (.appL (.tprod sA sB) sRest
              (.bvar 2)
              (.tprodE (.bvar 1) (.bvar 0)))))).atSpace
        (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest)))) := by
  have d_g_ty : SValid ε (.tprod (.dual (.tprod sA sB)) sRest) :=
    SValid.tprod (SValid.dual (SValid.tprod svA svB)) svR
  have d_body_ty : SValid ε (.tprod (.dual sA) (.tprod (.dual sB) sRest)) :=
    SValid.tprod (SValid.dual svA) (SValid.tprod (SValid.dual svB) svR)
  have d_body := Term.curry2NonReal_body_hasType h_fresh_g h_fresh_a h_fresh_b
    h_ga h_gb h_ab h_sRest_ne_real svA svB svR
  -- D1 bridge: rewrite each pointwise denotTermAux σ [v] inner_bvar back into the
  -- σ.bind g (openVar g inner_bvar) form so the keystone applies.
  have h_lc : Term.lc (Term.openVar Term.g_name
      (.llam sA (.tprod (.dual sB) sRest)
        (.llam sB sRest
          (.appL (.tprod sA sB) sRest (.bvar 2)
            (.tprodE (.bvar 1) (.bvar 0)))))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec_lc (SValid.lc svA),
      Space.openRec_lc (SValid.lc svB), Space.openRec_lc (SValid.lc svR),
      Space.openRec_lc (SValid.lc (SValid.tprod svA svB)),
      Space.openRec_lc (SValid.lc (SValid.dual svB)),
      Space.openRec_lc (SValid.lc (SValid.tprod (SValid.dual svB) svR))]
    exact (Term.curry2NonReal_body_hasType h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab h_sRest_ne_real svA svB svR).lc
  have h_fv : Term.g_name ∉ Term.fv
      (.llam sA (.tprod (.dual sB) sRest)
        (.llam sB sRest
          (.appL (.tprod sA sB) sRest (.bvar 2)
            (.tprodE (.bvar 1) (.bvar 0)))) : Term) := by
    have h_gA : Term.g_name ∉ Space.fv sA := svA.notMem_fv_of_notMem_ε h_fresh_g
    have h_gB : Term.g_name ∉ Space.fv sB := svB.notMem_fv_of_notMem_ε h_fresh_g
    have h_gR : Term.g_name ∉ Space.fv sRest := svR.notMem_fv_of_notMem_ε h_fresh_g
    simp only [Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty, or_false,
      Finset.mem_singleton]
    intro h
    repeat first
      | exact h_gA h | exact h_gB h | exact h_gR h
      | (rcases h with h | h)
  have h_bridge : (fun g_val :
        (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)).carrier =>
      (denotTermAux σ
          [.hil ⟨denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩]
        (.llam sA (.tprod (.dual sB) sRest)
          (.llam sB sRest
            (.appL (.tprod sA sB) sRest (.bvar 2)
              (.tprodE (.bvar 1) (.bvar 0)))))).atSpace
        (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest))))
    = (fun g_val :
        (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)).carrier =>
      (denotTerm (σ.bind Term.g_name
          (.hil ⟨denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩))
        (.llam sA (.tprod (.dual sB) sRest)
          (.llam sB sRest
            (.appL (.tprod sA sB) sRest
              (.var Term.g_name)
              (.tprodE (.bvar 1) (.bvar 0)))))).atSpace
        (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest)))) := by
    funext g_val
    rw [← denotTerm_openVar_bind h_lc h_fv]
    simp only [Term.openVar, Term.openRec, Space.openRec_lc (SValid.lc svA),
      Space.openRec_lc (SValid.lc svB), Space.openRec_lc (SValid.lc svR),
      Space.openRec_lc (SValid.lc (SValid.tprod svA svB)),
      Space.openRec_lc (SValid.lc (SValid.dual svB)),
      Space.openRec_lc (SValid.lc (SValid.tprod (SValid.dual svB) svR)),
      if_true, show ¬(1 = 0 + 1 + 1) from by decide,
      show ¬(0 = 0 + 1 + 1) from by decide, if_false, reduceIte]
  rw [h_bridge]
  exact denot_llam_body_isLinear Finmap.notMem_empty h_fresh_g
    d_g_ty d_body_ty d_body ctx_ε env_wf

private lemma curry2Real_denoted_midFn_isLinear
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (g_val : (denotSpace σ (.dual (.tprod sA sB))).carrier) :
    let σ_g := σ.bind Term.g_name (.hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩)
    IsLinearMap ℝ (fun a_val : (denotSpace σ_g sA).carrier =>
      (denotTerm (σ_g.bind Term.a_name (.hil ⟨denotSpace σ_g sA, a_val⟩))
        (.llam sB .real
          (.appI (.tprod sA sB)
            (.var Term.g_name)
            (.tprodE (.var Term.a_name) (.bvar 0))))).atSpace
        (denotSpace σ_g (.dual sB))) := by
  have d_sA : SValid ε sA := svA
  have d_body_ty_mid : SValid ε (.dual sB) := SValid.dual svB
  have d_body := Term.curry2Real_mid_hasType h_fresh_a h_fresh_b
    h_ga h_gb h_ab svA svB
  have d_g_ty : SValid ε (.dual (.tprod sA sB)) :=
    SValid.dual (SValid.tprod svA svB)
  have ctx_g := ctx_ε.extend_lin h_fresh_g d_g_ty
  have wf_g := env_wf.extend_lin ctx_ε h_fresh_g d_g_ty g_val
  have h_a_notin : Term.a_name ∉ (Finmap.insert Term.g_name
        (Space.dual (Space.tprod sA sB)) ∅ : LCtx) := by
    rw [Finmap.mem_insert]; push_neg
    exact ⟨h_ga.symm, Finmap.notMem_empty⟩
  exact denot_llam_body_isLinear h_a_notin h_fresh_a
    d_sA d_body_ty_mid d_body ctx_g wf_g

private lemma curry2Real_denoted_innermostFn_isLinear
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (g_val : (denotSpace σ (.dual (.tprod sA sB))).carrier)
    (a_val : (denotSpace σ sA).carrier) :
    let σ_g := σ.bind Term.g_name (.hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩)
    let σ_g_a := σ_g.bind Term.a_name (.hil ⟨denotSpace σ sA, a_val⟩)
    IsLinearMap ℝ (fun b_val : (denotSpace σ_g_a sB).carrier =>
      (denotTerm (σ_g_a.bind Term.b_name (.hil ⟨denotSpace σ_g_a sB, b_val⟩))
        (.appI (.tprod sA sB)
          (.var Term.g_name)
          (.tprodE (.var Term.a_name) (.var Term.b_name)))).atSpace
        (denotSpace σ_g_a .real)) := by
  have d_sB : SValid ε sB := svB
  have d_sReal : SValid ε .real := SValid.real
  have d_body := Term.curry2Real_innermost_hasType h_ga h_gb h_ab svA svB
  have d_g_ty : SValid ε (.dual (.tprod sA sB)) :=
    SValid.dual (SValid.tprod svA svB)
  have h_g_not_fv_sA : Term.g_name ∉ Space.fv sA :=
    svA.notMem_fv_of_notMem_ε h_fresh_g
  have ctx_g := ctx_ε.extend_lin h_fresh_g d_g_ty
  have wf_g := env_wf.extend_lin ctx_ε h_fresh_g d_g_ty g_val
  have h_denot_sA_g :
      denotSpace σ sA = denotSpace (σ.bind Term.g_name
        (.hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩)) sA :=
    (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sA)).symm
  have ctx_ga := ctx_g.extend_lin h_fresh_a svA
  have wf_ga := wf_g.extend_lin_at ctx_g h_fresh_a svA h_denot_sA_g a_val
  have h_b_notin : Term.b_name ∉ (Finmap.insert Term.a_name sA (Finmap.insert Term.g_name
        (Space.dual (Space.tprod sA sB)) ∅) : LCtx) := by
    rw [Finmap.mem_insert]; push_neg
    refine ⟨h_ab.symm, ?_⟩
    rw [Finmap.mem_insert]; push_neg
    exact ⟨h_gb.symm, Finmap.notMem_empty⟩
  exact denot_llam_body_isLinear h_b_notin h_fresh_b
    d_sB d_sReal d_body ctx_ga wf_ga

/-- Outer evaluation step: (denot σ curry2NonReal).asLinMap V_uncurried V_curried g_val
    equals (denot σ_g outer_body).atSpace V_curried. -/
private lemma curry2NonReal_outer_eval
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (g_val : (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)).carrier) :
    DVal.asLinMap (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest))
      (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest)))
      (denotTerm σ (Term.curry2NonReal sA sB sRest)) g_val =
    (denotTermAux σ
        [.hil ⟨denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩]
      (.llam sA (.tprod (.dual sB) sRest)
        (.llam sB sRest
          (.appL (.tprod sA sB) sRest
            (.bvar 2)
            (.tprodE (.bvar 1) (.bvar 0)))))).atSpace
      (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest))) := by
  show DVal.asLinMap _ _ (denotTerm σ
    (.llam (.tprod (.dual (.tprod sA sB)) sRest)
      (.tprod (.dual sA) (.tprod (.dual sB) sRest)) _)) g_val = _
  rw [denotTerm_llam_non_real (by intro h; cases h)]
  rw [asLinMap_llamTensorDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap
    (curry2NonReal_denoted_innerFn_isLinear h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab h_sRest_ne_real svA svB svR env_wf ctx_ε) g_val

private lemma curry2NonReal_innermost_appL_eval_at_inputs
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (g_val : (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)).carrier)
    (a_val : (denotSpace σ sA).carrier)
    (b_val : (denotSpace σ sB).carrier) :
    let σ_g := σ.bind Term.g_name (.hil ⟨denotSpace σ
                  (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩)
    let σ_g_a := σ_g.bind Term.a_name (.hil ⟨denotSpace σ sA, a_val⟩)
    let σ_g_a_b := σ_g_a.bind Term.b_name (.hil ⟨denotSpace σ sB, b_val⟩)
    (denotTerm σ_g_a_b
      (.appL (.tprod sA sB) sRest
        (.var Term.g_name)
        (.tprodE (.var Term.a_name) (.var Term.b_name)))).atSpace
      (denotSpace σ sRest)
      = dualTensorHom ℝ
          (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)).carrier
          (denotSpace σ sRest).carrier g_val
        (a_val ⊗ₜ[ℝ] b_val) := by
  -- FV-irrelevance setup.
  have h_g_not_fv_g_ty : Term.g_name ∉ Space.fv (.tprod (.dual (.tprod sA sB)) sRest) :=
    (SValid.tprod (SValid.dual (SValid.tprod svA svB)) svR).notMem_fv_of_notMem_ε h_fresh_g
  have h_g_not_fv_sA : Term.g_name ∉ Space.fv sA :=
    svA.notMem_fv_of_notMem_ε h_fresh_g
  have h_g_not_fv_sB : Term.g_name ∉ Space.fv sB :=
    svB.notMem_fv_of_notMem_ε h_fresh_g
  have h_g_not_fv_sR : Term.g_name ∉ Space.fv sRest :=
    svR.notMem_fv_of_notMem_ε h_fresh_g
  have h_a_not_fv_sA : Term.a_name ∉ Space.fv sA :=
    svA.notMem_fv_of_notMem_ε h_fresh_a
  have h_a_not_fv_sB : Term.a_name ∉ Space.fv sB :=
    svB.notMem_fv_of_notMem_ε h_fresh_a
  have h_a_not_fv_sR : Term.a_name ∉ Space.fv sRest :=
    svR.notMem_fv_of_notMem_ε h_fresh_a
  have h_b_not_fv_sA : Term.b_name ∉ Space.fv sA :=
    svA.notMem_fv_of_notMem_ε h_fresh_b
  have h_b_not_fv_sB : Term.b_name ∉ Space.fv sB :=
    svB.notMem_fv_of_notMem_ε h_fresh_b
  have h_b_not_fv_sR : Term.b_name ∉ Space.fv sRest :=
    svR.notMem_fv_of_notMem_ε h_fresh_b
  set σ_g : DEnv := σ.bind Term.g_name (.hil ⟨denotSpace σ
      (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩) with hσ_g
  set σ_g_a : DEnv := σ_g.bind Term.a_name (.hil ⟨denotSpace σ sA, a_val⟩) with hσ_g_a
  set σ_g_a_b : DEnv := σ_g_a.bind Term.b_name (.hil ⟨denotSpace σ sB, b_val⟩)
    with hσ_g_a_b
  -- FV-irrelevance: denotSpace σ_g_a_b sX = denotSpace σ sX for X ∈ {sA, sB, sRest, g_ty}.
  have h_dsA : denotSpace σ_g_a_b sA = denotSpace σ sA :=
    ((denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_b_not_fv_sA)).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_a_not_fv_sA))).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sA))
  have h_dsB : denotSpace σ_g_a_b sB = denotSpace σ sB :=
    ((denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_b_not_fv_sB)).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_a_not_fv_sB))).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sB))
  have h_dsR : denotSpace σ_g_a_b sRest = denotSpace σ sRest :=
    ((denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_b_not_fv_sR)).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_a_not_fv_sR))).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sR))
  have h_d_g_ty : denotSpace σ_g_a_b (.tprod (.dual (.tprod sA sB)) sRest)
      = denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest) := by
    show HSpace.tprod (HSpace.dual (HSpace.tprod (denotSpace σ_g_a_b sA)
          (denotSpace σ_g_a_b sB))) (denotSpace σ_g_a_b sRest)
      = HSpace.tprod (HSpace.dual (HSpace.tprod (denotSpace σ sA)
          (denotSpace σ sB))) (denotSpace σ sRest)
    rw [h_dsA, h_dsB, h_dsR]
  have h_d_AB : denotSpace σ_g_a_b (.tprod sA sB)
      = HSpace.tprod (denotSpace σ sA) (denotSpace σ sB) := by
    show HSpace.tprod (denotSpace σ_g_a_b sA) (denotSpace σ_g_a_b sB) = _
    rw [h_dsA, h_dsB]
  -- Var lookups at σ_g_a_b.
  have h_var_g : denotTerm σ_g_a_b (.var Term.g_name)
      = .hil ⟨denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩ := by
    show (σ_g_a_b.vars.lookup Term.g_name).getD DVal.default = _
    simp [σ_g_a_b, σ_g_a, σ_g, DEnv.bind,
          Finmap.lookup_insert_of_ne _ h_gb,
          Finmap.lookup_insert_of_ne _ h_ga,
          Finmap.lookup_insert]
  have h_var_a : denotTerm σ_g_a_b (.var Term.a_name)
      = .hil ⟨denotSpace σ sA, a_val⟩ := by
    show (σ_g_a_b.vars.lookup Term.a_name).getD DVal.default = _
    simp [σ_g_a_b, σ_g_a, σ_g, DEnv.bind,
          Finmap.lookup_insert_of_ne _ h_ab,
          Finmap.lookup_insert]
  have h_var_b : denotTerm σ_g_a_b (.var Term.b_name)
      = .hil ⟨denotSpace σ sB, b_val⟩ := by
    show (σ_g_a_b.vars.lookup Term.b_name).getD DVal.default = _
    simp [σ_g_a_b, DEnv.bind, Finmap.lookup_insert]
  -- Evaluate the .appL: denot_appL gives a .hil whose inner V uses σ_g_a_b;
  -- rewrite via FV-irrelevance to match the outer atSpace V (which uses σ).
  show DVal.atSpace (denotSpace σ sRest) (denotTerm σ_g_a_b
        (.appL (.tprod sA sB) sRest (.var Term.g_name)
          (.tprodE (.var Term.a_name) (.var Term.b_name)))) = _
  rw [denotTerm_appL]
  rw [h_dsR, h_d_AB]
  rw [atSpace_hil_self]
  rw [h_var_g]
  -- (.hil V_uncurried g_val).asLinMap V_AB V_sRest = dualTensorHom (atSpace V_uncurried) = dualTensorHom g_val.
  show (DVal.asLinMap (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))
      (denotSpace σ sRest)
      (DVal.hil ⟨HSpace.tprod (HSpace.dual
        (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))) (denotSpace σ sRest),
        g_val⟩)) _ = _
  rw [DVal.asLinMap_eq_of_matchesShape (DVal.matchesShape_hil_rfl _ _)]
  rw [atSpace_hil_self]

  show dualTensorHom ℝ (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)).carrier
        (denotSpace σ sRest).carrier g_val
      ((denotTerm σ_g_a_b (.tprodE (.var Term.a_name) (.var Term.b_name))).atSpace
        (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))) = _
  congr 1
  -- denot of .tprodE: .hil ⟨HSpace.tprod V_A V_B, a ⊗ b⟩. atSpace gives a ⊗ b.
  show (DVal.hil ⟨HSpace.tprod
      ((denotTerm σ_g_a_b (.var Term.a_name)).asHil.fst)
      ((denotTerm σ_g_a_b (.var Term.b_name)).asHil.fst),
      (denotTerm σ_g_a_b (.var Term.a_name)).asHil.snd ⊗ₜ[ℝ]
        (denotTerm σ_g_a_b (.var Term.b_name)).asHil.snd⟩).atSpace
        (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)) = _
  rw [h_var_a, h_var_b]
  show (DVal.hil ⟨HSpace.tprod (denotSpace σ sA) (denotSpace σ sB),
      a_val ⊗ₜ[ℝ] b_val⟩).atSpace
      (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)) = _
  rw [atSpace_hil_self]

/-- **Env-form bottom-of-chain** (LN D1). The bvar-indexed innermost appL,
    denoted directly at the 3-entry local env `[b, a, g]`, reduces to
    `dualTensorHom g_val (a ⊗ b)`. No σ-binds / var-lookups — the bvars
    read straight off the env. -/
private lemma curry2NonReal_innermost_appL_env_eval
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (g_val : (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)).carrier)
    (a_val : (denotSpace σ sA).carrier)
    (b_val : (denotSpace σ sB).carrier) :
    (denotTermAux σ
        [.hil ⟨denotSpace σ sB, b_val⟩, .hil ⟨denotSpace σ sA, a_val⟩,
          .hil ⟨denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩]
      (.appL (.tprod sA sB) sRest
        (.bvar 2)
        (.tprodE (.bvar 1) (.bvar 0)))).atSpace (denotSpace σ sRest)
      = dualTensorHom ℝ
          (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)).carrier
          (denotSpace σ sRest).carrier g_val
        (a_val ⊗ₜ[ℝ] b_val) := by
  set env : List DVal :=
    [.hil ⟨denotSpace σ sB, b_val⟩, .hil ⟨denotSpace σ sA, a_val⟩,
      .hil ⟨denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩] with henv
  -- denotSpaceAux σ env s = denotSpace σ s for the closed spaces involved.
  have h_dsR : denotSpaceAux σ env sRest = denotSpace σ sRest :=
    denotSpaceAux_lc_irrel (SValid.lc svR) σ env []
  have h_dsAB : denotSpaceAux σ env (.tprod sA sB)
      = HSpace.tprod (denotSpace σ sA) (denotSpace σ sB) := by
    show HSpace.tprod (denotSpaceAux σ env sA) (denotSpaceAux σ env sB) = _
    rw [denotSpaceAux_lc_irrel (SValid.lc svA) σ env [],
        denotSpaceAux_lc_irrel (SValid.lc svB) σ env []]
  show DVal.atSpace (denotSpace σ sRest)
        (let V₀ := denotSpaceAux σ env (.tprod sA sB)
         let V₁ := denotSpaceAux σ env sRest
         let f := (denotTermAux σ env (.bvar 2)).asLinMap V₀ V₁
         let v : V₀.carrier := (denotTermAux σ env (.tprodE (.bvar 1) (.bvar 0))).atSpace V₀
         DVal.hil ⟨V₁, f v⟩) = _
  simp only []
  rw [h_dsR, h_dsAB]
  rw [atSpace_hil_self]
  -- e₀ = bvar 2 = env.getD 2 = ⟨V_uncurried, g_val⟩.
  show (DVal.asLinMap (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))
      (denotSpace σ sRest)
      (env.getD 2 DVal.default)) _ = _
  rw [show env.getD 2 DVal.default
        = DVal.hil ⟨HSpace.tprod (HSpace.dual
            (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))) (denotSpace σ sRest),
            g_val⟩ from rfl]
  rw [DVal.asLinMap_eq_of_matchesShape (DVal.matchesShape_hil_rfl _ _)]
  rw [atSpace_hil_self]
  show dualTensorHom ℝ (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)).carrier
        (denotSpace σ sRest).carrier g_val
      ((denotTermAux σ env (.tprodE (.bvar 1) (.bvar 0))).atSpace
        (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))) = _
  congr 1
  show (DVal.hil ⟨HSpace.tprod
      ((env.getD 1 DVal.default).asHil.fst)
      ((env.getD 0 DVal.default).asHil.fst),
      (env.getD 1 DVal.default).asHil.snd ⊗ₜ[ℝ]
        (env.getD 0 DVal.default).asHil.snd⟩).atSpace
        (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)) = _
  show (DVal.hil ⟨HSpace.tprod (denotSpace σ sA) (denotSpace σ sB),
      a_val ⊗ₜ[ℝ] b_val⟩).atSpace
      (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)) = _
  rw [atSpace_hil_self]

private lemma curry2Real_innermost_appI_eval_at_inputs
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (g_val : (denotSpace σ (.dual (.tprod sA sB))).carrier)
    (a_val : (denotSpace σ sA).carrier)
    (b_val : (denotSpace σ sB).carrier) :
    let σ_g := σ.bind Term.g_name (.hil ⟨denotSpace σ
                  (.dual (.tprod sA sB)), g_val⟩)
    let σ_g_a := σ_g.bind Term.a_name (.hil ⟨denotSpace σ sA, a_val⟩)
    let σ_g_a_b := σ_g_a.bind Term.b_name (.hil ⟨denotSpace σ sB, b_val⟩)
    (denotTerm σ_g_a_b
      (.appI (.tprod sA sB)
        (.var Term.g_name)
        (.tprodE (.var Term.a_name) (.var Term.b_name)))).atSpace HSpace.real
      = (DVal.hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩).asLinFunctional
          (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))
          (a_val ⊗ₜ[ℝ] b_val) := by
  -- FV-irrelevance setup.
  have h_g_not_fv_sA : Term.g_name ∉ Space.fv sA :=
    svA.notMem_fv_of_notMem_ε h_fresh_g
  have h_g_not_fv_sB : Term.g_name ∉ Space.fv sB :=
    svB.notMem_fv_of_notMem_ε h_fresh_g
  have h_a_not_fv_sA : Term.a_name ∉ Space.fv sA :=
    svA.notMem_fv_of_notMem_ε h_fresh_a
  have h_a_not_fv_sB : Term.a_name ∉ Space.fv sB :=
    svB.notMem_fv_of_notMem_ε h_fresh_a
  have h_b_not_fv_sA : Term.b_name ∉ Space.fv sA :=
    svA.notMem_fv_of_notMem_ε h_fresh_b
  have h_b_not_fv_sB : Term.b_name ∉ Space.fv sB :=
    svB.notMem_fv_of_notMem_ε h_fresh_b
  set σ_g : DEnv := σ.bind Term.g_name (.hil ⟨denotSpace σ
      (.dual (.tprod sA sB)), g_val⟩) with hσ_g
  set σ_g_a : DEnv := σ_g.bind Term.a_name (.hil ⟨denotSpace σ sA, a_val⟩) with hσ_g_a
  set σ_g_a_b : DEnv := σ_g_a.bind Term.b_name (.hil ⟨denotSpace σ sB, b_val⟩)
    with hσ_g_a_b
  have h_dsA : denotSpace σ_g_a_b sA = denotSpace σ sA :=
    ((denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_b_not_fv_sA)).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_a_not_fv_sA))).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sA))
  have h_dsB : denotSpace σ_g_a_b sB = denotSpace σ sB :=
    ((denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_b_not_fv_sB)).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_a_not_fv_sB))).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sB))
  have h_d_AB : denotSpace σ_g_a_b (.tprod sA sB)
      = HSpace.tprod (denotSpace σ sA) (denotSpace σ sB) := by
    show HSpace.tprod (denotSpace σ_g_a_b sA) (denotSpace σ_g_a_b sB) = _
    rw [h_dsA, h_dsB]
  -- Var lookups at σ_g_a_b.
  have h_var_g : denotTerm σ_g_a_b (.var Term.g_name)
      = .hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩ := by
    show (σ_g_a_b.vars.lookup Term.g_name).getD DVal.default = _
    simp [σ_g_a_b, σ_g_a, σ_g, DEnv.bind,
          Finmap.lookup_insert_of_ne _ h_gb,
          Finmap.lookup_insert_of_ne _ h_ga,
          Finmap.lookup_insert]
  have h_var_a : denotTerm σ_g_a_b (.var Term.a_name)
      = .hil ⟨denotSpace σ sA, a_val⟩ := by
    show (σ_g_a_b.vars.lookup Term.a_name).getD DVal.default = _
    simp [σ_g_a_b, σ_g_a, σ_g, DEnv.bind,
          Finmap.lookup_insert_of_ne _ h_ab,
          Finmap.lookup_insert]
  have h_var_b : denotTerm σ_g_a_b (.var Term.b_name)
      = .hil ⟨denotSpace σ sB, b_val⟩ := by
    show (σ_g_a_b.vars.lookup Term.b_name).getD DVal.default = _
    simp [σ_g_a_b, DEnv.bind, Finmap.lookup_insert]
  -- Evaluate via denotTerm_appI.
  show DVal.atSpace HSpace.real (denotTerm σ_g_a_b
        (.appI (.tprod sA sB) (.var Term.g_name)
          (.tprodE (.var Term.a_name) (.var Term.b_name)))) = _
  rw [denotTerm_appI]
  rw [atSpace_hil_self]
  rw [h_d_AB]
  rw [h_var_g]

  congr 1
  show (DVal.hil ⟨HSpace.tprod
      ((denotTerm σ_g_a_b (.var Term.a_name)).asHil.fst)
      ((denotTerm σ_g_a_b (.var Term.b_name)).asHil.fst),
      (denotTerm σ_g_a_b (.var Term.a_name)).asHil.snd ⊗ₜ[ℝ]
        (denotTerm σ_g_a_b (.var Term.b_name)).asHil.snd⟩).atSpace
        (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)) = _
  rw [h_var_a, h_var_b]
  show (DVal.hil ⟨HSpace.tprod (denotSpace σ sA) (denotSpace σ sB),
      a_val ⊗ₜ[ℝ] b_val⟩).atSpace
      (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)) = _
  rw [atSpace_hil_self]

/-- Bottom-of-chain `.appL` evaluation: at any DEnv `τ`, the `.appL` of
    two terms `e₀, e₁` extracted at the codomain's denotSpace reduces to
    the `asLinMap`-application of `e₀`'s denot to `e₁`'s denot.atSpace.
    Pure structural unfolding via `denotTerm_appL` + `atSpace_hil_self`. -/
private lemma denotTerm_appL_atSpace_eq (τ : DEnv) (s₀ s₁ : Space) (e₀ e₁ : Term) :
    (denotTerm τ (.appL s₀ s₁ e₀ e₁)).atSpace (denotSpace τ s₁)
      = ((denotTerm τ e₀).asLinMap (denotSpace τ s₀) (denotSpace τ s₁))
          ((denotTerm τ e₁).atSpace (denotSpace τ s₀)) := by
  rw [denotTerm_appL, atSpace_hil_self]

/-- Variant of `denotTerm_appL_atSpace_eq` taking an explicit HSpace `V_T`
    along with `h_dT : denotSpace τ s₁ = V_T`. -/
private lemma denotTerm_appL_atSpace_eq_at (τ : DEnv) (s₀ s₁ : Space) (e₀ e₁ : Term)
    (V_T : HSpace) (h_dT : denotSpace τ s₁ = V_T) :
    (denotTerm τ (.appL s₀ s₁ e₀ e₁)).atSpace V_T
      = ((denotTerm τ e₀).asLinMap (denotSpace τ s₀) V_T)
          ((denotTerm τ e₁).atSpace (denotSpace τ s₀)) := by
  subst h_dT
  exact denotTerm_appL_atSpace_eq τ s₀ s₁ e₀ e₁

/-- Algebraic bridge: `(denot σ (uncurry2NonReal)).asLinMap V_curried V_uncurried`
    is the Moore-Penrose pseudo-inverse of curry's `asLinMap`. Follows
    directly from `uncurry2NonReal := .pinvT (curry2NonReal)` and
    `asLinMap_pinvTensorDVal`. -/
private lemma denot_uncurry2NonReal_asLinMap_eq_mooreInv
    (σ : DEnv) (sA sB sRest : Space) :
    let V_uncurried : HSpace := denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)
    let V_curried : HSpace := denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest))
    DVal.asLinMap V_curried V_uncurried
        (denotTerm σ (Term.uncurry2NonReal sA sB sRest))
      = LinearMap.mooreInv V_uncurried.innerIsIP V_curried.innerIsIP
          (DVal.asLinMap V_uncurried V_curried
            (denotTerm σ (Term.curry2NonReal sA sB sRest))) := by
  show DVal.asLinMap _ _ (pinvTensorDVal _ _ _) = _
  rw [asLinMap_pinvTensorDVal]

/-- Real-residual analog of `denot_uncurry2NonReal_asLinMap_eq_mooreInv`. -/
private lemma denot_uncurry2Real_asLinMap_eq_mooreInv
    (σ : DEnv) (sA sB : Space) :
    let V_uncurried : HSpace := denotSpace σ (.dual (.tprod sA sB))
    let V_curried : HSpace := denotSpace σ (.tprod (.dual sA) (.dual sB))
    DVal.asLinMap V_curried V_uncurried
        (denotTerm σ (Term.uncurry2Real sA sB))
      = LinearMap.mooreInv V_uncurried.innerIsIP V_curried.innerIsIP
          (DVal.asLinMap V_uncurried V_curried
            (denotTerm σ (Term.curry2Real sA sB))) := by
  show DVal.asLinMap _ _ (pinvTensorDVal _ _ _) = _
  rw [asLinMap_pinvTensorDVal]

/-- Dimension equality: `dim((V_A⊗V_B)*⊗V_R) = dim(V_A*⊗(V_B*⊗V_R))`.
    Both sides equal `dim V_A · dim V_B · dim V_R` via tensor and dual
    finrank lemmas. Building block for showing `curry2NonReal.asLinMap`
    is bijective (injectivity + finrank-equal → surjective). -/
private lemma curry2NonReal_finrank_eq (V_A V_B V_R : HSpace) :
    Module.finrank ℝ
        (HSpace.tprod (HSpace.dual (HSpace.tprod V_A V_B)) V_R).carrier
      = Module.finrank ℝ
          (HSpace.tprod (HSpace.dual V_A) (HSpace.tprod (HSpace.dual V_B) V_R)).carrier := by
  simp only [HSpace.tprod, HSpace.dual, Module.finrank_tensorProduct,
             Module.finrank_linearMap, Module.finrank_self, mul_one]
  ring

/-- Real-residual analog: `dim((V_A⊗V_B)*) = dim(V_A*⊗V_B*)`. -/
private lemma curry2Real_finrank_eq (V_A V_B : HSpace) :
    Module.finrank ℝ (HSpace.dual (HSpace.tprod V_A V_B)).carrier
      = Module.finrank ℝ (HSpace.tprod (HSpace.dual V_A) (HSpace.dual V_B)).carrier := by
  simp only [HSpace.tprod, HSpace.dual, Module.finrank_tensorProduct,
             Module.finrank_linearMap, Module.finrank_self, mul_one]

/-- `dualTensorHom ℝ V₀.carrier V₁.carrier : V₀*⊗V₁ → (V₀ →ₗ V₁)` is
    injective for HSpace V₀, V₁ (both finite-dim, hence finite + free
    over ℝ). Follows from `dualTensorHomEquiv` being a LinearEquiv. -/
private lemma dualTensorHom_injective_of_hSpace (V₀ V₁ : HSpace) :
    Function.Injective
      (dualTensorHom ℝ V₀.carrier V₁.carrier
        : Module.Dual ℝ V₀.carrier ⊗[ℝ] V₁.carrier →ₗ[ℝ] (V₀.carrier →ₗ[ℝ] V₁.carrier)) := by
  have : (dualTensorHom ℝ V₀.carrier V₁.carrier : _ →ₗ[ℝ] _)
      = (dualTensorHomEquiv ℝ V₀.carrier V₁.carrier).toLinearMap := by
    ext t
    simp [dualTensorHomEquiv]
  rw [this]
  exact (dualTensorHomEquiv ℝ V₀.carrier V₁.carrier).injective

/-- σ-frame version of `denot_llam_body_isLinear`. Lifts σ_outer-frame
    linearity to σ-frame via FV-irrelevance equalities on the V's.
    Proof: rewrite the goal's σ-frame V's to σ_outer-frame, then apply
    the σ_outer-frame linearity. -/
private lemma denot_llam_body_isLinear_at_σ
    {σ_outer σ : DEnv} {Δ : LCtx} {ε : NLCtx} {x : Name} {s_in s_τ : Space}
    {body : Term}
    (h_xΔ : x ∉ Δ) (h_xε : x ∉ ε)
    (d_s_in : SValid ε s_in) (d_s_τ : SValid ε s_τ)
    (d_body : HasType (Finmap.insert x s_in Δ) ε (Term.openVar x body) (.space s_τ))
    (ctx : CtxWF Δ ε)
    (wf_outer : EnvWF σ_outer Δ ε)
    (h_dsi : denotSpace σ_outer s_in = denotSpace σ s_in)
    (h_dsτ : denotSpace σ_outer s_τ = denotSpace σ s_τ)
    (h_lc : Term.lc (Term.openVar x body)) (h_fv : x ∉ Term.fv body) :
    IsLinearMap ℝ (fun v : (denotSpace σ s_in).carrier =>
      (denotTermAux σ_outer [.hil ⟨denotSpace σ s_in, v⟩] body).atSpace
        (denotSpace σ s_τ)) := by
  have h_lin_outer := denot_llam_body_isLinear h_xΔ h_xε d_s_in d_s_τ d_body ctx wf_outer
  rw [← h_dsi, ← h_dsτ]
  -- Bridge each pointwise value: denotTermAux σ_outer [v] body
  --   = denotTerm (σ_outer.bind x ⟨V,v⟩) (openVar x body).
  have h_bridge : (fun v : (denotSpace σ_outer s_in).carrier =>
      (denotTermAux σ_outer [.hil ⟨denotSpace σ_outer s_in, v⟩] body).atSpace
        (denotSpace σ_outer s_τ))
    = (fun v : (denotSpace σ_outer s_in).carrier =>
      (denotTerm (σ_outer.bind x (.hil ⟨denotSpace σ_outer s_in, v⟩)) (Term.openVar x body)).atSpace
        (denotSpace σ_outer s_τ)) := by
    funext v
    rw [denotTerm_openVar_bind h_lc h_fv]
  rw [h_bridge]
  exact h_lin_outer

/-- **Frame-bridge helper**: σ-frame asLinMap of a σ'-frame .llam DVal.

    Given a `.llam x s_in s_τ body` denoted at σ' (so its internal
    llamTensorDVal uses σ'-frame V's), and σ' satisfies FV-irrelevance
    for `s_in`, `s_τ`, this helper evaluates the σ-frame asLinMap at
    a σ-frame `a_val`, producing the body's denot evaluated at
    σ'.bind x (.hil ⟨V_s_in_σ, a_val⟩) (σ-frame binding).

    Linearity must be supplied at σ-frame V's. -/
private lemma denot_σ'_llam_apply_at_σ_eq
    {σ : DEnv} {σ' : DEnv} {s_in s_τ : Space} {body : Term}
    (h_sτ_ne_real : s_τ ≠ .real)
    (h_dsi : denotSpace σ' s_in = denotSpace σ s_in)
    (h_dsτ : denotSpace σ' s_τ = denotSpace σ s_τ)
    (h_lin : IsLinearMap ℝ (fun v : (denotSpace σ s_in).carrier =>
      (denotTermAux σ' [.hil ⟨denotSpace σ s_in, v⟩] body).atSpace
        (denotSpace σ s_τ)))
    (a_val : (denotSpace σ s_in).carrier) :
    (denotTerm σ' (.llam s_in s_τ body)).asLinMap
        (denotSpace σ s_in) (denotSpace σ s_τ) a_val
      = (denotTermAux σ' [.hil ⟨denotSpace σ s_in, a_val⟩] body).atSpace
          (denotSpace σ s_τ) := by
  rw [denotTerm_llam_non_real h_sτ_ne_real]
  -- LHS: asLinMap V_σ V_σ' (llamTensorDVal V_σ' V_σ' f) — V's mismatched.
  -- The internal f under LN is `fun v => denotTermAux σ' [v] body`.
  rw [show llamTensorDVal (denotSpace σ' s_in) (denotSpace σ' s_τ)
        (fun v => denotTermAux σ' [v] body)
      = llamTensorDVal (denotSpace σ s_in) (denotSpace σ s_τ)
        (fun v => denotTermAux σ' [v] body) from by rw [h_dsi, h_dsτ]]
  rw [asLinMap_llamTensorDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap h_lin a_val

/-- σ'-frame variant for .real-codomain .llam: atSpace of `(denot σ' (.llam
    x s_in .real body))` at `HSpace.dual (denotSpace σ' s_in)`, applied at
    v_val, equals the body's denot at HSpace.real. Mirror of
    `denot_σ'_llam_apply_at_σ_eq` but for .real-codomain (uses
    denotTerm_llam_real + atSpace_llamRealDVal). Pure σ'-frame; caller
    transports at the boundary if needed. -/
private lemma denot_σ'_llam_real_atSpace_apply_eq
    {σ' : DEnv} {s_in : Space} {body : Term}
    (h_lin : IsLinearMap ℝ (fun v : (denotSpace σ' s_in).carrier =>
      (denotTermAux σ' [.hil ⟨denotSpace σ' s_in, v⟩] body).atSpace
        HSpace.real))
    (v_val : (denotSpace σ' s_in).carrier) :
    DVal.atSpace (HSpace.dual (denotSpace σ' s_in))
      (denotTerm σ' (.llam s_in .real body)) v_val
      = (denotTermAux σ' [.hil ⟨denotSpace σ' s_in, v_val⟩] body).atSpace
          HSpace.real := by
  rw [denotTerm_llam_real]
  rw [atSpace_llamRealDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap h_lin v_val

/-- σ-frame variant of `denot_σ'_llam_real_atSpace_apply_eq`. Accepts an
    explicit propositional equality `h_dsi` and works in σ-frame v_val.
    Proven by generalizing the V's HSpace and substituting via h_dsi. -/
private lemma denot_σ_llam_real_atSpace_apply_eq
    {σ σ' : DEnv} {s_in : Space} {body : Term}
    (h_dsi : denotSpace σ' s_in = denotSpace σ s_in)
    (h_lin : IsLinearMap ℝ (fun v : (denotSpace σ s_in).carrier =>
      (denotTermAux σ' [.hil ⟨denotSpace σ s_in, v⟩] body).atSpace
        HSpace.real))
    (v_val : (denotSpace σ s_in).carrier) :
    DVal.atSpace (HSpace.dual (denotSpace σ s_in))
      (denotTerm σ' (.llam s_in .real body)) v_val
      = (denotTermAux σ' [.hil ⟨denotSpace σ s_in, v_val⟩] body).atSpace
          HSpace.real := by
  -- Generalize the V argument so subst can work.
  revert h_lin v_val
  -- Generalize `denotSpace σ s_in` as a fresh variable V.
  generalize hV : denotSpace σ s_in = V at *

  subst h_dsi
  intro h_lin v_val
  exact denot_σ'_llam_real_atSpace_apply_eq h_lin v_val

/-- DEnv binding HSpace is irrelevant: when two HSpaces V₁ V₂ are equal,
    binding x at `.hil ⟨V₁, v⟩` vs `.hil ⟨V₂, h ▸ v⟩` gives the same denotTerm result. -/
private lemma denotTerm_bind_HSpace_eq {σ : DEnv} {x : Name} {V₁ V₂ : HSpace}
    (h : V₁ = V₂) (v : V₁.carrier) (T : Term) :
    denotTerm (σ.bind x (.hil ⟨V₁, v⟩)) T = denotTerm (σ.bind x (.hil ⟨V₂, h ▸ v⟩)) T := by
  subst h
  rfl

/-- DEnv-level bind equality: when two HSpaces V₁ V₂ are equal, binding
    `x` at `.hil ⟨V₁, v⟩` produces the same `DEnv` as binding at
    `.hil ⟨V₂, h ▸ v⟩`. This rewrites every occurrence of the bind
    (both inside `denotTerm` and inside `denotSpace`). -/
private lemma DEnv_bind_HSpace_eq {σ : DEnv} {x : Name} {V₁ V₂ : HSpace}
    (h : V₁ = V₂) (v : V₁.carrier) :
    σ.bind x (.hil ⟨V₁, v⟩) = σ.bind x (.hil ⟨V₂, h ▸ v⟩) := by
  subst h
  rfl

/-- HSpace-swap bridge for `.atSpace` with a `HSpace.dual (denotSpace ...)`
    target and an external argument `d` at the dual's underlying carrier.
    Handles the dependent type of `d` via `subst`. -/
private lemma denotTerm_atSpace_dual_DEnv_bind_HSpace_swap
    {σ : DEnv} {x : Name} {V₁ V₂ : HSpace}
    (h : V₁ = V₂) (v : V₁.carrier) (T : Term) (s : Space)
    (d : (denotSpace (σ.bind x (.hil ⟨V₁, v⟩)) s).carrier) :
    (denotTerm (σ.bind x (.hil ⟨V₁, v⟩)) T).atSpace
        (HSpace.dual (denotSpace (σ.bind x (.hil ⟨V₁, v⟩)) s)) d
    = (denotTerm (σ.bind x (.hil ⟨V₂, h ▸ v⟩)) T).atSpace
        (HSpace.dual (denotSpace (σ.bind x (.hil ⟨V₂, h ▸ v⟩)) s))
        (by subst h; exact d) := by
  subst h
  rfl

/-- **Chain-step helper**: combines `denot_σ'_llam_apply_at_σ_eq` with
    `asLinMap_eq_of_matchesShape` to evaluate `dualTensorHom (atSpace ...)`
    of a σ'-frame `.llam` DVal at a σ-frame `a_val`. The matchesShape
    proof is derived inline from h_dsi and h_dsτ. -/
private lemma denot_σ'_llam_dualTensorHom_atSpace_eq
    {σ σ' : DEnv} {s_in s_τ : Space} {body : Term}
    (h_sτ_ne_real : s_τ ≠ .real)
    (h_dsi : denotSpace σ' s_in = denotSpace σ s_in)
    (h_dsτ : denotSpace σ' s_τ = denotSpace σ s_τ)
    (h_lin : IsLinearMap ℝ (fun v : (denotSpace σ s_in).carrier =>
      (denotTermAux σ' [.hil ⟨denotSpace σ s_in, v⟩] body).atSpace
        (denotSpace σ s_τ)))
    (a_val : (denotSpace σ s_in).carrier) :
    dualTensorHom ℝ (denotSpace σ s_in).carrier (denotSpace σ s_τ).carrier
      ((denotTerm σ' (.llam s_in s_τ body)).atSpace
        (HSpace.tprod (HSpace.dual (denotSpace σ s_in)) (denotSpace σ s_τ)))
      a_val
    = (denotTermAux σ' [.hil ⟨denotSpace σ s_in, a_val⟩] body).atSpace
        (denotSpace σ s_τ) := by
  -- Derive matchesShape from .llam structure + FV-irrelevance.
  have h_match : (denotTerm σ' (.llam s_in s_τ body)).matchesShape
      (.hil (HSpace.tprod (HSpace.dual (denotSpace σ s_in)) (denotSpace σ s_τ))) := by
    rw [denotTerm_llam_non_real h_sτ_ne_real]
    show HType.hil (HSpace.tprod (HSpace.dual (denotSpace σ' s_in)) (denotSpace σ' s_τ))
        = HType.hil (HSpace.tprod (HSpace.dual (denotSpace σ s_in)) (denotSpace σ s_τ))
    rw [h_dsi, h_dsτ]
  rw [← DVal.asLinMap_eq_of_matchesShape h_match]
  exact denot_σ'_llam_apply_at_σ_eq h_sτ_ne_real h_dsi h_dsτ h_lin a_val

/-- **Env-threaded apply helper** (LN D1). Generalizes
    `denot_σ'_llam_apply_at_σ_eq` to a non-empty local env `env`: a llam
    denoted under `denotTermAux σ env` reduces, when applied at `a_val`,
    to the body denoted at the pushed env `(.hil ⟨V,a_val⟩ :: env)`. -/
private lemma denotTermAux_llam_apply_at_σ_eq
    {σ : DEnv} {env : List DVal} {s_in s_τ : Space} {body : Term}
    (h_sτ_ne_real : s_τ ≠ .real)
    (h_dsi : denotSpaceAux σ env s_in = denotSpace σ s_in)
    (h_dsτ : denotSpaceAux σ env s_τ = denotSpace σ s_τ)
    (h_lin : IsLinearMap ℝ (fun v : (denotSpace σ s_in).carrier =>
      (denotTermAux σ (.hil ⟨denotSpace σ s_in, v⟩ :: env) body).atSpace
        (denotSpace σ s_τ)))
    (a_val : (denotSpace σ s_in).carrier) :
    (denotTermAux σ env (.llam s_in s_τ body)).asLinMap
        (denotSpace σ s_in) (denotSpace σ s_τ) a_val
      = (denotTermAux σ (.hil ⟨denotSpace σ s_in, a_val⟩ :: env) body).atSpace
          (denotSpace σ s_τ) := by
  rw [show denotTermAux σ env (.llam s_in s_τ body)
        = llamTensorDVal (denotSpace σ s_in) (denotSpace σ s_τ)
            (fun v => denotTermAux σ (v :: env) body) from by
      cases s_τ with
      | real => exact absurd rfl h_sτ_ne_real
      | _ =>
        simp only [denotTermAux]
        rw [h_dsi, h_dsτ]]
  rw [asLinMap_llamTensorDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap h_lin a_val

/-- **Env-threaded dualTensorHom chain step** (LN D1). Generalizes
    `denot_σ'_llam_dualTensorHom_atSpace_eq` to a non-empty local env. -/
private lemma denotTermAux_llam_dualTensorHom_atSpace_eq
    {σ : DEnv} {env : List DVal} {s_in s_τ : Space} {body : Term}
    (h_sτ_ne_real : s_τ ≠ .real)
    (h_dsi : denotSpaceAux σ env s_in = denotSpace σ s_in)
    (h_dsτ : denotSpaceAux σ env s_τ = denotSpace σ s_τ)
    (h_lin : IsLinearMap ℝ (fun v : (denotSpace σ s_in).carrier =>
      (denotTermAux σ (.hil ⟨denotSpace σ s_in, v⟩ :: env) body).atSpace
        (denotSpace σ s_τ)))
    (a_val : (denotSpace σ s_in).carrier) :
    dualTensorHom ℝ (denotSpace σ s_in).carrier (denotSpace σ s_τ).carrier
      ((denotTermAux σ env (.llam s_in s_τ body)).atSpace
        (HSpace.tprod (HSpace.dual (denotSpace σ s_in)) (denotSpace σ s_τ)))
      a_val
    = (denotTermAux σ (.hil ⟨denotSpace σ s_in, a_val⟩ :: env) body).atSpace
        (denotSpace σ s_τ) := by
  have h_match : (denotTermAux σ env (.llam s_in s_τ body)).matchesShape
      (.hil (HSpace.tprod (HSpace.dual (denotSpace σ s_in)) (denotSpace σ s_τ))) := by
    rw [show denotTermAux σ env (.llam s_in s_τ body)
          = llamTensorDVal (denotSpace σ s_in) (denotSpace σ s_τ)
              (fun v => denotTermAux σ (v :: env) body) from by
        cases s_τ with
        | real => exact absurd rfl h_sτ_ne_real
        | _ =>
          simp only [denotTermAux]
          rw [h_dsi, h_dsτ]]
    exact DVal.matchesShape_hil_rfl _ _
  rw [← DVal.asLinMap_eq_of_matchesShape h_match]
  exact denotTermAux_llam_apply_at_σ_eq h_sτ_ne_real h_dsi h_dsτ h_lin a_val

/-- **Env-threaded real-codomain apply helper** (LN D1). Env analogue of
    `denot_σ'_llam_real_atSpace_apply_eq`: `atSpace (HSpace.dual V_in)` of a
    `.real`-codomain `.llam` denoted under `denotTermAux σ env`, applied at
    `v_val`, equals the body denoted at the pushed env. -/
private lemma denotTermAux_llam_real_atSpace_apply_eq
    {σ : DEnv} {env : List DVal} {s_in : Space} {body : Term}
    (h_dsi : denotSpaceAux σ env s_in = denotSpace σ s_in)
    (h_lin : IsLinearMap ℝ (fun v : (denotSpace σ s_in).carrier =>
      (denotTermAux σ (.hil ⟨denotSpace σ s_in, v⟩ :: env) body).atSpace
        HSpace.real))
    (v_val : (denotSpace σ s_in).carrier) :
    DVal.atSpace (HSpace.dual (denotSpace σ s_in))
      (denotTermAux σ env (.llam s_in .real body)) v_val
      = (denotTermAux σ (.hil ⟨denotSpace σ s_in, v_val⟩ :: env) body).atSpace
          HSpace.real := by
  rw [show denotTermAux σ env (.llam s_in .real body)
        = llamRealDVal (denotSpace σ s_in)
            (fun v => (denotTermAux σ (v :: env) body).atSpace HSpace.real) from by
      simp only [denotTermAux]
      rw [h_dsi]]
  rw [atSpace_llamRealDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap h_lin v_val

/-- **2-binder env bridge** (LN keystone). Relate a 2-entry local-env
    denotation `denotTermAux σ [v1, v0] e` to a doubly-σ-bound denotation of
    the fully-opened body. The free vars `x0` (env index 1) and `x1`
    (env index 0) carry the two outer-binder values into `σ`. -/
private lemma denotTermAux_two_bind_bridge {σ : DEnv} {x0 x1 : Name}
    {v0 v1 : DVal} {e : Term}
    (h_x01 : x0 ≠ x1)
    (h_x0 : x0 ∉ Term.fv e) (h_x1 : x1 ∉ Term.fv e)
    (h_lc : Term.lc (Term.openVar x1 (Term.openRec 1 (.var x0) e))) :
    denotTerm ((σ.bind x0 v0).bind x1 v1)
        (Term.openVar x1 (Term.openRec 1 (.var x0) e))
      = denotTermAux σ [v1, v0] e := by

  show denotTermAux ((σ.bind x0 v0).bind x1 v1) []
      (Term.openVar x1 (Term.openRec 1 (.var x0) e)) = _
  rw [denotTermAux_lc_irrel h_lc ((σ.bind x0 v0).bind x1 v1) [] [v1, v0]]
  -- x1 ∉ fv (openRec 1 (.var x0) e): x1 ≠ x0 and x1 ∉ fv e.
  have h_x1_e' : x1 ∉ Term.fv (Term.openRec 1 (.var x0) e) := by
    intro hmem
    have hsub := Term.fv_openRec_subset 1 (.var x0) e hmem
    simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at hsub
    rcases hsub with h | h
    · exact h_x1 h
    · exact h_x01 h.symm
  -- Pull x1 out (env index 0).
  have B1 := denotTermAux_openRec_bind (x := x1) (σ.bind x0 v0) [v1, v0] 0
    (Term.openRec 1 (.var x0) e) h_x1_e'
  simp only [List.getD_cons_zero] at B1
  rw [Term.openVar] at *
  rw [B1]
  -- Pull x0 out (env index 1).
  have B2 := denotTermAux_openRec_bind (x := x0) σ [v1, v0] 1 e h_x0
  simp only [List.getD_cons_succ, List.getD_cons_zero] at B2
  rw [B2]

/-- **3-binder env bridge** (LN keystone). Relate a 3-entry local-env
    denotation `denotTermAux σ [v2, v1, v0] e` to a triply-σ-bound denotation
    of the fully-opened body. `x0` (env index 2), `x1` (env index 1),
    `x2` (env index 0). -/
private lemma denotTermAux_three_bind_bridge {σ : DEnv} {x0 x1 x2 : Name}
    {v0 v1 v2 : DVal} {e : Term}
    (h_x01 : x0 ≠ x1) (h_x02 : x0 ≠ x2) (h_x12 : x1 ≠ x2)
    (h_x0 : x0 ∉ Term.fv e) (h_x1 : x1 ∉ Term.fv e) (h_x2 : x2 ∉ Term.fv e)
    (h_lc : Term.lc
      (Term.openVar x2 (Term.openRec 1 (.var x1) (Term.openRec 2 (.var x0) e)))) :
    denotTerm (((σ.bind x0 v0).bind x1 v1).bind x2 v2)
        (Term.openVar x2 (Term.openRec 1 (.var x1) (Term.openRec 2 (.var x0) e)))
      = denotTermAux σ [v2, v1, v0] e := by
  show denotTermAux (((σ.bind x0 v0).bind x1 v1).bind x2 v2) []
      (Term.openVar x2 (Term.openRec 1 (.var x1) (Term.openRec 2 (.var x0) e))) = _
  rw [denotTermAux_lc_irrel h_lc (((σ.bind x0 v0).bind x1 v1).bind x2 v2) []
        [v2, v1, v0]]
  -- e₂ := openRec 2 (.var x0) e ; e₁ := openRec 1 (.var x1) e₂.
  set e₂ := Term.openRec 2 (.var x0) e with he₂
  set e₁ := Term.openRec 1 (.var x1) e₂ with he₁
  have h_x2_e₁ : x2 ∉ Term.fv e₁ := by
    intro hmem
    rw [he₁] at hmem
    have hsub := Term.fv_openRec_subset 1 (.var x1) e₂ hmem
    simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at hsub
    rcases hsub with h | h
    · rw [he₂] at h
      have hsub2 := Term.fv_openRec_subset 2 (.var x0) e h
      simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at hsub2
      rcases hsub2 with h' | h'
      · exact h_x2 h'
      · exact h_x02 h'.symm
    · exact h_x12 h.symm
  have h_x1_e₂ : x1 ∉ Term.fv e₂ := by
    intro hmem
    rw [he₂] at hmem
    have hsub := Term.fv_openRec_subset 2 (.var x0) e hmem
    simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at hsub
    rcases hsub with h | h
    · exact h_x1 h
    · exact h_x01 h.symm
  -- Pull x2 out (env index 0 of [v2, v1, v0]).
  have B1 := denotTermAux_openRec_bind (x := x2)
    ((σ.bind x0 v0).bind x1 v1) [v2, v1, v0] 0 e₁ h_x2_e₁
  simp only [List.getD_cons_zero] at B1
  rw [Term.openVar] at *
  rw [B1]
  -- Pull x1 out (env index 1).
  have B2 := denotTermAux_openRec_bind (x := x1)
    (σ.bind x0 v0) [v2, v1, v0] 1 e₂ h_x1_e₂
  simp only [List.getD_cons_succ, List.getD_cons_zero] at B2
  rw [he₁]
  rw [B2]
  -- Pull x0 out (env index 2).
  have B3 := denotTermAux_openRec_bind (x := x0) σ [v2, v1, v0] 2 e h_x0
  simp only [List.getD_cons_succ, List.getD_cons_zero] at B3
  rw [he₂]
  rw [B3]

/-- **4-binder env bridge** (LN keystone). Relate a 4-entry local-env
    denotation `denotTermAux σ [v3, v2, v1, v0] e` to a quadruply-σ-bound
    denotation of the fully-opened body. `x0` (env idx 3), `x1` (idx 2),
    `x2` (idx 1), `x3` (idx 0). -/
private lemma denotTermAux_four_bind_bridge {σ : DEnv} {x0 x1 x2 x3 : Name}
    {v0 v1 v2 v3 : DVal} {e : Term}
    (h_x01 : x0 ≠ x1) (h_x02 : x0 ≠ x2) (h_x03 : x0 ≠ x3)
    (h_x12 : x1 ≠ x2) (h_x13 : x1 ≠ x3) (h_x23 : x2 ≠ x3)
    (h_x0 : x0 ∉ Term.fv e) (h_x1 : x1 ∉ Term.fv e) (h_x2 : x2 ∉ Term.fv e)
    (h_x3 : x3 ∉ Term.fv e)
    (h_lc : Term.lc (Term.openVar x3 (Term.openRec 1 (.var x2)
      (Term.openRec 2 (.var x1) (Term.openRec 3 (.var x0) e))))) :
    denotTerm ((((σ.bind x0 v0).bind x1 v1).bind x2 v2).bind x3 v3)
        (Term.openVar x3 (Term.openRec 1 (.var x2)
          (Term.openRec 2 (.var x1) (Term.openRec 3 (.var x0) e))))
      = denotTermAux σ [v3, v2, v1, v0] e := by
  show denotTermAux ((((σ.bind x0 v0).bind x1 v1).bind x2 v2).bind x3 v3) []
      (Term.openVar x3 (Term.openRec 1 (.var x2)
        (Term.openRec 2 (.var x1) (Term.openRec 3 (.var x0) e)))) = _
  rw [denotTermAux_lc_irrel h_lc
    ((((σ.bind x0 v0).bind x1 v1).bind x2 v2).bind x3 v3) [] [v3, v2, v1, v0]]
  set e₃ := Term.openRec 3 (.var x0) e with he₃
  set e₂ := Term.openRec 2 (.var x1) e₃ with he₂
  set e₁ := Term.openRec 1 (.var x2) e₂ with he₁
  -- Freshness of x3 in e₁, x2 in e₂, x1 in e₃.
  have h_x3_e₁ : x3 ∉ Term.fv e₁ := by
    intro hmem; rw [he₁] at hmem
    have h := Term.fv_openRec_subset 1 (.var x2) e₂ hmem
    simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at h
    rcases h with h | h
    · rw [he₂] at h
      have h' := Term.fv_openRec_subset 2 (.var x1) e₃ h
      simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at h'
      rcases h' with h' | h'
      · rw [he₃] at h'
        have h'' := Term.fv_openRec_subset 3 (.var x0) e h'
        simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at h''
        rcases h'' with h'' | h''
        · exact h_x3 h''
        · exact h_x03 h''.symm
      · exact h_x13 h'.symm
    · exact h_x23 h.symm
  have h_x2_e₂ : x2 ∉ Term.fv e₂ := by
    intro hmem; rw [he₂] at hmem
    have h := Term.fv_openRec_subset 2 (.var x1) e₃ hmem
    simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at h
    rcases h with h | h
    · rw [he₃] at h
      have h' := Term.fv_openRec_subset 3 (.var x0) e h
      simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at h'
      rcases h' with h' | h'
      · exact h_x2 h'
      · exact h_x02 h'.symm
    · exact h_x12 h.symm
  have h_x1_e₃ : x1 ∉ Term.fv e₃ := by
    intro hmem; rw [he₃] at hmem
    have h := Term.fv_openRec_subset 3 (.var x0) e hmem
    simp only [Term.fv, Finset.mem_union, Finset.mem_singleton] at h
    rcases h with h | h
    · exact h_x1 h
    · exact h_x01 h.symm
  -- Pull x3 out (env index 0).
  have B1 := denotTermAux_openRec_bind (x := x3)
    (((σ.bind x0 v0).bind x1 v1).bind x2 v2) [v3, v2, v1, v0] 0 e₁ h_x3_e₁
  simp only [List.getD_cons_zero] at B1
  rw [Term.openVar] at *
  rw [B1]
  -- Pull x2 (idx 1).
  have B2 := denotTermAux_openRec_bind (x := x2)
    ((σ.bind x0 v0).bind x1 v1) [v3, v2, v1, v0] 1 e₂ h_x2_e₂
  simp only [List.getD_cons_succ, List.getD_cons_zero] at B2
  rw [he₁]; rw [B2]
  -- Pull x1 (idx 2).
  have B3 := denotTermAux_openRec_bind (x := x1)
    (σ.bind x0 v0) [v3, v2, v1, v0] 2 e₃ h_x1_e₃
  simp only [List.getD_cons_succ, List.getD_cons_zero] at B3
  rw [he₂]; rw [B3]
  -- Pull x0 (idx 3).
  have B4 := denotTermAux_openRec_bind (x := x0) σ [v3, v2, v1, v0] 3 e h_x0
  simp only [List.getD_cons_succ, List.getD_cons_zero] at B4
  rw [he₃]; rw [B4]

private lemma curry2NonReal_chain_app_eq
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (g_val : (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)).carrier)
    (a_val : (denotSpace σ sA).carrier)
    (b_val : (denotSpace σ sB).carrier) :
    dualTensorHom ℝ (denotSpace σ sB).carrier (denotSpace σ sRest).carrier
      (dualTensorHom ℝ (denotSpace σ sA).carrier
        (denotSpace σ (.tprod (.dual sB) sRest)).carrier
        ((denotTerm σ (Term.curry2NonReal sA sB sRest)).asLinMap
          (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest))
          (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest)))
          g_val)
        a_val)
      b_val
    = dualTensorHom ℝ
        (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)).carrier
        (denotSpace σ sRest).carrier g_val
        (a_val ⊗ₜ[ℝ] b_val) := by
  -- Env-form chain: outer_eval (env [g]) → dualTensorHom chain step (layer a,
  -- env [g] → [a,g]) → chain step (layer b, [a,g] → [b,a,g]) → innermost env eval.
  rw [curry2NonReal_outer_eval h_fresh_g h_fresh_a h_fresh_b
        h_ga h_gb h_ab h_sRest_ne_real svA svB svR env_wf ctx_ε g_val]
  rw [← curry2NonReal_innermost_appL_env_eval svA svB svR g_val a_val b_val]
  -- Common abbreviations.
  set g_bind : DVal :=
    .hil ⟨denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest), g_val⟩ with hg_bind
  -- FV-irrelevance: denotSpaceAux σ env s = denotSpace σ s for the closed spaces.
  have h_dsA_lc : SValid.lc svA = SValid.lc svA := rfl
  -- denotSpaceAux equalities for env [g_bind].
  have h_dsi_a : denotSpaceAux σ [g_bind] sA = denotSpace σ sA :=
    denotSpaceAux_lc_irrel (SValid.lc svA) σ [g_bind] []
  have h_dsmid_a : denotSpaceAux σ [g_bind] (.tprod (.dual sB) sRest)
      = denotSpace σ (.tprod (.dual sB) sRest) :=
    denotSpaceAux_lc_irrel (SValid.lc (SValid.tprod (SValid.dual svB) svR)) σ [g_bind] []
  -- Layer-a env linearity.
  have h_lin_a : IsLinearMap ℝ (fun a_v : (denotSpace σ sA).carrier =>
      (denotTermAux σ (.hil ⟨denotSpace σ sA, a_v⟩ :: [g_bind])
        (.llam sB sRest (.appL (.tprod sA sB) sRest (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0))))).atSpace
        (denotSpace σ (.tprod (.dual sB) sRest))) := by
    have hmid := curry2NonReal_denoted_midFn_isLinear h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab h_sRest_ne_real svA svB svR env_wf ctx_ε g_val
    simp only at hmid
    have h_g_not_fv_sA : Term.g_name ∉ Space.fv sA :=
      svA.notMem_fv_of_notMem_ε h_fresh_g
    have h_g_not_fv_sB : Term.g_name ∉ Space.fv sB :=
      svB.notMem_fv_of_notMem_ε h_fresh_g
    have h_g_not_fv_sR : Term.g_name ∉ Space.fv sRest :=
      svR.notMem_fv_of_notMem_ε h_fresh_g
    have h_dsA_σ_g : denotSpace (σ.bind Term.g_name g_bind) sA = denotSpace σ sA :=
      denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sA)
    have h_g_not_fv_mid : Term.g_name ∉ Space.fv (.tprod (.dual sB) sRest) :=
      (SValid.tprod (SValid.dual svB) svR).notMem_fv_of_notMem_ε h_fresh_g
    have h_dsmid_σ_g :
        denotSpace (σ.bind Term.g_name g_bind) (.tprod (.dual sB) sRest)
        = denotSpace σ (.tprod (.dual sB) sRest) :=
      denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_mid)
    rw [h_dsA_σ_g, h_dsmid_σ_g] at hmid
    refine IsLinearMap.congr hmid (fun a_v => ?_)
    -- pointwise: env-form = σ-bind-form via two_bind_bridge.
    have h_open : Term.openVar Term.a_name (Term.openRec 1 (.var Term.g_name)
          (.llam sB sRest (.appL (.tprod sA sB) sRest (.bvar 2)
            (.tprodE (.bvar 1) (.bvar 0)))))
        = .llam sB sRest (.appL (.tprod sA sB) sRest (.var Term.g_name)
            (.tprodE (.var Term.a_name) (.bvar 0))) := by
      simp only [Term.openVar, Term.openRec, Space.openRec,
        Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
        Space.openRec_lc (SValid.lc svR)]
      norm_num [Term.openRec]
    have h_lc : Term.lc (Term.openVar Term.a_name (Term.openRec 1 (.var Term.g_name)
          (.llam sB sRest (.appL (.tprod sA sB) sRest (.bvar 2)
            (.tprodE (.bvar 1) (.bvar 0)))))) := by
      rw [h_open]; exact (Term.curry2NonReal_mid_hasType h_fresh_a h_fresh_b
        h_ga h_gb h_ab h_sRest_ne_real svA svB svR).lc
    have h_mid_fv : ∀ y : Name, y ∉ ε → y ∉ Term.fv
        ((.llam sB sRest (.appL (.tprod sA sB) sRest (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0))) : Term)) := by
      intro y hy hmem
      simp only [Term.fv, Finset.mem_union, Finset.notMem_empty, or_false] at hmem
      rcases hmem with ((h | h) | (h | h))
      · exact svB.notMem_fv_of_notMem_ε hy h
      · exact svR.notMem_fv_of_notMem_ε hy h
      · exact (SValid.tprod svA svB).notMem_fv_of_notMem_ε hy h
      · exact svR.notMem_fv_of_notMem_ε hy h
    have h_a_fv := h_mid_fv _ h_fresh_a
    have h_g_fv := h_mid_fv _ h_fresh_g
    have hbr := denotTermAux_two_bind_bridge (σ := σ) (x0 := Term.g_name)
      (x1 := Term.a_name) (v0 := g_bind) (v1 := .hil ⟨denotSpace σ sA, a_v⟩)
      (e := .llam sB sRest (.appL (.tprod sA sB) sRest (.bvar 2)
        (.tprodE (.bvar 1) (.bvar 0))))
      h_ga h_g_fv h_a_fv h_lc
    rw [h_open] at hbr
    rw [hbr]
  show (dualTensorHom ℝ (denotSpace σ sB).carrier (denotSpace σ sRest).carrier)
      ((dualTensorHom ℝ (denotSpace σ sA).carrier
          (denotSpace σ (.tprod (.dual sB) sRest)).carrier)
        (DVal.atSpace (HSpace.tprod (HSpace.dual (denotSpace σ sA))
            (denotSpace σ (.tprod (.dual sB) sRest)))
          (denotTermAux σ [g_bind]
            (.llam sA (.tprod (.dual sB) sRest)
              (.llam sB sRest (.appL (.tprod sA sB) sRest (.bvar 2)
                (.tprodE (.bvar 1) (.bvar 0))))))) a_val) b_val = _
  rw [denotTermAux_llam_dualTensorHom_atSpace_eq (by intro h; cases h)
        h_dsi_a h_dsmid_a h_lin_a a_val]
  -- Layer b. env [a_bind, g_bind].
  set a_bind : DVal := .hil ⟨denotSpace σ sA, a_val⟩ with ha_bind
  have h_dsi_b : denotSpaceAux σ [a_bind, g_bind] sB = denotSpace σ sB :=
    denotSpaceAux_lc_irrel (SValid.lc svB) σ [a_bind, g_bind] []
  have h_dsR_b : denotSpaceAux σ [a_bind, g_bind] sRest = denotSpace σ sRest :=
    denotSpaceAux_lc_irrel (SValid.lc svR) σ [a_bind, g_bind] []
  have h_lin_b : IsLinearMap ℝ (fun b_v : (denotSpace σ sB).carrier =>
      (denotTermAux σ (.hil ⟨denotSpace σ sB, b_v⟩ :: [a_bind, g_bind])
        (.appL (.tprod sA sB) sRest (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0)))).atSpace (denotSpace σ sRest)) := by
    have hinner := curry2NonReal_denoted_innermostFn_isLinear h_fresh_g h_fresh_a
      h_fresh_b h_ga h_gb h_ab svA svB svR env_wf ctx_ε g_val a_val
    simp only at hinner
    have h_a_not_fv_sB : Term.a_name ∉ Space.fv sB :=
      svB.notMem_fv_of_notMem_ε h_fresh_a
    have h_a_not_fv_sR : Term.a_name ∉ Space.fv sRest :=
      svR.notMem_fv_of_notMem_ε h_fresh_a
    have h_g_not_fv_sB : Term.g_name ∉ Space.fv sB :=
      svB.notMem_fv_of_notMem_ε h_fresh_g
    have h_g_not_fv_sR : Term.g_name ∉ Space.fv sRest :=
      svR.notMem_fv_of_notMem_ε h_fresh_g
    have h_dsB_σ_g_a : denotSpace ((σ.bind Term.g_name g_bind).bind Term.a_name a_bind) sB
        = denotSpace σ sB :=
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_a_not_fv_sB)).trans
        (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sB))
    have h_dsR_σ_g_a : denotSpace ((σ.bind Term.g_name g_bind).bind Term.a_name a_bind) sRest
        = denotSpace σ sRest :=
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_a_not_fv_sR)).trans
        (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sR))
    rw [h_dsB_σ_g_a, h_dsR_σ_g_a] at hinner
    refine IsLinearMap.congr hinner (fun b_v => ?_)
    have h_open : Term.openVar Term.b_name (Term.openRec 1 (.var Term.a_name)
          (Term.openRec 2 (.var Term.g_name)
            (.appL (.tprod sA sB) sRest (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))))
        = .appL (.tprod sA sB) sRest (.var Term.g_name)
            (.tprodE (.var Term.a_name) (.var Term.b_name)) := by
      simp only [Term.openVar, Term.openRec, Space.openRec,
        Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB),
        Space.openRec_lc (SValid.lc svR)]
      norm_num [Term.openRec]
    have h_lc : Term.lc (Term.openVar Term.b_name (Term.openRec 1 (.var Term.a_name)
          (Term.openRec 2 (.var Term.g_name)
            (.appL (.tprod sA sB) sRest (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))))) := by
      rw [h_open]; exact (Term.curry2NonReal_innermost_hasType h_ga h_gb h_ab svA svB svR).lc
    have h_innerbody_fv : ∀ y : Name, y ∉ ε →
        y ∉ Term.fv (.appL (.tprod sA sB) sRest (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0)) : Term) := by
      intro y hy hmem
      simp only [Term.fv, Finset.mem_union, Finset.notMem_empty, or_false] at hmem
      rcases hmem with (h | h)
      · exact (SValid.tprod svA svB).notMem_fv_of_notMem_ε hy h
      · exact svR.notMem_fv_of_notMem_ε hy h
    have hbr := denotTermAux_three_bind_bridge (σ := σ) (x0 := Term.g_name)
      (x1 := Term.a_name) (x2 := Term.b_name) (v0 := g_bind) (v1 := a_bind)
      (v2 := .hil ⟨denotSpace σ sB, b_v⟩)
      (e := .appL (.tprod sA sB) sRest (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))
      h_ga h_gb h_ab
      (h_innerbody_fv _ h_fresh_g) (h_innerbody_fv _ h_fresh_a)
      (h_innerbody_fv _ h_fresh_b) h_lc
    rw [h_open] at hbr
    rw [hbr]
  show (dualTensorHom ℝ (denotSpace σ sB).carrier (denotSpace σ sRest).carrier)
      (DVal.atSpace (HSpace.tprod (HSpace.dual (denotSpace σ sB)) (denotSpace σ sRest))
        (denotTermAux σ [a_bind, g_bind]
          (.llam sB sRest (.appL (.tprod sA sB) sRest (.bvar 2)
            (.tprodE (.bvar 1) (.bvar 0)))))) b_val = _
  rw [denotTermAux_llam_dualTensorHom_atSpace_eq h_sRest_ne_real
        h_dsi_b h_dsR_b h_lin_b b_val]

private lemma curry2NonReal_asLinMap_injective
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    Function.Injective
      ((denotTerm σ (Term.curry2NonReal sA sB sRest)).asLinMap
        (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest))
        (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest)))) := by
  intro g₁ g₂ h_eq
  -- Reduce to dualTensorHom equality.
  apply dualTensorHom_injective_of_hSpace
    (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)) (denotSpace σ sRest)
  -- Goal: dualTensorHom V_AB V_sRest g₁ = dualTensorHom V_AB V_sRest g₂ (LinearMaps).
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero]
  | tmul a b =>
    -- Use chain_app_eq backwards on each side, then h_eq.
    rw [← curry2NonReal_chain_app_eq h_fresh_g h_fresh_a h_fresh_b h_ga h_gb h_ab
          h_sRest_ne_real svA svB svR env_wf ctx_ε g₁ a b]
    rw [← curry2NonReal_chain_app_eq h_fresh_g h_fresh_a h_fresh_b h_ga h_gb h_ab
          h_sRest_ne_real svA svB svR env_wf ctx_ε g₂ a b]
    rw [h_eq]
  | add p q ih_p ih_q =>
    rw [LinearMap.map_add, LinearMap.map_add, ih_p, ih_q]

private lemma curry2NonReal_asLinMap_bijective
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    Function.Bijective
      ((denotTerm σ (Term.curry2NonReal sA sB sRest)).asLinMap
        (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest))
        (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest)))) := by
  have h_inj := curry2NonReal_asLinMap_injective h_fresh_g h_fresh_a h_fresh_b
    h_ga h_gb h_ab h_sRest_ne_real svA svB svR env_wf ctx_ε
  refine ⟨h_inj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (curry2NonReal_finrank_eq (denotSpace σ sA) (denotSpace σ sB)
      (denotSpace σ sRest))).mp h_inj

private lemma denot_uncurry2NonReal_asLinMap_eq_symm
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    let V_uncurried : HSpace := denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)
    let V_curried : HSpace := denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest))
    let h_bij := curry2NonReal_asLinMap_bijective h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab h_sRest_ne_real svA svB svR env_wf ctx_ε
    DVal.asLinMap V_curried V_uncurried
        (denotTerm σ (Term.uncurry2NonReal sA sB sRest))
      = ((LinearEquiv.ofBijective
          ((denotTerm σ (Term.curry2NonReal sA sB sRest)).asLinMap
            V_uncurried V_curried)
          h_bij).symm : V_curried.carrier →ₗ[ℝ] V_uncurried.carrier) := by
  intro V_uncurried V_curried h_bij
  rw [denot_uncurry2NonReal_asLinMap_eq_mooreInv]
  exact mooreInv_bijective _ _ h_bij

/-- **Helper**: curry2NonReal undoes uncurry2NonReal. Given any value `X`
    in V_F_curried, applying uncurry2NonReal then curry2NonReal returns `X`.
    Uses B3 (uncurry = curry.symm) + LinearEquiv.apply_symm_apply. -/
private lemma curry2NonReal_uncurry2NonReal_id
    {σ : DEnv} {ε : NLCtx} {sA sB sRest : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (h_sRest_ne_real : sRest ≠ .real)
    (svA : SValid ε sA) (svB : SValid ε sB) (svR : SValid ε sRest)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (X : (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest))).carrier) :
    (denotTerm σ (Term.curry2NonReal sA sB sRest)).asLinMap
        (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest))
        (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest)))
        ((denotTerm σ (Term.uncurry2NonReal sA sB sRest)).asLinMap
          (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest)))
          (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest)) X)
      = X := by
  have h_bij := curry2NonReal_asLinMap_bijective h_fresh_g h_fresh_a h_fresh_b
    h_ga h_gb h_ab h_sRest_ne_real svA svB svR env_wf ctx_ε
  rw [denot_uncurry2NonReal_asLinMap_eq_symm h_fresh_g h_fresh_a h_fresh_b
        h_ga h_gb h_ab h_sRest_ne_real svA svB svR env_wf ctx_ε]
  exact LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective
    ((denotTerm σ (Term.curry2NonReal sA sB sRest)).asLinMap
      (denotSpace σ (.tprod (.dual (.tprod sA sB)) sRest))
      (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sRest)))) h_bij) X

/-- Env-form innerFn linearity for curry2Real: layer-g linearity over env
    `[g_bind]` of the outer body (`.llam a … .llam b … appI`). Bridged from
    the σ-bind `curry2Real_denoted_innerFn_isLinear` via `denotTerm_openVar_bind`. -/
private lemma curry2Real_innerFn_env_isLinear
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    IsLinearMap ℝ (fun g_val : (denotSpace σ (.dual (.tprod sA sB))).carrier =>
      (denotTermAux σ
          [.hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩]
        (.llam sA (.dual sB)
          (.llam sB .real
            (.appI (.tprod sA sB) (.bvar 2)
              (.tprodE (.bvar 1) (.bvar 0)))))).atSpace
        (denotSpace σ (.tprod (.dual sA) (.dual sB)))) := by
  have hsig := curry2Real_denoted_innerFn_isLinear h_fresh_g h_fresh_a h_fresh_b
    h_ga h_gb h_ab svA svB env_wf ctx_ε
  refine IsLinearMap.congr hsig (fun g_v => ?_)
  have h_open : Term.openVar Term.g_name
        (.llam sA (.dual sB) (.llam sB .real
          (.appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))))
      = .llam sA (.dual sB) (.llam sB .real
          (.appI (.tprod sA sB) (.var Term.g_name) (.tprodE (.bvar 1) (.bvar 0)))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec,
      Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB)]
    norm_num [Term.openRec]
  have h_lc : Term.lc (Term.openVar Term.g_name
        (.llam sA (.dual sB) (.llam sB .real
          (.appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))))) := by
    rw [h_open]
    exact (Term.curry2Real_body_hasType h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab svA svB).lc
  have h_g_fv : Term.g_name ∉ Term.fv
      ((.llam sA (.dual sB) (.llam sB .real
        (.appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))) : Term)) := by
    have h_gA : Term.g_name ∉ Space.fv sA := svA.notMem_fv_of_notMem_ε h_fresh_g
    have h_gB : Term.g_name ∉ Space.fv sB := svB.notMem_fv_of_notMem_ε h_fresh_g
    have h_gAB : Term.g_name ∉ Space.fv (.tprod sA sB) :=
      (SValid.tprod svA svB).notMem_fv_of_notMem_ε h_fresh_g
    have h_gDB : Term.g_name ∉ Space.fv (.dual sB) :=
      (SValid.dual svB).notMem_fv_of_notMem_ε h_fresh_g
    simp only [Term.fv, Finset.mem_union, Finset.notMem_empty, or_false]
    intro h
    rcases h with ((h | h) | (h | h) | h)
    · exact h_gA h
    · exact h_gDB h
    · exact h_gB h
    · exact (by simpa [Space.fv] using h)
    · exact h_gAB h
  have hbr := denotTerm_openVar_bind (σ := σ) (y := Term.g_name)
    (v := .hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_v⟩)
    (e := .llam sA (.dual sB) (.llam sB .real
      (.appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))))
    (by rw [h_open] at h_lc ⊢; exact h_lc) h_g_fv
  rw [h_open] at hbr
  rw [hbr]

private lemma curry2Real_chain_app_eq
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (g_val : (denotSpace σ (.dual (.tprod sA sB))).carrier)
    (a_val : (denotSpace σ sA).carrier)
    (b_val : (denotSpace σ sB).carrier) :
    (DVal.hil ⟨HSpace.dual (denotSpace σ sB),
      dualTensorHom ℝ (denotSpace σ sA).carrier
        (denotSpace σ (.dual sB)).carrier
        ((denotTerm σ (Term.curry2Real sA sB)).asLinMap
          (denotSpace σ (.dual (.tprod sA sB)))
          (denotSpace σ (.tprod (.dual sA) (.dual sB))) g_val)
        a_val⟩).asLinFunctional (denotSpace σ sB) b_val
      = (DVal.hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩).asLinFunctional
          (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))
          (a_val ⊗ₜ[ℝ] b_val) := by
  set g_bind : DVal := .hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩ with hg_bind
  set a_bind : DVal := .hil ⟨denotSpace σ sA, a_val⟩ with ha_bind
  -- denotSpaceAux equalities for the closed spaces.
  have h_dsi_g_a : denotSpaceAux σ [g_bind] sA = denotSpace σ sA :=
    denotSpaceAux_lc_irrel (SValid.lc svA) σ [g_bind] []
  have h_dsmid_g : denotSpaceAux σ [g_bind] (.dual sB) = denotSpace σ (.dual sB) :=
    denotSpaceAux_lc_irrel (SValid.lc (SValid.dual svB)) σ [g_bind] []
  have h_dsi_b : denotSpaceAux σ [a_bind, g_bind] sB = denotSpace σ sB :=
    denotSpaceAux_lc_irrel (SValid.lc svB) σ [a_bind, g_bind] []
  -- Reusable: free-var freshness for the inner closed bodies.
  have h_innerbody_fv : ∀ y : Name, y ∉ ε →
      y ∉ Term.fv (.appI (.tprod sA sB) (.bvar 2)
        (.tprodE (.bvar 1) (.bvar 0)) : Term) := by
    intro y hy hmem
    simp only [Term.fv, Finset.mem_union, Finset.notMem_empty, or_false] at hmem
    exact (SValid.tprod svA svB).notMem_fv_of_notMem_ε hy hmem
  -- Step 1: env-form outer_eval (asLinMap g_val → atSpace at env [g_bind]).
  have h_outer_eval : (denotTerm σ (Term.curry2Real sA sB)).asLinMap
        (denotSpace σ (.dual (.tprod sA sB)))
        (denotSpace σ (.tprod (.dual sA) (.dual sB))) g_val =
      (denotTermAux σ [g_bind]
        (.llam sA (.dual sB)
          (.llam sB .real
            (.appI (.tprod sA sB) (.bvar 2)
              (.tprodE (.bvar 1) (.bvar 0)))))).atSpace
      (denotSpace σ (.tprod (.dual sA) (.dual sB))) := by
    show DVal.asLinMap _ _ (denotTerm σ
      (.llam (.dual (.tprod sA sB)) (.tprod (.dual sA) (.dual sB)) _)) g_val = _
    rw [denotTerm_llam_non_real (by intro h; cases h)]
    rw [asLinMap_llamTensorDVal]
    exact LinearMap.ofFun_apply_of_isLinearMap
      (curry2Real_innerFn_env_isLinear h_fresh_g h_fresh_a h_fresh_b
        h_ga h_gb h_ab svA svB env_wf ctx_ε) g_val
  -- Layer-a env linearity (codomain .dual sB, non-real).
  have h_lin_a : IsLinearMap ℝ (fun a_v : (denotSpace σ sA).carrier =>
      (denotTermAux σ (.hil ⟨denotSpace σ sA, a_v⟩ :: [g_bind])
        (.llam sB .real (.appI (.tprod sA sB) (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0))))).atSpace (denotSpace σ (.dual sB))) := by
    have hmid := curry2Real_denoted_midFn_isLinear h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab svA svB env_wf ctx_ε g_val
    simp only at hmid
    have h_g_not_fv_sA : Term.g_name ∉ Space.fv sA :=
      svA.notMem_fv_of_notMem_ε h_fresh_g
    have h_g_not_fv_mid : Term.g_name ∉ Space.fv (.dual sB) :=
      (SValid.dual svB).notMem_fv_of_notMem_ε h_fresh_g
    have h_dsA_σ_g : denotSpace (σ.bind Term.g_name g_bind) sA = denotSpace σ sA :=
      denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sA)
    have h_dsmid_σ_g : denotSpace (σ.bind Term.g_name g_bind) (.dual sB)
        = denotSpace σ (.dual sB) :=
      denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_mid)
    rw [h_dsA_σ_g, h_dsmid_σ_g] at hmid
    refine IsLinearMap.congr hmid (fun a_v => ?_)
    have h_open : Term.openVar Term.a_name (Term.openRec 1 (.var Term.g_name)
          (.llam sB .real (.appI (.tprod sA sB) (.bvar 2)
            (.tprodE (.bvar 1) (.bvar 0)))))
        = .llam sB .real (.appI (.tprod sA sB) (.var Term.g_name)
            (.tprodE (.var Term.a_name) (.bvar 0))) := by
      simp only [Term.openVar, Term.openRec, Space.openRec,
        Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB)]
      norm_num [Term.openRec]
    have h_lc : Term.lc (Term.openVar Term.a_name (Term.openRec 1 (.var Term.g_name)
          (.llam sB .real (.appI (.tprod sA sB) (.bvar 2)
            (.tprodE (.bvar 1) (.bvar 0)))))) := by
      rw [h_open]; exact (Term.curry2Real_mid_hasType h_fresh_a h_fresh_b
        h_ga h_gb h_ab svA svB).lc
    have h_mid_fv : ∀ y : Name, y ∉ ε → y ∉ Term.fv
        ((.llam sB .real (.appI (.tprod sA sB) (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0))) : Term)) := by
      intro y hy hmem
      simp only [Term.fv, Finset.mem_union, Finset.notMem_empty,
        or_false] at hmem
      rcases hmem with ((h | h) | h)
      · exact svB.notMem_fv_of_notMem_ε hy h
      · exact (by simpa [Space.fv] using h)
      · exact (SValid.tprod svA svB).notMem_fv_of_notMem_ε hy h
    have hbr := denotTermAux_two_bind_bridge (σ := σ) (x0 := Term.g_name)
      (x1 := Term.a_name) (v0 := g_bind) (v1 := .hil ⟨denotSpace σ sA, a_v⟩)
      (e := .llam sB .real (.appI (.tprod sA sB) (.bvar 2)
        (.tprodE (.bvar 1) (.bvar 0))))
      h_ga (h_mid_fv _ h_fresh_g) (h_mid_fv _ h_fresh_a) h_lc
    rw [h_open] at hbr
    rw [hbr]
  -- Layer-b env linearity (codomain .real).
  have h_lin_b : IsLinearMap ℝ (fun b_v : (denotSpace σ sB).carrier =>
      (denotTermAux σ (.hil ⟨denotSpace σ sB, b_v⟩ :: [a_bind, g_bind])
        (.appI (.tprod sA sB) (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0)))).atSpace HSpace.real) := by
    have hinner := curry2Real_denoted_innermostFn_isLinear h_fresh_g h_fresh_a
      h_fresh_b h_ga h_gb h_ab svA svB env_wf ctx_ε g_val a_val
    simp only at hinner
    have h_a_not_fv_sB : Term.a_name ∉ Space.fv sB :=
      svB.notMem_fv_of_notMem_ε h_fresh_a
    have h_g_not_fv_sB : Term.g_name ∉ Space.fv sB :=
      svB.notMem_fv_of_notMem_ε h_fresh_g
    have h_dsB_σ_g_a : denotSpace ((σ.bind Term.g_name g_bind).bind Term.a_name a_bind) sB
        = denotSpace σ sB :=
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_a_not_fv_sB)).trans
        (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_g_not_fv_sB))
    -- Transport hinner fully to σ-frame sB carrier (rewrites both domain type and binding).
    have hinner' : IsLinearMap ℝ (fun b_v : (denotSpace σ sB).carrier =>
        (denotTerm (((σ.bind Term.g_name g_bind).bind Term.a_name a_bind).bind
            Term.b_name (.hil ⟨denotSpace σ sB, b_v⟩))
          (.appI (.tprod sA sB) (.var Term.g_name)
            (.tprodE (.var Term.a_name) (.var Term.b_name)))).atSpace HSpace.real) := by
      revert hinner
      generalize hV : denotSpace ((σ.bind Term.g_name g_bind).bind Term.a_name a_bind) sB = V
      rw [hV] at h_dsB_σ_g_a
      subst h_dsB_σ_g_a
      exact fun h => h
    refine IsLinearMap.congr hinner' (fun b_v => ?_)
    have h_open : Term.openVar Term.b_name (Term.openRec 1 (.var Term.a_name)
          (Term.openRec 2 (.var Term.g_name)
            (.appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))))
        = .appI (.tprod sA sB) (.var Term.g_name)
            (.tprodE (.var Term.a_name) (.var Term.b_name)) := by
      simp only [Term.openVar, Term.openRec, Space.openRec,
        Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB)]
      norm_num [Term.openRec]
    have h_lc : Term.lc (Term.openVar Term.b_name (Term.openRec 1 (.var Term.a_name)
          (Term.openRec 2 (.var Term.g_name)
            (.appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))))) := by
      rw [h_open]; exact (Term.curry2Real_innermost_hasType h_ga h_gb h_ab svA svB).lc
    have hbr := denotTermAux_three_bind_bridge (σ := σ) (x0 := Term.g_name)
      (x1 := Term.a_name) (x2 := Term.b_name) (v0 := g_bind) (v1 := a_bind)
      (v2 := .hil ⟨denotSpace σ sB, b_v⟩)
      (e := .appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))
      h_ga h_gb h_ab
      (h_innerbody_fv _ h_fresh_g) (h_innerbody_fv _ h_fresh_a)
      (h_innerbody_fv _ h_fresh_b) h_lc
    rw [h_open] at hbr
    rw [hbr]
  -- Assemble. Step 3: combine outer_eval + layer-a dualTensorHom step.
  have h_step_combined :
      dualTensorHom ℝ (denotSpace σ sA).carrier (denotSpace σ (.dual sB)).carrier
        ((denotTerm σ (Term.curry2Real sA sB)).asLinMap
          (denotSpace σ (.dual (.tprod sA sB)))
          (denotSpace σ (.tprod (.dual sA) (.dual sB))) g_val) a_val =
      (denotTermAux σ [a_bind, g_bind]
        (.llam sB .real (.appI (.tprod sA sB) (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0))))).atSpace (denotSpace σ (.dual sB)) := by
    rw [h_outer_eval]
    have := denotTermAux_llam_dualTensorHom_atSpace_eq (σ := σ) (env := [g_bind])
      (s_in := sA) (s_τ := .dual sB)
      (body := .llam sB .real (.appI (.tprod sA sB) (.bvar 2)
        (.tprodE (.bvar 1) (.bvar 0))))
      (by intro h; cases h) h_dsi_g_a h_dsmid_g h_lin_a a_val
    convert this using 2
  -- Step 4: lift through asLinFunctional via congrArg.
  rw [show (DVal.hil ⟨HSpace.dual (denotSpace σ sB),
        dualTensorHom ℝ (denotSpace σ sA).carrier (denotSpace σ (.dual sB)).carrier
          ((denotTerm σ (Term.curry2Real sA sB)).asLinMap
            (denotSpace σ (.dual (.tprod sA sB)))
            (denotSpace σ (.tprod (.dual sA) (.dual sB))) g_val) a_val⟩)
      = DVal.hil ⟨HSpace.dual (denotSpace σ sB),
        (denotTermAux σ [a_bind, g_bind]
          (.llam sB .real (.appI (.tprod sA sB) (.bvar 2)
            (.tprodE (.bvar 1) (.bvar 0))))).atSpace (denotSpace σ (.dual sB))⟩
      from by rw [h_step_combined]]
  rw [asLinFunctional_hil_dual]
  -- Step 5: layer-b real apply + innermost env eval.
  show (DVal.atSpace (HSpace.dual (denotSpace σ sB))
      (denotTermAux σ [a_bind, g_bind]
        (.llam sB .real (.appI (.tprod sA sB) (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0)))))) b_val = _
  rw [denotTermAux_llam_real_atSpace_apply_eq (σ := σ) (env := [a_bind, g_bind])
        (s_in := sB) (body := .appI (.tprod sA sB) (.bvar 2)
          (.tprodE (.bvar 1) (.bvar 0))) h_dsi_b h_lin_b b_val]
  -- Final: the innermost appI body env eval = asLinFunctional g_val (a⊗b).
  rw [← curry2Real_innermost_appI_eval_at_inputs h_fresh_g h_fresh_a h_fresh_b
        h_ga h_gb h_ab svA svB g_val a_val b_val]
  -- Bridge env-form [b,a,g] appI to σ_g_a_b appI (three_bind).
  have h_open : Term.openVar Term.b_name (Term.openRec 1 (.var Term.a_name)
        (Term.openRec 2 (.var Term.g_name)
          (.appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))))
      = .appI (.tprod sA sB) (.var Term.g_name)
          (.tprodE (.var Term.a_name) (.var Term.b_name)) := by
    simp only [Term.openVar, Term.openRec, Space.openRec,
      Space.openRec_lc (SValid.lc svA), Space.openRec_lc (SValid.lc svB)]
    norm_num [Term.openRec]
  have h_lc : Term.lc (Term.openVar Term.b_name (Term.openRec 1 (.var Term.a_name)
        (Term.openRec 2 (.var Term.g_name)
          (.appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))))) := by
    rw [h_open]; exact (Term.curry2Real_innermost_hasType h_ga h_gb h_ab svA svB).lc
  have hbr := denotTermAux_three_bind_bridge (σ := σ) (x0 := Term.g_name)
    (x1 := Term.a_name) (x2 := Term.b_name) (v0 := g_bind) (v1 := a_bind)
    (v2 := .hil ⟨denotSpace σ sB, b_val⟩)
    (e := .appI (.tprod sA sB) (.bvar 2) (.tprodE (.bvar 1) (.bvar 0)))
    h_ga h_gb h_ab
    (h_innerbody_fv _ h_fresh_g) (h_innerbody_fv _ h_fresh_a)
    (h_innerbody_fv _ h_fresh_b) h_lc
  rw [h_open] at hbr
  rw [hbr]

private lemma curry2Real_asLinMap_injective
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    Function.Injective
      ((denotTerm σ (Term.curry2Real sA sB)).asLinMap
        (denotSpace σ (.dual (.tprod sA sB)))
        (denotSpace σ (.tprod (.dual sA) (.dual sB)))) := by
  intro g₁ g₂ h_eq
  -- View g₁ g₂ as LinearMaps via @[reducible] HSpace.dual unfolding.
  show (g₁ : ((denotSpace σ sA).tprod (denotSpace σ sB)).carrier →ₗ[ℝ] ℝ) = g₂
  apply LinearMap.ext
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact (LinearMap.map_zero g₁).trans (LinearMap.map_zero g₂).symm
  | tmul a b =>
    have h_chain_1 := curry2Real_chain_app_eq h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab svA svB env_wf ctx_ε g₁ a b
    have h_chain_2 := curry2Real_chain_app_eq h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab svA svB env_wf ctx_ε g₂ a b
    -- Reduce the asLinFunctional RHS via asLinFunctional_hil_dual.
    -- The dval is .hil ⟨denotSpace σ (.dual (.tprod sA sB)), g_val⟩, where
    -- denotSpace σ (.dual (.tprod sA sB)) is defeq to HSpace.dual V_AB.
    have hRHS_1 :
        (DVal.hil ⟨denotSpace σ (.dual (.tprod sA sB)), g₁⟩).asLinFunctional
          (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))
        = (g₁ : ((denotSpace σ sA).tprod (denotSpace σ sB)).carrier →ₗ[ℝ] ℝ) :=
      asLinFunctional_hil_dual _ _
    have hRHS_2 :
        (DVal.hil ⟨denotSpace σ (.dual (.tprod sA sB)), g₂⟩).asLinFunctional
          (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))
        = (g₂ : ((denotSpace σ sA).tprod (denotSpace σ sB)).carrier →ₗ[ℝ] ℝ) :=
      asLinFunctional_hil_dual _ _
    rw [hRHS_1] at h_chain_1
    rw [hRHS_2] at h_chain_2

    have h_eq' :
        (DVal.asLinMap (denotSpace σ (sA.tprod sB).dual)
            (denotSpace σ (sA.dual.tprod sB.dual))
            (denotTerm σ (Term.curry2Real sA sB))) g₁
          = (DVal.asLinMap (denotSpace σ (sA.tprod sB).dual)
            (denotSpace σ (sA.dual.tprod sB.dual))
            (denotTerm σ (Term.curry2Real sA sB))) g₂ := h_eq
    have : (DVal.asLinFunctional (denotSpace σ sB)
            (DVal.hil
              ⟨(denotSpace σ sB).dual,
                ((dualTensorHom ℝ (denotSpace σ sA).carrier (denotSpace σ sB.dual).carrier)
                    ((DVal.asLinMap (denotSpace σ (sA.tprod sB).dual)
                        (denotSpace σ (sA.dual.tprod sB.dual))
                        (denotTerm σ (Term.curry2Real sA sB))) g₁)) a⟩)) b
          = (DVal.asLinFunctional (denotSpace σ sB)
            (DVal.hil
              ⟨(denotSpace σ sB).dual,
                ((dualTensorHom ℝ (denotSpace σ sA).carrier (denotSpace σ sB.dual).carrier)
                    ((DVal.asLinMap (denotSpace σ (sA.tprod sB).dual)
                        (denotSpace σ (sA.dual.tprod sB.dual))
                        (denotTerm σ (Term.curry2Real sA sB))) g₂)) a⟩)) b := by
      rw [h_eq']
    exact h_chain_1.symm.trans (this.trans h_chain_2)
  | add p q ih_p ih_q =>
    exact (LinearMap.map_add g₁ p q).trans
      (by rw [ih_p, ih_q]; exact (LinearMap.map_add g₂ p q).symm)

private lemma curry2Real_asLinMap_bijective
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    Function.Bijective
      ((denotTerm σ (Term.curry2Real sA sB)).asLinMap
        (denotSpace σ (.dual (.tprod sA sB)))
        (denotSpace σ (.tprod (.dual sA) (.dual sB)))) := by
  have h_inj := curry2Real_asLinMap_injective h_fresh_g h_fresh_a h_fresh_b
    h_ga h_gb h_ab svA svB env_wf ctx_ε
  refine ⟨h_inj, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (curry2Real_finrank_eq (denotSpace σ sA) (denotSpace σ sB))).mp h_inj

private lemma denot_uncurry2Real_asLinMap_eq_symm
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    let V_uncurried : HSpace := denotSpace σ (.dual (.tprod sA sB))
    let V_curried : HSpace := denotSpace σ (.tprod (.dual sA) (.dual sB))
    let h_bij := curry2Real_asLinMap_bijective h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab svA svB env_wf ctx_ε
    DVal.asLinMap V_curried V_uncurried (denotTerm σ (Term.uncurry2Real sA sB))
      = ((LinearEquiv.ofBijective
          ((denotTerm σ (Term.curry2Real sA sB)).asLinMap V_uncurried V_curried)
          h_bij).symm : V_curried.carrier →ₗ[ℝ] V_uncurried.carrier) := by
  intro V_uncurried V_curried h_bij
  rw [denot_uncurry2Real_asLinMap_eq_mooreInv]
  exact mooreInv_bijective _ _ h_bij

private lemma uncurry2Real_apply_eq_dualTensorHom
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (t : (denotSpace σ (.tprod (.dual sA) (.dual sB))).carrier)
    (a_val : (denotSpace σ sA).carrier)
    (b_val : (denotSpace σ sB).carrier) :
    (DVal.hil ⟨denotSpace σ (.dual (.tprod sA sB)),
        (denotTerm σ (Term.uncurry2Real sA sB)).asLinMap
          (denotSpace σ (.tprod (.dual sA) (.dual sB)))
          (denotSpace σ (.dual (.tprod sA sB))) t⟩).asLinFunctional
        (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))
        (a_val ⊗ₜ[ℝ] b_val)
    = (DVal.hil ⟨HSpace.dual (denotSpace σ sB),
        dualTensorHom ℝ (denotSpace σ sA).carrier (denotSpace σ sB.dual).carrier
          t a_val⟩).asLinFunctional (denotSpace σ sB) b_val := by
  -- Let f := uncurry2Real(t) ∈ V_sum_dual.
  -- By C3, uncurry2Real_asLinMap = (curry2Real_LinearEquiv).symm.
  -- So curry2Real_LinMap(f) = t (by LinearEquiv inverse).
  -- Apply curry2Real_chain_app_eq with g_val := f:
  --   dualTensorHom V_A V_dual_B (curry2Real_LinMap f) a b
  --     = (.hil ⟨V_uncurried, f⟩).asLinFunctional V_sum (a⊗b)
  --     = f(a⊗b) (via asLinFunctional_hil_dual)
  -- The LHS = dualTensorHom V_A V_dual_B t a b (since curry2Real_LinMap f = t).
  -- The RHS = uncurry2Real(t)(a⊗b) = (uncurry2Real.asLinMap V_τ V_sum_dual t)(a⊗b).
  set f : (denotSpace σ (.dual (.tprod sA sB))).carrier :=
    (denotTerm σ (Term.uncurry2Real sA sB)).asLinMap
      (denotSpace σ (.tprod (.dual sA) (.dual sB)))
      (denotSpace σ (.dual (.tprod sA sB))) t with hf
  -- Show curry2Real_LinMap(f) = t.
  have h_curry_uncurry : (denotTerm σ (Term.curry2Real sA sB)).asLinMap
      (denotSpace σ (.dual (.tprod sA sB)))
      (denotSpace σ (.tprod (.dual sA) (.dual sB))) f = t := by
    have h_C3 := denot_uncurry2Real_asLinMap_eq_symm h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab svA svB env_wf ctx_ε
    -- h_C3 : uncurry2Real_LinMap = (curry2Real_LinearEquiv).symm
    -- So (curry2Real_LinearEquiv) ∘ uncurry2Real_LinMap = id.
    -- f = uncurry2Real_LinMap t = curry2Real_LinearEquiv.symm t.
    -- curry2Real_LinMap f = curry2Real_LinearEquiv (curry2Real_LinearEquiv.symm t) = t. ✓
    have h_bij := curry2Real_asLinMap_bijective h_fresh_g h_fresh_a h_fresh_b
      h_ga h_gb h_ab svA svB env_wf ctx_ε
    have h_f_eq : f = ((LinearEquiv.ofBijective
        ((denotTerm σ (Term.curry2Real sA sB)).asLinMap
          (denotSpace σ (.dual (.tprod sA sB)))
          (denotSpace σ (.tprod (.dual sA) (.dual sB)))) h_bij).symm :
          _ →ₗ[ℝ] _) t := by
      rw [hf]
      rw [← h_C3]
    -- curry2Real_LinMap (LinearEquiv.symm t) = t (via LinearEquiv.apply_symm_apply).
    rw [h_f_eq]
    exact LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective
        ((denotTerm σ (Term.curry2Real sA sB)).asLinMap
          (denotSpace σ (.dual (.tprod sA sB)))
          (denotSpace σ (.tprod (.dual sA) (.dual sB)))) h_bij) t
  -- Apply curry2Real_chain_app_eq with g_val := f, a_val, b_val.
  have h_chain := curry2Real_chain_app_eq h_fresh_g h_fresh_a h_fresh_b
    h_ga h_gb h_ab svA svB env_wf ctx_ε f a_val b_val
  -- h_chain : (.hil ⟨V_dual_B, dualTensorHom V_A V_dual_B (curry2Real_LinMap f) a_val⟩).asLinFunctional V_B b_val
  --        = (.hil ⟨V_uncurried, f⟩).asLinFunctional V_sum (a⊗b)
  rw [h_curry_uncurry] at h_chain
  -- h_chain : (.hil ⟨V_dual_B, dualTensorHom V_A V_dual_B t a_val⟩).asLinFunctional V_B b_val
  --        = (.hil ⟨V_uncurried, f⟩).asLinFunctional V_sum (a⊗b)
  -- Goal: (.hil ⟨V_uncurried, f⟩).asLinFunctional V_sum (a⊗b)
  --     = (.hil ⟨V_dual_B, dualTensorHom V_A V_dual_B t a_val⟩).asLinFunctional V_B b_val
  -- (with f = uncurry2Real_LinMap t which equals the goal's LHS .hil contents)
  rw [hf]
  exact h_chain.symm

private lemma uncurry2Real_apply_eq_dualTensorHom_direct
    {σ : DEnv} {ε : NLCtx} {sA sB : Space}
    (h_fresh_g : Term.g_name ∉ ε)
    (h_fresh_a : Term.a_name ∉ ε) (h_fresh_b : Term.b_name ∉ ε)
    (h_ga : Term.g_name ≠ Term.a_name) (h_gb : Term.g_name ≠ Term.b_name)
    (h_ab : Term.a_name ≠ Term.b_name)
    (svA : SValid ε sA) (svB : SValid ε sB)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (t : (HSpace.tprod (HSpace.dual (denotSpace σ sA))
                       (HSpace.dual (denotSpace σ sB))).carrier)
    (a_val : (denotSpace σ sA).carrier)
    (b_val : (denotSpace σ sB).carrier) :
    ((denotTerm σ (Term.uncurry2Real sA sB)).asLinMap
        (HSpace.tprod (HSpace.dual (denotSpace σ sA)) (HSpace.dual (denotSpace σ sB)))
        (HSpace.dual (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))) t)
      (a_val ⊗ₜ[ℝ] b_val)
    = (dualTensorHom ℝ (denotSpace σ sA).carrier
        (HSpace.dual (denotSpace σ sB)).carrier t a_val) b_val := by
  have h := uncurry2Real_apply_eq_dualTensorHom h_fresh_g h_fresh_a h_fresh_b
    h_ga h_gb h_ab svA svB env_wf ctx_ε t a_val b_val
  -- h has the asLinFunctional wraps with denotSpace forms. Convert via change
  -- to HSpace.dual forms so the asLinFunctional_hil_dual rewrite can fire.
  change DVal.asLinFunctional (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))
      (DVal.hil ⟨HSpace.dual (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)),
        (denotTerm σ (Term.uncurry2Real sA sB)).asLinMap
          (HSpace.tprod (HSpace.dual (denotSpace σ sA)) (HSpace.dual (denotSpace σ sB)))
          (HSpace.dual (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB))) t⟩)
      (a_val ⊗ₜ[ℝ] b_val)
    = DVal.asLinFunctional (denotSpace σ sB)
        (DVal.hil ⟨HSpace.dual (denotSpace σ sB),
          dualTensorHom ℝ (denotSpace σ sA).carrier (HSpace.dual (denotSpace σ sB)).carrier
            t a_val⟩) b_val at h
  rw [asLinFunctional_hil_dual] at h
  rw [asLinFunctional_hil_dual] at h
  exact h

private lemma F_denoted_y00Fn_isLinear
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    IsLinearMap ℝ (fun y00 : (denotSpace σ s₀).carrier =>
      (denotTermAux σ [.hil ⟨denotSpace σ s₀, y00⟩]
        (.llam s₁
          (.tprod (.dual s₀) (.dual s₁))
          (.llam s₀ (.dual s₁)
            (.llam s₁ .real
              (.smul
                (Term.innerApp s₀ (.bvar 3) (.bvar 1))
                (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))).atSpace
        (denotSpace σ (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁))))) := by
  have h_body_lc : Term.lc (Term.openVar ("$y00" : Name)
      (.llam s₁ (.tprod (.dual s₀) (.dual s₁))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.bvar 3) (.bvar 1))
              (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
    exact (F_y00_body_hasType fresh.fresh_y00 fresh.fresh_y01 fresh.fresh_y10
      fresh.fresh_y11 sv₀ sv₁).lc
  have h_body_fv : ("$y00" : Name) ∉ Term.fv
      (.llam s₁ (.tprod (.dual s₀) (.dual s₁))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.bvar 3) (.bvar 1))
              (Term.innerApp s₁ (.bvar 2) (.bvar 0))))) : Term) := by
    have h_y00_s₀ : ("$y00" : Name) ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_y00
    have h_y00_s₁ : ("$y00" : Name) ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_y00
    simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
      or_false]
    intro h
    repeat first
      | exact h_y00_s₀ h | exact h_y00_s₁ h
      | (rcases h with h | h)
  have h_bridge : (fun y00 : (denotSpace σ s₀).carrier =>
      (denotTermAux σ [.hil ⟨denotSpace σ s₀, y00⟩]
        (.llam s₁ (.tprod (.dual s₀) (.dual s₁))
          (.llam s₀ (.dual s₁)
            (.llam s₁ .real
              (.smul
                (Term.innerApp s₀ (.bvar 3) (.bvar 1))
                (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))).atSpace
        (denotSpace σ (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁)))))
    = (fun y00 : (denotSpace σ s₀).carrier =>
      (denotTerm (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00⟩))
        (.llam s₁ (.tprod (.dual s₀) (.dual s₁))
          (.llam s₀ (.dual s₁)
            (.llam s₁ .real
              (.smul
                (Term.innerApp s₀ (.var "$y00") (.bvar 1))
                (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))).atSpace
        (denotSpace σ (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁))))) := by
    funext y00
    rw [← denotTerm_openVar_bind h_body_lc h_body_fv]
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁),
      Space.openRec_lc (SValid.lc (SValid.dual sv₁)),
      Space.openRec_lc (SValid.lc (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)))]
    norm_num [Term.openRec]
  rw [h_bridge]
  exact denot_llam_body_isLinear (Δ := ∅) Finmap.notMem_empty fresh.fresh_y00 sv₀
    (SValid.tprod (SValid.dual sv₁) (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)))
    (F_y00_body_hasType fresh.fresh_y00 fresh.fresh_y01 fresh.fresh_y10 fresh.fresh_y11
      sv₀ sv₁)
    ctx_ε env_wf

private lemma F_denoted_y01Fn_isLinear
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (y00_val : (denotSpace σ s₀).carrier) :
    let σ_y00 := σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)
    IsLinearMap ℝ (fun y01 : (denotSpace σ_y00 s₁).carrier =>
      (denotTermAux σ_y00 [.hil ⟨denotSpace σ_y00 s₁, y01⟩]
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.bvar 2) (.bvar 0)))))).atSpace
        (denotSpace σ_y00 (.tprod (.dual s₀) (.dual s₁)))) := by
  obtain ⟨h_00_01, _, _, _, _, _⟩ := Term.y_pairwise_distinct
  intro σ_y00
  -- Use the FV-transport helpers — replaces ~70 LOC of inline boilerplate.
  have ctx_y00 := ctx_ε.extend_lin fresh.fresh_y00 sv₀
  have wf_y00 := env_wf.extend_lin ctx_ε fresh.fresh_y00 sv₀ y00_val
  have h_y01_notin : ("$y01" : Name) ∉ (Finmap.insert ("$y00" : Name) s₀ ∅ : LCtx) := by
    rw [Finmap.mem_insert]
    push_neg
    exact ⟨h_00_01.symm, Finmap.notMem_empty⟩
  have h_y00_s₀ : ("$y00" : Name) ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_y00
  have h_y00_s₁ : ("$y00" : Name) ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_y00
  have h_y01_s₀ : ("$y01" : Name) ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_y01
  have h_y01_s₁ : ("$y01" : Name) ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_y01
  have h_body_lc : Term.lc (Term.openVar ("$y01" : Name)
      (.llam s₀ (.dual s₁)
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.bvar 2) (.bvar 0)))))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
    exact (F_y01_body_hasType fresh.fresh_y00 fresh.fresh_y01 fresh.fresh_y10
      fresh.fresh_y11 sv₀ sv₁).lc
  have h_body_fv : ("$y01" : Name) ∉ Term.fv
      (.llam s₀ (.dual s₁)
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.bvar 2) (.bvar 0)))) : Term) := by
    simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
      or_false, Finset.mem_singleton]
    intro h
    repeat first
      | exact h_y01_s₀ h | exact h_y01_s₁ h | exact h_00_01.symm h
      | (rcases h with h | h)
  have h_bridge : (fun y01 : (denotSpace σ_y00 s₁).carrier =>
      (denotTermAux σ_y00 [.hil ⟨denotSpace σ_y00 s₁, y01⟩]
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.bvar 2) (.bvar 0)))))).atSpace
        (denotSpace σ_y00 (.tprod (.dual s₀) (.dual s₁))))
    = (fun y01 : (denotSpace σ_y00 s₁).carrier =>
      (denotTerm (σ_y00.bind ("$y01" : Name) (.hil ⟨denotSpace σ_y00 s₁, y01⟩))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0)))))).atSpace
        (denotSpace σ_y00 (.tprod (.dual s₀) (.dual s₁)))) := by
    funext y01
    rw [← denotTerm_openVar_bind h_body_lc h_body_fv]
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
    norm_num [Term.openRec]
  rw [h_bridge]
  exact denot_llam_body_isLinear h_y01_notin fresh.fresh_y01
    sv₁ (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁))
    (F_y01_body_hasType fresh.fresh_y00 fresh.fresh_y01 fresh.fresh_y10 fresh.fresh_y11
      sv₀ sv₁)
    ctx_y00 wf_y00

private lemma F_y01_eval
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (y00_val : (denotSpace σ s₀).carrier)
    (y01_val : (denotSpace
      (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)) s₁).carrier) :
    DVal.asLinMap
      (denotSpace (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)) s₁)
      (denotSpace (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩))
        (.tprod (.dual s₀) (.dual s₁)))
      (denotTerm (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩))
        (.llam s₁
          (.tprod (.dual s₀) (.dual s₁))
          (.llam s₀ (.dual s₁)
            (.llam s₁ .real
              (.smul
                (Term.innerApp s₀ (.var "$y00") (.bvar 1))
                (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))) y01_val =
    (denotTermAux (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩))
      [.hil ⟨denotSpace (σ.bind ("$y00" : Name)
          (.hil ⟨denotSpace σ s₀, y00_val⟩)) s₁, y01_val⟩]
      (.llam s₀ (.dual s₁)
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.bvar 2) (.bvar 0)))))).atSpace
      (denotSpace (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩))
        (.tprod (.dual s₀) (.dual s₁))) := by
  rw [denotTerm_llam_non_real (by intro h; cases h)]
  rw [asLinMap_llamTensorDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap
    (F_denoted_y01Fn_isLinear fresh sv₀ sv₁ env_wf ctx_ε y00_val) y01_val

private lemma F_denoted_y10Fn_isLinear
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (y00_val : (denotSpace σ s₀).carrier)
    (y01_val : (denotSpace σ s₁).carrier) :
    let σ_y00 := σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)
    let σ_y00_y01 := σ_y00.bind ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)
    IsLinearMap ℝ (fun y10 : (denotSpace σ_y00_y01 s₀).carrier =>
      (denotTermAux σ_y00_y01 [.hil ⟨denotSpace σ_y00_y01 s₀, y10⟩]
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.var "$y01") (.bvar 0))))).atSpace
        (denotSpace σ_y00_y01 (.dual s₁))) := by
  obtain ⟨h_00_01, h_00_10, _, h_01_10, _, _⟩ := Term.y_pairwise_distinct
  intro σ_y00 σ_y00_y01
  have h_y00_not_fv_s₁ : ("$y00" : Name) ∉ Space.fv s₁ :=
    sv₁.notMem_fv_of_notMem_ε fresh.fresh_y00
  -- Use FV-transport helpers: chain extend_lin (1st), then extend_lin_at (2nd)
  -- with the y01_val transport via denotSpace_agree.
  have ctx_y00 := ctx_ε.extend_lin fresh.fresh_y00 sv₀
  have wf_y00 := env_wf.extend_lin ctx_ε fresh.fresh_y00 sv₀ y00_val
  have h_y01_notin : ("$y01" : Name) ∉ (Finmap.insert ("$y00" : Name) s₀ ∅ : LCtx) := by
    rw [Finmap.mem_insert]; push_neg; exact ⟨h_00_01.symm, Finmap.notMem_empty⟩
  have ctx_y0001 := ctx_y00.extend_lin fresh.fresh_y01 sv₁
  have h_denot_s₁_y00 :
      denotSpace σ s₁ = denotSpace (σ.bind ("$y00" : Name)
        (.hil ⟨denotSpace σ s₀, y00_val⟩)) s₁ :=
    (denotSpace_agree _
      (DEnv.AgreeOn.bind_left_of_not_mem h_y00_not_fv_s₁)).symm
  have wf_y0001 := wf_y00.extend_lin_at ctx_y00 fresh.fresh_y01 sv₁
    h_denot_s₁_y00 y01_val
  have h_y10_notin : ("$y10" : Name) ∉ (Finmap.insert ("$y01" : Name) s₁
        (Finmap.insert ("$y00" : Name) s₀ ∅) : LCtx) := by
    rw [Finmap.mem_insert]; push_neg
    refine ⟨h_01_10.symm, ?_⟩
    rw [Finmap.mem_insert]; push_neg
    exact ⟨h_00_10.symm, Finmap.notMem_empty⟩
  have h_y10_s₀ : ("$y10" : Name) ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_y10
  have h_y10_s₁ : ("$y10" : Name) ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_y10
  have h_body_lc : Term.lc (Term.openVar ("$y10" : Name)
      (.llam s₁ .real
        (.smul
          (Term.innerApp s₀ (.var "$y00") (.bvar 1))
          (Term.innerApp s₁ (.var "$y01") (.bvar 0))))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
    exact (F_y10_body_hasType fresh.fresh_y11 sv₀ sv₁).lc
  have h_body_fv : ("$y10" : Name) ∉ Term.fv
      (.llam s₁ .real
        (.smul
          (Term.innerApp s₀ (.var "$y00") (.bvar 1))
          (Term.innerApp s₁ (.var "$y01") (.bvar 0))) : Term) := by
    simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
      or_false, Finset.mem_singleton]
    intro h
    repeat first
      | exact h_y10_s₀ h | exact h_y10_s₁ h | exact h_00_10.symm h | exact h_01_10.symm h
      | (rcases h with h | h)
  have h_bridge : (fun y10 : (denotSpace σ_y00_y01 s₀).carrier =>
      (denotTermAux σ_y00_y01 [.hil ⟨denotSpace σ_y00_y01 s₀, y10⟩]
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.var "$y01") (.bvar 0))))).atSpace
        (denotSpace σ_y00_y01 (.dual s₁)))
    = (fun y10 : (denotSpace σ_y00_y01 s₀).carrier =>
      (denotTerm (σ_y00_y01.bind ("$y10" : Name) (.hil ⟨denotSpace σ_y00_y01 s₀, y10⟩))
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
            (Term.innerApp s₁ (.var "$y01") (.bvar 0))))).atSpace
        (denotSpace σ_y00_y01 (.dual s₁))) := by
    funext y10
    rw [← denotTerm_openVar_bind h_body_lc h_body_fv]
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
    norm_num [Term.openRec]
  rw [h_bridge]
  exact denot_llam_body_isLinear h_y10_notin fresh.fresh_y10
    sv₀ (SValid.dual sv₁)
    (F_y10_body_hasType fresh.fresh_y11 sv₀ sv₁)
    ctx_y0001 wf_y0001

private lemma F_y10_eval
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (y00_val : (denotSpace σ s₀).carrier)
    (y01_val : (denotSpace σ s₁).carrier)
    (y10_val : (denotSpace
      ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
        ("$y01" : Name)
        (.hil ⟨denotSpace σ s₁, y01_val⟩)) s₀).carrier) :
    DVal.asLinMap
      (denotSpace ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
        ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)) s₀)
      (HSpace.dual (denotSpace ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
        ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)) s₁))
      (denotTerm ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
          ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0)))))) y10_val =
    (denotTermAux (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
          ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)))
        [.hil ⟨denotSpace ((σ.bind ("$y00" : Name)
            (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
              ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)) s₀, y10_val⟩]
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.var "$y01") (.bvar 0))))).atSpace
      (HSpace.dual (denotSpace ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
        ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)) s₁)) := by
  show DVal.asLinMap _
      (denotSpace ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
        ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)) (.dual s₁)) _ y10_val
    = (denotTermAux _ _ _).atSpace
      (denotSpace ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
        ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)) (.dual s₁))
  rw [denotTerm_llam_non_real (by intro h; cases h)]
  rw [asLinMap_llamTensorDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap
    (F_denoted_y10Fn_isLinear fresh sv₀ sv₁ env_wf ctx_ε y00_val y01_val) y10_val

private lemma F_denoted_y11Fn_isLinear
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (y00_val : (denotSpace σ s₀).carrier)
    (y01_val : (denotSpace σ s₁).carrier)
    (y10_val : (denotSpace σ s₀).carrier) :
    let σ_y00 := σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)
    let σ_y00_y01 := σ_y00.bind ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)
    let σ_full := σ_y00_y01.bind ("$y10" : Name) (.hil ⟨denotSpace σ s₀, y10_val⟩)
    IsLinearMap ℝ (fun y11 : (denotSpace σ_full s₁).carrier =>
      (denotTermAux σ_full [.hil ⟨denotSpace σ_full s₁, y11⟩]
        (.smul
          (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
          (Term.innerApp s₁ (.var "$y01") (.bvar 0)))).atSpace
        (denotSpace σ_full .real)) := by
  obtain ⟨h_00_01, h_00_10, h_00_11, h_01_10, h_01_11, h_10_11⟩ :=
    Term.y_pairwise_distinct
  intro σ_y00 σ_y00_y01 σ_full
  have h_y00_not_fv_s₁ : ("$y00" : Name) ∉ Space.fv s₁ :=
    sv₁.notMem_fv_of_notMem_ε fresh.fresh_y00
  have h_y01_not_fv_s₀ : ("$y01" : Name) ∉ Space.fv s₀ :=
    sv₀.notMem_fv_of_notMem_ε fresh.fresh_y01
  have h_y10_not_fv_s₀ : ("$y10" : Name) ∉ Space.fv s₀ :=
    sv₀.notMem_fv_of_notMem_ε fresh.fresh_y10
  -- Use FV-transport helpers: extend_lin (1st), extend_lin_at (2nd, 3rd) with
  -- transports for y01_val, y10_val from σ-frame to current σ-frame.
  have ctx_y00 := ctx_ε.extend_lin fresh.fresh_y00 sv₀
  have wf_y00 := env_wf.extend_lin ctx_ε fresh.fresh_y00 sv₀ y00_val
  have h_y01_notin : ("$y01" : Name) ∉ (Finmap.insert ("$y00" : Name) s₀ ∅ : LCtx) := by
    rw [Finmap.mem_insert]; push_neg; exact ⟨h_00_01.symm, Finmap.notMem_empty⟩
  have h_denot_s₁_y00 :
      denotSpace σ s₁ = denotSpace (σ.bind ("$y00" : Name)
        (.hil ⟨denotSpace σ s₀, y00_val⟩)) s₁ :=
    (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y00_not_fv_s₁)).symm
  have ctx_y0001 := ctx_y00.extend_lin fresh.fresh_y01 sv₁
  have wf_y0001 := wf_y00.extend_lin_at ctx_y00 fresh.fresh_y01 sv₁
    h_denot_s₁_y00 y01_val
  have h_y10_notin : ("$y10" : Name) ∉ (Finmap.insert ("$y01" : Name) s₁
        (Finmap.insert ("$y00" : Name) s₀ ∅) : LCtx) := by
    rw [Finmap.mem_insert]; push_neg
    refine ⟨h_01_10.symm, ?_⟩
    rw [Finmap.mem_insert]; push_neg
    exact ⟨h_00_10.symm, Finmap.notMem_empty⟩
  have h_y00_not_fv_s₀ : ("$y00" : Name) ∉ Space.fv s₀ :=
    sv₀.notMem_fv_of_notMem_ε fresh.fresh_y00
  have h_denot_s₀_y01 :
      denotSpace σ s₀ = denotSpace
        ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
          ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)) s₀ :=
    ((denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y01_not_fv_s₀)).trans
      (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y00_not_fv_s₀))).symm
  have ctx_full := ctx_y0001.extend_lin fresh.fresh_y10 sv₀
  have wf_full := wf_y0001.extend_lin_at ctx_y0001 fresh.fresh_y10 sv₀
    h_denot_s₀_y01 y10_val
  have h_y11_notin : ("$y11" : Name) ∉ (Finmap.insert ("$y10" : Name) s₀
        (Finmap.insert ("$y01" : Name) s₁
          (Finmap.insert ("$y00" : Name) s₀ ∅)) : LCtx) := by
    rw [Finmap.mem_insert]; push_neg
    refine ⟨h_10_11.symm, ?_⟩
    rw [Finmap.mem_insert]; push_neg
    refine ⟨h_01_11.symm, ?_⟩
    rw [Finmap.mem_insert]; push_neg
    exact ⟨h_00_11.symm, Finmap.notMem_empty⟩
  have h_y11_s₁ : ("$y11" : Name) ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_y11
  have h_y11_s₀ : ("$y11" : Name) ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_y11
  have h_body_lc : Term.lc (Term.openVar ("$y11" : Name)
      (.smul
        (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
        (Term.innerApp s₁ (.var "$y01") (.bvar 0)))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
    exact (F_smul_body_hasType sv₀ sv₁).lc
  have h_body_fv : ("$y11" : Name) ∉ Term.fv
      (.smul
        (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
        (Term.innerApp s₁ (.var "$y01") (.bvar 0)) : Term) := by
    simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
      or_false, Finset.mem_singleton]
    intro h
    repeat first
      | exact h_y11_s₁ h | exact h_y11_s₀ h
      | exact h_00_11.symm h | exact h_01_11.symm h
      | exact h_10_11.symm h
      | (rcases h with h | h)
  have h_bridge : (fun y11 : (denotSpace σ_full s₁).carrier =>
      (denotTermAux σ_full [.hil ⟨denotSpace σ_full s₁, y11⟩]
        (.smul
          (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
          (Term.innerApp s₁ (.var "$y01") (.bvar 0)))).atSpace
        (denotSpace σ_full .real))
    = (fun y11 : (denotSpace σ_full s₁).carrier =>
      (denotTerm (σ_full.bind ("$y11" : Name) (.hil ⟨denotSpace σ_full s₁, y11⟩))
        (.smul
          (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
          (Term.innerApp s₁ (.var "$y01") (.var "$y11")))).atSpace
        (denotSpace σ_full .real)) := by
    funext y11
    rw [← denotTerm_openVar_bind h_body_lc h_body_fv]
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
    norm_num [Term.openRec]
  rw [h_bridge]
  exact denot_llam_body_isLinear h_y11_notin fresh.fresh_y11
    sv₁ SValid.real
    (F_smul_body_hasType sv₀ sv₁)
    ctx_full wf_full

private lemma F_y11_eval
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (y00_val : (denotSpace σ s₀).carrier)
    (y01_val : (denotSpace σ s₁).carrier)
    (y10_val : (denotSpace σ s₀).carrier)
    (y11_val : (denotSpace
      (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
        ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)).bind
          ("$y10" : Name) (.hil ⟨denotSpace σ s₀, y10_val⟩)) s₁).carrier) :
    ((denotTerm (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
          ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)).bind
            ("$y10" : Name) (.hil ⟨denotSpace σ s₀, y10_val⟩))
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
            (Term.innerApp s₁ (.var "$y01") (.bvar 0))))).atSpace
        (HSpace.dual (denotSpace (((σ.bind ("$y00" : Name)
            (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
              ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)).bind
                ("$y10" : Name) (.hil ⟨denotSpace σ s₀, y10_val⟩)) s₁))) y11_val =
    (denotTermAux (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
          ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)).bind
            ("$y10" : Name) (.hil ⟨denotSpace σ s₀, y10_val⟩))
      [.hil ⟨denotSpace (((σ.bind ("$y00" : Name)
          (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
            ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)).bind
              ("$y10" : Name) (.hil ⟨denotSpace σ s₀, y10_val⟩)) s₁,
        y11_val⟩]
      (.smul
        (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
        (Term.innerApp s₁ (.var "$y01") (.bvar 0)))).atSpace HSpace.real := by
  rw [denotTerm_llam_real]
  rw [atSpace_llamRealDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap
    (F_denoted_y11Fn_isLinear fresh sv₀ sv₁ env_wf ctx_ε y00_val y01_val y10_val) y11_val

private lemma F_innermost_smul_eval
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (y00_val y10_val : (denotSpace σ s₀).carrier)
    (y01_val y11_val : (denotSpace σ s₁).carrier) :
    let σ_full := (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
        ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)).bind
          ("$y10" : Name) (.hil ⟨denotSpace σ s₀, y10_val⟩)).bind
            ("$y11" : Name) (.hil ⟨denotSpace σ s₁, y11_val⟩)
    (denotTerm σ_full
      (.smul
        (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
        (Term.innerApp s₁ (.var "$y01") (.var "$y11")))).atSpace HSpace.real
      = (denotSpace σ s₀).innerProduct y00_val y10_val
        * (denotSpace σ s₁).innerProduct y01_val y11_val := by
  obtain ⟨h_00_01, h_00_10, h_00_11, h_01_10, h_01_11, h_10_11⟩ :=
    Term.y_pairwise_distinct
  have h_y00_not_fv_s₀ : ("$y00" : Name) ∉ Space.fv s₀ :=
    sv₀.notMem_fv_of_notMem_ε fresh.fresh_y00
  have h_y00_not_fv_s₁ : ("$y00" : Name) ∉ Space.fv s₁ :=
    sv₁.notMem_fv_of_notMem_ε fresh.fresh_y00
  have h_y01_not_fv_s₀ : ("$y01" : Name) ∉ Space.fv s₀ :=
    sv₀.notMem_fv_of_notMem_ε fresh.fresh_y01
  have h_y01_not_fv_s₁ : ("$y01" : Name) ∉ Space.fv s₁ :=
    sv₁.notMem_fv_of_notMem_ε fresh.fresh_y01
  have h_y10_not_fv_s₀ : ("$y10" : Name) ∉ Space.fv s₀ :=
    sv₀.notMem_fv_of_notMem_ε fresh.fresh_y10
  have h_y10_not_fv_s₁ : ("$y10" : Name) ∉ Space.fv s₁ :=
    sv₁.notMem_fv_of_notMem_ε fresh.fresh_y10
  have h_y11_not_fv_s₀ : ("$y11" : Name) ∉ Space.fv s₀ :=
    sv₀.notMem_fv_of_notMem_ε fresh.fresh_y11
  have h_y11_not_fv_s₁ : ("$y11" : Name) ∉ Space.fv s₁ :=
    sv₁.notMem_fv_of_notMem_ε fresh.fresh_y11
  set σ_full : DEnv := (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, y00_val⟩)).bind
        ("$y01" : Name) (.hil ⟨denotSpace σ s₁, y01_val⟩)).bind
          ("$y10" : Name) (.hil ⟨denotSpace σ s₀, y10_val⟩)).bind
            ("$y11" : Name) (.hil ⟨denotSpace σ s₁, y11_val⟩) with hσ_full
  -- FV-irrelevance for spaces sᵢ at σ_full.
  have h_dV₀ : denotSpace σ_full s₀ = denotSpace σ s₀ :=
    ((((denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_y11_not_fv_s₀)).trans
        (denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_y10_not_fv_s₀))).trans
      (denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_y01_not_fv_s₀))).trans
      (denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_y00_not_fv_s₀)))
  have h_dV₁ : denotSpace σ_full s₁ = denotSpace σ s₁ :=
    ((((denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_y11_not_fv_s₁)).trans
        (denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_y10_not_fv_s₁))).trans
      (denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_y01_not_fv_s₁))).trans
      (denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_y00_not_fv_s₁)))
  -- Var lookups at σ_full.
  have h_var_y00 : denotTerm σ_full (.var "$y00") = .hil ⟨denotSpace σ s₀, y00_val⟩ := by
    show (σ_full.vars.lookup "$y00").getD DVal.default = _
    simp [σ_full, DEnv.bind,
          Finmap.lookup_insert_of_ne _ h_00_11,
          Finmap.lookup_insert_of_ne _ h_00_10,
          Finmap.lookup_insert_of_ne _ h_00_01,
          Finmap.lookup_insert]
  have h_var_y01 : denotTerm σ_full (.var "$y01") = .hil ⟨denotSpace σ s₁, y01_val⟩ := by
    show (σ_full.vars.lookup "$y01").getD DVal.default = _
    simp [σ_full, DEnv.bind,
          Finmap.lookup_insert_of_ne _ h_01_11,
          Finmap.lookup_insert_of_ne _ h_01_10,
          Finmap.lookup_insert]
  have h_var_y10 : denotTerm σ_full (.var "$y10") = .hil ⟨denotSpace σ s₀, y10_val⟩ := by
    show (σ_full.vars.lookup "$y10").getD DVal.default = _
    simp [σ_full, DEnv.bind,
          Finmap.lookup_insert_of_ne _ h_10_11,
          Finmap.lookup_insert]
  have h_var_y11 : denotTerm σ_full (.var "$y11") = .hil ⟨denotSpace σ s₁, y11_val⟩ := by
    show (σ_full.vars.lookup "$y11").getD DVal.default = _
    simp [σ_full, DEnv.bind, Finmap.lookup_insert]
  -- inner s₀ denotation at σ_full.
  have h_inner_s₀ : denotTerm σ_full (.inner s₀)
      = HSpace.innerTensor (denotSpace σ s₀) (denotSpace σ s₀).innerProduct := by
    show (denotSpace σ_full s₀).innerTensor (denotSpace σ_full s₀).innerProduct = _
    rw [h_dV₀]
  have h_inner_s₁ : denotTerm σ_full (.inner s₁)
      = HSpace.innerTensor (denotSpace σ s₁) (denotSpace σ s₁).innerProduct := by
    show (denotSpace σ_full s₁).innerTensor (denotSpace σ_full s₁).innerProduct = _
    rw [h_dV₁]
  -- innerApp s₀ ($y00) ($y10) at σ_full = .hil ⟨HSpace.real, V₀.IP y00 y10⟩.
  have h_innerApp_0 : denotTerm σ_full
      (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
      = .hil ⟨HSpace.real, (denotSpace σ s₀).innerProduct y00_val y10_val⟩ := by
    show denotTerm σ_full
        (.appI s₀
          (.appL s₀ (.dual s₀) (.inner s₀) (.var "$y00"))
          (.var "$y10")) = _
    show DVal.hil ⟨HSpace.real,
          DVal.asLinFunctional (denotSpace σ_full s₀)
            (denotTerm σ_full (.appL s₀ (.dual s₀) (.inner s₀) (.var "$y00")))
          (DVal.atSpace (denotSpace σ_full s₀)
            (denotTerm σ_full (.var "$y10")))⟩ = _
    have h_appL : denotTerm σ_full (.appL s₀ (.dual s₀) (.inner s₀) (.var "$y00"))
        = .hil ⟨HSpace.dual (denotSpace σ s₀), (denotSpace σ s₀).innerProduct y00_val⟩ := by
      show DVal.hil ⟨denotSpace σ_full (.dual s₀),
            ((denotTerm σ_full (.inner s₀)).asLinMap
              (denotSpace σ_full s₀) (denotSpace σ_full (.dual s₀)))
            ((denotTerm σ_full (.var "$y00")).atSpace (denotSpace σ_full s₀))⟩ = _
      have h_dual : denotSpace σ_full (.dual s₀) = HSpace.dual (denotSpace σ s₀) := by
        show HSpace.dual (denotSpace σ_full s₀) = _; rw [h_dV₀]
      rw [h_dV₀, h_dual, h_inner_s₀, asLinMap_innerTensor, h_var_y00, atSpace_hil_self]
    rw [h_dV₀, h_appL, asLinFunctional_hil_dual, h_var_y10, atSpace_hil_self]
  have h_innerApp_1 : denotTerm σ_full
      (Term.innerApp s₁ (.var "$y01") (.var "$y11"))
      = .hil ⟨HSpace.real, (denotSpace σ s₁).innerProduct y01_val y11_val⟩ := by
    show denotTerm σ_full
        (.appI s₁
          (.appL s₁ (.dual s₁) (.inner s₁) (.var "$y01"))
          (.var "$y11")) = _
    show DVal.hil ⟨HSpace.real,
          DVal.asLinFunctional (denotSpace σ_full s₁)
            (denotTerm σ_full (.appL s₁ (.dual s₁) (.inner s₁) (.var "$y01")))
          (DVal.atSpace (denotSpace σ_full s₁)
            (denotTerm σ_full (.var "$y11")))⟩ = _
    have h_appL : denotTerm σ_full (.appL s₁ (.dual s₁) (.inner s₁) (.var "$y01"))
        = .hil ⟨HSpace.dual (denotSpace σ s₁), (denotSpace σ s₁).innerProduct y01_val⟩ := by
      show DVal.hil ⟨denotSpace σ_full (.dual s₁),
            ((denotTerm σ_full (.inner s₁)).asLinMap
              (denotSpace σ_full s₁) (denotSpace σ_full (.dual s₁)))
            ((denotTerm σ_full (.var "$y01")).atSpace (denotSpace σ_full s₁))⟩ = _
      have h_dual : denotSpace σ_full (.dual s₁) = HSpace.dual (denotSpace σ s₁) := by
        show HSpace.dual (denotSpace σ_full s₁) = _; rw [h_dV₁]
      rw [h_dV₁, h_dual, h_inner_s₁, asLinMap_innerTensor, h_var_y01, atSpace_hil_self]
    rw [h_dV₁, h_appL, asLinFunctional_hil_dual, h_var_y11, atSpace_hil_self]

  show DVal.atSpace HSpace.real (denotTerm σ_full
        ((Term.innerApp s₀ (Term.var "$y00") (Term.var "$y10")).smul
          (Term.innerApp s₁ (Term.var "$y01") (Term.var "$y11")))) = _
  rw [denotTerm_smul_real σ_full _ _ _ h_innerApp_1, atSpace_hil_self, h_innerApp_0]
  show (DVal.hil ⟨HSpace.real, (denotSpace σ s₀).innerProduct y00_val y10_val⟩).asReal
        * (denotSpace σ s₁).innerProduct y01_val y11_val = _
  rw [DVal.asReal_hil_real]

private lemma F_y00_eval
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (y00_val : (denotSpace σ s₀).carrier) :
    DVal.asLinMap (denotSpace σ s₀)
      (denotSpace σ (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁))))
      (denotTerm σ
        (.llam s₀
          (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁)))
          (.llam s₁
            (.tprod (.dual s₀) (.dual s₁))
            (.llam s₀ (.dual s₁)
              (.llam s₁ .real
                (.smul
                  (Term.innerApp s₀ (.bvar 3) (.bvar 1))
                  (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))))
        y00_val =
    (denotTermAux σ [.hil ⟨denotSpace σ s₀, y00_val⟩]
      (.llam s₁
        (.tprod (.dual s₀) (.dual s₁))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.bvar 3) (.bvar 1))
              (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))).atSpace
      (denotSpace σ (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁)))) := by
  rw [denotTerm_llam_non_real (by intro h; cases h)]
  rw [asLinMap_llamTensorDVal]
  exact LinearMap.ofFun_apply_of_isLinearMap
    (F_denoted_y00Fn_isLinear fresh sv₀ sv₁ env_wf ctx_ε) y00_val

private lemma step1_asLinMap_at_aXb_eval
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε)
    (a : (denotSpace σ s₀).carrier) (b : (denotSpace σ s₁).carrier) :
    ((denotTerm σ
      (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
        (tprod_F s₀ s₁))).asLinMap
        (HSpace.tprod (denotSpace σ s₀) (denotSpace σ s₁))
        (HSpace.tprod (HSpace.dual (denotSpace σ s₀))
          (HSpace.dual (denotSpace σ s₁))))
      (a ⊗ₜ[ℝ] b)
    = (denotTerm
        ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
          ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0))))) ).atSpace
      (HSpace.tprod (HSpace.dual (denotSpace σ s₀))
        (HSpace.dual (denotSpace σ s₁))) := by
  have h_ga : Term.g_name ≠ Term.a_name := by decide
  have h_gb : Term.g_name ≠ Term.b_name := by decide
  have h_ab : Term.a_name ≠ Term.b_name := by decide
  have h_τ_ne_real : (Space.tprod (.dual s₀) (.dual s₁)) ≠ .real := by intro h; cases h
  have d_τ : SValid ε (.tprod (.dual s₀) (.dual s₁)) :=
    SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)
  set step1_term : Term :=
    Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
      (tprod_F s₀ s₁) with hstep1_def
  -- Step A: step1.asLinMap → dualTensorHom.
  have h_step1_match : (denotTerm σ step1_term).matchesShape
      (.hil (HSpace.tprod
        (HSpace.dual (HSpace.tprod (denotSpace σ s₀) (denotSpace σ s₁)))
        (HSpace.tprod (HSpace.dual (denotSpace σ s₀)) (HSpace.dual (denotSpace σ s₁))))) := by
    rw [hstep1_def]
    unfold Term.applyUncurry2NonReal
    rw [denotTerm_appL]
    rfl
  rw [DVal.asLinMap_eq_of_matchesShape h_step1_match]
  -- Bridge to chain_app_eq's denotSpace form via change.
  change (dualTensorHom ℝ (HSpace.tprod (denotSpace σ s₀) (denotSpace σ s₁)).carrier
      (denotSpace σ (.tprod (.dual s₀) (.dual s₁))).carrier
      ((denotTerm σ step1_term).atSpace
        (HSpace.tprod (HSpace.dual (HSpace.tprod (denotSpace σ s₀) (denotSpace σ s₁)))
          (denotSpace σ (.tprod (.dual s₀) (.dual s₁))))))
      (a ⊗ₜ[ℝ] b)
    = (denotTerm
        ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
          ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0)))))).atSpace
      (denotSpace σ (.tprod (.dual s₀) (.dual s₁)))
  -- Step B: chain_app_eq backwards.
  rw [← curry2NonReal_chain_app_eq fresh.fresh_g fresh.fresh_a fresh.fresh_b
        h_ga h_gb h_ab h_τ_ne_real sv₀ sv₁ d_τ env_wf ctx_ε
        ((denotTerm σ step1_term).atSpace
          (HSpace.tprod (HSpace.dual (HSpace.tprod (denotSpace σ s₀) (denotSpace σ s₁)))
            (denotSpace σ (.tprod (.dual s₀) (.dual s₁)))))
        a b]
  -- Step C: step1's tensor = uncurry of F's tensor.
  have h_step1_tensor_eq :
      (denotTerm σ step1_term).atSpace
        (HSpace.tprod (HSpace.dual (HSpace.tprod (denotSpace σ s₀) (denotSpace σ s₁)))
          (denotSpace σ (.tprod (.dual s₀) (.dual s₁))))
      = ((denotTerm σ (Term.uncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁)))).asLinMap
          (denotSpace σ (.tprod (.dual s₀) (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁)))))
          (denotSpace σ (.tprod (.dual (.tprod s₀ s₁)) (.tprod (.dual s₀) (.dual s₁)))))
        ((denotTerm σ
          (tprod_F s₀ s₁)).atSpace
          (denotSpace σ (.tprod (.dual s₀) (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁)))))) := by
    rw [hstep1_def]
    unfold Term.applyUncurry2NonReal
    rw [denotTerm_appL]
    change DVal.atSpace
        (denotSpace σ ((s₀.tprod s₁).dual.tprod (s₀.dual.tprod s₁.dual)))
        (DVal.hil ⟨denotSpace σ ((s₀.tprod s₁).dual.tprod (s₀.dual.tprod s₁.dual)), _⟩) = _
    rw [atSpace_hil_self]
  rw [h_step1_tensor_eq]
  -- Step D: curry2NonReal of uncurry2NonReal = id.
  rw [curry2NonReal_uncurry2NonReal_id fresh.fresh_g fresh.fresh_a fresh.fresh_b
        h_ga h_gb h_ab h_τ_ne_real sv₀ sv₁ d_τ env_wf ctx_ε]
  -- Step E: dualTensorHom V₀ V_curried_mid (F.atSpace) a → F.asLinMap V₀ V_curried_mid a.
  change (dualTensorHom ℝ (denotSpace σ s₁).carrier (denotSpace σ (s₀.dual.tprod s₁.dual)).carrier
      ((dualTensorHom ℝ (denotSpace σ s₀).carrier
            (denotSpace σ (s₁.dual.tprod (s₀.dual.tprod s₁.dual))).carrier)
        (DVal.atSpace ((denotSpace σ s₀).dual.tprod
            (denotSpace σ (s₁.dual.tprod (s₀.dual.tprod s₁.dual))))
          (denotTerm σ
            (tprod_F s₀ s₁)))
        a)) b
    = _
  have h_F_match : (denotTerm σ
      (tprod_F s₀ s₁)).matchesShape
      (.hil (HSpace.tprod (HSpace.dual (denotSpace σ s₀))
        (denotSpace σ (.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁)))))) := by
    rw [denotTerm_llam_non_real (by intro h; cases h)]
    rfl
  rw [← DVal.asLinMap_eq_of_matchesShape h_F_match]
  -- Step F: F.asLinMap V₀ V_y00_body a → (denot σ_y00 F_y00_body).atSpace V_y00_body.
  rw [F_y00_eval fresh sv₀ sv₁ env_wf ctx_ε a]
  -- Bridge F_y00_eval's denotTermAux output back to a denotTerm σ_y00 (.var-form) body.
  have h_y00b_lc : Term.lc (Term.openVar ("$y00" : Name)
      (.llam s₁ (.tprod (.dual s₀) (.dual s₁))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.bvar 3) (.bvar 1))
              (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
    exact (F_y00_body_hasType fresh.fresh_y00 fresh.fresh_y01 fresh.fresh_y10
      fresh.fresh_y11 sv₀ sv₁).lc
  have h_y00b_fv : ("$y00" : Name) ∉ Term.fv
      (.llam s₁ (.tprod (.dual s₀) (.dual s₁))
        (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.bvar 3) (.bvar 1))
              (Term.innerApp s₁ (.bvar 2) (.bvar 0))))) : Term) := by
    have h0 : ("$y00" : Name) ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_y00
    have h1 : ("$y00" : Name) ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_y00
    simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
      or_false]
    intro h
    repeat first
      | exact h0 h | exact h1 h
      | (rcases h with h | h)
  rw [← denotTerm_openVar_bind h_y00b_lc h_y00b_fv]
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  norm_num [Term.openRec]
  -- Step G: dualTensorHom V₁ V_τ ((denot σ_y00 F_y00_body).atSpace V_curried_mid) b
  --       → (denot σ_y00 F_y00_body).asLinMap V₁ V_τ b
  have h_y00_fv_s₀ : ("$y00" : Name) ∉ Space.fv s₀ :=
    sv₀.notMem_fv_of_notMem_ε fresh.fresh_y00
  have h_y00_fv_s₁ : ("$y00" : Name) ∉ Space.fv s₁ :=
    sv₁.notMem_fv_of_notMem_ε fresh.fresh_y00
  have h_dsA_σ_y00 : denotSpace (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)) s₀
      = denotSpace σ s₀ :=
    denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y00_fv_s₀)
  have h_dsB_σ_y00 : denotSpace (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)) s₁
      = denotSpace σ s₁ :=
    denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y00_fv_s₁)
  have h_F_y00_body_match :
      (denotTerm (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩))
        (.llam s₁
          (.tprod (.dual s₀) (.dual s₁))
          (.llam s₀ (.dual s₁)
            (.llam s₁ .real
              (.smul
                (Term.innerApp s₀ (.var "$y00") (.bvar 1))
                (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))).matchesShape
      (.hil (HSpace.tprod (HSpace.dual (denotSpace σ s₁))
        (denotSpace σ (.tprod (.dual s₀) (.dual s₁))))) := by
    rw [denotTerm_llam_non_real (by intro h; cases h)]
    show HType.hil (HSpace.tprod
        (HSpace.dual (denotSpace (σ.bind ("$y00" : Name) _) s₁))
        (denotSpace (σ.bind ("$y00" : Name) _) (.tprod (.dual s₀) (.dual s₁))))
      = HType.hil (HSpace.tprod (HSpace.dual (denotSpace σ s₁))
          (denotSpace σ (.tprod (.dual s₀) (.dual s₁))))
    show HType.hil (HSpace.tprod
        (HSpace.dual (denotSpace (σ.bind ("$y00" : Name) _) s₁))
        (HSpace.tprod (HSpace.dual (denotSpace (σ.bind ("$y00" : Name) _) s₀))
          (HSpace.dual (denotSpace (σ.bind ("$y00" : Name) _) s₁))))
      = HType.hil (HSpace.tprod (HSpace.dual (denotSpace σ s₁))
          (HSpace.tprod (HSpace.dual (denotSpace σ s₀))
            (HSpace.dual (denotSpace σ s₁))))
    rw [h_dsA_σ_y00, h_dsB_σ_y00]
  set σ_y00 : DEnv := σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩) with hσ_y00
  set V_curried_mid : HSpace :=
    HSpace.tprod (HSpace.dual (denotSpace σ s₁))
      (denotSpace σ (.tprod (.dual s₀) (.dual s₁))) with hV_curried_mid
  change (dualTensorHom ℝ (denotSpace σ s₁).carrier
      (denotSpace σ (.tprod (.dual s₀) (.dual s₁))).carrier
      (DVal.atSpace V_curried_mid (denotTerm σ_y00
        (.llam s₁
          (.tprod (.dual s₀) (.dual s₁))
          (.llam s₀ (.dual s₁)
            (.llam s₁ .real
              (.smul
                (Term.innerApp s₀ (.var "$y00") (.bvar 1))
                (Term.innerApp s₁ (.bvar 2) (.bvar 0)))))))) ) b = _
  rw [← DVal.asLinMap_eq_of_matchesShape h_F_y00_body_match]
  -- Step H: Apply F_y01_eval at σ_y00-frame, then bridge to σ-frame.
  have h_dsτ_σ_y00 : denotSpace σ_y00 (.tprod (.dual s₀) (.dual s₁))
      = denotSpace σ (.tprod (.dual s₀) (.dual s₁)) := by
    show HSpace.tprod (HSpace.dual (denotSpace σ_y00 s₀))
        (HSpace.dual (denotSpace σ_y00 s₁))
      = HSpace.tprod (HSpace.dual (denotSpace σ s₀)) (HSpace.dual (denotSpace σ s₁))
    rw [h_dsA_σ_y00, h_dsB_σ_y00]
  -- The bridge: reformulate as a forall, generalize over the HSpace's,
  -- then specialize after the rewrite.
  suffices h : ∀ (V₁ : HSpace) (hV₁ : V₁ = denotSpace σ_y00 s₁)
      (V_τ : HSpace) (hVτ : V_τ = denotSpace σ_y00 (.tprod (.dual s₀) (.dual s₁)))
      (b' : V₁.carrier),
      (denotTerm σ_y00
        (.llam s₁
          (.tprod (.dual s₀) (.dual s₁))
          (.llam s₀ (.dual s₁)
            (.llam s₁ .real
              (.smul
                (Term.innerApp s₀ (.var "$y00") (.bvar 1))
                (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))).asLinMap V₁ V_τ b'
      = (denotTerm
          (σ_y00.bind ("$y01" : Name) (.hil ⟨V₁, b'⟩))
          (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0)))))).atSpace V_τ by
    exact h (denotSpace σ s₁) h_dsB_σ_y00.symm
            (denotSpace σ (.tprod (.dual s₀) (.dual s₁))) h_dsτ_σ_y00.symm b
  intro V₁ hV₁ V_τ hVτ b'
  subst hV₁
  subst hVτ
  rw [F_y01_eval fresh sv₀ sv₁ env_wf ctx_ε a b']
  -- Bridge F_y01_eval's denotTermAux output back to denotTerm (σ_y00.bind "$y01") var-form.
  have h_y01b_lc : Term.lc (Term.openVar ("$y01" : Name)
      (.llam s₀ (.dual s₁)
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.bvar 2) (.bvar 0)))))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
    exact (F_y01_body_hasType fresh.fresh_y00 fresh.fresh_y01 fresh.fresh_y10
      fresh.fresh_y11 sv₀ sv₁).lc
  have h_y01b_fv : ("$y01" : Name) ∉ Term.fv
      (.llam s₀ (.dual s₁)
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.bvar 2) (.bvar 0)))) : Term) := by
    obtain ⟨h_00_01, _, _, _, _, _⟩ := Term.y_pairwise_distinct
    have h0 : ("$y01" : Name) ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_y01
    have h1 : ("$y01" : Name) ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_y01
    simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
      or_false, Finset.mem_singleton]
    intro h
    repeat first
      | exact h0 h | exact h1 h | exact h_00_01.symm h
      | (rcases h with h | h)
  have hbridge := denotTerm_openVar_bind (σ := σ_y00)
    (y := ("$y01" : Name)) (v := .hil ⟨denotSpace σ_y00 s₁, b'⟩)
    (e := (.llam s₀ (.dual s₁)
        (.llam s₁ .real
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.bvar 1))
            (Term.innerApp s₁ (.bvar 2) (.bvar 0))))))
    h_y01b_lc h_y01b_fv
  rw [← hbridge]
  congr 1
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  norm_num [Term.openRec]

/-- Freshness helper: `p` is not free in `Term.uncurry2Real s₀ s₁`, provided
    `p ∉ Space.fv s₀ ∪ Space.fv s₁`. -/
private lemma p_name_not_in_fv_uncurry2Real {s₀ s₁ : Space}
    (h_p_fv_s₀ : Term.p_name ∉ Space.fv s₀)
    (h_p_fv_s₁ : Term.p_name ∉ Space.fv s₁) :
    Term.p_name ∉ Term.fv (Term.uncurry2Real s₀ s₁) := by
  have h_p_not_g : Term.p_name ≠ Term.g_name := by decide
  have h_p_not_a : Term.p_name ≠ Term.a_name := by decide
  have h_p_not_b : Term.p_name ≠ Term.b_name := by decide
  unfold Term.uncurry2Real Term.curry2Real
  simp only [Term.fv, Space.fv, Finset.mem_union, Finset.mem_erase,
             not_or, Finset.notMem_empty,
             Finset.mem_singleton, h_p_fv_s₀, h_p_fv_s₁,
             h_p_not_g, h_p_not_a, h_p_not_b, ne_eq]
  tauto

/-- Freshness helper: `p` is not free in `Term.uncurry2NonReal s₀ s₁ sRest`,
    provided `p ∉ Space.fv s₀ ∪ Space.fv s₁ ∪ Space.fv sRest`. -/
private lemma p_name_not_in_fv_uncurry2NonReal {s₀ s₁ sRest : Space}
    (h_p_fv_s₀ : Term.p_name ∉ Space.fv s₀)
    (h_p_fv_s₁ : Term.p_name ∉ Space.fv s₁)
    (h_p_fv_sRest : Term.p_name ∉ Space.fv sRest) :
    Term.p_name ∉ Term.fv (Term.uncurry2NonReal s₀ s₁ sRest) := by
  have h_p_not_g : Term.p_name ≠ Term.g_name := by decide
  have h_p_not_a : Term.p_name ≠ Term.a_name := by decide
  have h_p_not_b : Term.p_name ≠ Term.b_name := by decide
  unfold Term.uncurry2NonReal Term.curry2NonReal
  simp only [Term.fv, Space.fv, Finset.mem_union, Finset.mem_erase,
             not_or, Finset.mem_singleton, h_p_fv_s₀, h_p_fv_s₁, h_p_fv_sRest,
             h_p_not_g, h_p_not_a, h_p_not_b, ne_eq]
  tauto

/-- Freshness helper: `p` is not free in F (the 4-binder inner lambda of iof_tprod).
    The binders `$y00..$y11` differ from `p`. -/
private lemma p_name_not_in_fv_F_term {s₀ s₁ : Space}
    (h_p_fv_s₀ : Term.p_name ∉ Space.fv s₀)
    (h_p_fv_s₁ : Term.p_name ∉ Space.fv s₁) :
    Term.p_name ∉ Term.fv
      (tprod_F s₀ s₁) := by
  have h_p_not_y00 : Term.p_name ≠ ("$y00" : Name) := by decide
  have h_p_not_y01 : Term.p_name ≠ ("$y01" : Name) := by decide
  have h_p_not_y10 : Term.p_name ≠ ("$y10" : Name) := by decide
  have h_p_not_y11 : Term.p_name ≠ ("$y11" : Name) := by decide
  simp only [tprod_F, Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.mem_erase,
             not_or, Finset.notMem_empty,
             Finset.mem_singleton, h_p_fv_s₀, h_p_fv_s₁,
             h_p_not_y00, h_p_not_y01, h_p_not_y10, h_p_not_y11, ne_eq]
  tauto

private lemma iof_tprod_body_isLinear
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    IsLinearMap ℝ (fun y : (denotSpace σ (.tprod s₀ s₁)).carrier =>
      (denotTermAux σ [.hil ⟨denotSpace σ (.tprod s₀ s₁), y⟩]
        (Term.applyUncurry2Real s₀ s₁
          (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
            (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
              (tprod_F s₀ s₁))
            (.bvar 0)))).atSpace
        (denotSpace σ (.dual (.tprod s₀ s₁)))) := by
  have h_p_notin_empty : Term.p_name ∉ (∅ : LCtx) := Finmap.notMem_empty
  have h_p_fv_s₀ : Term.p_name ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_p
  have h_p_fv_s₁ : Term.p_name ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_p
  have h_body_fv : Term.p_name ∉ Term.fv
      (Term.applyUncurry2Real s₀ s₁
        (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁))
          (.bvar 0)) : Term) := by
    have h_uR := p_name_not_in_fv_uncurry2Real h_p_fv_s₀ h_p_fv_s₁
    have h_uNR := p_name_not_in_fv_uncurry2NonReal h_p_fv_s₀ h_p_fv_s₁
      (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁) |>.notMem_fv_of_notMem_ε fresh.fresh_p)
    have h_F := p_name_not_in_fv_F_term h_p_fv_s₀ h_p_fv_s₁
    have h_appNR : Term.p_name ∉ Term.fv (Term.applyUncurry2NonReal s₀ s₁
        (.tprod (.dual s₀) (.dual s₁)) (tprod_F s₀ s₁)) := by
      unfold Term.applyUncurry2NonReal
      simp only [tprod_F, Term.fv, Space.fv, Term.innerApp, Finset.mem_union,
        Finset.notMem_empty, or_false, Finset.mem_singleton]
      intro h
      repeat first
        | exact h_p_fv_s₀ h | exact h_p_fv_s₁ h
        | exact h_uNR h
        | (rcases h with h | h)
    intro hmem
    rw [show (Term.applyUncurry2Real s₀ s₁
        (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁))
          (.bvar 0)))
      = Term.appL (.tprod (.dual s₀) (.dual s₁)) (.dual (.tprod s₀ s₁))
          (Term.uncurry2Real s₀ s₁)
          (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
            (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
              (tprod_F s₀ s₁))
            (.bvar 0)) from rfl] at hmem
    simp only [Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty, or_false,
      Finset.mem_singleton] at hmem
    repeat first
      | exact h_p_fv_s₀ hmem | exact h_p_fv_s₁ hmem
      | exact h_uR hmem | exact h_appNR hmem
      | exact absurd hmem (Finset.notMem_empty _)
      | (rcases hmem with hmem | hmem)
  have h_uR_lc : Term.lc (Term.uncurry2Real s₀ s₁) :=
    HasType.lc (Term.uncurry2Real_hasType sv₀ sv₁)
  have h_step1_lc : Term.lc (Term.applyUncurry2NonReal s₀ s₁
      (.tprod (.dual s₀) (.dual s₁)) (tprod_F s₀ s₁)) :=
    HasType.lc (Term.applyUncurry2NonReal_hasType (by intro h; cases h) sv₀ sv₁
      (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)) (tprod_F_hasType sv₀ sv₁))
  have h_open : Term.openVar Term.p_name
      (Term.applyUncurry2Real s₀ s₁
        (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁))
          (.bvar 0)))
    = Term.applyUncurry2Real s₀ s₁
        (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁))
          (.var Term.p_name)) := by
    simp only [Term.applyUncurry2Real, Term.openVar, Term.openRec, Space.openRec, if_true,
      Term.openRec_lc h_uR_lc, Term.openRec_lc h_step1_lc,
      Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
  have h_body_lc : Term.lc (Term.openVar Term.p_name
      (Term.applyUncurry2Real s₀ s₁
        (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁))
          (.bvar 0)))) := by
    rw [h_open]; exact (iof_tprod_body_hasType fresh sv₀ sv₁).lc
  have h_bridge : (fun y : (denotSpace σ (.tprod s₀ s₁)).carrier =>
      (denotTermAux σ [.hil ⟨denotSpace σ (.tprod s₀ s₁), y⟩]
        (Term.applyUncurry2Real s₀ s₁
          (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
            (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
              (tprod_F s₀ s₁))
            (.bvar 0)))).atSpace
        (denotSpace σ (.dual (.tprod s₀ s₁))))
    = (fun y : (denotSpace σ (.tprod s₀ s₁)).carrier =>
      (denotTerm (σ.bind Term.p_name (.hil ⟨denotSpace σ (.tprod s₀ s₁), y⟩))
        (Term.applyUncurry2Real s₀ s₁
          (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
            (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
              (tprod_F s₀ s₁))
            (.var Term.p_name)))).atSpace
        (denotSpace σ (.dual (.tprod s₀ s₁)))) := by
    funext y
    rw [← denotTerm_openVar_bind h_body_lc h_body_fv, h_open]
  rw [h_bridge]
  exact denot_llam_body_isLinear h_p_notin_empty fresh.fresh_p
    (SValid.tprod sv₀ sv₁) (SValid.dual (SValid.tprod sv₀ sv₁))
    (iof_tprod_body_hasType fresh sv₀ sv₁)
    ctx_ε env_wf

private lemma asLinMap_iof_tprod
    {σ : DEnv} {ε : NLCtx} {s₀ s₁ : Space}
    (fresh : IofFresh ε) (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    (HSpace.tprod (denotSpace σ s₀) (denotSpace σ s₁)).innerProduct =
      (denotTerm σ (Space.iof (.tprod s₀ s₁))).asLinMap
        (HSpace.tprod (denotSpace σ s₀) (denotSpace σ s₁))
        (HSpace.dual (HSpace.tprod (denotSpace σ s₀) (denotSpace σ s₁))) := by
  -- Strategy: TensorProduct.ext via LinearMap.ext + induction_on twice.
  -- Both sides are bilinear forms on V_sum = V₀ ⊗ V₁.
  -- Sufficient to show agreement on pure tensors (a⊗b, c⊗d).
  set V₀ := denotSpace σ s₀
  set V₁ := denotSpace σ s₁
  set V_sum := HSpace.tprod V₀ V₁
  -- LHS = V_sum.IP = LinearMap.BilinForm.tmul V₀.IP V₁.IP (by HSpace.tprod def).
  -- RHS = iof_denot.asLinMap V_sum V_sum*.
  -- Apply ext lemma for tensor products: both LinearMaps from V_sum agree
  -- iff they agree on all pure tensor inputs.
  apply LinearMap.ext
  intro p
  apply LinearMap.ext
  intro q
  -- Goal: V_sum.IP p q = iof_denot.asLinMap V_sum V_sum* p q.
  -- Pure-tensor case: a⊗b, c⊗d → V₀.IP a c * V₁.IP b d on both sides.
  -- Tensor induction handles general p, q via bilinearity.
  --
  -- Pure-tensor reduction of RHS (a⊗b)(c⊗d):
  --   iof = λ p ⊸ applyUncurry2Real (.appL step1 (.var p)) where step1 = uncurry F.
  --   At p = a⊗b:
  --     step1.asLinMap V_sum V_dual_01 (a⊗b) ∈ V_dual_01 = V₀*⊗V₁*.
  --       This is the canonical pairing V₀.IP(a, ·) ⊗ V₁.IP(b, ·) (after uncurry inverse).
  --     uncurry2Real_denoted applied: V_dual_01 → V_dual_sum element.
  --       Maps "φ ⊗ ψ" to functional (c⊗d) ↦ φ(c)·ψ(d).
  --     Applied to c⊗d: V₀.IP a c · V₁.IP b d.
  --
  -- This pure-tensor reduction requires identifying denoted curry2NonReal/Real
  -- as specific canonical iso `dualTensorHomEquiv`-style maps, then using
  -- mooreInv_bijective to get their inverses. Substantial Mathlib bridge.
  --
  -- The exact characterization: there exists a unique element θ ∈
  -- (V_sum)* ⊗ (V_sum)* such that θ.asLinMap = iof_denot.asLinMap and
  -- θ corresponds (via dualTensorHomEquiv) to the bilinear functional
  -- (a⊗b, c⊗d) ↦ V₀.IP a c · V₁.IP b d.
  --
  -- Use TensorProduct.induction_on twice and reduce to pure-tensor case.
  induction p using TensorProduct.induction_on with
  | zero =>
    simp only [LinearMap.map_zero, LinearMap.zero_apply]
  | tmul a b =>
    induction q using TensorProduct.induction_on with
    | zero =>
      simp only [LinearMap.map_zero]
    | tmul c d =>
      -- The substantive pure-tensor case: LHS = V₀.IP a c · V₁.IP b d via
      -- tensorDistrib_tmul; RHS = same via the curry/uncurry chain.
      -- LHS reduction:
      have h_lhs : V_sum.innerProduct (a ⊗ₜ[ℝ] b) (c ⊗ₜ[ℝ] d)
          = V₀.innerProduct a c * V₁.innerProduct b d := by
        show LinearMap.BilinForm.tmul V₀.innerProduct V₁.innerProduct
              (a ⊗ₜ[ℝ] b) (c ⊗ₜ[ℝ] d) = _
        rw [LinearMap.BilinForm.tensorDistrib_tmul]
        show V₁.innerProduct b d • V₀.innerProduct a c
            = V₀.innerProduct a c * V₁.innerProduct b d
        exact mul_comm _ _
      rw [h_lhs]
      -- RHS reduction: peel away the outer .llam first, then dive into the
      -- uncurry chain.
      symm
      show ((denotTerm σ
              (.llam (.tprod s₀ s₁) (.dual (.tprod s₀ s₁))
                (Term.applyUncurry2Real s₀ s₁
                  (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
                    (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
                      (tprod_F s₀ s₁))
                    (.bvar 0))))).asLinMap V_sum (HSpace.dual V_sum)
                      (a ⊗ₜ[ℝ] b)) (c ⊗ₜ[ℝ] d)
        = V₀.innerProduct a c * V₁.innerProduct b d
      rw [denotTerm_llam_non_real (by intro h; cases h)]

      show ((llamTensorDVal V_sum (HSpace.dual V_sum) _).asLinMap V_sum
              (HSpace.dual V_sum) (a ⊗ₜ[ℝ] b)) (c ⊗ₜ[ℝ] d)
        = V₀.innerProduct a c * V₁.innerProduct b d
      rw [asLinMap_llamTensorDVal]

      -- to reduce to a concrete body evaluation at σ_p := σ.bind p ⟨V_sum, a⊗b⟩.
      -- (V_sum := HSpace.tprod V₀ V₁ ≡ denotSpace σ (.tprod s₀ s₁) defeq, so
      -- we re-package the linearity at V_sum's literal carrier.)
      have h_lin : IsLinearMap ℝ (fun y : V_sum.carrier =>
          (denotTermAux σ [.hil ⟨V_sum, y⟩]
            (Term.applyUncurry2Real s₀ s₁
              (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
                (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
                  (tprod_F s₀ s₁))
                (.bvar 0)))).atSpace (HSpace.dual V_sum)) :=
        iof_tprod_body_isLinear fresh sv₀ sv₁ env_wf ctx_ε
      rw [LinearMap.ofFun_apply_of_isLinearMap h_lin]
      -- Bridge denotTermAux σ [v] body_bvar → denotTerm (σ.bind p v) body_var.
      have hp0 : Term.p_name ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_p
      have hp1 : Term.p_name ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_p
      have hbody_fv : Term.p_name ∉ Term.fv
          (Term.applyUncurry2Real s₀ s₁
            (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
              (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
                (tprod_F s₀ s₁))
              (.bvar 0)) : Term) := by
        have h_uR := p_name_not_in_fv_uncurry2Real hp0 hp1
        have h_appNR : Term.p_name ∉ Term.fv (Term.applyUncurry2NonReal s₀ s₁
            (.tprod (.dual s₀) (.dual s₁)) (tprod_F s₀ s₁)) := by
          unfold Term.applyUncurry2NonReal
          simp only [tprod_F, Term.fv, Space.fv, Term.innerApp, Finset.mem_union,
            Finset.notMem_empty, or_false, Finset.mem_singleton]
          intro h
          repeat first
            | exact hp0 h | exact hp1 h
            | exact (p_name_not_in_fv_uncurry2NonReal hp0 hp1
                (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)
                  |>.notMem_fv_of_notMem_ε fresh.fresh_p)) h
            | (rcases h with h | h)
        unfold Term.applyUncurry2Real
        simp only [Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
          or_false, Finset.mem_singleton]
        intro h
        repeat first
          | exact hp0 h | exact hp1 h | exact h_uR h | exact h_appNR h
          | exact absurd h (Finset.notMem_empty _)
          | (rcases h with h | h)
      have hbody_lc : Term.lc (Term.openVar Term.p_name
          (Term.applyUncurry2Real s₀ s₁
            (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
              (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
                (tprod_F s₀ s₁))
              (.bvar 0)))) := by
        have h_uR_lc : Term.lc (Term.uncurry2Real s₀ s₁) :=
          HasType.lc (Term.uncurry2Real_hasType sv₀ sv₁)
        have h_step1_lc : Term.lc (Term.applyUncurry2NonReal s₀ s₁
            (.tprod (.dual s₀) (.dual s₁)) (tprod_F s₀ s₁)) :=
          HasType.lc (Term.applyUncurry2NonReal_hasType (by intro h; cases h) sv₀ sv₁
            (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)) (tprod_F_hasType sv₀ sv₁))
        simp only [Term.applyUncurry2Real, Term.openVar, Term.openRec, Space.openRec, if_true,
          Term.openRec_lc h_uR_lc, Term.openRec_lc h_step1_lc,
          Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
        exact (iof_tprod_body_hasType fresh sv₀ sv₁).lc
      rw [denotTerm_openVar_bind (σ := σ) (y := Term.p_name)
            (v := .hil ⟨V_sum, a ⊗ₜ[ℝ] b⟩) hbody_lc hbody_fv |>.symm]
      simp only [Term.applyUncurry2Real, Term.openVar, Term.openRec, Space.openRec, if_true,
        Term.openRec_lc (HasType.lc (Term.uncurry2Real_hasType sv₀ sv₁)),
        Term.openRec_lc (HasType.lc (Term.applyUncurry2NonReal_hasType (by intro h; cases h)
          sv₀ sv₁ (SValid.tprod (SValid.dual sv₀) (SValid.dual sv₁)) (tprod_F_hasType sv₀ sv₁))),
        Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
      -- Goal: ((denot σ_p body).atSpace V_sum*) (c⊗d) = V₀.IP a c * V₁.IP b d.
      -- σ_p binds p := a⊗b. body = applyUncurry2Real s₀ s₁ (.appL step1 .var_p) =
      -- .appL V_τ V_sum_dual uncurry2Real (.appL V_sum V_τ step1 .var_p).
      -- Reduce via denotTerm_appL_atSpace_eq twice, then use C3 + characterization
      -- of step1(a⊗b) as the bilinear form V₀.IP(a, ·) ⊗ V₁.IP(b, ·).
      set σ_p : DEnv := σ.bind Term.p_name (.hil ⟨V_sum, a ⊗ₜ[ℝ] b⟩) with hσ_p
      set V_τ : HSpace := HSpace.tprod (HSpace.dual V₀) (HSpace.dual V₁) with hV_τ
      -- Step 1: peel the outer .appL of body.
      show ((denotTerm σ_p
            (.appL (.tprod (.dual s₀) (.dual s₁)) (.dual (.tprod s₀ s₁))
              (Term.uncurry2Real s₀ s₁)
              (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
                (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
                  (tprod_F s₀ s₁))
                (.var Term.p_name)))).atSpace (HSpace.dual V_sum))
            (c ⊗ₜ[ℝ] d)
        = V₀.innerProduct a c * V₁.innerProduct b d
      -- FV-irrelevance: p ∉ fv s₀, s₁ since fresh.fresh_p ∉ ε ⊇ fv-of-sv₀-sv₁.
      have h_p_fv_s₀ : Term.p_name ∉ Space.fv s₀ :=
        sv₀.notMem_fv_of_notMem_ε fresh.fresh_p
      have h_p_fv_s₁ : Term.p_name ∉ Space.fv s₁ :=
        sv₁.notMem_fv_of_notMem_ε fresh.fresh_p
      have h_dV₀_σ_p : denotSpace σ_p s₀ = V₀ :=
        denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_p_fv_s₀)
      have h_dV₁_σ_p : denotSpace σ_p s₁ = V₁ :=
        denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_p_fv_s₁)
      have h_dV_sum_σ_p : denotSpace σ_p (.tprod s₀ s₁) = V_sum := by
        show HSpace.tprod (denotSpace σ_p s₀) (denotSpace σ_p s₁) = V_sum
        rw [h_dV₀_σ_p, h_dV₁_σ_p]
      have h_dV_τ_σ_p : denotSpace σ_p (.tprod (.dual s₀) (.dual s₁)) = V_τ := by
        show HSpace.tprod (HSpace.dual (denotSpace σ_p s₀))
            (HSpace.dual (denotSpace σ_p s₁)) = V_τ
        rw [h_dV₀_σ_p, h_dV₁_σ_p]
      have h_dV_sum_dual_σ_p : denotSpace σ_p (.dual (.tprod s₀ s₁)) = HSpace.dual V_sum := by
        show HSpace.dual (denotSpace σ_p (.tprod s₀ s₁)) = HSpace.dual V_sum
        rw [h_dV_sum_σ_p]
      -- Step 1: peel outer .appL using the at-variant with V_T = HSpace.dual V_sum.
      rw [denotTerm_appL_atSpace_eq_at σ_p (.tprod (.dual s₀) (.dual s₁))
            (.dual (.tprod s₀ s₁))
            (Term.uncurry2Real s₀ s₁)
            (.appL (.tprod s₀ s₁) (.tprod (.dual s₀) (.dual s₁))
              (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
                (tprod_F s₀ s₁))
              (.var Term.p_name))
            (HSpace.dual V_sum) h_dV_sum_dual_σ_p]
      -- Step 2: peel inner .appL (natural form, no bridge needed).
      rw [denotTerm_appL_atSpace_eq]
      -- Bridge denotSpace σ_p _ to σ-frame V's via FV-irrelevance.
      rw [h_dV_sum_σ_p, h_dV_τ_σ_p]
      -- Step 3: evaluate (.var p) at σ_p — lookup gives .hil ⟨V_sum, a⊗b⟩.
      have h_var_p_lookup : denotTerm σ_p (.var Term.p_name)
          = .hil ⟨V_sum, a ⊗ₜ[ℝ] b⟩ := by
        show (σ_p.vars.lookup Term.p_name).getD DVal.default = _
        simp [σ_p, DEnv.bind, Finmap.lookup_insert]
      have h_var_p_eval : (denotTerm σ_p (.var Term.p_name)).atSpace V_sum = a ⊗ₜ[ℝ] b := by
        rw [h_var_p_lookup, atSpace_hil_self]
      rw [h_var_p_eval]
      -- Step 4: rewrite denot σ_p of closed-on-p subterms to denot σ via FV.
      have h_p_not_y00 : Term.p_name ≠ ("$y00" : Name) := by decide
      have h_p_not_y01 : Term.p_name ≠ ("$y01" : Name) := by decide
      have h_p_not_y10 : Term.p_name ≠ ("$y10" : Name) := by decide
      have h_p_not_y11 : Term.p_name ≠ ("$y11" : Name) := by decide
      have h_p_not_g : Term.p_name ≠ Term.g_name := by decide
      have h_p_not_a : Term.p_name ≠ Term.a_name := by decide
      have h_p_not_b : Term.p_name ≠ Term.b_name := by decide
      -- p ∉ Term.fv (Term.uncurry2Real s₀ s₁) follows from p ∉ fv s₀, s₁.
      have h_p_fv_uncurry2Real : Term.p_name ∉ Term.fv (Term.uncurry2Real s₀ s₁) := by
        unfold Term.uncurry2Real Term.curry2Real
        simp only [Term.fv, Space.fv, Finset.mem_union, Finset.mem_erase,
                   not_or, Finset.notMem_empty,
                   Finset.mem_singleton, h_p_fv_s₀, h_p_fv_s₁,
                   h_p_not_g, h_p_not_a, h_p_not_b, ne_eq]
        tauto
      -- denot σ_p (uncurry2Real s₀ s₁) = denot σ (uncurry2Real s₀ s₁)
      have h_denot_uncurry2Real_eq : denotTerm σ_p (Term.uncurry2Real s₀ s₁)
          = denotTerm σ (Term.uncurry2Real s₀ s₁) :=
        denotTerm_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_p_fv_uncurry2Real)
      rw [h_denot_uncurry2Real_eq]
      -- step1_term = .appL ... (uncurry2NonReal s₀ s₁ τ_rest) F.
      -- p ∉ Term.fv step1_term follows from p ∉ Term.fv uncurry2NonReal AND p ∉ Term.fv F
      -- AND p ∉ Space.fv of the appL type arguments.
      have h_p_fv_tprod_dual_dual : Term.p_name ∉ Space.fv (.tprod (.dual s₀) (.dual s₁)) := by
        simp only [Space.fv, Finset.mem_union, not_or]
        exact ⟨h_p_fv_s₀, h_p_fv_s₁⟩
      have h_F : Term.p_name ∉ Term.fv
          (tprod_F s₀ s₁) :=
        p_name_not_in_fv_F_term h_p_fv_s₀ h_p_fv_s₁
      have h_uncurry2NonReal : Term.p_name ∉ Term.fv
          (Term.uncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))) :=
        p_name_not_in_fv_uncurry2NonReal h_p_fv_s₀ h_p_fv_s₁ h_p_fv_tprod_dual_dual
      have h_p_fv_step1 : Term.p_name ∉ Term.fv
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁)) := by
        unfold Term.applyUncurry2NonReal
        intro h
        rw [Term.fv] at h
        rw [Finset.mem_union, Finset.mem_union, Finset.mem_union] at h
        rcases h with ((h1 | h2) | h3) | h4
        · -- p ∈ Space.fv (s₀*⊗s₁*⊗τ_rest)
          revert h1
          show Term.p_name ∉ Space.fv (Space.tprod (.dual s₀)
              (Space.tprod (.dual s₁) (.tprod (.dual s₀) (.dual s₁))))
          simp only [Space.fv, Finset.notMem_union]
          exact ⟨h_p_fv_s₀, h_p_fv_s₁, h_p_fv_s₀, h_p_fv_s₁⟩
        · -- p ∈ Space.fv ((s₀⊗s₁)*⊗τ_rest)
          revert h2
          show Term.p_name ∉ Space.fv (Space.tprod (.dual (.tprod s₀ s₁))
              (.tprod (.dual s₀) (.dual s₁)))
          simp only [Space.fv, Finset.notMem_union]
          exact ⟨⟨h_p_fv_s₀, h_p_fv_s₁⟩, h_p_fv_s₀, h_p_fv_s₁⟩
        · exact h_uncurry2NonReal h3
        · exact h_F h4
      -- denot σ_p step1 = denot σ step1
      have h_denot_step1_eq : denotTerm σ_p
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁))
          = denotTerm σ _ :=
        denotTerm_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_p_fv_step1)
      rw [h_denot_step1_eq]
      have h_ga' : Term.g_name ≠ Term.a_name := by decide
      have h_gb' : Term.g_name ≠ Term.b_name := by decide
      have h_ab' : Term.a_name ≠ Term.b_name := by decide
      -- Apply F1 direct variant with t = step1.asLinMap V_sum V_τ (a⊗b), a_val = c, b_val = d.
      -- F1_direct: (uncurry2Real_LinMap t)(c⊗d) = (dualTensorHom V₀ V_dual_1 t c) d
      -- The HSpace forms in F1_direct's statement are defeq to the goal's denotSpace forms.
      rw [uncurry2Real_apply_eq_dualTensorHom_direct
        fresh.fresh_g fresh.fresh_a fresh.fresh_b h_ga' h_gb' h_ab'
        sv₀ sv₁ env_wf ctx_ε
        ((denotTerm σ
          (Term.applyUncurry2NonReal s₀ s₁ (.tprod (.dual s₀) (.dual s₁))
            (tprod_F s₀ s₁)) ).asLinMap
              V_sum V_τ (a ⊗ₜ[ℝ] b))
        c d]
      -- Goal: (dualTensorHom V₀ V_dual_1 (step1.asLinMap V_sum V_τ (a⊗b)) c) d
      --     = V₀.IP a c * V₁.IP b d.
      -- Apply step1_asLinMap_at_aXb_eval to reduce step1's application.
      rw [step1_asLinMap_at_aXb_eval fresh sv₀ sv₁ env_wf ctx_ε a b]
      -- Setup σ_y00 and σ_y00_y01 frames.
      set σ_y00 : DEnv := σ.bind ("$y00" : Name) (.hil ⟨V₀, a⟩) with hσ_y00
      set σ_y00_y01 : DEnv := σ_y00.bind ("$y01" : Name) (.hil ⟨V₁, b⟩) with hσ_y00_y01
      -- FV-irrelevance equalities at σ_y00_y01 frame.
      have h_y00_fv_s₀ : ("$y00" : Name) ∉ Space.fv s₀ :=
        sv₀.notMem_fv_of_notMem_ε fresh.fresh_y00
      have h_y00_fv_s₁ : ("$y00" : Name) ∉ Space.fv s₁ :=
        sv₁.notMem_fv_of_notMem_ε fresh.fresh_y00
      have h_y01_fv_s₀ : ("$y01" : Name) ∉ Space.fv s₀ :=
        sv₀.notMem_fv_of_notMem_ε fresh.fresh_y01
      have h_y01_fv_s₁ : ("$y01" : Name) ∉ Space.fv s₁ :=
        sv₁.notMem_fv_of_notMem_ε fresh.fresh_y01
      have h_dsA_σ_y00_y01 : denotSpace σ_y00_y01 s₀ = V₀ :=
        (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y01_fv_s₀)).trans
          (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y00_fv_s₀))
      have h_dsB_σ_y00_y01 : denotSpace σ_y00_y01 s₁ = V₁ :=
        (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y01_fv_s₁)).trans
          (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y00_fv_s₁))
      -- Use suffices+subst, generalizing V_A (=V₀) only. V_B_dual stays as
      -- HSpace.dual V₁ (specific, allowing function application of d via @[reducible]).
      suffices h : ∀ (V_A : HSpace) (hVA : V_A = denotSpace σ_y00_y01 s₀)
          (c' : V_A.carrier),
          ((denotTerm σ_y00_y01
              (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0)))))).asLinMap V_A
              (HSpace.dual V₁) c') d
          = V₀.innerProduct a (h_dsA_σ_y00_y01 ▸ (hVA ▸ c'))
            * V₁.innerProduct b d by
        -- Apply h with V_A := V₀.
        -- First convert dualTensorHom form to asLinMap form via h_F_y01_body_match.
        have h_F_y01_body_match :
            (denotTerm σ_y00_y01
              (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0)))))).matchesShape
            (.hil (HSpace.tprod (HSpace.dual V₀) (HSpace.dual V₁))) := by
          rw [denotTerm_llam_non_real (by intro h; cases h)]
          show HType.hil (HSpace.tprod (HSpace.dual (denotSpace σ_y00_y01 s₀))
              (denotSpace σ_y00_y01 (.dual s₁)))
            = HType.hil (HSpace.tprod (HSpace.dual V₀) (HSpace.dual V₁))
          show HType.hil (HSpace.tprod (HSpace.dual (denotSpace σ_y00_y01 s₀))
              (HSpace.dual (denotSpace σ_y00_y01 s₁)))
            = HType.hil (HSpace.tprod (HSpace.dual V₀) (HSpace.dual V₁))
          rw [h_dsA_σ_y00_y01, h_dsB_σ_y00_y01]
        rw [← DVal.asLinMap_eq_of_matchesShape h_F_y01_body_match]
        have h_app := h V₀ h_dsA_σ_y00_y01.symm c
        simp only [eqRec_eq_cast, cast_cast, cast_eq] at h_app
        exact h_app
      intro V_A hVA c'
      subst hVA
      -- Inner suffices: generalize V_B (= V₁) at σ_y00_y01-frame.
      -- This matches F_y10_eval's V₁ arg (which is σ_y00_y01-frame).
      suffices h_inner : ∀ (V_B : HSpace)
          (hVB : V_B = denotSpace σ_y00_y01 s₁)
          (d' : V_B.carrier),
          ((DVal.asLinMap (denotSpace σ_y00_y01 s₀) (HSpace.dual V_B)
              (denotTerm σ_y00_y01
                (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0))))))) c') d'
          = V₀.innerProduct a (h_dsA_σ_y00_y01 ▸ c') *
            V₁.innerProduct b (h_dsB_σ_y00_y01 ▸ (hVB ▸ d')) by
        have h_app := h_inner V₁ h_dsB_σ_y00_y01.symm d
        simp only [eqRec_eq_cast, cast_cast, cast_eq] at h_app ⊢
        exact h_app
      intro V_B hVB d'
      subst hVB
      -- Unfold σ_y00_y01 (the `set`) so F_y10_eval matches.
      show ((DVal.asLinMap (denotSpace
          ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
            ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩)) s₀)
          (HSpace.dual (denotSpace
            ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
              ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩)) s₁))
          (denotTerm
            ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
              ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩))
            (.llam s₀ (.dual s₁)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0))))))) c') d'
        = _
      have hF10 := F_y10_eval fresh sv₀ sv₁ env_wf ctx_ε a b c'
      rw [hF10]
      -- Bridge F_y10_eval's denotTermAux output → denotTerm (σ_y00_y01.bind "$y10").
      have h10b_fv : ("$y10" : Name) ∉ Term.fv
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0))) : Term) := by
        obtain ⟨_, h_00_10, _, h_01_10, _, _⟩ := Term.y_pairwise_distinct
        have h0 : ("$y10" : Name) ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_y10
        have h1 : ("$y10" : Name) ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_y10
        simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
          or_false, Finset.mem_singleton]
        intro h
        repeat first
          | exact h0 h | exact h1 h | exact h_00_10.symm h | exact h_01_10.symm h
          | (rcases h with h | h)
      have h10b_lc : Term.lc (Term.openVar ("$y10" : Name)
          (.llam s₁ .real
            (.smul
              (Term.innerApp s₀ (.var "$y00") (.bvar 1))
              (Term.innerApp s₁ (.var "$y01") (.bvar 0))))) := by
        simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
          Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
        exact (F_y10_body_hasType fresh.fresh_y11 sv₀ sv₁).lc
      rw [← denotTerm_openVar_bind (σ := (σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
            ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩))
          (y := ("$y10" : Name))
          (v := .hil ⟨denotSpace ((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
            ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩)) s₀, c'⟩) h10b_lc h10b_fv]
      simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
        Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
      norm_num [Term.openRec]

      have h_y10_fv_s₁ : ("$y10" : Name) ∉ Space.fv s₁ :=
        sv₁.notMem_fv_of_notMem_ε fresh.fresh_y10
      have h_dsB_σ_y10_eq : denotSpace
          (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
              ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩)).bind
              ("$y10" : Name) (.hil ⟨denotSpace σ_y00_y01 s₀, c'⟩)) s₁
          = denotSpace σ_y00_y01 s₁ :=
        denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y10_fv_s₁)
      -- Inner-inner suffices: generalize V_B'' at σ_y10-frame for F_y11_eval.
      suffices h_inner2 : ∀ (V_B' : HSpace)
          (hVB' : V_B' = denotSpace
              (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
                  ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩)).bind
                  ("$y10" : Name) (.hil ⟨denotSpace σ_y00_y01 s₀, c'⟩)) s₁)
          (d'' : V_B'.carrier),
          (denotTerm
              (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
                  ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩)).bind
                  ("$y10" : Name) (.hil ⟨denotSpace σ_y00_y01 s₀, c'⟩))
              (.llam s₁ .real
              (.smul
                (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
                (Term.innerApp s₁ (.var "$y01") (.bvar 0))))).atSpace
            (HSpace.dual V_B') d''
          = V₀.innerProduct a (h_dsA_σ_y00_y01 ▸ c') *
            V₁.innerProduct b (h_dsB_σ_y00_y01 ▸ (h_dsB_σ_y10_eq ▸ (hVB' ▸ d''))) by
        have h_app := h_inner2 (denotSpace σ_y00_y01 s₁) h_dsB_σ_y10_eq.symm d'
        simp only [eqRec_eq_cast, cast_cast, cast_eq] at h_app ⊢
        exact h_app
      intro V_B' hVB' d''
      subst hVB'
      -- Establish equalities at unfolded denotSpace form for the cast targets.
      have h_dsA' : denotSpace σ_y00_y01 s₀ = denotSpace σ s₀ := h_dsA_σ_y00_y01
      have h_dsB' : denotSpace σ_y00_y01 s₁ = denotSpace σ s₁ := h_dsB_σ_y00_y01

      rw [denotTerm_atSpace_dual_DEnv_bind_HSpace_swap h_dsA' c'
            (.llam s₁ .real
              (.smul
                (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
                (Term.innerApp s₁ (.var "$y01") (.bvar 0))))
            s₁ d'']

      rw [F_y11_eval fresh sv₀ sv₁ env_wf ctx_ε a b (h_dsA' ▸ c')]
      -- Apply F_innermost_smul_eval. Signature order: y00, y10, y01, y11.
      have h_smul := F_innermost_smul_eval fresh sv₀ sv₁ a (h_dsA' ▸ c') b
        (h_dsB' ▸ (h_dsB_σ_y10_eq ▸ d''))
      -- Unfold the let-binding `σ_full` inside h_smul so the y11 bind pattern
      -- becomes accessible to rewrites.
      simp only [] at h_smul
      -- h_smul has the y11 binding at V₁ = denotSpace σ s₁. The goal expects
      -- it at denotSpace σ_y10_NEW s₁. They're propositionally equal via
      -- FV-irrelevance for y10 ∉ fv s₁. Bridge h_smul's y11 binding.
      have h_dsB_σ_y10_NEW : denotSpace
          (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
              ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩)).bind
                ("$y10" : Name) (.hil ⟨denotSpace σ s₀, h_dsA' ▸ c'⟩)) s₁
          = denotSpace σ_y00_y01 s₁ :=
        denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_y10_fv_s₁)
      have h_y11_bridge : denotSpace σ s₁ = denotSpace
          (((σ.bind ("$y00" : Name) (.hil ⟨denotSpace σ s₀, a⟩)).bind
              ("$y01" : Name) (.hil ⟨denotSpace σ s₁, b⟩)).bind
                ("$y10" : Name) (.hil ⟨denotSpace σ s₀, h_dsA' ▸ c'⟩)) s₁ :=
        (h_dsB_σ_y10_NEW.trans h_dsB_σ_y00_y01).symm
      rw [denotTerm_bind_HSpace_eq h_y11_bridge (h_dsB' ▸ (h_dsB_σ_y10_eq ▸ d''))
            ((Term.innerApp s₀ (.var "$y00") (.var "$y10")).smul
              (Term.innerApp s₁ (.var "$y01") (.var "$y11")))] at h_smul
      -- Bridge h_smul's denotTerm (σ_full3.bind "$y11") → denotTermAux σ_full3 [v]
      -- so it matches F_y11_eval's output form in the goal.
      have h11b_fv : ("$y11" : Name) ∉ Term.fv
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
            (Term.innerApp s₁ (.var "$y01") (.bvar 0)) : Term) := by
        obtain ⟨_, _, h_00_11, _, h_01_11, h_10_11⟩ := Term.y_pairwise_distinct
        have h0 : ("$y11" : Name) ∉ Space.fv s₀ := sv₀.notMem_fv_of_notMem_ε fresh.fresh_y11
        have h1 : ("$y11" : Name) ∉ Space.fv s₁ := sv₁.notMem_fv_of_notMem_ε fresh.fresh_y11
        simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
          or_false, Finset.mem_singleton]
        intro h
        repeat first
          | exact h0 h | exact h1 h | exact h_00_11.symm h | exact h_01_11.symm h
          | exact h_10_11.symm h
          | (rcases h with h | h)
      have h11b_lc : Term.lc (Term.openVar ("$y11" : Name)
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
            (Term.innerApp s₁ (.var "$y01") (.bvar 0)))) := by
        simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
          Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
        exact (F_smul_body_hasType sv₀ sv₁).lc
      have h11_open : Term.openVar ("$y11" : Name)
          (.smul
            (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
            (Term.innerApp s₁ (.var "$y01") (.bvar 0)))
        = (.smul
            (Term.innerApp s₀ (.var "$y00") (.var "$y10"))
            (Term.innerApp s₁ (.var "$y01") (.var "$y11"))) := by
        simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
          Space.openRec_lc (SValid.lc sv₀), Space.openRec_lc (SValid.lc sv₁)]
        norm_num [Term.openRec]
      rw [← h11_open, denotTerm_openVar_bind h11b_lc h11b_fv] at h_smul
      simp only [eqRec_eq_cast, cast_cast] at h_smul ⊢
      exact h_smul
    | add q₁ q₂ ih₁ ih₂ =>
      rw [LinearMap.map_add, LinearMap.map_add, ih₁, ih₂]
  | add p₁ p₂ ih₁ ih₂ =>
    -- Linearity in first argument of both sides.
    have h_lhs : (V_sum.innerProduct (p₁ + p₂)) q
        = (V_sum.innerProduct p₁) q + (V_sum.innerProduct p₂) q := by
      rw [LinearMap.map_add, LinearMap.add_apply]
    have h_rhs : ((denotTerm σ (Space.iof (.tprod s₀ s₁))).asLinMap V_sum
            (HSpace.dual V_sum) (p₁ + p₂)) q
        = ((denotTerm σ (Space.iof (.tprod s₀ s₁))).asLinMap V_sum
              (HSpace.dual V_sum) p₁) q +
          ((denotTerm σ (Space.iof (.tprod s₀ s₁))).asLinMap V_sum
              (HSpace.dual V_sum) p₂) q := by
      rw [LinearMap.map_add, LinearMap.add_apply]
    rw [h_lhs, h_rhs, ih₁, ih₂]

/-- Combined bridge: `(denot σ kproj0).asLinMap V_sum V₀ = LinearMap.fst`. -/
private lemma asLinMap_denotTerm_kproj0_eq_fst
    {ε : NLCtx} (σ : DEnv) (s₀ s₁ : Space)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (h_fresh_s₀ : Term.x0 ∉ Space.fv s₀) (h_fresh_s₁ : Term.x0 ∉ Space.fv s₁) :
    DVal.asLinMap (HSpace.dsum (denotSpace σ s₀) (denotSpace σ s₁)) (denotSpace σ s₀)
        (denotTerm σ (Term.kproj0 s₀ s₁))
      = LinearMap.fst ℝ (denotSpace σ s₀).carrier (denotSpace σ s₁).carrier := by
  set V₀ := denotSpace σ s₀
  set V₁ := denotSpace σ s₁
  show DVal.asLinMap (HSpace.dsum V₀ V₁) V₀
      (pinvTensorDVal V₀ (HSpace.dsum V₀ V₁) (denotTerm σ (Term.kembed0 s₀ s₁))) = _
  rw [asLinMap_pinvTensorDVal V₀ (HSpace.dsum V₀ V₁) (denotTerm σ (Term.kembed0 s₀ s₁))]
  rw [asLinMap_denotTerm_kembed0 σ s₀ s₁ sv₀ sv₁ h_fresh_s₀ h_fresh_s₁]
  exact mooreInv_inl_eq_fst V₀ V₁

/-- Combined bridge: `(denot σ kproj1).asLinMap V_sum V₁ = LinearMap.snd`. -/
private lemma asLinMap_denotTerm_kproj1_eq_snd
    {ε : NLCtx} (σ : DEnv) (s₀ s₁ : Space)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (h_fresh_s₀ : Term.x0 ∉ Space.fv s₀) :
    DVal.asLinMap (HSpace.dsum (denotSpace σ s₀) (denotSpace σ s₁)) (denotSpace σ s₁)
        (denotTerm σ (Term.kproj1 s₀ s₁))
      = LinearMap.snd ℝ (denotSpace σ s₀).carrier (denotSpace σ s₁).carrier := by
  set V₀ := denotSpace σ s₀
  set V₁ := denotSpace σ s₁
  show DVal.asLinMap (HSpace.dsum V₀ V₁) V₁
      (pinvTensorDVal V₁ (HSpace.dsum V₀ V₁) (denotTerm σ (Term.kembed1 s₀ s₁))) = _
  rw [asLinMap_pinvTensorDVal V₁ (HSpace.dsum V₀ V₁) (denotTerm σ (Term.kembed1 s₀ s₁))]
  rw [asLinMap_denotTerm_kembed1 σ s₀ s₁ sv₀ sv₁ h_fresh_s₀]
  exact mooreInv_inr_eq_snd V₀ V₁

/-- Helper for the four fundamental-subspace cases (`.ker / .coker / .img /
    .coimg`). Each has the same iof shape — `λ x0:sub ⊸ λ x1:sub ⊸
    innerApp s_amb (.embed sub · x0) (.embed sub · x1)` — and reduces to
    `V_amb.IP (K.subtype y) (K.subtype y') = bilinRestrict V_amb.IP K y y' =
    V_sub.innerProduct y y'`.

    Caller supplies `V_amb`, `K`, the denot-equalities and freshness facts. -/
private lemma isCanonical_fundSubspace
    (σ : DEnv) (sub s_amb : Space)
    (V_amb : HSpace) (K : Submodule ℝ V_amb.carrier)
    (h_denot_sub : denotSpace σ sub = HSpace.ofSubmodule V_amb K)
    (h_denot_amb : denotSpace σ s_amb = V_amb)
    (h_embed_denot : denotTerm σ (.embed sub)
        = embedDVal (HSpace.ofSubmodule V_amb K) V_amb K.subtype)
    (h_fresh_x0_sub : Term.x0 ∉ Space.fv sub)
    (h_fresh_x1_sub : Term.x1 ∉ Space.fv sub)
    (h_fresh_x0_amb : Term.x0 ∉ Space.fv s_amb)
    (h_fresh_x1_amb : Term.x1 ∉ Space.fv s_amb)
    (h_fresh_x0_embed : Term.x0 ∉ Term.fv (.embed sub))
    (h_fresh_x1_embed : Term.x1 ∉ Term.fv (.embed sub))
    (h_lc_sub : Space.lc sub) (h_lc_amb : Space.lc s_amb) :
    (denotSpace σ sub).innerProduct =
      (denotTerm σ (Space.iofSubBody sub s_amb)).asLinMap
        (denotSpace σ sub) (HSpace.dual (denotSpace σ sub)) := by
  set V_sub := HSpace.ofSubmodule V_amb K with hV_sub
  rw [h_denot_sub]
  show V_sub.innerProduct = _
  symm
  unfold Space.iofSubBody
  rw [denotTerm_llam_non_real (by intro h; cases h)]
  show DVal.asLinMap V_sub (HSpace.dual V_sub)
      (llamTensorDVal (denotSpace σ sub) (denotSpace σ (.dual sub)) _) = _
  rw [show (denotSpace σ sub) = V_sub from h_denot_sub,
      show (denotSpace σ (.dual sub)) = HSpace.dual V_sub from by
        show HSpace.dual (denotSpace σ sub) = _; rw [h_denot_sub]]
  rw [asLinMap_llamTensorDVal]
  apply linearMap_ofFun_eq_of_pt _ V_sub.innerProduct
  intro y
  set σ' := σ.bind Term.x0 (.hil ⟨V_sub, y⟩) with hσ'
  have h_dSub : denotSpace σ' sub = V_sub :=
    (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_x0_sub)).trans h_denot_sub
  have h_dV_amb : denotSpace σ' s_amb = V_amb :=
    (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_x0_amb)).trans h_denot_amb
  have h_dSub_dual : denotSpace σ' (.dual sub) = HSpace.dual V_sub := by
    show HSpace.dual (denotSpace σ' sub) = _; rw [h_dSub]
  show (denotTermAux σ [.hil ⟨V_sub, y⟩]
        (.llam sub .real
          (Term.innerApp s_amb
            (Term.embedApp sub s_amb (.bvar 1))
            (Term.embedApp sub s_amb (.bvar 0)))) ).atSpace
            (HSpace.dual V_sub) = V_sub.innerProduct y
  -- Bridge denotTermAux σ [v] body → denotTerm (σ.bind x0 v) (openVar x0 body).
  have hx0b_fv : Term.x0 ∉ Term.fv
      (.llam sub .real
        (Term.innerApp s_amb
          (Term.embedApp sub s_amb (.bvar 1))
          (Term.embedApp sub s_amb (.bvar 0))) : Term) := by
    simp only [Term.embedApp, Term.innerApp, Term.fv, Finset.mem_union, Finset.notMem_empty,
      or_false]
    intro h
    repeat first
      | exact h_fresh_x0_sub h | exact h_fresh_x0_amb h
      | exact h_fresh_x0_embed (by simpa [Term.fv] using h)
      | (rcases h with h | h)
  have hx0b_lc : Term.lc (Term.openVar Term.x0
      (.llam sub .real
        (Term.innerApp s_amb
          (Term.embedApp sub s_amb (.bvar 1))
          (Term.embedApp sub s_amb (.bvar 0))))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Term.embedApp, Space.openRec_lc h_lc_sub, Space.openRec_lc h_lc_amb]
    refine Term.lc.llam ∅ h_lc_sub Space.lc.real (fun x _ => ?_)
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc h_lc_sub, Space.openRec_lc h_lc_amb]
    refine Term.lc.appI h_lc_amb (Term.lc.appL h_lc_amb (Space.lc.dual h_lc_amb)
      (Term.lc.inner h_lc_amb) ?_) ?_
    · exact Term.lc.appL h_lc_sub h_lc_amb (Term.lc.embed h_lc_sub) Term.lc.var
    · exact Term.lc.appL h_lc_sub h_lc_amb (Term.lc.embed h_lc_sub) Term.lc.var
  rw [← denotTerm_openVar_bind (σ := σ) (y := Term.x0) (v := .hil ⟨V_sub, y⟩)
        hx0b_lc hx0b_fv]
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Term.embedApp, Space.openRec_lc h_lc_sub, Space.openRec_lc h_lc_amb]
  norm_num [Term.openRec]
  rw [← hσ']
  rw [denotTerm_llam_real]
  show (llamRealDVal (denotSpace σ' sub) _).atSpace _ = _
  rw [h_dSub]
  rw [atSpace_llamRealDVal]
  apply linearMap_ofFun_eq_of_pt _ (V_sub.innerProduct y)
  intro y'
  set σ'' := σ'.bind Term.x1 (.hil ⟨V_sub, y'⟩) with hσ''
  -- Bridge inner denotTermAux σ' [v_x1] body → denotTerm σ'' body_var.
  have hx1b_fv : Term.x1 ∉ Term.fv
      (Term.innerApp s_amb
        (.appL sub s_amb (.embed sub) (.var Term.x0))
        (.appL sub s_amb (.embed sub) (.bvar 0)) : Term) := by
    simp only [Term.innerApp, Term.fv, Finset.mem_union, Finset.notMem_empty,
      or_false, Finset.mem_singleton]
    intro h
    repeat first
      | exact h_fresh_x1_sub h | exact h_fresh_x1_amb h
      | exact h_fresh_x1_embed (by simpa [Term.fv] using h)
      | exact Term.x0_ne_x1.symm h
      | (rcases h with h | h)
  have hx1b_lc : Term.lc (Term.openVar Term.x1
      (Term.innerApp s_amb
        (.appL sub s_amb (.embed sub) (.var Term.x0))
        (.appL sub s_amb (.embed sub) (.bvar 0)))) := by
    simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
      Space.openRec_lc h_lc_sub, Space.openRec_lc h_lc_amb]
    refine Term.lc.appI h_lc_amb (Term.lc.appL h_lc_amb (Space.lc.dual h_lc_amb)
      (Term.lc.inner h_lc_amb) ?_) ?_
    · exact Term.lc.appL h_lc_sub h_lc_amb (Term.lc.embed h_lc_sub) Term.lc.var
    · exact Term.lc.appL h_lc_sub h_lc_amb (Term.lc.embed h_lc_sub) Term.lc.var
  rw [← denotTerm_openVar_bind (σ := σ') (y := Term.x1) (v := .hil ⟨V_sub, y'⟩)
        hx1b_lc hx1b_fv]
  simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
    Space.openRec_lc h_lc_sub, Space.openRec_lc h_lc_amb]
  rw [← hσ'']
  have h_dSub_2 : denotSpace σ'' sub = V_sub :=
    (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_x1_sub)).trans h_dSub
  have h_dV_amb_2 : denotSpace σ'' s_amb = V_amb :=
    (denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_x1_amb)).trans h_dV_amb
  have h_dSub_2_dual : denotSpace σ'' (.dual sub) = HSpace.dual V_sub := by
    show HSpace.dual (denotSpace σ'' sub) = _; rw [h_dSub_2]
  have h_dV_amb_2_dual : denotSpace σ'' (.dual s_amb) = HSpace.dual V_amb := by
    show HSpace.dual (denotSpace σ'' s_amb) = _; rw [h_dV_amb_2]
  -- denot σ'' (.embed sub) = embedDVal V_sub V_amb K.subtype, via FV-irrelevance from σ.
  have h_agree_embed : σ''.AgreeOn σ (Term.fv (.embed sub)) := by
    have ha₁ : σ''.AgreeOn σ' (Term.fv (.embed sub)) :=
      DEnv.AgreeOn.bind_left_of_not_mem h_fresh_x1_embed
    have ha₂ : σ'.AgreeOn σ (Term.fv (.embed sub)) :=
      DEnv.AgreeOn.bind_left_of_not_mem h_fresh_x0_embed
    constructor
    intro y hy
    exact (ha₁.vars y hy).trans (ha₂.vars y hy)
  have h_embed_2 : denotTerm σ'' (.embed sub)
      = embedDVal V_sub V_amb K.subtype := by
    rw [denotTerm_agree _ h_agree_embed]
    exact h_embed_denot
  have h_var_x0 : denotTerm σ'' (.var Term.x0) = .hil ⟨V_sub, y⟩ := by
    show denotTerm (σ'.bind Term.x1 _) (.var Term.x0) = _
    rw [denotTerm_var_bind_other_bind_self
      (.hil ⟨V_sub, y⟩) (.hil ⟨V_sub, y'⟩) Term.x0_ne_x1]
  have h_var_x1 : denotTerm σ'' (.var Term.x1) = .hil ⟨V_sub, y'⟩ := by
    show denotTerm (σ'.bind Term.x1 _) (.var Term.x1) = _
    rw [denotTerm_var_bind_self]
  have h_appL : ∀ (xi : Name) (c : V_sub.carrier),
      denotTerm σ'' (.var xi) = .hil ⟨V_sub, c⟩ →
      denotTerm σ'' (.appL sub s_amb (.embed sub) (.var xi))
        = .hil ⟨V_amb, K.subtype c⟩ := by
    intro xi c h_var_eq
    show DVal.hil ⟨denotSpace σ'' s_amb,
          ((denotTerm σ'' (.embed sub)).asLinMap
            (denotSpace σ'' sub) (denotSpace σ'' s_amb))
          ((denotTerm σ'' (.var xi)).atSpace (denotSpace σ'' sub))⟩ = _
    rw [h_dV_amb_2, h_dSub_2, h_embed_2, asLinMap_embedDVal, h_var_eq, atSpace_hil_self]
  have h_appL_x0 := h_appL Term.x0 y h_var_x0
  have h_appL_x1 := h_appL Term.x1 y' h_var_x1
  have h_inner : denotTerm σ'' (.inner s_amb) = HSpace.innerTensor V_amb V_amb.innerProduct := by
    show (denotSpace σ'' s_amb).innerTensor (denotSpace σ'' s_amb).innerProduct = _
    rw [h_dV_amb_2]
  have h_inner_app : denotTerm σ''
        (.appL s_amb (.dual s_amb) (.inner s_amb)
          (.appL sub s_amb (.embed sub) (.var Term.x0)))
      = .hil ⟨HSpace.dual V_amb, V_amb.innerProduct (K.subtype y)⟩ := by
    show DVal.hil ⟨denotSpace σ'' (.dual s_amb),
          ((denotTerm σ'' (.inner s_amb)).asLinMap
            (denotSpace σ'' s_amb) (denotSpace σ'' (.dual s_amb)))
          ((denotTerm σ'' (.appL sub s_amb (.embed sub) (.var Term.x0))).atSpace
            (denotSpace σ'' s_amb))⟩ = _
    rw [h_dV_amb_2, h_dV_amb_2_dual, h_inner, asLinMap_innerTensor, h_appL_x0,
        atSpace_hil_self]
  show DVal.atSpace HSpace.real
        (DVal.hil ⟨HSpace.real,
          DVal.asLinFunctional (denotSpace σ'' s_amb)
            (denotTerm σ''
              (.appL s_amb (.dual s_amb) (.inner s_amb)
                (.appL sub s_amb (.embed sub) (.var Term.x0))))
          (DVal.atSpace (denotSpace σ'' s_amb)
            (denotTerm σ''
              (.appL sub s_amb (.embed sub) (.var Term.x1))))⟩) = _
  rw [h_dV_amb_2, h_inner_app, asLinFunctional_hil_dual, h_appL_x1, atSpace_hil_self,
      atSpace_hil_self]
  symm
  exact bilinRestrict_apply V_amb.innerProduct K y y'

theorem DEnv.IsCanonical_holds (σ : DEnv) (ε : NLCtx) (fresh : IofFresh ε)
    (env_wf : EnvWF σ ∅ ε) (ctx_ε : CtxWF ∅ ε) :
    σ.IsCanonical ε := by
  intro s sv
  match s, sv with
  | .empty, _ =>
      -- Both sides are LinearMaps PUnit → PUnit → ℝ; PUnit subsingleton gives equality.
      apply bilin_punit_eq
  | .real, _ =>
      -- LHS = HSpace.real.innerProduct = LinearMap.mul ℝ ℝ (by definition).
      -- RHS reduces to LinearMap.mul ℝ ℝ via the same chain as the .real
      -- proof in the alternative IP theorem.
      show (LinearMap.mul ℝ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) =
        (denotTerm σ (Space.iof .real)).asLinMap
          HSpace.real (HSpace.dual HSpace.real)
      symm
      show (denotTerm σ (.llam .real (.dual .real)
              (.llam .real .real
                (.smul (.bvar 1) (.bvar 0))))).asLinMap
              HSpace.real (HSpace.dual HSpace.real) = _
      rw [denotTerm_llam_non_real (by intro h; cases h)]
      show (llamTensorDVal HSpace.real (HSpace.dual HSpace.real) _).asLinMap
            HSpace.real (HSpace.dual HSpace.real) = _
      rw [asLinMap_llamTensorDVal]
      apply linearMap_ofFun_eq_of_pt _ (LinearMap.mul ℝ ℝ)
      intro y
      show (denotTermAux σ [.hil ⟨HSpace.real, y⟩]
            (.llam .real .real
              (.smul (.bvar 1) (.bvar 0)))).atSpace
              (HSpace.dual HSpace.real) = LinearMap.mul ℝ ℝ y
      rw [show denotTermAux σ [.hil ⟨HSpace.real, y⟩]
              (.llam .real .real (.smul (.bvar 1) (.bvar 0)))
            = llamRealDVal HSpace.real (fun v =>
                (denotTermAux σ (v :: [.hil ⟨HSpace.real, y⟩]) (.smul (.bvar 1) (.bvar 0))).atSpace
                  HSpace.real) from rfl]
      rw [atSpace_llamRealDVal]
      apply linearMap_ofFun_eq_of_pt _ (LinearMap.mul ℝ ℝ y)
      intro y'
      show (denotTermAux σ [.hil ⟨HSpace.real, y'⟩, .hil ⟨HSpace.real, y⟩]
            (.smul (.bvar 1) (.bvar 0))).atSpace HSpace.real =
            LinearMap.mul ℝ ℝ y y'
      show (DVal.hil ⟨_, _⟩).atSpace HSpace.real = _
      rw [atSpace_hil_self]
      show ((denotTermAux σ [.hil ⟨HSpace.real, y'⟩, .hil ⟨HSpace.real, y⟩] (.bvar 1)).asReal)
            • ((denotTermAux σ [.hil ⟨HSpace.real, y'⟩, .hil ⟨HSpace.real, y⟩] (.bvar 0)).asHil.snd)
          = y * y'
      show (DVal.hil ⟨HSpace.real, y⟩ : DVal).asReal • (DVal.hil ⟨HSpace.real, y'⟩ : DVal).asHil.snd
          = y * y'
      simp only [DVal.asReal_hil_real, DVal.asHil_hil]
      exact smul_eq_mul y y'
  | .dual s₀, sv =>
      -- Setup: freshness against s₀ (from IofFresh ε + SValid sv → FV(s₀) ⊆ ε keys).
      have sv₀ : SValid ε s₀ := by cases sv with | dual sv₀ => exact sv₀
      have h_fresh_s₀ : Term.x0 ∉ Space.fv s₀ := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv₀ h)
      have h_fresh_x1_s₀ : Term.x1 ∉ Space.fv s₀ := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv₀ h)
      set V := denotSpace σ s₀ with hV
      -- Goal: (denotSpace σ (.dual s₀)).innerProduct = (denot iof).asLinMap ...
      show (HSpace.dual V).innerProduct =
          (denotTerm σ (Space.iof (.dual s₀))).asLinMap
            (HSpace.dual V) (HSpace.dual (HSpace.dual V))
      symm
      show (denotTerm σ
          (.llam (.dual s₀) (.dual (.dual s₀))
            (.llam (.dual s₀) .real
              (Term.innerApp s₀
                (.appL (.dual s₀) s₀ (Term.sharp s₀) (.bvar 1))
                (.appL (.dual s₀) s₀ (Term.sharp s₀) (.bvar 0)))))).asLinMap
            (HSpace.dual V) (HSpace.dual (HSpace.dual V)) =
            (HSpace.dual V).innerProduct
      have h_lc_d : Space.lc (.dual s₀) := Space.lc.dual sv₀.lc
      have h_sharp_lc : Term.lc (Term.sharp s₀) := HasType.lc (Term.sharp_hasType sv₀)
      rw [denotTerm_llam_non_real (by intro h; cases h)]
      show DVal.asLinMap (HSpace.dual V) (HSpace.dual (HSpace.dual V))
        (llamTensorDVal (HSpace.dual V) (HSpace.dual (HSpace.dual V)) _) = _
      rw [asLinMap_llamTensorDVal]
      apply linearMap_ofFun_eq_of_pt _ (HSpace.dual V).innerProduct
      intro φ
      -- Inner llam reduction.
      set σ' := σ.bind Term.x0 (.hil ⟨HSpace.dual V, φ⟩) with hσ'
      -- denotSpace σ' s₀ = V (since x0 ∉ FV(s₀)).
      have h_dV : denotSpace σ' s₀ = V := denotSpace_agree s₀
        (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_s₀)
      have h_dV' : denotSpace σ' (.dual s₀) = HSpace.dual V := by
        show HSpace.dual (denotSpace σ' s₀) = HSpace.dual V
        rw [h_dV]
      -- Bridge denotTermAux σ [φ] body → denotTerm σ' (openVar x0 body).
      have h_x0_sharp : Term.x0 ∉ Term.fv (Term.sharp s₀) := fun h => by
        have hmem := (Term.sharp_hasType sv₀).fv_closure h
        rw [Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · exact absurd hmem (by simp)
        · exact fresh.fresh_x0 (Finmap.mem_keys.mp hmem)
      have hx0d_fv : Term.x0 ∉ Term.fv
          (.llam (.dual s₀) .real
            (Term.innerApp s₀
              (.appL (.dual s₀) s₀ (Term.sharp s₀) (.bvar 1))
              (.appL (.dual s₀) s₀ (Term.sharp s₀) (.bvar 0))) : Term) := by
        simp only [Term.innerApp, Term.fv, Finset.mem_union, Finset.notMem_empty, or_false]
        intro h
        repeat first
          | exact h_fresh_s₀ h
          | exact h_x0_sharp h
          | (rcases h with h | h)
      have hx0d_lc : Term.lc (Term.openVar Term.x0
          (.llam (.dual s₀) .real
            (Term.innerApp s₀
              (.appL (.dual s₀) s₀ (Term.sharp s₀) (.bvar 1))
              (.appL (.dual s₀) s₀ (Term.sharp s₀) (.bvar 0))))) := by
        simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
          Space.openRec_lc h_lc_d, Space.openRec_lc sv₀.lc, Term.openRec_lc h_sharp_lc]
        refine Term.lc.llam ∅ h_lc_d Space.lc.real (fun x _ => ?_)
        simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
          Space.openRec_lc h_lc_d, Space.openRec_lc sv₀.lc, Term.openRec_lc h_sharp_lc]
        refine Term.lc.appI sv₀.lc (Term.lc.appL sv₀.lc (Space.lc.dual sv₀.lc)
          (Term.lc.inner sv₀.lc) ?_) ?_
        · exact Term.lc.appL h_lc_d sv₀.lc h_sharp_lc Term.lc.var
        · exact Term.lc.appL h_lc_d sv₀.lc h_sharp_lc Term.lc.var
      rw [← denotTerm_openVar_bind (σ := σ) (y := Term.x0) (v := .hil ⟨HSpace.dual V, φ⟩)
            hx0d_lc hx0d_fv]
      simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
        Space.openRec_lc h_lc_d, Space.openRec_lc sv₀.lc, Term.openRec_lc h_sharp_lc]
      norm_num [Term.openRec]
      rw [← hσ']
      show (denotTerm σ'
          (.llam (.dual s₀) .real
            (Term.innerApp s₀
              (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var Term.x0))
              (.appL (.dual s₀) s₀ (Term.sharp s₀) (.bvar 0)))) ).atSpace
              (HSpace.dual (HSpace.dual V)) =
            (HSpace.dual V).innerProduct φ
      rw [denotTerm_llam_real]
      show (llamRealDVal (denotSpace σ' (.dual s₀)) _).atSpace
            (HSpace.dual (HSpace.dual V)) = _
      rw [h_dV']
      show (llamRealDVal (HSpace.dual V) _).atSpace
            (HSpace.dual (HSpace.dual V)) = _
      rw [atSpace_llamRealDVal]
      apply linearMap_ofFun_eq_of_pt _ ((HSpace.dual V).innerProduct φ)
      intro ψ
      -- Innermost body: innerApp s₀ (sharp x0) (sharp x1)
      -- = .appI s₀ (.appL s₀ s₀* (.inner s₀) (sharp_x0_app)) (sharp_x1_app)
      -- where sharp_xi_app := .appL (.dual s₀) s₀ (Term.sharp s₀) (.var xi).
      set σ'' := σ'.bind Term.x1 (.hil ⟨HSpace.dual V, ψ⟩) with hσ''
      -- Bridge inner denotTermAux σ' [ψ] body → denotTerm σ'' body_var.
      have h_x1_sharp : Term.x1 ∉ Term.fv (Term.sharp s₀) := fun h => by
        have hmem := (Term.sharp_hasType sv₀).fv_closure h
        rw [Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · exact absurd hmem (by simp)
        · exact fresh.fresh_x1 (Finmap.mem_keys.mp hmem)
      have hx1d_fv : Term.x1 ∉ Term.fv
          (Term.innerApp s₀
            (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var Term.x0))
            (.appL (.dual s₀) s₀ (Term.sharp s₀) (.bvar 0)) : Term) := by
        simp only [Term.innerApp, Term.fv, Finset.mem_union, Finset.notMem_empty, or_false,
          Finset.mem_singleton]
        intro h
        repeat first
          | exact h_fresh_x1_s₀ h | exact h_x1_sharp h | exact Term.x0_ne_x1.symm h
          | (rcases h with h | h)
      have hx1d_lc : Term.lc (Term.openVar Term.x1
          (Term.innerApp s₀
            (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var Term.x0))
            (.appL (.dual s₀) s₀ (Term.sharp s₀) (.bvar 0)))) := by
        simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
          Space.openRec_lc h_lc_d, Space.openRec_lc sv₀.lc, Term.openRec_lc h_sharp_lc]
        refine Term.lc.appI sv₀.lc (Term.lc.appL sv₀.lc (Space.lc.dual sv₀.lc)
          (Term.lc.inner sv₀.lc) ?_) ?_
        · exact Term.lc.appL h_lc_d sv₀.lc h_sharp_lc Term.lc.var
        · exact Term.lc.appL h_lc_d sv₀.lc h_sharp_lc Term.lc.var
      rw [← denotTerm_openVar_bind (σ := σ') (y := Term.x1) (v := .hil ⟨HSpace.dual V, ψ⟩)
            hx1d_lc hx1d_fv]
      simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
        Space.openRec_lc h_lc_d, Space.openRec_lc sv₀.lc, Term.openRec_lc h_sharp_lc]
      rw [← hσ'']
      have h_dV_2 : denotSpace σ'' s₀ = V :=
        (denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_x1_s₀)).trans h_dV
      have h_dV_2_dual : denotSpace σ'' (.dual s₀) = HSpace.dual V := by
        show HSpace.dual (denotSpace σ'' s₀) = HSpace.dual V
        rw [h_dV_2]
      -- Show body denot.atSpace HSpace.real = (HSpace.dual V).IP φ ψ.
      -- Body = innerApp s₀ A B = .appI s₀ (.appL s₀ (.dual s₀) (.inner s₀) A) B.
      -- A = .appL (.dual s₀) s₀ (Term.sharp s₀) (.var x0).
      -- B = .appL (.dual s₀) s₀ (Term.sharp s₀) (.var x1).
      --
      -- Bridge: (denot σ'' (Term.sharp s₀)).asLinMap V* V = rieszInv (V.IP).
      -- This uses asLinMap_denotTerm_sharp_eq_rieszInv with x0 ∉ FV(s₀).
      have h_sharp : DVal.asLinMap (HSpace.dual V) V (denotTerm σ'' (Term.sharp s₀))
          = V.innerIsIP.rieszInv := by
        have h_eq : denotSpace σ'' s₀ = V := h_dV_2
        have h_sharp_pre := asLinMap_denotTerm_sharp_eq_rieszInv σ'' s₀ sv₀ h_fresh_s₀
        -- h_sharp_pre : asLinMap (denotSpace σ'' s₀).dual (denotSpace σ'' s₀) (...)
        --              = (denotSpace σ'' s₀).innerIsIP.rieszInv
        rw [h_eq] at h_sharp_pre
        exact h_sharp_pre
      -- Compute body denot.
      -- denot σ'' (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var x0)):
      -- f := (denot σ'' (sharp s₀)).asLinMap (denotSpace σ'' (.dual s₀)) (denotSpace σ'' s₀)
      --    = rieszInv V.IP (via h_sharp, h_dV_2_dual, h_dV_2).
      -- v := (denot σ'' (var x0)).atSpace (denotSpace σ'' (.dual s₀))
      --    = (.hil ⟨V*, φ⟩).atSpace V*  (var x0 looks up σ'' which goes back to σ' = σ.bind x0 ⟨V*, φ⟩)
      --    = φ.
      -- Result: .hil ⟨V, rieszInv φ⟩.
      --
      -- Similarly for B with x1: .hil ⟨V, rieszInv ψ⟩.
      --
      -- Then .appL s₀ s₀* (inner s₀) (.hil ⟨V, rieszInv φ⟩):
      -- f := (inner s₀ denot).asLinMap V V* = V.IP.
      -- v := atSpace V (.hil ⟨V, rieszInv φ⟩) = rieszInv φ.
      -- Result: .hil ⟨V*, V.IP (rieszInv φ)⟩.
      --
      -- .appI s₀ (.hil ⟨V*, V.IP (rieszInv φ)⟩) (.hil ⟨V, rieszInv ψ⟩):
      -- φ' := asLinFunctional V of .hil ⟨V*, V.IP (rieszInv φ)⟩ = V.IP (rieszInv φ).
      -- v₁ := atSpace V of .hil ⟨V, rieszInv ψ⟩ = rieszInv ψ.
      -- Result: .hil ⟨HSpace.real, V.IP (rieszInv φ) (rieszInv ψ)⟩.
      --
      -- .atSpace HSpace.real = V.IP (rieszInv φ) (rieszInv ψ).
      --
      -- RHS: (HSpace.dual V).IP φ ψ = V.IP.compl₁₂ rieszInv rieszInv φ ψ
      --    = V.IP (rieszInv φ) (rieszInv ψ).  MATCH.
      have h_var_x0 : denotTerm σ'' (.var Term.x0) = .hil ⟨HSpace.dual V, φ⟩ := by
        show denotTerm (σ'.bind Term.x1 _) (.var Term.x0) = _
        rw [denotTerm_var_bind_other_bind_self
          (.hil ⟨HSpace.dual V, φ⟩) (.hil ⟨HSpace.dual V, ψ⟩) Term.x0_ne_x1]
      have h_var_x1 : denotTerm σ'' (.var Term.x1) = .hil ⟨HSpace.dual V, ψ⟩ := by
        show denotTerm (σ'.bind Term.x1 _) (.var Term.x1) = _
        rw [denotTerm_var_bind_self]
      -- denot σ'' (.appL (.dual s₀) s₀ (sharp s₀) (var x_i)) reduces to .hil ⟨V, rieszInv _⟩.
      have h_appL : ∀ (xi : Name) (c : V.dual.carrier),
          denotTerm σ'' (.var xi) = .hil ⟨HSpace.dual V, c⟩ →
          denotTerm σ'' (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var xi))
            = .hil ⟨V, V.innerIsIP.rieszInv c⟩ := by
        intro xi c h_var_eq
        show DVal.hil ⟨denotSpace σ'' s₀,
              ((denotTerm σ'' (Term.sharp s₀)).asLinMap
                (denotSpace σ'' (.dual s₀)) (denotSpace σ'' s₀))
              ((denotTerm σ'' (.var xi)).atSpace (denotSpace σ'' (.dual s₀)))⟩ = _
        rw [h_dV_2, h_dV_2_dual, h_sharp, h_var_eq, atSpace_hil_self]
      have h_appL_x0 := h_appL Term.x0 φ h_var_x0
      have h_appL_x1 := h_appL Term.x1 ψ h_var_x1
      -- denot σ'' (.inner s₀) = innerTensor V V.IP.
      have h_inner : denotTerm σ'' (.inner s₀) = HSpace.innerTensor V V.innerProduct := by
        show (denotSpace σ'' s₀).innerTensor (denotSpace σ'' s₀).innerProduct = _
        rw [h_dV_2]
      -- denot σ'' (.appL s₀ s₀* (inner s₀) (appL_x0))
      --   = .hil ⟨V*, V.IP (rieszInv φ)⟩.
      have h_inner_app : denotTerm σ''
            (.appL s₀ (.dual s₀) (.inner s₀)
              (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var Term.x0)))
          = .hil ⟨HSpace.dual V, V.innerProduct (V.innerIsIP.rieszInv φ)⟩ := by
        show DVal.hil ⟨denotSpace σ'' (.dual s₀),
              ((denotTerm σ'' (.inner s₀)).asLinMap
                (denotSpace σ'' s₀) (denotSpace σ'' (.dual s₀)))
              ((denotTerm σ'' (.appL (.dual s₀) s₀ (Term.sharp s₀)
                (.var Term.x0))).atSpace (denotSpace σ'' s₀))⟩ = _
        rw [h_dV_2, h_dV_2_dual, h_inner, asLinMap_innerTensor, h_appL_x0, atSpace_hil_self]
      -- Final: denot σ'' (.appI s₀ inner_app appL_x1) = .hil ⟨ℝ, V.IP (rieszInv φ) (rieszInv ψ)⟩.
      show (denotTerm σ''
            (.appI s₀
              (.appL s₀ (.dual s₀) (.inner s₀)
                (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var Term.x0)))
              (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var Term.x1)))).atSpace
              HSpace.real = (HSpace.dual V).innerProduct φ ψ
      show DVal.atSpace HSpace.real
            (DVal.hil ⟨HSpace.real,
              DVal.asLinFunctional (denotSpace σ'' s₀)
                (denotTerm σ''
                  (.appL s₀ (.dual s₀) (.inner s₀)
                    (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var Term.x0))))
              (DVal.atSpace (denotSpace σ'' s₀)
                (denotTerm σ''
                  (.appL (.dual s₀) s₀ (Term.sharp s₀) (.var Term.x1))))⟩) = _
      rw [h_dV_2, h_inner_app, asLinFunctional_hil_dual, h_appL_x1, atSpace_hil_self,
          atSpace_hil_self]
      -- Goal: V.IP (rieszInv φ) (rieszInv ψ) = (HSpace.dual V).IP φ ψ.
      -- (HSpace.dual V).IP = V.IP.compl₁₂ rieszInv rieszInv (by HSpace.dual def).
      rfl
  | .ker s₀ s₁ e, sv =>
      -- Use the fundamental-subspace helper with V_amb := V₀ = denotSpace σ s₀
      -- and K := ker f.
      have sv₀ : SValid ε s₀ := by cases sv with | ker sv₀ _ _ => exact sv₀
      have h_fresh_sub : Term.x0 ∉ Space.fv (.ker s₀ s₁ e) := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv h)
      have h_fresh_x1_sub : Term.x1 ∉ Space.fv (.ker s₀ s₁ e) := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv h)
      have h_fresh_s₀ : Term.x0 ∉ Space.fv s₀ := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv₀ h)
      have h_fresh_x1_s₀ : Term.x1 ∉ Space.fv s₀ := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv₀ h)
      exact isCanonical_fundSubspace σ (.ker s₀ s₁ e) s₀
        (denotSpace σ s₀)
        (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))
        rfl rfl rfl
        h_fresh_sub h_fresh_x1_sub h_fresh_s₀ h_fresh_x1_s₀
        h_fresh_sub h_fresh_x1_sub sv.lc sv₀.lc
  | .coker s₀ s₁ e, sv =>
      have sv₀ : SValid ε s₀ := by cases sv with | coker sv₀ _ _ => exact sv₀
      have h_fresh_sub : Term.x0 ∉ Space.fv (.coker s₀ s₁ e) := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv h)
      have h_fresh_x1_sub : Term.x1 ∉ Space.fv (.coker s₀ s₁ e) := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv h)
      have h_fresh_s₀ : Term.x0 ∉ Space.fv s₀ := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv₀ h)
      have h_fresh_x1_s₀ : Term.x1 ∉ Space.fv s₀ := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv₀ h)
      exact isCanonical_fundSubspace σ (.coker s₀ s₁ e) s₀
        (denotSpace σ s₀)
        (Submodule.orthRel (denotSpace σ s₀).innerProduct
          (LinearMap.ker ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))))
        rfl rfl rfl
        h_fresh_sub h_fresh_x1_sub h_fresh_s₀ h_fresh_x1_s₀
        h_fresh_sub h_fresh_x1_sub sv.lc sv₀.lc
  | .img s₀ s₁ e, sv =>
      have sv₁ : SValid ε s₁ := by cases sv with | img _ sv₁ _ => exact sv₁
      have h_fresh_sub : Term.x0 ∉ Space.fv (.img s₀ s₁ e) := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv h)
      have h_fresh_x1_sub : Term.x1 ∉ Space.fv (.img s₀ s₁ e) := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv h)
      have h_fresh_s₁ : Term.x0 ∉ Space.fv s₁ := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv₁ h)
      have h_fresh_x1_s₁ : Term.x1 ∉ Space.fv s₁ := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv₁ h)
      exact isCanonical_fundSubspace σ (.img s₀ s₁ e) s₁
        (denotSpace σ s₁)
        (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)))
        rfl rfl rfl
        h_fresh_sub h_fresh_x1_sub h_fresh_s₁ h_fresh_x1_s₁
        h_fresh_sub h_fresh_x1_sub sv.lc sv₁.lc
  | .coimg s₀ s₁ e, sv =>
      have sv₁ : SValid ε s₁ := by cases sv with | coimg _ sv₁ _ => exact sv₁
      have h_fresh_sub : Term.x0 ∉ Space.fv (.coimg s₀ s₁ e) := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv h)
      have h_fresh_x1_sub : Term.x1 ∉ Space.fv (.coimg s₀ s₁ e) := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv h)
      have h_fresh_s₁ : Term.x0 ∉ Space.fv s₁ := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv₁ h)
      have h_fresh_x1_s₁ : Term.x1 ∉ Space.fv s₁ := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv₁ h)
      exact isCanonical_fundSubspace σ (.coimg s₀ s₁ e) s₁
        (denotSpace σ s₁)
        (Submodule.orthRel (denotSpace σ s₁).innerProduct
          (LinearMap.range ((denotTerm σ e).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))))
        rfl rfl rfl
        h_fresh_sub h_fresh_x1_sub h_fresh_s₁ h_fresh_x1_s₁
        h_fresh_sub h_fresh_x1_sub sv.lc sv₁.lc
  | .dsum s₀ s₁, sv =>
      have sv₀ : SValid ε s₀ := by cases sv with | dsum sv₀ _ => exact sv₀
      have sv₁ : SValid ε s₁ := by cases sv with | dsum _ sv₁ => exact sv₁
      have h_fresh_s₀ : Term.x0 ∉ Space.fv s₀ := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv₀ h)
      have h_fresh_s₁ : Term.x0 ∉ Space.fv s₁ := fun h =>
        fresh.fresh_x0 (SValid.fv_closure sv₁ h)
      have h_fresh_x1_s₀ : Term.x1 ∉ Space.fv s₀ := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv₀ h)
      have h_fresh_x1_s₁ : Term.x1 ∉ Space.fv s₁ := fun h =>
        fresh.fresh_x1 (SValid.fv_closure sv₁ h)
      set V₀ := denotSpace σ s₀ with hV₀
      set V₁ := denotSpace σ s₁ with hV₁
      set V_sum := HSpace.dsum V₀ V₁ with hV_sum
      show V_sum.innerProduct = _
      symm
      show (denotTerm σ
          (.llam (.dsum s₀ s₁) (.dual (.dsum s₀ s₁))
            (.llam (.dsum s₀ s₁) .real
              (.add
                (Term.innerApp s₀
                  (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.bvar 1))
                  (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.bvar 0)))
                (Term.innerApp s₁
                  (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.bvar 1))
                  (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.bvar 0))))))).asLinMap
            V_sum (HSpace.dual V_sum) = V_sum.innerProduct
      have h_lc_sum : Space.lc (.dsum s₀ s₁) := Space.lc.dsum sv₀.lc sv₁.lc
      have h_kp0_lc : Term.lc (Term.kproj0 s₀ s₁) := HasType.lc (Term.kproj0_hasType sv₀ sv₁)
      have h_kp1_lc : Term.lc (Term.kproj1 s₀ s₁) := HasType.lc (Term.kproj1_hasType sv₀ sv₁)
      have h_x0_kp0 : Term.x0 ∉ Term.fv (Term.kproj0 s₀ s₁) := fun h => by
        have hmem := (Term.kproj0_hasType sv₀ sv₁).fv_closure h
        rw [Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · exact absurd hmem (by simp)
        · exact fresh.fresh_x0 (Finmap.mem_keys.mp hmem)
      have h_x1_kp0 : Term.x1 ∉ Term.fv (Term.kproj0 s₀ s₁) := fun h => by
        have hmem := (Term.kproj0_hasType sv₀ sv₁).fv_closure h
        rw [Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · exact absurd hmem (by simp)
        · exact fresh.fresh_x1 (Finmap.mem_keys.mp hmem)
      have h_x0_kp1 : Term.x0 ∉ Term.fv (Term.kproj1 s₀ s₁) := fun h => by
        have hmem := (Term.kproj1_hasType sv₀ sv₁).fv_closure h
        rw [Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · exact absurd hmem (by simp)
        · exact fresh.fresh_x0 (Finmap.mem_keys.mp hmem)
      have h_x1_kp1 : Term.x1 ∉ Term.fv (Term.kproj1 s₀ s₁) := fun h => by
        have hmem := (Term.kproj1_hasType sv₀ sv₁).fv_closure h
        rw [Finset.mem_union] at hmem
        rcases hmem with hmem | hmem
        · exact absurd hmem (by simp)
        · exact fresh.fresh_x1 (Finmap.mem_keys.mp hmem)
      rw [denotTerm_llam_non_real (by intro h; cases h)]
      show DVal.asLinMap V_sum (HSpace.dual V_sum)
        (llamTensorDVal V_sum (HSpace.dual V_sum) _) = _
      rw [asLinMap_llamTensorDVal]
      apply linearMap_ofFun_eq_of_pt _ V_sum.innerProduct
      intro y
      set σ' := σ.bind Term.x0 (.hil ⟨V_sum, y⟩) with hσ'
      have h_dV₀ : denotSpace σ' s₀ = V₀ :=
        denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_s₀)
      have h_dV₁ : denotSpace σ' s₁ = V₁ :=
        denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_s₁)
      have h_dSum : denotSpace σ' (.dsum s₀ s₁) = V_sum := by
        show HSpace.dsum (denotSpace σ' s₀) (denotSpace σ' s₁) = _
        rw [h_dV₀, h_dV₁]
      -- Bridge denotTermAux σ [y] body → denotTerm σ' (openVar x0 body).
      have hx0s_fv : Term.x0 ∉ Term.fv
          (.llam (.dsum s₀ s₁) .real
            (.add
              (Term.innerApp s₀
                (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.bvar 1))
                (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.bvar 0)))
              (Term.innerApp s₁
                (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.bvar 1))
                (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.bvar 0)))) : Term) := by
        simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
          or_false]
        intro h
        repeat first
          | exact h_fresh_s₀ h | exact h_fresh_s₁ h | exact h_x0_kp0 h | exact h_x0_kp1 h
          | (rcases h with h | h)
      have hx0s_lc : Term.lc (Term.openVar Term.x0
          (.llam (.dsum s₀ s₁) .real
            (.add
              (Term.innerApp s₀
                (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.bvar 1))
                (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.bvar 0)))
              (Term.innerApp s₁
                (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.bvar 1))
                (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.bvar 0)))))) := by
        simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
          Space.openRec_lc h_lc_sum, Space.openRec_lc sv₀.lc, Space.openRec_lc sv₁.lc,
          Term.openRec_lc h_kp0_lc, Term.openRec_lc h_kp1_lc]
        refine Term.lc.llam ∅ h_lc_sum Space.lc.real (fun x _ => ?_)
        simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
          Space.openRec_lc h_lc_sum, Space.openRec_lc sv₀.lc, Space.openRec_lc sv₁.lc,
          Term.openRec_lc h_kp0_lc, Term.openRec_lc h_kp1_lc]
        refine Term.lc.add (Term.lc.appI sv₀.lc (Term.lc.appL sv₀.lc (Space.lc.dual sv₀.lc)
          (Term.lc.inner sv₀.lc) (Term.lc.appL h_lc_sum sv₀.lc h_kp0_lc Term.lc.var))
          (Term.lc.appL h_lc_sum sv₀.lc h_kp0_lc Term.lc.var))
          (Term.lc.appI sv₁.lc (Term.lc.appL sv₁.lc (Space.lc.dual sv₁.lc)
          (Term.lc.inner sv₁.lc) (Term.lc.appL h_lc_sum sv₁.lc h_kp1_lc Term.lc.var))
          (Term.lc.appL h_lc_sum sv₁.lc h_kp1_lc Term.lc.var))
      rw [← denotTerm_openVar_bind (σ := σ) (y := Term.x0) (v := .hil ⟨V_sum, y⟩)
            hx0s_lc hx0s_fv]
      simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
        Space.openRec_lc h_lc_sum, Space.openRec_lc sv₀.lc, Space.openRec_lc sv₁.lc,
        Term.openRec_lc h_kp0_lc, Term.openRec_lc h_kp1_lc]
      norm_num [Term.openRec]
      rw [← hσ']
      show (denotTerm σ' _).atSpace (HSpace.dual V_sum) = V_sum.innerProduct y
      rw [denotTerm_llam_real]
      show (llamRealDVal (denotSpace σ' (.dsum s₀ s₁)) _).atSpace _ = _
      rw [h_dSum]
      rw [atSpace_llamRealDVal]
      apply linearMap_ofFun_eq_of_pt _ (V_sum.innerProduct y)
      intro y'
      set σ'' := σ'.bind Term.x1 (.hil ⟨V_sum, y'⟩) with hσ''
      -- Bridge inner denotTermAux σ' [y'] body → denotTerm σ'' body_var.
      have hx1s_fv : Term.x1 ∉ Term.fv
          (.add
            (Term.innerApp s₀
              (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var Term.x0))
              (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.bvar 0)))
            (Term.innerApp s₁
              (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var Term.x0))
              (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.bvar 0))) : Term) := by
        simp only [Term.innerApp, Term.fv, Space.fv, Finset.mem_union, Finset.notMem_empty,
          or_false, Finset.mem_singleton]
        intro h
        repeat first
          | exact h_fresh_x1_s₀ h | exact h_fresh_x1_s₁ h | exact h_x1_kp0 h | exact h_x1_kp1 h
          | exact Term.x0_ne_x1.symm h
          | (rcases h with h | h)
      have hx1s_lc : Term.lc (Term.openVar Term.x1
          (.add
            (Term.innerApp s₀
              (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var Term.x0))
              (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.bvar 0)))
            (Term.innerApp s₁
              (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var Term.x0))
              (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.bvar 0))))) := by
        simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
          Space.openRec_lc h_lc_sum, Space.openRec_lc sv₀.lc, Space.openRec_lc sv₁.lc,
          Term.openRec_lc h_kp0_lc, Term.openRec_lc h_kp1_lc]
        refine Term.lc.add (Term.lc.appI sv₀.lc (Term.lc.appL sv₀.lc (Space.lc.dual sv₀.lc)
          (Term.lc.inner sv₀.lc) (Term.lc.appL h_lc_sum sv₀.lc h_kp0_lc Term.lc.var))
          (Term.lc.appL h_lc_sum sv₀.lc h_kp0_lc Term.lc.var))
          (Term.lc.appI sv₁.lc (Term.lc.appL sv₁.lc (Space.lc.dual sv₁.lc)
          (Term.lc.inner sv₁.lc) (Term.lc.appL h_lc_sum sv₁.lc h_kp1_lc Term.lc.var))
          (Term.lc.appL h_lc_sum sv₁.lc h_kp1_lc Term.lc.var))
      rw [← denotTerm_openVar_bind (σ := σ') (y := Term.x1) (v := .hil ⟨V_sum, y'⟩)
            hx1s_lc hx1s_fv]
      simp only [Term.openVar, Term.openRec, Space.openRec, Term.openRec_innerApp,
        Space.openRec_lc h_lc_sum, Space.openRec_lc sv₀.lc, Space.openRec_lc sv₁.lc,
        Term.openRec_lc h_kp0_lc, Term.openRec_lc h_kp1_lc]
      norm_num [Term.openRec]
      rw [← hσ'']
      have h_dV₀_2 : denotSpace σ'' s₀ = V₀ :=
        (denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_x1_s₀)).trans h_dV₀
      have h_dV₁_2 : denotSpace σ'' s₁ = V₁ :=
        (denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_fresh_x1_s₁)).trans h_dV₁
      have h_dSum_2 : denotSpace σ'' (.dsum s₀ s₁) = V_sum := by
        show HSpace.dsum (denotSpace σ'' s₀) (denotSpace σ'' s₁) = _
        rw [h_dV₀_2, h_dV₁_2]
      have h_dV₀_2_dual : denotSpace σ'' (.dual s₀) = HSpace.dual V₀ := by
        show HSpace.dual (denotSpace σ'' s₀) = _; rw [h_dV₀_2]
      have h_dV₁_2_dual : denotSpace σ'' (.dual s₁) = HSpace.dual V₁ := by
        show HSpace.dual (denotSpace σ'' s₁) = _; rw [h_dV₁_2]
      -- kproj0/kproj1 bridges under σ''.
      have h_kproj0_denot : (denotTerm σ'' (Term.kproj0 s₀ s₁)).asLinMap V_sum V₀
          = LinearMap.fst ℝ V₀.carrier V₁.carrier := by
        have h := asLinMap_denotTerm_kproj0_eq_fst σ'' s₀ s₁ sv₀ sv₁ h_fresh_s₀ h_fresh_s₁
        -- h is at denotSpace σ'' which equals V₀, V₁ via h_dV₀_2, h_dV₁_2.
        rw [show denotSpace σ'' s₀ = V₀ from h_dV₀_2,
            show denotSpace σ'' s₁ = V₁ from h_dV₁_2] at h
        exact h
      have h_kproj1_denot : (denotTerm σ'' (Term.kproj1 s₀ s₁)).asLinMap V_sum V₁
          = LinearMap.snd ℝ V₀.carrier V₁.carrier := by
        have h := asLinMap_denotTerm_kproj1_eq_snd σ'' s₀ s₁ sv₀ sv₁ h_fresh_s₀
        rw [show denotSpace σ'' s₀ = V₀ from h_dV₀_2,
            show denotSpace σ'' s₁ = V₁ from h_dV₁_2] at h
        exact h
      have h_var_x0 : denotTerm σ'' (.var Term.x0) = .hil ⟨V_sum, y⟩ := by
        show denotTerm (σ'.bind Term.x1 _) (.var Term.x0) = _
        rw [denotTerm_var_bind_other_bind_self
          (.hil ⟨V_sum, y⟩) (.hil ⟨V_sum, y'⟩) Term.x0_ne_x1]
      have h_var_x1 : denotTerm σ'' (.var Term.x1) = .hil ⟨V_sum, y'⟩ := by
        show denotTerm (σ'.bind Term.x1 _) (.var Term.x1) = _
        rw [denotTerm_var_bind_self]
      -- denot σ'' (.appL sum s₀ kproj0 (var xi)) = .hil ⟨V₀, yi.1⟩.
      have h_appL_0 : ∀ (xi : Name) (c : V_sum.carrier),
          denotTerm σ'' (.var xi) = .hil ⟨V_sum, c⟩ →
          denotTerm σ'' (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var xi))
            = .hil ⟨V₀, c.1⟩ := by
        intro xi c h_var_eq
        show DVal.hil ⟨denotSpace σ'' s₀,
              ((denotTerm σ'' (Term.kproj0 s₀ s₁)).asLinMap
                (denotSpace σ'' (.dsum s₀ s₁)) (denotSpace σ'' s₀))
              ((denotTerm σ'' (.var xi)).atSpace (denotSpace σ'' (.dsum s₀ s₁)))⟩ = _
        rw [h_dV₀_2, h_dSum_2, h_kproj0_denot, h_var_eq, atSpace_hil_self]
        rfl
      have h_appL_1 : ∀ (xi : Name) (c : V_sum.carrier),
          denotTerm σ'' (.var xi) = .hil ⟨V_sum, c⟩ →
          denotTerm σ'' (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var xi))
            = .hil ⟨V₁, c.2⟩ := by
        intro xi c h_var_eq
        show DVal.hil ⟨denotSpace σ'' s₁,
              ((denotTerm σ'' (Term.kproj1 s₀ s₁)).asLinMap
                (denotSpace σ'' (.dsum s₀ s₁)) (denotSpace σ'' s₁))
              ((denotTerm σ'' (.var xi)).atSpace (denotSpace σ'' (.dsum s₀ s₁)))⟩ = _
        rw [h_dV₁_2, h_dSum_2, h_kproj1_denot, h_var_eq, atSpace_hil_self]
        rfl
      have h_appL_0_x0 := h_appL_0 Term.x0 y h_var_x0
      have h_appL_0_x1 := h_appL_0 Term.x1 y' h_var_x1
      have h_appL_1_x0 := h_appL_1 Term.x0 y h_var_x0
      have h_appL_1_x1 := h_appL_1 Term.x1 y' h_var_x1
      have h_inner_0 : denotTerm σ'' (.inner s₀)
          = HSpace.innerTensor V₀ V₀.innerProduct := by
        show (denotSpace σ'' s₀).innerTensor (denotSpace σ'' s₀).innerProduct = _
        rw [h_dV₀_2]
      have h_inner_1 : denotTerm σ'' (.inner s₁)
          = HSpace.innerTensor V₁ V₁.innerProduct := by
        show (denotSpace σ'' s₁).innerTensor (denotSpace σ'' s₁).innerProduct = _
        rw [h_dV₁_2]
      have h_inner_app_0 : denotTerm σ''
            (.appL s₀ (.dual s₀) (.inner s₀)
              (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var Term.x0)))
          = .hil ⟨HSpace.dual V₀, V₀.innerProduct y.1⟩ := by
        show DVal.hil ⟨denotSpace σ'' (.dual s₀),
              ((denotTerm σ'' (.inner s₀)).asLinMap
                (denotSpace σ'' s₀) (denotSpace σ'' (.dual s₀)))
              ((denotTerm σ'' (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁)
                (.var Term.x0))).atSpace (denotSpace σ'' s₀))⟩ = _
        rw [h_dV₀_2, h_dV₀_2_dual, h_inner_0, asLinMap_innerTensor,
            h_appL_0_x0, atSpace_hil_self]
      have h_inner_app_1 : denotTerm σ''
            (.appL s₁ (.dual s₁) (.inner s₁)
              (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var Term.x0)))
          = .hil ⟨HSpace.dual V₁, V₁.innerProduct y.2⟩ := by
        show DVal.hil ⟨denotSpace σ'' (.dual s₁),
              ((denotTerm σ'' (.inner s₁)).asLinMap
                (denotSpace σ'' s₁) (denotSpace σ'' (.dual s₁)))
              ((denotTerm σ'' (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁)
                (.var Term.x0))).atSpace (denotSpace σ'' s₁))⟩ = _
        rw [h_dV₁_2, h_dV₁_2_dual, h_inner_1, asLinMap_innerTensor,
            h_appL_1_x0, atSpace_hil_self]
      -- denot σ'' (innerApp s₀ ... ...) at HSpace.real = V₀.IP y.1 y'.1.
      have h_innerApp_0 : denotTerm σ''
            (Term.innerApp s₀
              (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var Term.x0))
              (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var Term.x1)))
          = .hil ⟨HSpace.real, V₀.innerProduct y.1 y'.1⟩ := by
        show denotTerm σ''
              (.appI s₀
                (.appL s₀ (.dual s₀) (.inner s₀)
                  (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var Term.x0)))
                (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var Term.x1))) = _
        show DVal.hil ⟨HSpace.real,
              DVal.asLinFunctional (denotSpace σ'' s₀)
                (denotTerm σ''
                  (.appL s₀ (.dual s₀) (.inner s₀)
                    (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var Term.x0))))
              (DVal.atSpace (denotSpace σ'' s₀)
                (denotTerm σ''
                  (.appL (.dsum s₀ s₁) s₀ (Term.kproj0 s₀ s₁) (.var Term.x1))))⟩ = _
        rw [h_dV₀_2, h_inner_app_0, asLinFunctional_hil_dual, h_appL_0_x1,
            atSpace_hil_self]
      have h_innerApp_1 : denotTerm σ''
            (Term.innerApp s₁
              (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var Term.x0))
              (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var Term.x1)))
          = .hil ⟨HSpace.real, V₁.innerProduct y.2 y'.2⟩ := by
        show denotTerm σ''
              (.appI s₁
                (.appL s₁ (.dual s₁) (.inner s₁)
                  (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var Term.x0)))
                (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var Term.x1))) = _
        show DVal.hil ⟨HSpace.real,
              DVal.asLinFunctional (denotSpace σ'' s₁)
                (denotTerm σ''
                  (.appL s₁ (.dual s₁) (.inner s₁)
                    (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var Term.x0))))
              (DVal.atSpace (denotSpace σ'' s₁)
                (denotTerm σ''
                  (.appL (.dsum s₀ s₁) s₁ (Term.kproj1 s₀ s₁) (.var Term.x1))))⟩ = _
        rw [h_dV₁_2, h_inner_app_1, asLinFunctional_hil_dual, h_appL_1_x1,
            atSpace_hil_self]
      -- .add of the two innerApp results = .hil ⟨ℝ, V₀.IP y.1 y'.1 + V₁.IP y.2 y'.2⟩.
      -- atSpace HSpace.real = V₀.IP y.1 y'.1 + V₁.IP y.2 y'.2.
      -- RHS = V_sum.IP y y' = V₀.IP y.1 y'.1 + V₁.IP y.2 y'.2 (by HSpace.dsum def).
      rw [denotTerm_add_real σ'' _ _ _ _ h_innerApp_0 h_innerApp_1]
      rw [atSpace_hil_self]
      rfl
  | .tprod s₀ s₁, sv =>
      have sv₀ : SValid ε s₀ := by cases sv with | tprod sv₀ _ => exact sv₀
      have sv₁ : SValid ε s₁ := by cases sv with | tprod _ sv₁ => exact sv₁
      -- LHS = V_tprod.IP = BilinForm.tmul V₀.IP V₁.IP (by HSpace.tprod def).
      -- RHS = denot iof.asLinMap V_tprod V_tprod*. Bridge below shows this
      -- equals BilinForm.tmul V₀.IP V₁.IP (= LHS).
      exact asLinMap_iof_tprod fresh sv₀ sv₁ env_wf ctx_ε

/-- Default `IofFresh` for empty ε — all binder names are trivially fresh. -/
def IofFresh.empty : IofFresh ∅ where
  fresh_x0 := by simp [Finmap.notMem_empty]
  fresh_x1 := by simp [Finmap.notMem_empty]
  fresh_y00 := by simp [Finmap.notMem_empty]
  fresh_y01 := by simp [Finmap.notMem_empty]
  fresh_y10 := by simp [Finmap.notMem_empty]
  fresh_y11 := by simp [Finmap.notMem_empty]
  fresh_g := by simp [Finmap.notMem_empty]
  fresh_a := by simp [Finmap.notMem_empty]
  fresh_b := by simp [Finmap.notMem_empty]
  fresh_p := by simp [Finmap.notMem_empty]

theorem exists_canonical_DEnv_empty :
    ∃ σ : DEnv, σ.IsCanonical ∅ ∧ EnvWF σ ∅ ∅ := by
  have env_wf_empty : EnvWF (⟨∅⟩ : DEnv) ∅ ∅ := {
    lin_match := fun x s hx => by simp [Finmap.lookup_empty] at hx
    nl_match := fun x τ hx => by simp [Finmap.lookup_empty] at hx
  }
  have ctx_empty : CtxWF (∅ : LCtx) ∅ := {
    disjoint := fun x hx _ => by exact Finmap.notMem_empty hx
    lin_fv_in_ε := fun x s hx z _ => by simp [Finmap.lookup_empty] at hx
    nl_fv_in_ε := fun x τ hx z _ => by simp [Finmap.lookup_empty] at hx
  }
  exact ⟨⟨∅⟩, DEnv.IsCanonical_holds _ _ IofFresh.empty env_wf_empty ctx_empty,
    env_wf_empty⟩

/-- **Existence of a canonical σ for any ε** (with `IofFresh ε`). -/
theorem exists_canonical_DEnv {σ : DEnv} (ε : NLCtx)
    (fresh : IofFresh ε) (env_wf : EnvWF σ ∅ ε) (ctx : CtxWF ∅ ε) :
    σ.IsCanonical ε :=
  DEnv.IsCanonical_holds _ _ fresh env_wf ctx

theorem Space.iof_denot_isInnerProduct
    {σ : DEnv} {ε : NLCtx} (fresh : IofFresh ε)
    (env_wf : EnvWF σ ∅ ε) (ctx : CtxWF ∅ ε)
    {s : Space} (sv : SValid ε s) :
    IsInnerProduct
      ((denotTerm σ (Space.iof s)).asLinMap
        (denotSpace σ s) (HSpace.dual (denotSpace σ s))) :=
  Space.iof_denot_isInnerProduct_canonical
    (DEnv.IsCanonical_holds σ ε fresh env_wf ctx) sv

theorem applyUncurry2NonReal_denot_tmul
    {σ : DEnv} {ε : NLCtx} {sA sB sR : Space}
    (fresh : IofFresh ε) (hR : sR ≠ .real)
    (hA : SValid ε sA) (hB : SValid ε sB) (hC : SValid ε sR)
    (henv : EnvWF σ ∅ ε) (hctx : CtxWF ∅ ε)
    (f : Term) (a : (denotSpace σ sA).carrier) (b : (denotSpace σ sB).carrier) :
    (denotTerm σ (Term.applyUncurry2NonReal sA sB sR f)).asLinMap
      (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)) (denotSpace σ sR)
      (a ⊗ₜ[ℝ] b) =
    dualTensorHom ℝ (denotSpace σ sB).carrier (denotSpace σ sR).carrier
      (dualTensorHom ℝ (denotSpace σ sA).carrier
        (denotSpace σ (.tprod (.dual sB) sR)).carrier
        ((denotTerm σ f).atSpace
          (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sR)))) a) b := by
  have hga : Term.g_name ≠ Term.a_name := by decide
  have hgb : Term.g_name ≠ Term.b_name := by decide
  have hab : Term.a_name ≠ Term.b_name := by decide
  have hm : (denotTerm σ (Term.applyUncurry2NonReal sA sB sR f)).matchesShape
      (.hil (HSpace.tprod (HSpace.dual (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)))
        (denotSpace σ sR))) := by
    rw [Term.applyUncurry2NonReal, denotTerm_appL]
    rfl
  rw [DVal.asLinMap_eq_of_matchesShape hm]
  rw [← curry2NonReal_chain_app_eq fresh.fresh_g fresh.fresh_a fresh.fresh_b
    hga hgb hab hR hA hB hC henv hctx]
  have he : (denotTerm σ (Term.applyUncurry2NonReal sA sB sR f)).atSpace
      (HSpace.tprod (HSpace.dual (HSpace.tprod (denotSpace σ sA) (denotSpace σ sB)))
        (denotSpace σ sR)) =
      (denotTerm σ (Term.uncurry2NonReal sA sB sR)).asLinMap
        (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sR)))
        (denotSpace σ (.tprod (.dual (.tprod sA sB)) sR))
        ((denotTerm σ f).atSpace
          (denotSpace σ (.tprod (.dual sA) (.tprod (.dual sB) sR)))) := by
    rw [Term.applyUncurry2NonReal, denotTerm_appL]
    exact atSpace_hil_self _ _
  rw [he, curry2NonReal_uncurry2NonReal_id fresh.fresh_g fresh.fresh_a fresh.fresh_b
    hga hgb hab hR hA hB hC henv hctx]

end GLang
