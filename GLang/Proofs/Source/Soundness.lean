

import GLang.Annotated.Binding
import GLang.Proofs.Source.FreeVars
import GLang.Annotated.Judgments
import GLang.Annotated.Denotation
import GLang.Proofs.Source.FVIrrelevance
import GLang.Proofs.Source.Wellformed
import GLang.Proofs.Source.Substitution
import GLang.Proofs.Source.Regularity
import Mathlib.Algebra.Module.LinearMap.Defs

namespace GLang

open scoped TensorProduct

/-- The linearity claim (b): when `τ` is a vector type `.space s_τ`, the
function `y : (denotSpace σ s).carrier ↦ (denotTerm (σ.bind x ⟨V_s, y⟩) e)
.atSpace (denotSpace σ s_τ)` is a ℝ-linear map. For piTy result types,
the claim is vacuous (no vector-space structure on a set of sections).

With (a) using `matchesShape`, the `.atSpace` extraction at the body's
denotation has no cast: the body's `.asHil.fst` *equals* `denotSpace σ' s_τ`
exactly (and via FV-irrelevance, `denotSpace σ s_τ` since x ∉ Space.fv s_τ
under Barendregt). -/
def LinearAtVar (σ : DEnv) (x : Name) (s : Space) (e : Term) : Ty → Prop
  | .space s_τ =>
      IsLinearMap ℝ (fun y : (denotSpace σ s).carrier =>
        (denotTerm (σ.bind x (.hil ⟨denotSpace σ s, y⟩)) e).atSpace
          (denotSpace σ s_τ))
  | .piTy _ _ => True

def SoundClaim (σ : DEnv) (Δ : LCtx) (e : Term) (τ : Ty) : Prop :=
  (denotTerm σ e).matchesShape (denotTy σ τ) ∧
  ∀ x s, Δ.lookup x = some s → LinearAtVar σ x s e τ

/-! ## Inversion helpers for CtxWF / EnvWF over sub-contexts. -/

namespace CtxWF

/-- A linear sub-context inherits well-formedness. -/
theorem of_sub_Δ {Δ Δ' : LCtx} {ε : NLCtx}
    (h : CtxWF Δ ε) (hsub : ∀ x s, Δ'.lookup x = some s → Δ.lookup x = some s) :
    CtxWF Δ' ε where
  disjoint x hx := by
    rcases Finmap.mem_iff.mp hx with ⟨s, hs⟩
    exact h.disjoint x (Finmap.mem_iff.mpr ⟨s, hsub x s hs⟩)
  lin_fv_in_ε x s hx := h.lin_fv_in_ε x s (hsub x s hx)
  nl_fv_in_ε := h.nl_fv_in_ε

/-- Extend `CtxWF` by a non-linear binding `x ↦ τ₀`. -/
theorem insert_nl {Δ : LCtx} {ε : NLCtx}
    (ctx : CtxWF Δ ε)
    {x : Name} {τ₀ : Ty}
    (hx_not_Δ : x ∉ Δ) (_hx_not_ε : x ∉ ε)
    (h_fv_τ₀ : Ty.fv τ₀ ⊆ ε.keys) :
    CtxWF Δ (Finmap.insert x τ₀ ε) where
  disjoint x' hx' := by
    -- x' ∈ Δ ⇒ x' ∉ ε (outer disjoint). And x' ≠ x because x ∉ Δ.
    intro hx'_in_insert
    rcases Finmap.mem_insert.mp hx'_in_insert with heq | hx'_in_ε
    · exact hx_not_Δ (heq ▸ hx')
    · exact ctx.disjoint x' hx' hx'_in_ε
  lin_fv_in_ε x' s' hx' z hz :=
    -- ctx.lin_fv_in_ε gives z ∈ ε; insert preserves it.
    Finmap.mem_insert.mpr (Or.inr (ctx.lin_fv_in_ε x' s' hx' z hz))
  nl_fv_in_ε x' τ' hx' z hz := by
    by_cases hx'_eq : x' = x
    · -- x' = x: τ' = τ₀, use the Barendregt closure hypothesis.
      subst x'
      rw [Finmap.lookup_insert] at hx'
      have h_eq : τ' = τ₀ := (Option.some.inj hx').symm
      rw [h_eq] at hz
      exact Finmap.mem_insert.mpr (Or.inr (Finmap.mem_keys.mp (h_fv_τ₀ hz)))
    · -- x' ≠ x: use outer ctx.nl_fv_in_ε.
      rw [Finmap.lookup_insert_of_ne _ hx'_eq] at hx'
      exact Finmap.mem_insert.mpr (Or.inr (ctx.nl_fv_in_ε x' τ' hx' z hz))

end CtxWF

namespace EnvWF

/-- An EnvWF over the union of two disjoint linear contexts restricts
    to either summand. Left-biased union (Mathlib's `Finmap.union`)
    makes `Δ₀.lookup x = some s → (Δ₀ ∪ Δ₁).lookup x = some s` trivial,
    so values inherit. -/
theorem of_sub_Δ {σ : DEnv} {Δ Δ' : LCtx} {ε : NLCtx}
    (h : EnvWF σ Δ ε) (hsub : ∀ x s, Δ'.lookup x = some s → Δ.lookup x = some s) :
    EnvWF σ Δ' ε where
  lin_match x s hx := h.lin_match x s (hsub x s hx)
  nl_match := h.nl_match

end EnvWF

namespace DVal

/-- `.hil ⟨V, v⟩` matches `HType.hil V'` exactly when `V = V'`. -/
theorem matchesShape_hil (V V' : HSpace) (v : V.carrier) (h : V = V') :
    (DVal.hil ⟨V, v⟩).matchesShape (.hil V') := by
  unfold matchesShape shape
  rw [h]

theorem matchesShape_hil_rfl (V : HSpace) (v : V.carrier) :
    (DVal.hil ⟨V, v⟩).matchesShape (.hil V) :=
  matchesShape_hil V V v rfl

/-- `.pi T f` matches `HType.sec T g` when their codomain functions
    agree pointwise (in `matchesShape`). -/
theorem matchesShape_pi (T : Type) (f : T → DVal) (g : T → HType)
    (h : ∀ y, (f y).matchesShape (g y)) :
    (DVal.pi T f).matchesShape (.sec T g) := by
  unfold matchesShape shape
  congr 1
  funext y
  exact h y

/-- Inversion: from `matchesShape` on `.hil V`, extract the HSpace
    equality on the value's `.asHil.fst`. -/
theorem matchesShape_hil_asHil_fst {v : DVal} {V : HSpace}
    (h : v.matchesShape (.hil V)) : v.asHil.fst = V := by
  cases v with
  | hil h_elem =>
      obtain ⟨V', _⟩ := h_elem
      simp only [matchesShape, shape] at h
      cases h
      rfl
  | pi _ _ =>
      simp only [matchesShape, shape] at h
      exact HType.noConfusion h

/-- Inversion: from `matchesShape` on `.hil V`, the value is `.hil ⟨V, _⟩`
    for some content (with HSpace `V` exactly, not just carrier-equal). -/
theorem matchesShape_hil_eq {v : DVal} {V : HSpace}
    (h : v.matchesShape (.hil V)) : ∃ v', v = .hil ⟨V, v'⟩ := by
  cases v with
  | hil h_elem =>
      obtain ⟨V', v'⟩ := h_elem
      simp only [matchesShape, shape] at h
      cases h
      exact ⟨v', rfl⟩
  | pi _ _ =>
      simp only [matchesShape, shape] at h
      exact HType.noConfusion h

/-- Inversion: from `matchesShape` on `.sec T g`, the value is
    `.pi T f` with `(f y).matchesShape (g y)` for all `y`. -/
theorem matchesShape_sec_eq {v : DVal} {T : Type} {g : T → HType}
    (h : v.matchesShape (.sec T g)) :
    ∃ f : T → DVal, v = .pi T f ∧ ∀ y, (f y).matchesShape (g y) := by
  cases v with
  | hil _ =>
      simp only [matchesShape, shape] at h
      exact HType.noConfusion h
  | pi T' f' =>
      simp only [matchesShape, shape] at h
      -- h : HType.sec T' (fun y => (f' y).shape) = HType.sec T g
      injection h with h_T h_g
      subst h_T
      -- h_g : (fun y => (f' y).shape) ≍ g (HEq; both sides T → HType)
      have h_g' : (fun y => (f' y).shape) = g := eq_of_heq h_g
      refine ⟨f', rfl, ?_⟩
      intro y
      show (f' y).shape = g y
      rw [← h_g']

/-- `.atSpace V` on a `.hil ⟨V, v⟩` (same `V`) returns `v` — the Classical
    cast resolves to identity. -/
@[simp] theorem atSpace_hil_self (V : HSpace) (v : V.carrier) :
    (DVal.hil ⟨V, v⟩).atSpace V = v := by
  unfold atSpace asHil
  simp

end DVal

/-- Round-trip: `T.embed (T.extract d) = d` when `d` deeply matches `T`.
    Used in `.app_nonlinear`'s soundness to align the body's denotation
    with the substituted form. -/
theorem HType.embed_extract_of_matchesShape :
    ∀ {T : HType} {d : DVal}, d.matchesShape T →
      T.embed (T.extract d) = d
  | .hil V, d, h => by
      obtain ⟨v, rfl⟩ := DVal.matchesShape_hil_eq h
      simp [HType.extract, HType.embed]
  | .sec T_dom f, d, h => by
      obtain ⟨g, rfl, hg⟩ := DVal.matchesShape_sec_eq h
      simp only [HType.extract, HType.embed, dite_true]
      refine congrArg (DVal.pi T_dom) ?_
      funext y
      exact HType.embed_extract_of_matchesShape (hg y)

/-- The shape of `T.embed v` is exactly `T`. By induction on `T`. -/
theorem HType.embed_shape : ∀ (T : HType) (v : T.El), (T.embed v).shape = T
  | .hil _, _ => rfl
  | .sec T_dom f, g => by
      show HType.sec T_dom (fun y => (HType.embed (f y) (g y)).shape) =
           HType.sec T_dom f
      congr 1
      funext y
      exact HType.embed_shape (f y) (g y)

/-- `T.embed v` matchesShape `T` — alias for `embed_shape`. -/
theorem HType.embed_matchesShape (T : HType) (v : T.El) :
    (T.embed v).matchesShape T :=
  HType.embed_shape T v

namespace DVal

/-- `.atSpace V` of `.hil ⟨V, 0⟩` is `0`. (Special case of `atSpace_hil_self`.) -/
theorem atSpace_hil_zero_same (V : HSpace) :
    (DVal.hil ⟨V, (0 : V.carrier)⟩).atSpace V = 0 :=
  atSpace_hil_self V 0

/-- `DVal.addAt`'s result has the same outer HSpace as its left operand. -/
@[simp] theorem addAt_asHil_fst (d₀ d₁ : DVal) :
    (d₀.addAt d₁).asHil.fst = d₀.asHil.fst := by
  simp only [DVal.addAt, DVal.asHil]
  split_ifs <;> rfl

/-- `.atSpace V` of a value with `matchesShape (.hil V)` extracts the
    underlying carrier value. Uses `matchesShape`'s HSpace equality to
    sidestep the `atSpace` cast. -/
theorem atSpace_of_matchesShape {v : DVal} {V : HSpace}
    (h : v.matchesShape (.hil V)) :
    ∃ v', v = .hil ⟨V, v'⟩ ∧ v.atSpace V = v' := by
  obtain ⟨v', rfl⟩ := matchesShape_hil_eq h
  exact ⟨v', rfl, atSpace_hil_self V v'⟩

/-- Cast-free addition lemma. When both operands have `matchesShape
    (.hil V)`, their `addAt` followed by `atSpace V` is the literal sum
    of each operand's `atSpace V`. No cast machinery required. -/
theorem addAt_atSpace_eq_add {d₀ d₁ : DVal} {V : HSpace}
    (h₀ : d₀.matchesShape (.hil V)) (h₁ : d₁.matchesShape (.hil V)) :
    (d₀.addAt d₁).atSpace V = d₀.atSpace V + d₁.atSpace V := by
  obtain ⟨v₀, rfl⟩ := matchesShape_hil_eq h₀
  obtain ⟨v₁, rfl⟩ := matchesShape_hil_eq h₁
  simp [addAt, asHil, atSpace_hil_self]
  rfl

/-- Scalar-mult variant: when `d` has `matchesShape (.hil V)`, scaling
    its `asHil` content by `r` and re-bundling gives `r • (d.atSpace V)`
    after re-extraction. -/
theorem smul_hil_atSpace_eq {d : DVal} {V : HSpace} (r : ℝ)
    (h : d.matchesShape (.hil V)) :
    (DVal.hil ⟨d.asHil.fst, r • d.asHil.snd⟩).atSpace V
      = r • (d.atSpace V) := by
  obtain ⟨v, rfl⟩ := matchesShape_hil_eq h
  simp [asHil, atSpace_hil_self]
  rfl

/-- Pair-construction variant: when `d_i` has `matchesShape (.hil V_i)`,
    bundling their snds into an HSpace.dsum and extracting at the dsum
    target gives the pair of each operand's `atSpace V_i`. -/
theorem dsumE_atSpace_eq {d₀ d₁ : DVal} {V₀ V₁ : HSpace}
    (h₀ : d₀.matchesShape (.hil V₀)) (h₁ : d₁.matchesShape (.hil V₁)) :
    (DVal.hil ⟨HSpace.dsum d₀.asHil.fst d₁.asHil.fst,
                (d₀.asHil.snd, d₁.asHil.snd)⟩).atSpace (HSpace.dsum V₀ V₁)
      = (d₀.atSpace V₀, d₁.atSpace V₁) := by
  obtain ⟨v₀, rfl⟩ := matchesShape_hil_eq h₀
  obtain ⟨v₁, rfl⟩ := matchesShape_hil_eq h₁
  simp [asHil, atSpace_hil_self]

/-- Tensor-product variant: analogous to `dsumE_atSpace_eq` but for
    `HSpace.tprod` / `⊗ₜ`. -/
theorem tprodE_atSpace_eq {d₀ d₁ : DVal} {V₀ V₁ : HSpace}
    (h₀ : d₀.matchesShape (.hil V₀)) (h₁ : d₁.matchesShape (.hil V₁)) :
    (DVal.hil ⟨HSpace.tprod d₀.asHil.fst d₁.asHil.fst,
                d₀.asHil.snd ⊗ₜ[ℝ] d₁.asHil.snd⟩).atSpace (HSpace.tprod V₀ V₁)
      = d₀.atSpace V₀ ⊗ₜ[ℝ] d₁.atSpace V₁ := by
  obtain ⟨v₀, rfl⟩ := matchesShape_hil_eq h₀
  obtain ⟨v₁, rfl⟩ := matchesShape_hil_eq h₁
  simp only [asHil, atSpace_hil_self]
  rfl

/-- When `d` has `matchesShape (.hil (HSpace.tprod (HSpace.dual V₀) V₁))`,
    its `asLinMap` is `dualTensorHom` of its `atSpace` at the same
    HSpace.tprod. -/
theorem asLinMap_eq_of_matchesShape {d : DVal} {V₀ V₁ : HSpace}
    (h : d.matchesShape (.hil (HSpace.tprod (HSpace.dual V₀) V₁))) :
    d.asLinMap V₀ V₁ = dualTensorHom ℝ V₀.carrier V₁.carrier
      (d.atSpace (HSpace.tprod (HSpace.dual V₀) V₁)) := by
  obtain ⟨t, rfl⟩ := matchesShape_hil_eq h
  simp [asLinMap, asHil, atSpace_hil_self]

/-- When `d` has `matchesShape (.hil (HSpace.dual V))`, its `asLinFunctional`
    is the underlying carrier value (a linear functional). -/
theorem asLinFunctional_eq_of_matchesShape {d : DVal} {V : HSpace}
    (h : d.matchesShape (.hil (HSpace.dual V))) :
    d.asLinFunctional V = d.atSpace (HSpace.dual V) := by
  obtain ⟨φ, rfl⟩ := matchesShape_hil_eq h
  simp [asLinFunctional, asHil, atSpace_hil_self]

/-! ### Frame-transport helpers for `asLinMap` / `atSpace`.

When two HSpaces are propositionally equal (typically via FV-irrelevance:
`denotSpace σ s = denotSpace σ' s` when `σ.AgreeOn σ' (Space.fv s)`), the
`asLinMap` and `atSpace` operations on a DVal give the "same value" modulo
type transport. These helpers consolidate the `subst`/`HEq` pattern that
would otherwise be repeated at each chain layer.

Usage: when chaining `asLinMap` calls at σ-frame and σ_g-frame V's,
use `asLinMap_apply_HEq_of_HSpace_eq` to bridge. -/

/-- `asLinMap V₀ V₁ d` at propositionally-equal HSpaces gives HEq LinearMaps. -/
theorem asLinMap_HEq_of_HSpace_eq
    {V₀ V₀' V₁ V₁' : HSpace} (h₀ : V₀ = V₀') (h₁ : V₁ = V₁') (d : DVal) :
    HEq (d.asLinMap V₀ V₁) (d.asLinMap V₀' V₁') := by
  subst h₀; subst h₁; rfl

/-- `asLinMap` applied at a value: HEq of results when HSpaces match
    propositionally and values are HEq. -/
theorem asLinMap_apply_HEq_of_HSpace_eq
    {V₀ V₀' V₁ V₁' : HSpace} (h₀ : V₀ = V₀') (h₁ : V₁ = V₁')
    {d : DVal} {v : V₀.carrier} {v' : V₀'.carrier} (hv : HEq v v') :
    HEq (d.asLinMap V₀ V₁ v) (d.asLinMap V₀' V₁' v') := by
  subst h₀; subst h₁
  cases hv
  rfl

/-- `atSpace` at propositionally-equal HSpaces gives HEq results. -/
theorem atSpace_HEq_of_HSpace_eq
    {V V' : HSpace} (h : V = V') (d : DVal) :
    HEq (d.atSpace V) (d.atSpace V') := by
  subst h; rfl

end DVal

/-! ## Single-step `denotTerm` unfolding lemmas.

These avoid `unfold denotTerm`'s tendency to unfold *all* `denotTerm`
occurrences in the goal (including inside subterm denotations), which
produces unreadable match-explosion goals.  -/

/-- D1 wrapper-form: a `.space` type denotes to `HType.hil` of the wrapper
    `denotSpace`. Used to expose the wrapper (not `denotSpaceAux`) head in IH
    types so the `denotSpace_agree` rewrites match. -/
theorem denotTy_space (σ : DEnv) (s : Space) :
    denotTy σ (.space s) = HType.hil (denotSpace σ s) := rfl

theorem denotTerm_appL (σ : DEnv) (s₀ s₁ : Space) (e₀ e₁ : Term) :
    denotTerm σ (.appL s₀ s₁ e₀ e₁) =
      .hil ⟨denotSpace σ s₁,
            ((denotTerm σ e₀).asLinMap (denotSpace σ s₀) (denotSpace σ s₁))
              ((denotTerm σ e₁).atSpace (denotSpace σ s₀))⟩ := rfl

theorem denotTerm_appI (σ : DEnv) (s : Space) (e₀ e₁ : Term) :
    denotTerm σ (.appI s e₀ e₁) =
      .hil ⟨HSpace.real,
            ((denotTerm σ e₀).asLinFunctional (denotSpace σ s))
              ((denotTerm σ e₁).atSpace (denotSpace σ s))⟩ := rfl

theorem denotTerm_llam_real (σ : DEnv) (s₀ : Space) (body : Term) :
    denotTerm σ (.llam s₀ Space.real body) =
      llamRealDVal (denotSpace σ s₀)
        (fun v => (denotTermAux σ [v] body).atSpace HSpace.real) := rfl

theorem denotTerm_llam_non_real {s : Space} (h : s ≠ .real)
    (σ : DEnv) (s₀ : Space) (body : Term) :
    denotTerm σ (.llam s₀ s body) =
      llamTensorDVal (denotSpace σ s₀) (denotSpace σ s)
        (fun v => denotTermAux σ [v] body) := by
  cases s with
  | real => exact absurd rfl h
  | empty | dual _ | dsum _ _ | tprod _ _
  | ker _ _ _ | coker _ _ _ | img _ _ _ | coimg _ _ _ => rfl

namespace DVal

end DVal

/-! ## DEnv.AgreeOn helpers used in the soundness proof. -/

/-! ## Environment-rebinding lemma.

Lives here (after `DVal.matchesShape_*` and `DEnv.AgreeOn` helpers,
before the soundness mutual block) so it has access to FV-irrelevance
(`denotSpace_agree`, `denotTy_agree`) and the matchesShape API. -/

namespace EnvWF

/-- Re-bind a linear variable `x ∈ Δ` to a fresh element `y` of its
    space. The new environment remains well-formed against the same
    context — by FV-irrelevance (`denotSpace_agree`, `denotTy_agree`)
    plus Barendregt (`x ∉ Space.fv s'` for any `s'` bound elsewhere in
    `Δ ∪ ε`, derived from `CtxWF.lin_fv_in_ε` / `nl_fv_in_ε` and
    `disjoint`). -/
theorem bind_lin {σ : DEnv} {Δ : LCtx} {ε : NLCtx}
    (wf : EnvWF σ Δ ε) (ctx : CtxWF Δ ε)
    {x : Name} {s : Space} (hx : Δ.lookup x = some s)
    (y : (denotSpace σ s).carrier) :
    EnvWF (σ.bind x (.hil ⟨denotSpace σ s, y⟩)) Δ ε where
  lin_match x' s' hx' := by
    have hx_in_Δ : x ∈ Δ := Finmap.mem_iff.mpr ⟨s, hx⟩
    have hx_not_ε : x ∉ ε := ctx.disjoint x hx_in_Δ
    have hx_not_fv : x ∉ Space.fv s' := fun hin =>
      hx_not_ε (ctx.lin_fv_in_ε x' s' hx' x hin)
    have hagree : (σ.bind x (.hil ⟨denotSpace σ s, y⟩)).AgreeOn σ (Space.fv s') :=
      DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv
    have hd : denotSpace (σ.bind x (.hil ⟨denotSpace σ s, y⟩)) s' = denotSpace σ s' :=
      denotSpace_agree s' hagree
    by_cases h_eq : x' = x
    · subst h_eq
      have hs : s' = s := by
        rw [hx] at hx'
        exact ((Option.some.injEq _ _).mp hx').symm
      subst hs
      refine ⟨.hil ⟨denotSpace σ s', y⟩, ?_, ?_⟩
      · simp [DEnv.bind, Finmap.lookup_insert]
      · rw [hd]; exact DVal.matchesShape_hil_rfl _ _
    · obtain ⟨v, h_lookup, h_match⟩ := wf.lin_match x' s' hx'
      refine ⟨v, ?_, ?_⟩
      · simp [DEnv.bind, Finmap.lookup_insert_of_ne _ h_eq, h_lookup]
      · rw [hd]; exact h_match
  nl_match x' τ' hx' := by
    have hx_in_Δ : x ∈ Δ := Finmap.mem_iff.mpr ⟨s, hx⟩
    have hx_not_ε : x ∉ ε := ctx.disjoint x hx_in_Δ
    have hx'_in_ε : x' ∈ ε := Finmap.mem_iff.mpr ⟨τ', hx'⟩
    have hx'_ne : x' ≠ x := fun heq => hx_not_ε (heq ▸ hx'_in_ε)
    have hx_not_fv : x ∉ Ty.fv τ' := fun hin =>
      hx_not_ε (ctx.nl_fv_in_ε x' τ' hx' x hin)
    have hagree : (σ.bind x (.hil ⟨denotSpace σ s, y⟩)).AgreeOn σ (Ty.fv τ') :=
      DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv
    have hd : denotTy (σ.bind x (.hil ⟨denotSpace σ s, y⟩)) τ' = denotTy σ τ' :=
      denotTy_agree τ' hagree
    obtain ⟨v, h_lookup, h_match⟩ := wf.nl_match x' τ' hx'
    refine ⟨v, ?_, ?_⟩
    · simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hx'_ne, h_lookup]
    · rw [hd]; exact h_match

/-- Extend `EnvWF` by a non-linear binding `x ↦ embed y` where
    `y : (denotTy σ τ₀).El`. -/
theorem bind_nl {σ : DEnv} {Δ : LCtx} {ε : NLCtx}
    (wf : EnvWF σ Δ ε) (ctx : CtxWF Δ ε)
    {x : Name} {τ₀ : Ty}
    (hx_not_Δ : x ∉ Δ) (hx_not_ε : x ∉ ε) (hx_not_fv_τ₀ : x ∉ Ty.fv τ₀)
    (y : (denotTy σ τ₀).El) :
    EnvWF (σ.bind x ((denotTy σ τ₀).embed y)) Δ (Finmap.insert x τ₀ ε) where
  lin_match x' s' hx' := by
    have hx'_in_Δ : x' ∈ Δ := Finmap.mem_iff.mpr ⟨s', hx'⟩
    have hx'_ne : x' ≠ x := fun heq => hx_not_Δ (heq ▸ hx'_in_Δ)
    have hx_not_fv_s' : x ∉ Space.fv s' := fun hin =>
      hx_not_ε (ctx.lin_fv_in_ε x' s' hx' x hin)
    have hagree : (σ.bind x ((denotTy σ τ₀).embed y)).AgreeOn σ (Space.fv s') :=
      DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_s'
    have hd : denotSpace (σ.bind x ((denotTy σ τ₀).embed y)) s' = denotSpace σ s' :=
      denotSpace_agree s' hagree
    obtain ⟨v, h_lookup, h_match⟩ := wf.lin_match x' s' hx'
    refine ⟨v, ?_, ?_⟩
    · simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hx'_ne, h_lookup]
    · rw [hd]; exact h_match
  nl_match x' τ' hx' := by
    by_cases hx'_eq : x' = x
    · -- x' = x: extract from insert.
      subst x'
      rw [Finmap.lookup_insert] at hx'
      have h_eq : τ' = τ₀ := (Option.some.inj hx').symm
      refine ⟨(denotTy σ τ₀).embed y, ?_, ?_⟩
      · simp [DEnv.bind, Finmap.lookup_insert]
      · rw [h_eq]
        have hd : denotTy (σ.bind x ((denotTy σ τ₀).embed y)) τ₀ = denotTy σ τ₀ :=
          denotTy_agree τ₀ (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_τ₀)
        rw [hd]
        exact HType.embed_matchesShape _ y
    · -- x' ≠ x: lookup falls through to outer ε.
      rw [Finmap.lookup_insert_of_ne _ hx'_eq] at hx'
      obtain ⟨v, h_lookup, h_match⟩ := wf.nl_match x' τ' hx'
      have hx_not_fv_τ' : x ∉ Ty.fv τ' := fun hin =>
        hx_not_ε (ctx.nl_fv_in_ε x' τ' hx' x hin)
      have hd : denotTy (σ.bind x ((denotTy σ τ₀).embed y)) τ' = denotTy σ τ' :=
        denotTy_agree τ' (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_τ')
      refine ⟨v, ?_, ?_⟩
      · simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hx'_eq, h_lookup]
      · rw [hd]; exact h_match

end EnvWF

/-! ## Linearity helpers. -/

/-- A function that is constantly `0` is ℝ-linear. -/
theorem IsLinearMap_const_zero {α β : Type*}
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β] :
    IsLinearMap ℝ (fun _ : α => (0 : β)) :=
  ⟨fun _ _ => by simp, fun _ _ => by simp⟩

/-- A pointwise-zero function is ℝ-linear. -/
theorem IsLinearMap.of_eq_zero {α β : Type*}
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    (f : α → β) (h : ∀ x, f x = 0) : IsLinearMap ℝ f where
  map_add x y := by rw [h, h, h]; simp
  map_smul c x := by rw [h, h]; simp

/-- Pointwise sum of ℝ-linear functions is ℝ-linear. -/
theorem IsLinearMap.add_apply {α β : Type*}
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    {f g : α → β} (hf : IsLinearMap ℝ f) (hg : IsLinearMap ℝ g) :
    IsLinearMap ℝ (fun v => f v + g v) where
  map_add x y := by
    rw [hf.map_add, hg.map_add]
    abel
  map_smul c x := by
    rw [hf.map_smul, hg.map_smul, smul_add]

/-- Scalar product of a linear function with a constant vector is linear in the scalar. -/
theorem IsLinearMap.smul_const {α β : Type*}
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    {r : α → ℝ} (hr : IsLinearMap ℝ r) (v : β) :
    IsLinearMap ℝ (fun y => r y • v) where
  map_add x y := by rw [hr.map_add, add_smul]
  map_smul c x := by rw [hr.map_smul, smul_assoc]

/-- Scalar multiplication by a constant scalar preserves linearity. -/
theorem IsLinearMap.const_smul {α β : Type*}
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    {f : α → β} (hf : IsLinearMap ℝ f) (c : ℝ) :
    IsLinearMap ℝ (fun y => c • f y) where
  map_add x y := by rw [hf.map_add, smul_add]
  map_smul d x := by rw [hf.map_smul, smul_comm]

/-- Pair construction of two linear functions is linear. -/
theorem IsLinearMap.prod_mk {α β γ : Type*}
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    [AddCommGroup γ] [Module ℝ γ]
    {f : α → β} {g : α → γ} (hf : IsLinearMap ℝ f) (hg : IsLinearMap ℝ g) :
    IsLinearMap ℝ (fun y => (f y, g y)) where
  map_add x y := by
    show (f (x + y), g (x + y)) = (f x, g x) + (f y, g y)
    rw [hf.map_add, hg.map_add]; rfl
  map_smul c x := by
    show (f (c • x), g (c • x)) = c • (f x, g x)
    rw [hf.map_smul, hg.map_smul]; rfl

/-- Tensoring a linear-valued function with a constant element is linear. -/
theorem IsLinearMap.tmul_const {α : Type*} {V W : Type*}
    [AddCommGroup α] [Module ℝ α]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {f : α → V} (hf : IsLinearMap ℝ f) (w : W) :
    IsLinearMap ℝ (fun y => f y ⊗ₜ[ℝ] w) where
  map_add x y := by rw [hf.map_add, TensorProduct.add_tmul]
  map_smul c x := by rw [hf.map_smul, TensorProduct.smul_tmul']

/-- Tensoring a constant element with a linear-valued function is linear. -/
theorem IsLinearMap.const_tmul {α : Type*} {V W : Type*}
    [AddCommGroup α] [Module ℝ α]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (v : V) {f : α → W} (hf : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun y => v ⊗ₜ[ℝ] f y) where
  map_add x y := by rw [hf.map_add, TensorProduct.tmul_add]
  map_smul c x := by rw [hf.map_smul, TensorProduct.tmul_smul]

/-- Postcomposition of a linear function with a Mathlib `LinearMap`
    yields a linear function. -/
theorem IsLinearMap.linearMap_comp {α β γ : Type*}
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    [AddCommGroup γ] [Module ℝ γ]
    (L : β →ₗ[ℝ] γ) {f : α → β} (hf : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun y => L (f y)) where
  map_add x y := by rw [hf.map_add]; exact L.map_add _ _
  map_smul c x := by rw [hf.map_smul]; exact L.map_smul _ _

/-- `LinearMap.ofFun f` applied to `v` gives `f v` when `f` is linear. -/
theorem LinearMap.ofFun_apply_of_isLinearMap {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {f : V → W} (h : IsLinearMap ℝ f) (v : V) :
    LinearMap.ofFun f v = f v := by
  unfold LinearMap.ofFun
  rw [dif_pos h.map_add, dif_pos h.map_smul]
  rfl

/-- If for each `y`, `g y` is linear, and additionally `y ↦ (g y) v` is
    linear in `y` for each `v`, then `y ↦ LinearMap.ofFun (g y)` is
    linear (as a function into the LinearMap space). -/
theorem IsLinearMap.ofFun_param {α V W : Type*}
    [AddCommGroup α] [Module ℝ α]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {g : α → V → W}
    (h_lin_v : ∀ y, IsLinearMap ℝ (g y))
    (h_lin_y : ∀ v, IsLinearMap ℝ (fun y => g y v)) :
    IsLinearMap ℝ (fun y => LinearMap.ofFun (g y)) where
  map_add y₁ y₂ := by
    apply LinearMap.ext
    intro v
    show (LinearMap.ofFun (g (y₁ + y₂))) v
          = ((LinearMap.ofFun (g y₁)) + (LinearMap.ofFun (g y₂))) v
    rw [LinearMap.ofFun_apply_of_isLinearMap (h_lin_v _),
        LinearMap.add_apply,
        LinearMap.ofFun_apply_of_isLinearMap (h_lin_v _),
        LinearMap.ofFun_apply_of_isLinearMap (h_lin_v _)]
    exact (h_lin_y v).map_add y₁ y₂
  map_smul c y := by
    apply LinearMap.ext
    intro v
    show (LinearMap.ofFun (g (c • y))) v = (c • LinearMap.ofFun (g y)) v
    rw [LinearMap.ofFun_apply_of_isLinearMap (h_lin_v _),
        LinearMap.smul_apply,
        LinearMap.ofFun_apply_of_isLinearMap (h_lin_v _)]
    exact (h_lin_y v).map_smul c y

/-- Linearity is preserved by pointwise equality. -/
theorem IsLinearMap.congr {α β : Type*}
    [AddCommGroup α] [Module ℝ α] [AddCommGroup β] [Module ℝ β]
    {f g : α → β} (hf : IsLinearMap ℝ f) (h : ∀ x, f x = g x) :
    IsLinearMap ℝ g where
  map_add x y := by rw [← h, ← h, ← h]; exact hf.map_add x y
  map_smul c x := by rw [← h, ← h]; exact hf.map_smul c x

theorem Term.fv_openVar_body_subset {e : Term} {L A : Finset Name}
    (h : ∀ y, y ∉ L → ∀ z, z ∈ Term.fv (Term.openVar y e) → z = y ∨ z ∈ A) :
    Term.fv e ⊆ A := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Term.fv e)
  simp only [Finset.mem_union, not_or] at hy
  intro z hz
  rcases h y hy.1 z (Term.fv_subset_openRec hz) with rfl | hzA
  · exact absurd hz hy.2
  · exact hzA

/-- Cofinite FV-closure for a type binder codomain. -/
theorem Ty.fv_openVar_body_subset {τ : Ty} {L A : Finset Name}
    (h : ∀ y, y ∉ L → ∀ z, z ∈ Ty.fv (Ty.openVar y τ) → z = y ∨ z ∈ A) :
    Ty.fv τ ⊆ A := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv τ)
  simp only [Finset.mem_union, not_or] at hy
  intro z hz
  rcases h y hy.1 z (Ty.fv_subset_openRec hz) with rfl | hzA
  · exact absurd hz hy.2
  · exact hzA

mutual

theorem SValid.fv_closure {ε s} (d : SValid ε s) : Space.fv s ⊆ ε.keys := by
  match d with
  | .empty => simp [Space.fv]
  | .real  => simp [Space.fv]
  | .dual d' =>
      simp only [Space.fv]
      exact SValid.fv_closure d'
  | .dsum d₀ d₁ =>
      simp only [Space.fv]
      exact Finset.union_subset (SValid.fv_closure d₀) (SValid.fv_closure d₁)
  | .tprod d₀ d₁ =>
      simp only [Space.fv]
      exact Finset.union_subset (SValid.fv_closure d₀) (SValid.fv_closure d₁)
  | .ker d_s₀ d_s₁ d_e =>
      simp only [Space.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact SValid.fv_closure d_s₀
      · exact SValid.fv_closure d_s₁
      · have := HasType.fv_closure d_e
        simp only [Finmap.keys_empty, Finset.empty_union] at this
        exact this
  | .coker d_s₀ d_s₁ d_e =>
      simp only [Space.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact SValid.fv_closure d_s₀
      · exact SValid.fv_closure d_s₁
      · have := HasType.fv_closure d_e
        simp only [Finmap.keys_empty, Finset.empty_union] at this
        exact this
  | .img d_s₀ d_s₁ d_e =>
      simp only [Space.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact SValid.fv_closure d_s₀
      · exact SValid.fv_closure d_s₁
      · have := HasType.fv_closure d_e
        simp only [Finmap.keys_empty, Finset.empty_union] at this
        exact this
  | .coimg d_s₀ d_s₁ d_e =>
      simp only [Space.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact SValid.fv_closure d_s₀
      · exact SValid.fv_closure d_s₁
      · have := HasType.fv_closure d_e
        simp only [Finmap.keys_empty, Finset.empty_union] at this
        exact this

/-- FV closure for `TValid`: a well-formed type's free variables all
    live in the non-linear namespace. -/
theorem TValid.fv_closure {ε τ k} (d : TValid ε τ k) : Ty.fv τ ⊆ ε.keys := by
  match d with
  | .space d_s =>
      simp only [Ty.fv]
      exact SValid.fv_closure d_s
  | @TValid.piTy _ τ₀ τ₁ _ _ L d_τ₀ d_τ₁ =>
      simp only [Ty.fv]
      refine Finset.union_subset (TValid.fv_closure d_τ₀) ?_
      -- Ty.fv τ₁ ⊆ ε.keys via the cofinite codomain premise.
      refine Ty.fv_openVar_body_subset (L := L) (fun y _hy z hz => ?_)
      have h := TValid.fv_closure (d_τ₁ y _hy) hz
      rcases Finmap.mem_insert.mp (Finmap.mem_keys.mp h) with rfl | h_in_ε
      · exact Or.inl rfl
      · exact Or.inr (Finmap.mem_keys.mpr h_in_ε)

/-- FV closure for `SubType`. -/
theorem SubType.fv_closure {ε s₀ s₁} (d : SubType ε s₀ s₁) :
    Space.fv s₀ ⊆ ε.keys ∧ Space.fv s₁ ⊆ ε.keys := by
  match d with
  | .sub_ker d_s₀ d_s₁ d_e =>
      refine ⟨?_, SValid.fv_closure d_s₀⟩
      simp only [Space.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact SValid.fv_closure d_s₀
      · exact SValid.fv_closure d_s₁
      · have := HasType.fv_closure d_e
        simp only [Finmap.keys_empty, Finset.empty_union] at this
        exact this
  | .sub_coker d_s₀ d_s₁ d_e =>
      refine ⟨?_, SValid.fv_closure d_s₀⟩
      simp only [Space.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact SValid.fv_closure d_s₀
      · exact SValid.fv_closure d_s₁
      · have := HasType.fv_closure d_e
        simp only [Finmap.keys_empty, Finset.empty_union] at this
        exact this
  | .sub_img d_s₀ d_s₁ d_e =>
      refine ⟨?_, SValid.fv_closure d_s₁⟩
      simp only [Space.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact SValid.fv_closure d_s₀
      · exact SValid.fv_closure d_s₁
      · have := HasType.fv_closure d_e
        simp only [Finmap.keys_empty, Finset.empty_union] at this
        exact this
  | .sub_coimg d_s₀ d_s₁ d_e =>
      refine ⟨?_, SValid.fv_closure d_s₁⟩
      simp only [Space.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact SValid.fv_closure d_s₀
      · exact SValid.fv_closure d_s₁
      · have := HasType.fv_closure d_e
        simp only [Finmap.keys_empty, Finset.empty_union] at this
        exact this

/-- FV closure for `HasType`: a well-typed term's free variables live
    in the union of the linear and non-linear namespaces. -/
theorem HasType.fv_closure {Δ ε e τ} (d : HasType Δ ε e τ) :
    Term.fv e ⊆ Δ.keys ∪ ε.keys := by
  match d with
  | .zero d_s =>
      simp only [Term.fv]
      exact (SValid.fv_closure d_s).trans Finset.subset_union_right
  | .smul _ split d₀ d₁ =>
      simp only [Term.fv]
      refine Finset.union_subset ?_ ?_
      · refine (HasType.fv_closure d₀).trans ?_
        rw [Finmap.keys_union]
        exact Finset.union_subset_union_left Finset.subset_union_left
      · refine (HasType.fv_closure d₁).trans ?_
        rw [Finmap.keys_union]
        exact Finset.union_subset_union_left Finset.subset_union_right
  | .add _ d₀ d₁ =>
      simp only [Term.fv]
      exact Finset.union_subset (HasType.fv_closure d₀) (HasType.fv_closure d₁)
  | .inner d_s =>
      simp only [Term.fv]
      exact (SValid.fv_closure d_s).trans Finset.subset_union_right
  | .real_lit _ =>
      simp only [Term.fv]
      exact Finset.empty_subset _
  | .app_linear d_s₀ d_s₁ split d₀ d₁ =>
      simp only [Term.fv]
      refine Finset.union_subset (Finset.union_subset (Finset.union_subset ?_ ?_) ?_) ?_
      · exact (SValid.fv_closure d_s₀).trans Finset.subset_union_right
      · exact (SValid.fv_closure d_s₁).trans Finset.subset_union_right
      · refine (HasType.fv_closure d₀).trans ?_
        rw [Finmap.keys_union]
        exact Finset.union_subset_union_left Finset.subset_union_left
      · refine (HasType.fv_closure d₁).trans ?_
        rw [Finmap.keys_union]
        exact Finset.union_subset_union_left Finset.subset_union_right
  | .app_inner d_s split d₀ d₁ =>
      simp only [Term.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact (SValid.fv_closure d_s).trans Finset.subset_union_right
      · refine (HasType.fv_closure d₀).trans ?_
        rw [Finmap.keys_union]
        exact Finset.union_subset_union_left Finset.subset_union_left
      · refine (HasType.fv_closure d₁).trans ?_
        rw [Finmap.keys_union]
        exact Finset.union_subset_union_left Finset.subset_union_right
  | .app_nonlinear d₀ d₁ =>
      simp only [Term.fv]
      refine Finset.union_subset (HasType.fv_closure d₀) (HasType.fv_closure d₁)
  | @HasType.var_lin _ x s =>
      simp only [Term.fv]
      intro y hy
      rw [Finset.mem_singleton] at hy
      subst hy
      apply Finset.mem_union_left
      exact Finmap.mem_keys.mpr (Finmap.mem_iff.mpr ⟨s, Finmap.lookup_singleton_eq⟩)
  | .var_nlin h_ε =>
      simp only [Term.fv]
      intro y hy
      rw [Finset.mem_singleton] at hy
      subst hy
      apply Finset.mem_union_right
      exact Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some h_ε)
  | .pinv_tensor d_s₀ d_s₁ d_e =>
      simp only [Term.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact (SValid.fv_closure d_s₀).trans Finset.subset_union_right
      · exact (SValid.fv_closure d_s₁).trans Finset.subset_union_right
      · exact HasType.fv_closure d_e
  | .pinv_dual d_s d_e =>
      simp only [Term.fv]
      refine Finset.union_subset ?_ ?_
      · exact (SValid.fv_closure d_s).trans Finset.subset_union_right
      · exact HasType.fv_closure d_e
  | @HasType.promote _ _ _ _ lin _h_disjΔ _h_disjε _h_fresh d =>
      -- Inner derivation has Term.fv e ⊆ (lin ∪ Δ).keys ∪ ε'.keys
      --                              = lin.keys ∪ Δ.keys ∪ ε'.keys
      -- Outer goal: Term.fv e ⊆ Δ.keys ∪ (lin.toNL ∪ ε').keys
      --                       = Δ.keys ∪ (lin.keys ∪ ε'.keys)
      have h := HasType.fv_closure d
      rw [Finmap.keys_union] at h
      refine h.trans ?_
      rw [Finmap.keys_union, LCtx.toNL_keys]
      intro y hy
      rcases Finset.mem_union.mp hy with hy_lD | hy_ε
      · rcases Finset.mem_union.mp hy_lD with hy_l | hy_D
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ hy_l)
        · exact Finset.mem_union_left _ hy_D
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hy_ε)
  | .dsumE _ _ d₀ d₁ =>
      simp only [Term.fv]
      exact Finset.union_subset (HasType.fv_closure d₀) (HasType.fv_closure d₁)
  | .tprodE _ _ split d₀ d₁ =>
      simp only [Term.fv]
      refine Finset.union_subset ?_ ?_
      · refine (HasType.fv_closure d₀).trans ?_
        rw [Finmap.keys_union]
        exact Finset.union_subset_union_left Finset.subset_union_left
      · refine (HasType.fv_closure d₁).trans ?_
        rw [Finmap.keys_union]
        exact Finset.union_subset_union_left Finset.subset_union_right
  | @HasType.llam_real Δ ε s e L d_s d_body =>
      simp only [Term.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact (SValid.fv_closure d_s).trans Finset.subset_union_right
      · -- Space.fv .real = ∅
        simp [Space.fv]
      · -- Term.fv e ⊆ Δ.keys ∪ ε.keys via the cofinite body premise.
        refine Term.fv_openVar_body_subset (L := L) (fun y _hy z hz => ?_)
        have h := HasType.fv_closure (d_body y _hy) hz
        rcases Finset.mem_union.mp h with h_inΔ | h_inε
        · rcases Finmap.mem_insert.mp (Finmap.mem_keys.mp h_inΔ) with rfl | h_inD
          · exact Or.inl rfl
          · exact Or.inr (Finset.mem_union_left _ (Finmap.mem_keys.mpr h_inD))
        · exact Or.inr (Finset.mem_union_right _ h_inε)
  | @HasType.llam_tensor Δ ε s₀ s e L _hne d_s₀ d_s d_body =>
      simp only [Term.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact (SValid.fv_closure d_s₀).trans Finset.subset_union_right
      · exact (SValid.fv_closure d_s).trans Finset.subset_union_right
      · refine Term.fv_openVar_body_subset (L := L) (fun y _hy z hz => ?_)
        have h := HasType.fv_closure (d_body y _hy) hz
        rcases Finset.mem_union.mp h with h_inΔ | h_inε
        · rcases Finmap.mem_insert.mp (Finmap.mem_keys.mp h_inΔ) with rfl | h_inD
          · exact Or.inl rfl
          · exact Or.inr (Finset.mem_union_left _ (Finmap.mem_keys.mpr h_inD))
        · exact Or.inr (Finset.mem_union_right _ h_inε)
  | .embed d_sub =>
      simp only [Term.fv]
      -- Term.fv (.embed s₀) = Space.fv s₀
      have ⟨h₀, _⟩ := SubType.fv_closure d_sub
      exact h₀.trans Finset.subset_union_right
  | @HasType.nllam ε τ₀ τ₁ _ _ e L d_τ d_body =>
      simp only [Term.fv]
      refine Finset.union_subset ?_ ?_
      · -- Ty.fv τ₀ ⊆ ε.keys (from TValid.fv_closure on the piTy premise)
        have h_τ := TValid.fv_closure d_τ
        simp only [Ty.fv] at h_τ
        refine ((Finset.union_subset_iff.mp h_τ).1).trans ?_
        exact Finset.subset_union_right
      · -- Term.fv e ⊆ ∅.keys ∪ ε.keys via the cofinite body premise.
        refine Term.fv_openVar_body_subset (L := L) (fun y _hy z hz => ?_)
        have h := HasType.fv_closure (d_body y _hy) hz
        rcases Finset.mem_union.mp h with h_inΔ | h_inε
        · simp [Finmap.keys_empty] at h_inΔ
        · rcases Finmap.mem_insert.mp (Finmap.mem_keys.mp h_inε) with rfl | h_inε'
          · exact Or.inl rfl
          · exact Or.inr (Finset.mem_union_right _ (Finmap.mem_keys.mpr h_inε'))

theorem soundness {Δ ε e τ}
    (d : HasType Δ ε e τ)
    {σ : DEnv} (ctx : CtxWF Δ ε) (wf : EnvWF σ Δ ε) :
    SoundClaim σ Δ e τ := by
  match d with
  | .real_lit r =>
      refine ⟨?_, ?_⟩
      · exact DVal.matchesShape_hil_rfl _ _
      · intro x s hx; simp [Finmap.lookup_empty] at hx
  | .var_nlin h_ε =>
      refine ⟨?_, ?_⟩
      · obtain ⟨v, h_lookup, h_match⟩ := wf.nl_match _ _ h_ε
        show (denotTerm σ (.var _)).matchesShape (denotTy σ _)
        unfold denotTerm denotTermAux
        rw [h_lookup]
        exact h_match
      · intro x s hx; simp [Finmap.lookup_empty] at hx
  | @HasType.var_lin _ x₀ s₀ =>
      -- Δ = Finmap.singleton x₀ s₀
      refine ⟨?_, ?_⟩
      · -- (a) The looked-up value at x₀ matches HType.hil (denotSpace σ s₀) by EnvWF.lin_match.
        obtain ⟨v, h_lookup, h_match⟩ :=
          wf.lin_match x₀ s₀ Finmap.lookup_singleton_eq
        show (denotTerm σ (.var x₀)).matchesShape (denotTy σ (.space s₀))
        unfold denotTerm denotTermAux denotTy denotTyAux
        rw [h_lookup]
        exact h_match
      · -- (b) For Δ = singleton x₀ s₀, the only x' is x₀. The function
        --   `z ↦ ⟦.var x₀⟧σ[x₀↦⟨V_s₀, z⟩].atSpace V_s₀` is the identity z↦z.
        intro x' s' hx'
        have h_mem : x' ∈ (Finmap.singleton x₀ s₀ : LCtx) :=
          Finmap.mem_iff.mpr ⟨s', hx'⟩
        have h_eq_x : x' = x₀ := (Finmap.mem_singleton _ _ _).mp h_mem
        have h_eq_s : s' = s₀ := by
          rw [h_eq_x, Finmap.lookup_singleton_eq] at hx'
          exact ((Option.some.injEq _ _).mp hx').symm
        rw [h_eq_x, h_eq_s]
        unfold LinearAtVar
        refine ⟨?_, ?_⟩
        · intro y₁ y₂
          simp [DEnv.bind, denotTerm, denotTermAux, Finmap.lookup_insert, DVal.atSpace_hil_self]
        · intro c y
          simp [DEnv.bind, denotTerm, denotTermAux, Finmap.lookup_insert, DVal.atSpace_hil_self]
  | .inner d_s =>
      refine ⟨?_, ?_⟩
      · -- (a) denotation is .hil ⟨HSpace.tprod (HSpace.dual V) (HSpace.dual V), _⟩
        -- type denotation is .hil (HSpace.tprod (HSpace.dual V) (HSpace.dual V)). Match.
        show (denotTerm σ (.inner _)).matchesShape (denotTy σ _)
        unfold denotTerm denotTermAux denotTy denotTyAux HSpace.innerTensor
        exact DVal.matchesShape_hil_rfl _ _
      · intro x s hx; simp [Finmap.lookup_empty] at hx
  | .pinv_tensor d_s₀ d_s₁ d_e =>
      refine ⟨?_, ?_⟩
      · show (denotTerm σ (.pinvT _ _ _)).matchesShape (denotTy σ _)
        unfold denotTerm denotTermAux denotTy denotTyAux pinvTensorDVal
        exact DVal.matchesShape_hil_rfl _ _
      · intro x s hx; simp [Finmap.lookup_empty] at hx
  | .pinv_dual d_s d_e =>
      refine ⟨?_, ?_⟩
      · show (denotTerm σ (.pinvD _ _)).matchesShape (denotTy σ _)
        unfold denotTerm denotTermAux denotTy denotTyAux pinvDualDVal
        exact DVal.matchesShape_hil_rfl _ _
      · intro x s hx; simp [Finmap.lookup_empty] at hx
  | @HasType.nllam ε τ₀ τ₁ k₀ k₁ e L d_τ d_body =>
      refine ⟨?_, ?_⟩
      · -- (a) Build matchesShape (HType.sec T_outer.El _) on the .pi denot
        -- by invoking soundness IH on the body opened at a FRESH `x ∉ L`,
        -- then transporting to the local-env fiber form via the open-bridge.
        have h_fv_τ₀ : Ty.fv τ₀ ⊆ ε.keys := by
          have h := TValid.fv_closure d_τ; simp only [Ty.fv] at h
          exact (Finset.union_subset_iff.mp h).1
        obtain ⟨L', hτ₁_lc⟩ : ∃ L', ∀ z, z ∉ L' → Ty.lc (Ty.openVar z τ₁) := by
          cases TValid.lc d_τ with | piTy L' _ hb => exact ⟨L', hb⟩
        obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
          (L ∪ L' ∪ Term.fv e ∪ Ty.fv τ₁ ∪ Ty.fv τ₀ ∪ ε.keys)
        simp only [Finset.mem_union, not_or] at hx
        obtain ⟨⟨⟨⟨⟨hxL, hxL'⟩, hx_fve⟩, hx_fvτ₁⟩, h_x_not_fv_τ₀⟩, hx_εk⟩ := hx
        have h_x_not_ε : x ∉ ε := fun h => hx_εk (Finmap.mem_keys.mpr h)
        show (DVal.pi (denotTy σ τ₀).El _).matchesShape
              (HType.sec (denotTy σ τ₀).El _)
        refine DVal.matchesShape_pi _ _ _ ?_
        intro y
        -- Construct ctx_ext and wf_ext for the body's IH.
        have ctx_ext : CtxWF ∅ (Finmap.insert x τ₀ ε) := {
          disjoint := fun x' hx' => by
            simp [Finmap.mem_iff] at hx'
          lin_fv_in_ε := fun x' s' hx' _ _ => by
            simp [Finmap.lookup_empty] at hx'
          nl_fv_in_ε := fun x' τ' hx' z hz => by
            by_cases hx'_eq : x' = x
            · -- x' = x: τ' = τ₀
              subst x'
              rw [Finmap.lookup_insert] at hx'
              have h_eq : τ' = τ₀ := (Option.some.inj hx').symm
              rw [h_eq] at hz
              have : z ∈ ε := Finmap.mem_keys.mp (h_fv_τ₀ hz)
              exact Finmap.mem_insert.mpr (Or.inr this)
            · -- x' ≠ x: use outer ctx.nl_fv_in_ε
              rw [Finmap.lookup_insert_of_ne _ hx'_eq] at hx'
              have hz_in_ε : z ∈ ε := ctx.nl_fv_in_ε x' τ' hx' z hz
              exact Finmap.mem_insert.mpr (Or.inr hz_in_ε)
        }
        have h_embed_match :
            ((denotTy σ τ₀).embed y).matchesShape (denotTy σ τ₀) :=
          HType.embed_matchesShape _ y
        have wf_ext : EnvWF (σ.bind x ((denotTy σ τ₀).embed y)) ∅
                            (Finmap.insert x τ₀ ε) := {
          lin_match := fun x' s' hx' => by
            simp [Finmap.lookup_empty] at hx'
          nl_match := fun x' τ' hx' => by
            by_cases hx'_eq : x' = x
            · -- x' = x: lookup gives τ₀; use the bound value.
              subst x'
              rw [Finmap.lookup_insert] at hx'
              have h_eq : τ' = τ₀ := (Option.some.inj hx').symm
              refine ⟨(denotTy σ τ₀).embed y, ?_, ?_⟩
              · simp [DEnv.bind, Finmap.lookup_insert]
              · -- Need matchesShape (... .embed y) (denotTy σ' τ').
                rw [h_eq]
                -- By FV-irrelevance, denotTy σ' τ₀ = denotTy σ τ₀ (x ∉ Ty.fv τ₀).
                have hd : denotTy (σ.bind x ((denotTy σ τ₀).embed y)) τ₀
                        = denotTy σ τ₀ :=
                  denotTy_agree τ₀
                    (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_τ₀)
                rw [hd]
                exact h_embed_match
            · -- x' ≠ x: lookup falls through to outer ε.
              rw [Finmap.lookup_insert_of_ne _ hx'_eq] at hx'
              obtain ⟨v, h_lookup, h_match⟩ := wf.nl_match x' τ' hx'
              refine ⟨v, ?_, ?_⟩
              · simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hx'_eq,
                      h_lookup]
              · -- denotTy σ' τ' = denotTy σ τ' by FV-irrelevance.
                have hx_not_fv_τ' : x ∉ Ty.fv τ' := fun hin =>
                  h_x_not_ε (ctx.nl_fv_in_ε x' τ' hx' x hin)
                have hd : denotTy (σ.bind x ((denotTy σ τ₀).embed y)) τ'
                        = denotTy σ τ' :=
                  denotTy_agree τ'
                    (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_τ')
                rw [hd]
                exact h_match
        }
        have ih := (soundness (d_body x hxL) ctx_ext wf_ext).1
        rw [denotTerm_openVar_bind (HasType.lc (d_body x hxL)) hx_fve,
            denotTy_openVar_bind (hτ₁_lc x hxL') hx_fvτ₁] at ih
        exact ih
      · intro x s hx; simp [Finmap.lookup_empty] at hx
  | @HasType.zero _ _ s d_s =>
      refine ⟨?_, ?_⟩
      · -- (a) zero of s has carrier `(denotSpace σ s).carrier`.
        show (DVal.hil ⟨denotSpace σ s, (0 : (denotSpace σ s).carrier)⟩).matchesShape _
        exact DVal.matchesShape_hil_rfl _ _
      · -- (b) For each linear var x ∈ Δ with binding s', the function
        --     y ↦ ⟦.zero s⟧σ[x↦⟨V_s', y⟩].atSpace V_s
        -- is constantly 0 (by Barendregt: x ∉ Space.fv s, so denotSpace
        -- doesn't depend on y; and atSpace of zero is zero).
        intro x s' hx
        have h_x_in_Δ : x ∈ Δ := Finmap.mem_iff.mpr ⟨s', hx⟩
        have h_x_not_ε : x ∉ ε := ctx.disjoint x h_x_in_Δ
        have h_x_not_fv_s : x ∉ Space.fv s := fun h_in =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s h_in))
        show LinearAtVar σ x s' (.zero s) (.space s)
        unfold LinearAtVar
        apply IsLinearMap.of_eq_zero
        intro y
        -- Goal: (denotTerm (σ.bind x _) (.zero s)).atSpace (denotSpace σ s) = 0
        -- FV-irrelevance at the TERM level (avoids the dependent denotSpace rewrite).
        rw [denotTerm_agree (.zero s) (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s)]
        show (DVal.hil ⟨denotSpace σ s, _⟩).atSpace (denotSpace σ s) = 0
        exact DVal.atSpace_hil_self _ _
  | @HasType.embed _ s₀ s₁ d_sub =>
      refine ⟨?_, ?_⟩
      · -- (a) Branch on `s₀`'s SubType flavor.
        cases d_sub with
        | sub_ker d_s₀_amb d_s₁ d_e =>
            show ((denotTerm σ (.embed (.ker _ _ _))).matchesShape _)
            unfold denotTerm denotTermAux embedDVal
            exact DVal.matchesShape_hil_rfl _ _
        | sub_coker d_s₀_amb d_s₁ d_e =>
            show ((denotTerm σ (.embed (.coker _ _ _))).matchesShape _)
            unfold denotTerm denotTermAux embedDVal
            exact DVal.matchesShape_hil_rfl _ _
        | sub_img d_s₀ d_s₁_amb d_e =>
            show ((denotTerm σ (.embed (.img _ _ _))).matchesShape _)
            unfold denotTerm denotTermAux embedDVal
            exact DVal.matchesShape_hil_rfl _ _
        | sub_coimg d_s₀ d_s₁_amb d_e =>
            show ((denotTerm σ (.embed (.coimg _ _ _))).matchesShape _)
            unfold denotTerm denotTermAux embedDVal
            exact DVal.matchesShape_hil_rfl _ _
      · -- (b) Δ = ∅, vacuous
        intro x s hx; simp [Finmap.lookup_empty] at hx
  | @HasType.app_linear Δ₀ Δ₁ _ e₀ e₁ s₀ s₁ d_s₀ d_s₁ hsplit d₀ d₁ =>
      have hsub₀ : ∀ x s, Δ₀.lookup x = some s → (Δ₀ ∪ Δ₁).lookup x = some s := fun x s h => by
        rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some h)]; exact h
      have hsub₁ : ∀ x s, Δ₁.lookup x = some s → (Δ₀ ∪ Δ₁).lookup x = some s := fun x s h => by
        have h_mem : x ∈ Δ₁ := Finmap.mem_of_lookup_eq_some h
        have h_not : x ∉ Δ₀ := fun h' => @hsplit x h' h_mem
        rw [Finmap.lookup_union_right h_not]; exact h
      have ctx₀ : CtxWF Δ₀ _ := ctx.of_sub_Δ hsub₀
      have ctx₁ : CtxWF Δ₁ _ := ctx.of_sub_Δ hsub₁
      have wf₀ : EnvWF σ Δ₀ _ := wf.of_sub_Δ hsub₀
      have wf₁ : EnvWF σ Δ₁ _ := wf.of_sub_Δ hsub₁
      refine ⟨?_, ?_⟩
      · show (denotTerm σ (.appL s₀ s₁ _ _)).matchesShape _
        unfold denotTerm
        exact DVal.matchesShape_hil_rfl _ _
      · intro x s' hx
        show IsLinearMap ℝ _
        have h_x_in : x ∈ Δ₀ ∪ Δ₁ := Finmap.mem_iff.mpr ⟨s', hx⟩
        have h_x_not_ε := ctx.disjoint x h_x_in
        have h_x_not_fv_s₀ : x ∉ Space.fv s₀ := fun hin =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s₀ hin))
        have h_x_not_fv_s₁ : x ∉ Space.fv s₁ := fun hin =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s₁ hin))
        have h_x_not_fv_tprod : x ∉ Space.fv (.tprod (.dual s₀) s₁) := by
          simp only [Space.fv]
          intro hin
          rcases Finset.mem_union.mp hin with h | h
          · exact h_x_not_fv_s₀ h
          · exact h_x_not_fv_s₁ h
        by_cases hx_Δ₀ : x ∈ Δ₀
        · -- Tensor varies; vector constant.
          have hx₀ : Δ₀.lookup x = some s' := by
            rw [Finmap.lookup_union_left hx_Δ₀] at hx; exact hx
          have ih₀_b := (soundness d₀ ctx₀ wf₀).2 x s' hx₀
          dsimp only [LinearAtVar] at ih₀_b
          have hx_not_Δ₁ : x ∉ Δ₁ := fun hin => @hsplit x hx_Δ₀ hin
          have hx_not_fv_e₁ : x ∉ Term.fv e₁ := fun hin =>
            (Finset.mem_union.mp (HasType.fv_closure d₁ hin)).elim
              (fun h => hx_not_Δ₁ (Finmap.mem_keys.mp h))
              (fun h => h_x_not_ε (Finmap.mem_keys.mp h))
          have h_e1_const : ∀ y : (denotSpace σ s').carrier,
              denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁ = denotTerm σ e₁ := fun y =>
            denotTerm_agree e₁ (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_e₁)
          -- The constant LinearMap: t ↦ dualTensorHom t v_const, where v_const = e₁'s value.
          let v_const : (denotSpace σ s₀).carrier := (denotTerm σ e₁).atSpace (denotSpace σ s₀)
          let L : (Module.Dual ℝ (denotSpace σ s₀).carrier ⊗[ℝ] (denotSpace σ s₁).carrier)
                  →ₗ[ℝ] (denotSpace σ s₁).carrier :=
            { toFun := fun t => dualTensorHom ℝ (denotSpace σ s₀).carrier
                                  (denotSpace σ s₁).carrier t v_const
              map_add' := fun t₁ t₂ => by simp [LinearMap.add_apply]
              map_smul' := fun r t => by simp [LinearMap.smul_apply] }
          have h_fun_eq :
              (fun y : (denotSpace σ s').carrier =>
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.appL s₀ s₁ e₀ e₁)).atSpace
                    (denotSpace σ s₁)) =
              (fun y => L ((denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).atSpace
                          (HSpace.tprod (HSpace.dual (denotSpace σ s₀)) (denotSpace σ s₁)))) := by
            funext y
            have wf' : EnvWF (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) Δ₀ _ :=
              (wf.bind_lin ctx hx y).of_sub_Δ hsub₀
            have ih₀_a := (soundness d₀ ctx₀ wf').1
            rw [denotTy_space] at ih₀_a
            have hd_tp : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩))
                          (.tprod (.dual s₀) s₁) =
                          denotSpace σ (.tprod (.dual s₀) s₁) :=
              denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_tprod)
            have hd₀ : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s₀ =
                        denotSpace σ s₀ :=
              denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s₀)
            have hd₁ : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s₁ =
                        denotSpace σ s₁ :=
              denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s₁)
            rw [hd_tp] at ih₀_a
            rw [denotTerm_appL]
            rw [hd₀, hd₁, DVal.atSpace_hil_self]
            rw [DVal.asLinMap_eq_of_matchesShape ih₀_a]
            rw [h_e1_const y]
            rfl
          rw [h_fun_eq]
          exact IsLinearMap.linearMap_comp L ih₀_b
        · -- Vector varies; tensor constant.
          have hx_Δ₁ : x ∈ Δ₁ := by
            rcases Finmap.mem_union.mp h_x_in with h | h
            · exact absurd h hx_Δ₀
            · exact h
          have hx₁ : Δ₁.lookup x = some s' := by
            rw [Finmap.lookup_union_right hx_Δ₀] at hx; exact hx
          have ih₁_b := (soundness d₁ ctx₁ wf₁).2 x s' hx₁
          dsimp only [LinearAtVar] at ih₁_b
          have hx_not_fv_e₀ : x ∉ Term.fv e₀ := fun hin =>
            (Finset.mem_union.mp (HasType.fv_closure d₀ hin)).elim
              (fun h => hx_Δ₀ (Finmap.mem_keys.mp h))
              (fun h => h_x_not_ε (Finmap.mem_keys.mp h))
          have h_e0_const : ∀ y : (denotSpace σ s').carrier,
              denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀ = denotTerm σ e₀ := fun y =>
            denotTerm_agree e₀ (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_e₀)
          have ih₀_a := (soundness d₀ ctx₀ wf₀).1
          rw [denotTy_space] at ih₀_a
          -- f_const := dualTensorHom (t_const) : V₀ →ₗ V₁
          let f_const : (denotSpace σ s₀).carrier →ₗ[ℝ] (denotSpace σ s₁).carrier :=
            (denotTerm σ e₀).asLinMap (denotSpace σ s₀) (denotSpace σ s₁)
          have h_fun_eq :
              (fun y : (denotSpace σ s').carrier =>
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.appL s₀ s₁ e₀ e₁)).atSpace
                    (denotSpace σ s₁)) =
              (fun y => f_const ((denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁).atSpace
                          (denotSpace σ s₀))) := by
            funext y
            have hd₀ : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s₀ =
                        denotSpace σ s₀ :=
              denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s₀)
            have hd₁ : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s₁ =
                        denotSpace σ s₁ :=
              denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s₁)
            rw [denotTerm_appL]
            rw [hd₀, hd₁, DVal.atSpace_hil_self]
            rw [h_e0_const y]
          rw [h_fun_eq]
          exact IsLinearMap.linearMap_comp f_const ih₁_b
  | @HasType.app_inner Δ₀ Δ₁ _ e₀ e₁ s d_s hsplit d₀ d₁ =>
      have hsub₀ : ∀ x s, Δ₀.lookup x = some s → (Δ₀ ∪ Δ₁).lookup x = some s := fun x s h => by
        rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some h)]; exact h
      have hsub₁ : ∀ x s, Δ₁.lookup x = some s → (Δ₀ ∪ Δ₁).lookup x = some s := fun x s h => by
        have h_mem : x ∈ Δ₁ := Finmap.mem_of_lookup_eq_some h
        have h_not : x ∉ Δ₀ := fun h' => @hsplit x h' h_mem
        rw [Finmap.lookup_union_right h_not]; exact h
      have ctx₀ : CtxWF Δ₀ _ := ctx.of_sub_Δ hsub₀
      have ctx₁ : CtxWF Δ₁ _ := ctx.of_sub_Δ hsub₁
      have wf₀ : EnvWF σ Δ₀ _ := wf.of_sub_Δ hsub₀
      have wf₁ : EnvWF σ Δ₁ _ := wf.of_sub_Δ hsub₁
      refine ⟨?_, ?_⟩
      · show (denotTerm σ (.appI s _ _)).matchesShape _
        unfold denotTerm
        exact DVal.matchesShape_hil_rfl _ _
      · intro x s' hx
        show IsLinearMap ℝ _
        have h_x_in : x ∈ Δ₀ ∪ Δ₁ := Finmap.mem_iff.mpr ⟨s', hx⟩
        have h_x_not_ε := ctx.disjoint x h_x_in
        have h_x_not_fv_s : x ∉ Space.fv s := fun hin =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s hin))
        have h_x_not_fv_dual : x ∉ Space.fv (.dual s) := h_x_not_fv_s
        by_cases hx_Δ₀ : x ∈ Δ₀
        · -- Functional varies; vector constant.
          have hx₀ : Δ₀.lookup x = some s' := by
            rw [Finmap.lookup_union_left hx_Δ₀] at hx; exact hx
          have ih₀_b := (soundness d₀ ctx₀ wf₀).2 x s' hx₀
          dsimp only [LinearAtVar] at ih₀_b
          have hx_not_Δ₁ : x ∉ Δ₁ := fun hin => @hsplit x hx_Δ₀ hin
          have hx_not_fv_e₁ : x ∉ Term.fv e₁ := fun hin =>
            (Finset.mem_union.mp (HasType.fv_closure d₁ hin)).elim
              (fun h => hx_not_Δ₁ (Finmap.mem_keys.mp h))
              (fun h => h_x_not_ε (Finmap.mem_keys.mp h))
          have h_e1_const : ∀ y : (denotSpace σ s').carrier,
              denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁ = denotTerm σ e₁ := fun y =>
            denotTerm_agree e₁ (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_e₁)
          let v_const : (denotSpace σ s).carrier :=
            (denotTerm σ e₁).atSpace (denotSpace σ s)
          let L : (Module.Dual ℝ (denotSpace σ s).carrier) →ₗ[ℝ] ℝ :=
            { toFun := fun φ => φ v_const
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          have h_fun_eq :
              (fun y : (denotSpace σ s').carrier =>
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.appI s e₀ e₁)).atSpace
                    (denotSpace σ .real)) =
              (fun y => L ((denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).atSpace
                            (HSpace.dual (denotSpace σ s)))) := by
            funext y
            have wf' : EnvWF (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) Δ₀ _ :=
              (wf.bind_lin ctx hx y).of_sub_Δ hsub₀
            have ih₀_a := (soundness d₀ ctx₀ wf').1
            rw [denotTy_space] at ih₀_a
            have hd_dual : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.dual s) =
                            denotSpace σ (.dual s) :=
              denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_dual)
            have hd_s : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s = denotSpace σ s :=
              denotSpace_agree s (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s)
            rw [hd_dual] at ih₀_a
            rw [denotTerm_appI]
            rw [hd_s]
            show DVal.atSpace HSpace.real (DVal.hil ⟨HSpace.real, _⟩) = _
            rw [DVal.atSpace_hil_self]
            rw [DVal.asLinFunctional_eq_of_matchesShape ih₀_a]
            rw [h_e1_const y]
            rfl
          rw [h_fun_eq]
          exact IsLinearMap.linearMap_comp L ih₀_b
        · -- Vector varies; functional constant.
          have hx_Δ₁ : x ∈ Δ₁ := by
            rcases Finmap.mem_union.mp h_x_in with h | h
            · exact absurd h hx_Δ₀
            · exact h
          have hx₁ : Δ₁.lookup x = some s' := by
            rw [Finmap.lookup_union_right hx_Δ₀] at hx; exact hx
          have ih₁_b := (soundness d₁ ctx₁ wf₁).2 x s' hx₁
          dsimp only [LinearAtVar] at ih₁_b
          have hx_not_fv_e₀ : x ∉ Term.fv e₀ := fun hin =>
            (Finset.mem_union.mp (HasType.fv_closure d₀ hin)).elim
              (fun h => hx_Δ₀ (Finmap.mem_keys.mp h))
              (fun h => h_x_not_ε (Finmap.mem_keys.mp h))
          have h_e0_const : ∀ y : (denotSpace σ s').carrier,
              denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀ = denotTerm σ e₀ := fun y =>
            denotTerm_agree e₀ (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_e₀)
          let φ_const : (denotSpace σ s).carrier →ₗ[ℝ] ℝ :=
            (denotTerm σ e₀).asLinFunctional (denotSpace σ s)
          have h_fun_eq :
              (fun y : (denotSpace σ s').carrier =>
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.appI s e₀ e₁)).atSpace
                    (denotSpace σ .real)) =
              (fun y => φ_const ((denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁).atSpace
                            (denotSpace σ s))) := by
            funext y
            have hd_s : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s = denotSpace σ s :=
              denotSpace_agree s (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s)
            rw [denotTerm_appI]
            rw [hd_s]
            show DVal.atSpace HSpace.real (DVal.hil ⟨HSpace.real, _⟩) = _
            rw [DVal.atSpace_hil_self]
            rw [h_e0_const y]
          rw [h_fun_eq]
          exact IsLinearMap.linearMap_comp φ_const ih₁_b
  | @HasType.app_nonlinear ε e₀ e₁ τ₀ τ₁ d₀ d₁ =>
      refine ⟨?_, ?_⟩
      · -- (a) Reduce the result type via the INSTANTIATE bridge:
        --   `denotTy σ (Ty.instantiate e₁ τ₁) = denotTyAux σ [⟦e₁⟧] τ₁`  (lc e₁).
        -- Then `applyAsPi` of e₀'s section denotation at e₁'s value lands on the
        -- fiber `f y_val` (`y_val = T.extract ⟦e₁⟧`), whose matchesShape against
        -- `denotTyAux σ [T.embed y_val] τ₁` is IH(a) at e₀; the round-trip
        -- `T.embed (T.extract ⟦e₁⟧) = ⟦e₁⟧` (IH(a) on e₁) aligns it.
        have ih₀ := (soundness d₀ ctx wf).1
        have ih₁ := (soundness d₁ ctx wf).1
        show (denotTerm σ (.appN e₀ e₁)).matchesShape (denotTy σ (Ty.instantiate e₁ τ₁))
        rw [denotTy_instantiate (HasType.lc d₁) σ τ₁]
        simp only [denotTy, denotTyAux] at ih₀
        obtain ⟨f', h_e0, h_f⟩ := DVal.matchesShape_sec_eq ih₀
        have h_round :
            (denotTy σ τ₀).embed ((denotTy σ τ₀).extract (denotTerm σ e₁))
              = denotTerm σ e₁ :=
          HType.embed_extract_of_matchesShape ih₁
        show (DVal.applyAsPi (denotTerm σ e₀) (denotTerm σ e₁)).matchesShape
                (denotTyAux σ [denotTerm σ e₁] τ₁)
        rw [h_e0]
        simp only [DVal.applyAsPi, DVal.asPi]
        rw [show (denotTerm σ e₁).shape = denotTy σ τ₀ from ih₁]
        rw [dif_pos rfl]
        have h_f_at := h_f ((denotTy σ τ₀).extract (denotTerm σ e₁))
        rw [h_round] at h_f_at
        exact h_f_at
      · -- (b) Δ = ∅, vacuous
        intro x s hx; simp [Finmap.lookup_empty] at hx
  | @HasType.llam_real Δ ε s₀ e L d_s d_body =>
      refine ⟨?_, ?_⟩
      · -- (a) result is `.hil ⟨HSpace.dual V₀, _⟩` via llamRealDVal.
        show (denotTerm σ (.llam _ Space.real _)).matchesShape _
        unfold denotTerm denotTermAux llamRealDVal
        exact DVal.matchesShape_hil_rfl _ _
      · -- (b) For each outer linear var x' ∈ Δ, show that the .llam's
        -- denotation is linear in y. LN/D1: choose a FRESH `x_lam ∉ Δ,ε,L,fv e`,
        -- open the body there (`d_body x_lam`), and convert the D1 env-fiber
        -- `denotTermAux env [v] e` to the named form `denotTerm (env.bind x_lam v)
        -- (openVar x_lam e)` via the open-bridge — after which the proof is the
        -- named-binder argument (ofFun_param over the doubly-bound env).
        intro x' s_x' hx'
        obtain ⟨x_lam, hx_lam⟩ := Infinite.exists_notMem_finset
          (Δ.keys ∪ ε.keys ∪ L ∪ Term.fv e)
        simp only [Finset.mem_union, not_or] at hx_lam
        obtain ⟨⟨⟨hx_lam_Δk, hx_lam_εk⟩, hx_lam_L⟩, hx_lam_fve⟩ := hx_lam
        have h_xΔ : x_lam ∉ Δ := fun h => hx_lam_Δk (Finmap.mem_keys.mpr h)
        have h_xε : x_lam ∉ ε := fun h => hx_lam_εk (Finmap.mem_keys.mpr h)
        have hbody_lc : Term.lc (Term.openVar x_lam e) := HasType.lc (d_body x_lam hx_lam_L)
        have h_x'_in_Δ : x' ∈ Δ := Finmap.mem_iff.mpr ⟨s_x', hx'⟩
        have h_x'_not_ε : x' ∉ ε := ctx.disjoint x' h_x'_in_Δ
        have h_x_lam_ne_x' : x_lam ≠ x' := fun heq => h_xΔ (heq ▸ h_x'_in_Δ)
        have h_x'_not_fv_s_x' : x' ∉ Space.fv s_x' := fun hin =>
          h_x'_not_ε (ctx.lin_fv_in_ε x' s_x' hx' x' hin)
        have h_x'_not_fv_s₀ : x' ∉ Space.fv s₀ := fun hin =>
          h_x'_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s hin))
        have h_x_lam_not_fv_s_x' : x_lam ∉ Space.fv s_x' := fun hin =>
          h_xε (ctx.lin_fv_in_ε x' s_x' hx' x_lam hin)
        have h_x_lam_not_fv_s₀ : x_lam ∉ Space.fv s₀ := fun hin =>
          h_xε (Finmap.mem_keys.mp (SValid.fv_closure d_s hin))
        -- ctx_inner over the extended Δ (with x_lam).
        have ctx_inner : CtxWF (Finmap.insert x_lam s₀ Δ) ε := {
          disjoint := fun x'' hx'' hx''_ε => by
            rcases Finmap.mem_insert.mp hx'' with rfl | hx_in_Δ
            · exact h_xε hx''_ε
            · exact ctx.disjoint x'' hx_in_Δ hx''_ε
          lin_fv_in_ε := fun x'' s'' hx'' z hz => by
            by_cases h_eq : x'' = x_lam
            · subst x''
              rw [Finmap.lookup_insert] at hx''
              have h_eq_s : s'' = s₀ := (Option.some.inj hx'').symm
              rw [h_eq_s] at hz
              exact Finmap.mem_keys.mp (SValid.fv_closure d_s hz)
            · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
              exact ctx.lin_fv_in_ε x'' s'' hx'' z hz
          nl_fv_in_ε := ctx.nl_fv_in_ε
        }
        -- Helper: build EnvWF (σ.bind x_lam v) (insert x_lam s₀ Δ) ε
        -- for any v that matches (denotSpace σ s₀).
        have build_wf_xlam : ∀ v : DVal,
            v.matchesShape (HType.hil (denotSpace σ s₀)) →
            EnvWF (σ.bind x_lam v) (Finmap.insert x_lam s₀ Δ) ε := by
          intro v h_v
          refine {
            lin_match := fun x'' s'' hx'' => ?_
            nl_match := fun x'' τ'' hx'' => ?_
          }
          · by_cases h_eq : x'' = x_lam
            · subst x''
              rw [Finmap.lookup_insert] at hx''
              have h_eq_s : s'' = s₀ := (Option.some.inj hx'').symm
              rw [h_eq_s]
              refine ⟨v, ?_, ?_⟩
              · simp [DEnv.bind, Finmap.lookup_insert]
              · have hd : denotSpace (σ.bind x_lam v) s₀ = denotSpace σ s₀ :=
                  denotSpace_agree s₀
                    (DEnv.AgreeOn.bind_left_of_not_mem h_x_lam_not_fv_s₀)
                rw [hd]; exact h_v
            · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
              obtain ⟨w, h_lookup, h_match⟩ := wf.lin_match x'' s'' hx''
              refine ⟨w, ?_, ?_⟩
              · simp [DEnv.bind, Finmap.lookup_insert_of_ne _ h_eq, h_lookup]
              · have h_xlam_not_fv : x_lam ∉ Space.fv s'' := fun hin =>
                  h_xε (ctx.lin_fv_in_ε x'' s'' hx'' x_lam hin)
                have hd : denotSpace (σ.bind x_lam v) s'' = denotSpace σ s'' :=
                  denotSpace_agree s''
                    (DEnv.AgreeOn.bind_left_of_not_mem h_xlam_not_fv)
                rw [hd]; exact h_match
          · have h_x_lam_ne_x'' : x_lam ≠ x'' := fun heq =>
              h_xε (heq ▸ Finmap.mem_of_lookup_eq_some hx'')
            obtain ⟨w, h_lookup, h_match⟩ := wf.nl_match x'' τ'' hx''
            refine ⟨w, ?_, ?_⟩
            · simp [DEnv.bind,
                    Finmap.lookup_insert_of_ne _ (Ne.symm h_x_lam_ne_x''),
                    h_lookup]
            · have h_xlam_not_fv : x_lam ∉ Ty.fv τ'' := fun hin =>
                h_xε (ctx.nl_fv_in_ε x'' τ'' hx'' x_lam hin)
              have hd : denotTy (σ.bind x_lam v) τ'' = denotTy σ τ'' :=
                denotTy_agree τ''
                  (DEnv.AgreeOn.bind_left_of_not_mem h_xlam_not_fv)
              rw [hd]; exact h_match
        -- The body's (b) at x_lam (under wf-of σ with x' rebound and
        -- x_lam dummy-bound): gives `IsLinearMap ℝ (fun y_c => ...)`.
        -- We use it parameterically over y_outer via x' rebinding through bind_lin.
        show IsLinearMap ℝ _
        -- Unfold the .llam denot and atSpace.
        have V₀ := denotSpace σ s₀
        have h_V_dual : denotSpace σ (.dual s₀) = HSpace.dual (denotSpace σ s₀) := rfl
        -- For each y_outer, denotation collapses to `LinearMap.ofFun g_y`.
        have h_fun_eq : (fun y : (denotSpace σ s_x').carrier =>
            (denotTerm (σ.bind x' (.hil ⟨denotSpace σ s_x', y⟩))
                (.llam s₀ Space.real e)).atSpace (denotSpace σ (.dual s₀)))
            = (fun y => LinearMap.ofFun (fun y_c : (denotSpace σ s₀).carrier =>
                (denotTerm ((σ.bind x' (.hil ⟨denotSpace σ s_x', y⟩)).bind x_lam
                              (.hil ⟨denotSpace σ s₀, y_c⟩)) (Term.openVar x_lam e)).atSpace
                              HSpace.real)) := by
          funext y
          have hd_s₀ : denotSpace (σ.bind x' (.hil ⟨denotSpace σ s_x', y⟩)) s₀
                     = denotSpace σ s₀ :=
            denotSpace_agree s₀
              (DEnv.AgreeOn.bind_left_of_not_mem h_x'_not_fv_s₀)
          rw [denotTerm_llam_real, hd_s₀]
          show (llamRealDVal (denotSpace σ s₀) _).atSpace (HSpace.dual (denotSpace σ s₀)) = _
          unfold llamRealDVal
          rw [DVal.atSpace_hil_self]
          -- D1: convert the env-fiber `denotTermAux env [v] e` to the named form.
          refine congrArg LinearMap.ofFun (funext fun y_c => ?_)
          exact congrArg (DVal.atSpace HSpace.real)
            (denotTerm_openVar_bind hbody_lc hx_lam_fve).symm
        rw [h_fun_eq]

        refine IsLinearMap.ofFun_param ?h_lin_v ?h_lin_y
        case h_lin_v =>
          -- ∀ y_outer, IsLinearMap ℝ (fun y_c => body atSpace at σ.bind x' y_outer.bind x_lam y_c).
          intro y_outer
          -- The body's IH(b) at x_lam under wf_inner_y_outer (σ.bind x' y_outer
          -- extended with x_lam dummy-bound).
          have wf_outer_rebound :
              EnvWF (σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)) Δ ε :=
            wf.bind_lin ctx hx' y_outer
          -- Extend with x_lam binding for soundness invocation.
          have wf_inner_y_outer :
              EnvWF ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                        (.hil ⟨denotSpace σ s₀, 0⟩))
                    (Finmap.insert x_lam s₀ Δ) ε := by
            have h_v : (DVal.hil ⟨denotSpace σ s₀, (0 : (denotSpace σ s₀).carrier)⟩).matchesShape
                          (HType.hil (denotSpace σ s₀)) :=
              DVal.matchesShape_hil_rfl _ _
            -- Build the EnvWF manually using h_v.
            refine {
              lin_match := fun x'' s'' hx'' => ?_
              nl_match := fun x'' τ'' hx'' => ?_
            }
            · by_cases h_eq : x'' = x_lam
              · subst x''
                rw [Finmap.lookup_insert] at hx''
                have h_eq_s : s'' = s₀ := (Option.some.inj hx'').symm
                rw [h_eq_s]
                refine ⟨.hil ⟨denotSpace σ s₀, 0⟩, ?_, ?_⟩
                · simp [DEnv.bind, Finmap.lookup_insert]
                · have hd : denotSpace
                              ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                                  (.hil ⟨denotSpace σ s₀, 0⟩)) s₀ = denotSpace σ s₀ := by
                    apply denotSpace_agree
                    refine ⟨fun z hz => ?_⟩
                    have h_z_ne_xlam : z ≠ x_lam := fun heq => h_x_lam_not_fv_s₀ (heq ▸ hz)
                    have h_z_ne_x' : z ≠ x' := fun heq => h_x'_not_fv_s₀ (heq ▸ hz)
                    simp [DEnv.bind, Finmap.lookup_insert_of_ne _ h_z_ne_xlam,
                          Finmap.lookup_insert_of_ne _ h_z_ne_x']
                  rw [hd]
                  exact h_v
              · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
                obtain ⟨w, h_lookup, h_match⟩ := wf_outer_rebound.lin_match x'' s'' hx''
                refine ⟨w, ?_, ?_⟩
                · show Finmap.lookup x''
                       (Finmap.insert x_lam _
                         (Finmap.insert x' (.hil ⟨denotSpace σ s_x', y_outer⟩) σ.vars)) = some w
                  rw [Finmap.lookup_insert_of_ne _ h_eq]
                  exact h_lookup
                · have h_xlam_not_fv : x_lam ∉ Space.fv s'' := fun hin =>
                    h_xε (ctx.lin_fv_in_ε x'' s'' hx'' x_lam hin)
                  have hd : denotSpace
                              ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                                  (.hil ⟨denotSpace σ s₀, 0⟩)) s''
                          = denotSpace (σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)) s'' :=
                    denotSpace_agree s''
                      (DEnv.AgreeOn.bind_left_of_not_mem h_xlam_not_fv)
                  rw [hd]
                  exact h_match
            · have h_x_lam_ne_x'' : x_lam ≠ x'' := fun heq =>
                h_xε (heq ▸ Finmap.mem_of_lookup_eq_some hx'')
              obtain ⟨w, h_lookup, h_match⟩ := wf_outer_rebound.nl_match x'' τ'' hx''
              refine ⟨w, ?_, ?_⟩
              · show Finmap.lookup x''
                     (Finmap.insert x_lam _
                       (Finmap.insert x' (.hil ⟨denotSpace σ s_x', y_outer⟩) σ.vars)) = some w
                rw [Finmap.lookup_insert_of_ne _ (Ne.symm h_x_lam_ne_x'')]
                exact h_lookup
              · have h_xlam_not_fv : x_lam ∉ Ty.fv τ'' := fun hin =>
                  h_xε (ctx.nl_fv_in_ε x'' τ'' hx'' x_lam hin)
                have hd : denotTy
                            ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                                (.hil ⟨denotSpace σ s₀, 0⟩)) τ''
                        = denotTy (σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)) τ'' :=
                  denotTy_agree τ''
                    (DEnv.AgreeOn.bind_left_of_not_mem h_xlam_not_fv)
                rw [hd]
                exact h_match
          have ih_lam := (soundness (d_body x_lam hx_lam_L) ctx_inner wf_inner_y_outer).2 x_lam s₀
                            (by simp [Finmap.lookup_insert])
          dsimp only [LinearAtVar] at ih_lam
          -- ih_lam: IsLinearMap ℝ (fun y_c => body atSpace at σ'.bind x_lam ⟨V₀_σ', y_c⟩)
          -- where σ' = σ.bind x' ... .bind x_lam ⟨V₀, 0⟩.
          -- σ'.bind x_lam ⟨V₀_σ', y_c⟩ overwrites the x_lam binding → σ.bind x' .bind x_lam ⟨V₀_σ', y_c⟩.
          have h_V₀_eq : denotSpace ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                                      (.hil ⟨denotSpace σ s₀, 0⟩)) s₀
                       = denotSpace σ s₀ := by
            apply denotSpace_agree
            refine ⟨fun z hz => ?_⟩
            have h_z_ne_xlam : z ≠ x_lam := fun heq => h_x_lam_not_fv_s₀ (heq ▸ hz)
            have h_z_ne_x' : z ≠ x' := fun heq => h_x'_not_fv_s₀ (heq ▸ hz)
            simp [DEnv.bind, Finmap.lookup_insert_of_ne _ h_z_ne_xlam,
                  Finmap.lookup_insert_of_ne _ h_z_ne_x']
          rw [h_V₀_eq] at ih_lam
          -- Goal: IsLinearMap ℝ (fun y_c => body atSpace at σ.bind x' .bind x_lam ⟨V₀, y_c⟩)
          -- ih_lam: same after .bind x_lam ⟨V₀, 0⟩ + .bind x_lam ⟨V₀, y_c⟩ overwrites to the second.
          refine IsLinearMap.congr ih_lam ?_
          intro y_c
          show DVal.atSpace HSpace.real _ = DVal.atSpace HSpace.real _
          rw [DEnv.bind_overwrite]
        case h_lin_y =>
          -- ∀ y_c, IsLinearMap ℝ (fun y_outer => body atSpace at σ.bind x' y_outer.bind x_lam y_c).
          intro y_c
          -- The body's IH(b) at x' under wf_inner_y_c (σ.bind x_lam ⟨V₀, y_c⟩).
          have wf_inner_y_c :
              EnvWF (σ.bind x_lam (.hil ⟨denotSpace σ s₀, y_c⟩))
                    (Finmap.insert x_lam s₀ Δ) ε :=
            build_wf_xlam _ (DVal.matchesShape_hil_rfl _ _)
          have hx'_in_inner : (Finmap.insert x_lam s₀ Δ).lookup x' = some s_x' := by
            rw [Finmap.lookup_insert_of_ne _ (Ne.symm h_x_lam_ne_x')]; exact hx'
          have ih_x' := (soundness (d_body x_lam hx_lam_L) ctx_inner wf_inner_y_c).2 x' s_x' hx'_in_inner
          dsimp only [LinearAtVar] at ih_x'
          -- ih_x': IsLinearMap ℝ (fun y => body atSpace at σ.bind x_lam ... .bind x' ⟨V_x'_σ', y⟩)
          -- where σ' = σ.bind x_lam (.hil ⟨V₀, y_c⟩).
          -- σ'.bind x' ⟨V_x'_σ', y⟩ = (σ.bind x_lam ...).bind x' ⟨V_x'_σ', y⟩
          --   = σ.bind x' ⟨V_x'_σ, y⟩ .bind x_lam ... (by bind_comm)
          -- with V_x'_σ' = V_x'_σ by FV-irrelevance.
          have h_V_x'_eq : denotSpace (σ.bind x_lam (.hil ⟨denotSpace σ s₀, y_c⟩)) s_x'
                         = denotSpace σ s_x' :=
            denotSpace_agree s_x'
              (DEnv.AgreeOn.bind_left_of_not_mem h_x_lam_not_fv_s_x')
          rw [h_V_x'_eq] at ih_x'
          refine IsLinearMap.congr ih_x' ?_
          intro y
          show DVal.atSpace HSpace.real _ = DVal.atSpace HSpace.real _
          rw [DEnv.bind_comm _ _ h_x_lam_ne_x']
  | @HasType.llam_tensor Δ ε s₀ s e L hs_ne d_s₀ d_s d_body =>
      refine ⟨?_, ?_⟩
      · -- (a) result is `.hil ⟨HSpace.tprod (HSpace.dual V₀) V₁, _⟩` via llamTensorDVal.
        show (denotTerm σ (.llam _ s _)).matchesShape _
        rw [denotTerm_llam_non_real hs_ne]
        exact DVal.matchesShape_hil_rfl _ _
      · -- (b) Same structure as .llam_real (b) but using llamTensorDVal; D1: fresh
        -- x_lam + open-bridge converts the env-fiber to the named form.
        intro x' s_x' hx'
        obtain ⟨x_lam, hx_lam⟩ := Infinite.exists_notMem_finset
          (Δ.keys ∪ ε.keys ∪ L ∪ Term.fv e)
        simp only [Finset.mem_union, not_or] at hx_lam
        obtain ⟨⟨⟨hx_lam_Δk, hx_lam_εk⟩, hx_lam_L⟩, hx_lam_fve⟩ := hx_lam
        have h_xΔ : x_lam ∉ Δ := fun h => hx_lam_Δk (Finmap.mem_keys.mpr h)
        have h_xε : x_lam ∉ ε := fun h => hx_lam_εk (Finmap.mem_keys.mpr h)
        have hbody_lc : Term.lc (Term.openVar x_lam e) := HasType.lc (d_body x_lam hx_lam_L)
        have h_x'_in_Δ : x' ∈ Δ := Finmap.mem_iff.mpr ⟨s_x', hx'⟩
        have h_x'_not_ε : x' ∉ ε := ctx.disjoint x' h_x'_in_Δ
        have h_x_lam_ne_x' : x_lam ≠ x' := fun heq => h_xΔ (heq ▸ h_x'_in_Δ)
        have h_x'_not_fv_s_x' : x' ∉ Space.fv s_x' := fun hin =>
          h_x'_not_ε (ctx.lin_fv_in_ε x' s_x' hx' x' hin)
        have h_x'_not_fv_s₀ : x' ∉ Space.fv s₀ := fun hin =>
          h_x'_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s₀ hin))
        have h_x'_not_fv_s : x' ∉ Space.fv s := fun hin =>
          h_x'_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s hin))
        have h_x_lam_not_fv_s_x' : x_lam ∉ Space.fv s_x' := fun hin =>
          h_xε (ctx.lin_fv_in_ε x' s_x' hx' x_lam hin)
        have h_x_lam_not_fv_s₀ : x_lam ∉ Space.fv s₀ := fun hin =>
          h_xε (Finmap.mem_keys.mp (SValid.fv_closure d_s₀ hin))
        have h_x_lam_not_fv_s : x_lam ∉ Space.fv s := fun hin =>
          h_xε (Finmap.mem_keys.mp (SValid.fv_closure d_s hin))
        have ctx_inner : CtxWF (Finmap.insert x_lam s₀ Δ) ε := {
          disjoint := fun x'' hx'' hx''_ε => by
            rcases Finmap.mem_insert.mp hx'' with rfl | hx_in_Δ
            · exact h_xε hx''_ε
            · exact ctx.disjoint x'' hx_in_Δ hx''_ε
          lin_fv_in_ε := fun x'' s'' hx'' z hz => by
            by_cases h_eq : x'' = x_lam
            · subst x''
              rw [Finmap.lookup_insert] at hx''
              have h_eq_s : s'' = s₀ := (Option.some.inj hx'').symm
              rw [h_eq_s] at hz
              exact Finmap.mem_keys.mp (SValid.fv_closure d_s₀ hz)
            · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
              exact ctx.lin_fv_in_ε x'' s'' hx'' z hz
          nl_fv_in_ε := ctx.nl_fv_in_ε
        }
        have build_wf_xlam : ∀ v : DVal,
            v.matchesShape (HType.hil (denotSpace σ s₀)) →
            EnvWF (σ.bind x_lam v) (Finmap.insert x_lam s₀ Δ) ε := by
          intro v h_v
          refine {
            lin_match := fun x'' s'' hx'' => ?_
            nl_match := fun x'' τ'' hx'' => ?_
          }
          · by_cases h_eq : x'' = x_lam
            · subst x''
              rw [Finmap.lookup_insert] at hx''
              have h_eq_s : s'' = s₀ := (Option.some.inj hx'').symm
              rw [h_eq_s]
              refine ⟨v, ?_, ?_⟩
              · simp [DEnv.bind, Finmap.lookup_insert]
              · have hd : denotSpace (σ.bind x_lam v) s₀ = denotSpace σ s₀ :=
                  denotSpace_agree s₀
                    (DEnv.AgreeOn.bind_left_of_not_mem h_x_lam_not_fv_s₀)
                rw [hd]; exact h_v
            · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
              obtain ⟨w, h_lookup, h_match⟩ := wf.lin_match x'' s'' hx''
              refine ⟨w, ?_, ?_⟩
              · simp [DEnv.bind, Finmap.lookup_insert_of_ne _ h_eq, h_lookup]
              · have h_xlam_not_fv : x_lam ∉ Space.fv s'' := fun hin =>
                  h_xε (ctx.lin_fv_in_ε x'' s'' hx'' x_lam hin)
                have hd : denotSpace (σ.bind x_lam v) s'' = denotSpace σ s'' :=
                  denotSpace_agree s''
                    (DEnv.AgreeOn.bind_left_of_not_mem h_xlam_not_fv)
                rw [hd]; exact h_match
          · have h_x_lam_ne_x'' : x_lam ≠ x'' := fun heq =>
              h_xε (heq ▸ Finmap.mem_of_lookup_eq_some hx'')
            obtain ⟨w, h_lookup, h_match⟩ := wf.nl_match x'' τ'' hx''
            refine ⟨w, ?_, ?_⟩
            · simp [DEnv.bind,
                    Finmap.lookup_insert_of_ne _ (Ne.symm h_x_lam_ne_x''),
                    h_lookup]
            · have h_xlam_not_fv : x_lam ∉ Ty.fv τ'' := fun hin =>
                h_xε (ctx.nl_fv_in_ε x'' τ'' hx'' x_lam hin)
              have hd : denotTy (σ.bind x_lam v) τ'' = denotTy σ τ'' :=
                denotTy_agree τ''
                  (DEnv.AgreeOn.bind_left_of_not_mem h_xlam_not_fv)
              rw [hd]; exact h_match
        show IsLinearMap ℝ _
        -- For each y_outer, denotation collapses to (dualTensorHomEquiv).symm (LinearMap.ofFun g_y).
        have h_fun_eq : (fun y : (denotSpace σ s_x').carrier =>
            (denotTerm (σ.bind x' (.hil ⟨denotSpace σ s_x', y⟩))
                (.llam s₀ s e)).atSpace (denotSpace σ (.tprod (.dual s₀) s)))
            = (fun y =>
                (dualTensorHomEquiv ℝ (denotSpace σ s₀).carrier (denotSpace σ s).carrier).symm
                  (LinearMap.ofFun (fun y_c : (denotSpace σ s₀).carrier =>
                    ((denotTerm ((σ.bind x' (.hil ⟨denotSpace σ s_x', y⟩)).bind x_lam
                                  (.hil ⟨denotSpace σ s₀, y_c⟩)) (Term.openVar x_lam e)).atSpace
                                    (denotSpace σ s))))) := by
          funext y
          have hd_s₀ : denotSpace (σ.bind x' (.hil ⟨denotSpace σ s_x', y⟩)) s₀
                     = denotSpace σ s₀ :=
            denotSpace_agree s₀
              (DEnv.AgreeOn.bind_left_of_not_mem h_x'_not_fv_s₀)
          have hd_s : denotSpace (σ.bind x' (.hil ⟨denotSpace σ s_x', y⟩)) s
                    = denotSpace σ s :=
            denotSpace_agree s
              (DEnv.AgreeOn.bind_left_of_not_mem h_x'_not_fv_s)
          rw [denotTerm_llam_non_real hs_ne, hd_s₀, hd_s]
          show (llamTensorDVal (denotSpace σ s₀) (denotSpace σ s) _).atSpace
                  (HSpace.tprod (HSpace.dual (denotSpace σ s₀)) (denotSpace σ s)) = _
          unfold llamTensorDVal
          rw [DVal.atSpace_hil_self]
          -- D1: convert the env-fiber `denotTermAux env [v] e` to the named form.
          refine congrArg (dualTensorHomEquiv ℝ (denotSpace σ s₀).carrier (denotSpace σ s).carrier).symm
            (congrArg LinearMap.ofFun (funext fun y_c => ?_))
          exact congrArg (DVal.atSpace (denotSpace σ s))
            (denotTerm_openVar_bind hbody_lc hx_lam_fve).symm
        rw [h_fun_eq]
        -- Compose IsLinearMap.ofFun_param with (dualTensorHomEquiv).symm.
        -- The .symm is a LinearEquiv, so it preserves linearity.
        let L := dualTensorHomEquiv ℝ (denotSpace σ s₀).carrier (denotSpace σ s).carrier
        suffices h_inner :
            IsLinearMap ℝ (fun y : (denotSpace σ s_x').carrier =>
              LinearMap.ofFun (fun y_c : (denotSpace σ s₀).carrier =>
                ((denotTerm ((σ.bind x' (.hil ⟨denotSpace σ s_x', y⟩)).bind x_lam
                              (.hil ⟨denotSpace σ s₀, y_c⟩)) (Term.openVar x_lam e)).atSpace
                                (denotSpace σ s)))) by
          refine ⟨fun y₁ y₂ => ?_, fun c y => ?_⟩
          · show L.symm _ = L.symm _ + L.symm _
            rw [h_inner.map_add]; exact L.symm.map_add _ _
          · show L.symm _ = c • L.symm _
            rw [h_inner.map_smul]; exact L.symm.map_smul _ _
        refine IsLinearMap.ofFun_param ?h_lin_v ?h_lin_y
        case h_lin_v =>
          intro y_outer
          have wf_outer_rebound :
              EnvWF (σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)) Δ ε :=
            wf.bind_lin ctx hx' y_outer
          have h_v : (DVal.hil ⟨denotSpace σ s₀, (0 : (denotSpace σ s₀).carrier)⟩).matchesShape
                          (HType.hil (denotSpace σ s₀)) :=
              DVal.matchesShape_hil_rfl _ _
          have wf_inner_y_outer :
              EnvWF ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                        (.hil ⟨denotSpace σ s₀, 0⟩))
                    (Finmap.insert x_lam s₀ Δ) ε := by
            refine {
              lin_match := fun x'' s'' hx'' => ?_
              nl_match := fun x'' τ'' hx'' => ?_
            }
            · by_cases h_eq : x'' = x_lam
              · subst x''
                rw [Finmap.lookup_insert] at hx''
                have h_eq_s : s'' = s₀ := (Option.some.inj hx'').symm
                rw [h_eq_s]
                refine ⟨.hil ⟨denotSpace σ s₀, 0⟩, ?_, ?_⟩
                · simp [DEnv.bind, Finmap.lookup_insert]
                · have hd : denotSpace
                              ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                                  (.hil ⟨denotSpace σ s₀, 0⟩)) s₀ = denotSpace σ s₀ := by
                    apply denotSpace_agree
                    refine ⟨fun z hz => ?_⟩
                    have h_z_ne_xlam : z ≠ x_lam := fun heq => h_x_lam_not_fv_s₀ (heq ▸ hz)
                    have h_z_ne_x' : z ≠ x' := fun heq => h_x'_not_fv_s₀ (heq ▸ hz)
                    simp [DEnv.bind, Finmap.lookup_insert_of_ne _ h_z_ne_xlam,
                          Finmap.lookup_insert_of_ne _ h_z_ne_x']
                  rw [hd]; exact h_v
              · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
                obtain ⟨w, h_lookup, h_match⟩ := wf_outer_rebound.lin_match x'' s'' hx''
                refine ⟨w, ?_, ?_⟩
                · show Finmap.lookup x''
                       (Finmap.insert x_lam _
                         (Finmap.insert x' (.hil ⟨denotSpace σ s_x', y_outer⟩) σ.vars)) = some w
                  rw [Finmap.lookup_insert_of_ne _ h_eq]
                  exact h_lookup
                · have h_xlam_not_fv : x_lam ∉ Space.fv s'' := fun hin =>
                    h_xε (ctx.lin_fv_in_ε x'' s'' hx'' x_lam hin)
                  have hd : denotSpace
                              ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                                  (.hil ⟨denotSpace σ s₀, 0⟩)) s''
                          = denotSpace (σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)) s'' :=
                    denotSpace_agree s''
                      (DEnv.AgreeOn.bind_left_of_not_mem h_xlam_not_fv)
                  rw [hd]; exact h_match
            · have h_x_lam_ne_x'' : x_lam ≠ x'' := fun heq =>
                h_xε (heq ▸ Finmap.mem_of_lookup_eq_some hx'')
              obtain ⟨w, h_lookup, h_match⟩ := wf_outer_rebound.nl_match x'' τ'' hx''
              refine ⟨w, ?_, ?_⟩
              · show Finmap.lookup x''
                     (Finmap.insert x_lam _
                       (Finmap.insert x' (.hil ⟨denotSpace σ s_x', y_outer⟩) σ.vars)) = some w
                rw [Finmap.lookup_insert_of_ne _ (Ne.symm h_x_lam_ne_x'')]
                exact h_lookup
              · have h_xlam_not_fv : x_lam ∉ Ty.fv τ'' := fun hin =>
                  h_xε (ctx.nl_fv_in_ε x'' τ'' hx'' x_lam hin)
                have hd : denotTy
                            ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                                (.hil ⟨denotSpace σ s₀, 0⟩)) τ''
                        = denotTy (σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)) τ'' :=
                  denotTy_agree τ''
                    (DEnv.AgreeOn.bind_left_of_not_mem h_xlam_not_fv)
                rw [hd]; exact h_match
          have ih_lam := (soundness (d_body x_lam hx_lam_L) ctx_inner wf_inner_y_outer).2 x_lam s₀
                            (by simp [Finmap.lookup_insert])
          dsimp only [LinearAtVar] at ih_lam
          have h_V₀_eq : denotSpace ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                                      (.hil ⟨denotSpace σ s₀, 0⟩)) s₀
                       = denotSpace σ s₀ := by
            apply denotSpace_agree
            refine ⟨fun z hz => ?_⟩
            have h_z_ne_xlam : z ≠ x_lam := fun heq => h_x_lam_not_fv_s₀ (heq ▸ hz)
            have h_z_ne_x' : z ≠ x' := fun heq => h_x'_not_fv_s₀ (heq ▸ hz)
            simp [DEnv.bind, Finmap.lookup_insert_of_ne _ h_z_ne_xlam,
                  Finmap.lookup_insert_of_ne _ h_z_ne_x']
          have h_V_eq : denotSpace ((σ.bind x' (.hil ⟨denotSpace σ s_x', y_outer⟩)).bind x_lam
                                      (.hil ⟨denotSpace σ s₀, 0⟩)) s
                       = denotSpace σ s := by
            apply denotSpace_agree
            refine ⟨fun z hz => ?_⟩
            have h_z_ne_xlam : z ≠ x_lam := fun heq => h_x_lam_not_fv_s (heq ▸ hz)
            have h_z_ne_x' : z ≠ x' := fun heq => h_x'_not_fv_s (heq ▸ hz)
            simp [DEnv.bind, Finmap.lookup_insert_of_ne _ h_z_ne_xlam,
                  Finmap.lookup_insert_of_ne _ h_z_ne_x']
          rw [h_V₀_eq, h_V_eq] at ih_lam
          refine IsLinearMap.congr ih_lam ?_
          intro y_c
          rw [DEnv.bind_overwrite]
        case h_lin_y =>
          intro y_c
          have wf_inner_y_c :
              EnvWF (σ.bind x_lam (.hil ⟨denotSpace σ s₀, y_c⟩))
                    (Finmap.insert x_lam s₀ Δ) ε :=
            build_wf_xlam _ (DVal.matchesShape_hil_rfl _ _)
          have hx'_in_inner : (Finmap.insert x_lam s₀ Δ).lookup x' = some s_x' := by
            rw [Finmap.lookup_insert_of_ne _ (Ne.symm h_x_lam_ne_x')]; exact hx'
          have ih_x' := (soundness (d_body x_lam hx_lam_L) ctx_inner wf_inner_y_c).2 x' s_x' hx'_in_inner
          dsimp only [LinearAtVar] at ih_x'
          have h_V_x'_eq : denotSpace (σ.bind x_lam (.hil ⟨denotSpace σ s₀, y_c⟩)) s_x'
                         = denotSpace σ s_x' :=
            denotSpace_agree s_x'
              (DEnv.AgreeOn.bind_left_of_not_mem h_x_lam_not_fv_s_x')
          have h_V_eq : denotSpace (σ.bind x_lam (.hil ⟨denotSpace σ s₀, y_c⟩)) s
                       = denotSpace σ s :=
            denotSpace_agree s
              (DEnv.AgreeOn.bind_left_of_not_mem h_x_lam_not_fv_s)
          rw [h_V_x'_eq, h_V_eq] at ih_x'
          refine IsLinearMap.congr ih_x' ?_
          intro y
          rw [DEnv.bind_comm _ _ h_x_lam_ne_x']
  | @HasType.dsumE _ _ e₀ e₁ s₀ s₁ d_s₀ d_s₁ d₀ d₁ =>
      refine ⟨?_, ?_⟩
      · have ih₀ := soundness d₀ ctx wf
        have ih₁ := soundness d₁ ctx wf
        obtain ⟨v₀, h_e0⟩ := DVal.matchesShape_hil_eq ih₀.1
        obtain ⟨v₁, h_e1⟩ := DVal.matchesShape_hil_eq ih₁.1
        show (denotTerm σ (.dsumE e₀ e₁)).matchesShape (HType.hil _)
        unfold denotTerm denotTermAux
        simp only [denotTerm] at h_e0 h_e1
        rw [h_e0, h_e1]
        exact DVal.matchesShape_hil_rfl _ _
      · intro x s' hx
        show IsLinearMap ℝ _
        have ih₀_b := (soundness d₀ ctx wf).2 x s' hx
        have ih₁_b := (soundness d₁ ctx wf).2 x s' hx
        dsimp only [LinearAtVar] at ih₀_b ih₁_b
        have h_x_in_Δ : x ∈ (_ : LCtx) := Finmap.mem_iff.mpr ⟨s', hx⟩
        have h_x_not_ε := ctx.disjoint x h_x_in_Δ
        have h_x_not_fv_s₀ : x ∉ Space.fv s₀ := fun hin =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s₀ hin))
        have h_x_not_fv_s₁ : x ∉ Space.fv s₁ := fun hin =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s₁ hin))
        have h_fun_eq :
            (fun y : (denotSpace σ s').carrier =>
              (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.dsumE e₀ e₁)).atSpace
                  (denotSpace σ (.dsum s₀ s₁))) =
            (fun y =>
              ((denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).atSpace
                  (denotSpace σ s₀),
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁).atSpace
                  (denotSpace σ s₁))) := by
          funext y
          have wf' : EnvWF (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) _ _ :=
            wf.bind_lin ctx hx y
          have ih₀_a := (soundness d₀ ctx wf').1
          have ih₁_a := (soundness d₁ ctx wf').1
          rw [denotTy_space] at ih₀_a ih₁_a
          have hd₀ : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s₀ =
                     denotSpace σ s₀ :=
            denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s₀)
          have hd₁ : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s₁ =
                     denotSpace σ s₁ :=
            denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s₁)
          rw [hd₀] at ih₀_a
          rw [hd₁] at ih₁_a
          show ((DVal.hil ⟨HSpace.dsum (denotTerm _ e₀).asHil.fst
                                       (denotTerm _ e₁).asHil.fst,
                            ((denotTerm _ e₀).asHil.snd,
                             (denotTerm _ e₁).asHil.snd)⟩)).atSpace _ = _
          show (DVal.hil ⟨_, _⟩).atSpace
              (HSpace.dsum (denotSpace σ s₀) (denotSpace σ s₁)) = _
          exact DVal.dsumE_atSpace_eq ih₀_a ih₁_a
        rw [h_fun_eq]
        exact IsLinearMap.prod_mk ih₀_b ih₁_b
  | @HasType.tprodE Δ₀ Δ₁ _ e₀ e₁ s₀ s₁ d_s₀ d_s₁ hsplit d₀ d₁ =>
      have hsub₀ : ∀ x s, Δ₀.lookup x = some s → (Δ₀ ∪ Δ₁).lookup x = some s := fun x s h => by
        rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some h)]; exact h
      have hsub₁ : ∀ x s, Δ₁.lookup x = some s → (Δ₀ ∪ Δ₁).lookup x = some s := fun x s h => by
        have h_mem : x ∈ Δ₁ := Finmap.mem_of_lookup_eq_some h
        have h_not : x ∉ Δ₀ := fun h' => @hsplit x h' h_mem
        rw [Finmap.lookup_union_right h_not]; exact h
      have ctx₀ : CtxWF Δ₀ _ := ctx.of_sub_Δ hsub₀
      have ctx₁ : CtxWF Δ₁ _ := ctx.of_sub_Δ hsub₁
      have wf₀ : EnvWF σ Δ₀ _ := wf.of_sub_Δ hsub₀
      have wf₁ : EnvWF σ Δ₁ _ := wf.of_sub_Δ hsub₁
      refine ⟨?_, ?_⟩
      · have ih₀ := soundness d₀ ctx₀ wf₀
        have ih₁ := soundness d₁ ctx₁ wf₁
        obtain ⟨v₀, h_e0⟩ := DVal.matchesShape_hil_eq ih₀.1
        obtain ⟨v₁, h_e1⟩ := DVal.matchesShape_hil_eq ih₁.1
        show (denotTerm σ (.tprodE e₀ e₁)).matchesShape (HType.hil _)
        unfold denotTerm denotTermAux
        simp only [denotTerm] at h_e0 h_e1
        rw [h_e0, h_e1]
        exact DVal.matchesShape_hil_rfl _ _
      · intro x s' hx
        show IsLinearMap ℝ _
        have h_x_in : x ∈ Δ₀ ∪ Δ₁ := Finmap.mem_iff.mpr ⟨s', hx⟩
        have h_x_not_ε := ctx.disjoint x h_x_in
        have h_x_not_fv_s₀ : x ∉ Space.fv s₀ := fun hin =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s₀ hin))
        have h_x_not_fv_s₁ : x ∉ Space.fv s₁ := fun hin =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s₁ hin))
        by_cases hx_Δ₀ : x ∈ Δ₀
        · -- e₀ varies; e₁ constant.
          have hx₀ : Δ₀.lookup x = some s' := by
            rw [Finmap.lookup_union_left hx_Δ₀] at hx; exact hx
          have ih₀_b := (soundness d₀ ctx₀ wf₀).2 x s' hx₀
          dsimp only [LinearAtVar] at ih₀_b
          have hx_not_Δ₁ : x ∉ Δ₁ := fun hin => @hsplit x hx_Δ₀ hin
          have hx_not_fv_e₁ : x ∉ Term.fv e₁ := fun hin =>
            (Finset.mem_union.mp (HasType.fv_closure d₁ hin)).elim
              (fun h => hx_not_Δ₁ (Finmap.mem_keys.mp h))
              (fun h => h_x_not_ε (Finmap.mem_keys.mp h))
          have h_e1_const : ∀ y : (denotSpace σ s').carrier,
              denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁ = denotTerm σ e₁ := fun y =>
            denotTerm_agree e₁ (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_e₁)
          have ih₁_a := (soundness d₁ ctx₁ wf₁).1
          rw [denotTy_space] at ih₁_a
          have h_fun_eq :
              (fun y : (denotSpace σ s').carrier =>
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.tprodE e₀ e₁)).atSpace
                    (denotSpace σ (.tprod s₀ s₁))) =
              (fun y => (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).atSpace
                          (denotSpace σ s₀) ⊗ₜ[ℝ]
                        (denotTerm σ e₁).atSpace (denotSpace σ s₁)) := by
            funext y
            have wf' : EnvWF (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) Δ₀ _ :=
              (wf.bind_lin ctx hx y).of_sub_Δ hsub₀
            have ih₀_a := (soundness d₀ ctx₀ wf').1
            rw [denotTy_space] at ih₀_a
            have hd₀ : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s₀ =
                       denotSpace σ s₀ :=
              denotSpace_agree s₀ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s₀)
            rw [hd₀] at ih₀_a
            show (DVal.hil ⟨HSpace.tprod (denotTerm _ e₀).asHil.fst
                            (denotTerm _ e₁).asHil.fst,
                          (denotTerm _ e₀).asHil.snd ⊗ₜ[ℝ]
                            (denotTerm _ e₁).asHil.snd⟩).atSpace _ = _
            rw [h_e1_const y]
            exact DVal.tprodE_atSpace_eq ih₀_a ih₁_a
          rw [h_fun_eq]
          exact IsLinearMap.tmul_const ih₀_b _
        · -- e₁ varies; e₀ constant.
          have hx_Δ₁ : x ∈ Δ₁ := by
            rcases Finmap.mem_union.mp h_x_in with h | h
            · exact absurd h hx_Δ₀
            · exact h
          have hx₁ : Δ₁.lookup x = some s' := by
            rw [Finmap.lookup_union_right hx_Δ₀] at hx; exact hx
          have ih₁_b := (soundness d₁ ctx₁ wf₁).2 x s' hx₁
          dsimp only [LinearAtVar] at ih₁_b
          have hx_not_fv_e₀ : x ∉ Term.fv e₀ := fun hin =>
            (Finset.mem_union.mp (HasType.fv_closure d₀ hin)).elim
              (fun h => hx_Δ₀ (Finmap.mem_keys.mp h))
              (fun h => h_x_not_ε (Finmap.mem_keys.mp h))
          have h_e0_const : ∀ y : (denotSpace σ s').carrier,
              denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀ = denotTerm σ e₀ := fun y =>
            denotTerm_agree e₀ (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_e₀)
          have ih₀_a := (soundness d₀ ctx₀ wf₀).1
          rw [denotTy_space] at ih₀_a
          have h_fun_eq :
              (fun y : (denotSpace σ s').carrier =>
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.tprodE e₀ e₁)).atSpace
                    (denotSpace σ (.tprod s₀ s₁))) =
              (fun y => (denotTerm σ e₀).atSpace (denotSpace σ s₀) ⊗ₜ[ℝ]
                        (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁).atSpace
                          (denotSpace σ s₁)) := by
            funext y
            have wf' : EnvWF (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) Δ₁ _ :=
              (wf.bind_lin ctx hx y).of_sub_Δ hsub₁
            have ih₁_a := (soundness d₁ ctx₁ wf').1
            rw [denotTy_space] at ih₁_a
            have hd₁ : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s₁ =
                       denotSpace σ s₁ :=
              denotSpace_agree s₁ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s₁)
            rw [hd₁] at ih₁_a
            show (DVal.hil ⟨HSpace.tprod (denotTerm _ e₀).asHil.fst
                            (denotTerm _ e₁).asHil.fst,
                          (denotTerm _ e₀).asHil.snd ⊗ₜ[ℝ]
                            (denotTerm _ e₁).asHil.snd⟩).atSpace _ = _
            rw [h_e0_const y]
            exact DVal.tprodE_atSpace_eq ih₀_a ih₁_a
          rw [h_fun_eq]
          exact IsLinearMap.const_tmul _ ih₁_b
  | @HasType.smul Δ₀ Δ₁ _ e₀ e₁ s d_s hsplit d₀ d₁ =>
      have hsub₀ : ∀ x s, Δ₀.lookup x = some s → (Δ₀ ∪ Δ₁).lookup x = some s := fun x s h => by
        rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some h)]; exact h
      have hsub₁ : ∀ x s, Δ₁.lookup x = some s → (Δ₀ ∪ Δ₁).lookup x = some s := fun x s h => by
        have h_mem : x ∈ Δ₁ := Finmap.mem_of_lookup_eq_some h
        have h_not : x ∉ Δ₀ := fun h' => @hsplit x h' h_mem
        rw [Finmap.lookup_union_right h_not]; exact h
      have ctx₀ : CtxWF Δ₀ _ := ctx.of_sub_Δ hsub₀
      have ctx₁ : CtxWF Δ₁ _ := ctx.of_sub_Δ hsub₁
      have wf₀ : EnvWF σ Δ₀ _ := wf.of_sub_Δ hsub₀
      have wf₁ : EnvWF σ Δ₁ _ := wf.of_sub_Δ hsub₁
      refine ⟨?_, ?_⟩
      · have ih₁ := soundness d₁ ctx₁ wf₁
        obtain ⟨v₁, h_e1⟩ := DVal.matchesShape_hil_eq ih₁.1
        show (denotTerm σ (.smul e₀ e₁)).matchesShape (HType.hil _)
        unfold denotTerm denotTermAux
        simp only [denotTerm] at h_e1
        rw [h_e1]
        exact DVal.matchesShape_hil_rfl _ _
      · intro x s' hx
        show IsLinearMap ℝ _
        -- x ∈ Δ₀ ∪ Δ₁. Case on which side.
        have h_x_in : x ∈ Δ₀ ∪ Δ₁ := Finmap.mem_iff.mpr ⟨s', hx⟩
        have h_x_not_ε : x ∉ _ := ctx.disjoint x h_x_in
        have h_x_not_fv_s : x ∉ Space.fv s := fun hin =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s hin))
        -- For each y, denotSpace σ_y s = denotSpace σ s by FV-irrelevance
        have h_d_eq : ∀ y : (denotSpace σ s').carrier,
            denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s = denotSpace σ s := fun y =>
          denotSpace_agree s (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s)
        by_cases hx_Δ₀ : x ∈ Δ₀
        · -- x ∈ Δ₀: linearity from d₀'s IH(b); e₁ is constant via FV-irrelevance.
          have hx₀ : Δ₀.lookup x = some s' := by
            rw [Finmap.lookup_union_left hx_Δ₀] at hx; exact hx
          have ih₀_b := (soundness d₀ ctx₀ wf₀).2 x s' hx₀
          dsimp only [LinearAtVar] at ih₀_b
          -- x ∉ Term.fv e₁ (since x ∈ Δ₀, disjoint from Δ₁; x ∉ ε via ctx.disjoint).
          have hx_not_Δ₁ : x ∉ Δ₁ := fun hin => @hsplit x hx_Δ₀ hin
          have hx_not_fv_e₁ : x ∉ Term.fv e₁ := fun hin =>
            (Finset.mem_union.mp (HasType.fv_closure d₁ hin)).elim
              (fun h => hx_not_Δ₁ (Finmap.mem_keys.mp h))
              (fun h => h_x_not_ε (Finmap.mem_keys.mp h))
          -- v_const = (denotTerm σ e₁).atSpace (denotSpace σ s)
          have h_e1_const : ∀ y : (denotSpace σ s').carrier,
              denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁ = denotTerm σ e₁ := fun y =>
            denotTerm_agree e₁ (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_e₁)
          have ih₁_a := (soundness d₁ ctx₁ wf₁).1
          rw [denotTy_space] at ih₁_a
          -- Pointwise reduction: f(y) = r(y) • v_const, where r is IH(b) on e₀.
          have h_fun_eq :
              (fun y : (denotSpace σ s').carrier =>
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.smul e₀ e₁)).atSpace
                    (denotSpace σ s)) =
              (fun y => (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).atSpace
                          HSpace.real • (denotTerm σ e₁).atSpace (denotSpace σ s)) := by
            funext y
            show ((DVal.hil ⟨(denotTerm _ e₁).asHil.fst,
                  (denotTerm _ e₀).asReal • (denotTerm _ e₁).asHil.snd⟩)).atSpace
                  (denotSpace σ s) = _
            rw [h_e1_const y]
            rw [DVal.smul_hil_atSpace_eq _ ih₁_a]
            rfl
          rw [h_fun_eq]
          exact IsLinearMap.smul_const ih₀_b _
        · -- x ∈ Δ₁: linearity from d₁'s IH(b); e₀ is constant via FV-irrelevance.
          have hx_Δ₁ : x ∈ Δ₁ := by
            rcases Finmap.mem_union.mp h_x_in with h | h
            · exact absurd h hx_Δ₀
            · exact h
          have hx₁ : Δ₁.lookup x = some s' := by
            rw [Finmap.lookup_union_right hx_Δ₀] at hx; exact hx
          have ih₁_b := (soundness d₁ ctx₁ wf₁).2 x s' hx₁
          dsimp only [LinearAtVar] at ih₁_b
          have hx_not_fv_e₀ : x ∉ Term.fv e₀ := fun hin =>
            (Finset.mem_union.mp (HasType.fv_closure d₀ hin)).elim
              (fun h => hx_Δ₀ (Finmap.mem_keys.mp h))
              (fun h => h_x_not_ε (Finmap.mem_keys.mp h))
          have h_e0_const : ∀ y : (denotSpace σ s').carrier,
              denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀ = denotTerm σ e₀ := fun y =>
            denotTerm_agree e₀ (DEnv.AgreeOn.bind_left_of_not_mem hx_not_fv_e₀)
          have h_fun_eq :
              (fun y : (denotSpace σ s').carrier =>
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.smul e₀ e₁)).atSpace
                    (denotSpace σ s)) =
              (fun y => (denotTerm σ e₀).asReal •
                  (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁).atSpace
                    (denotSpace σ s)) := by
            funext y
            show ((DVal.hil ⟨(denotTerm _ e₁).asHil.fst,
                  (denotTerm _ e₀).asReal • (denotTerm _ e₁).asHil.snd⟩)).atSpace
                  (denotSpace σ s) = _
            have wf' : EnvWF (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) Δ₁ _ :=
              (wf.bind_lin ctx hx y).of_sub_Δ hsub₁
            have ih₁_a := (soundness d₁ ctx₁ wf').1
            rw [denotTy_space] at ih₁_a
            rw [h_d_eq y] at ih₁_a
            rw [h_e0_const y]
            rw [DVal.smul_hil_atSpace_eq _ ih₁_a]
          rw [h_fun_eq]
          exact IsLinearMap.const_smul ih₁_b _
  | @HasType.add _ _ e₀ e₁ s d_s d₀ d₁ =>
      refine ⟨?_, ?_⟩
      · have ih₀ := soundness d₀ ctx wf
        have ih₁ := soundness d₁ ctx wf
        obtain ⟨v₀, h_e0⟩ := DVal.matchesShape_hil_eq ih₀.1
        obtain ⟨v₁, h_e1⟩ := DVal.matchesShape_hil_eq ih₁.1
        show (denotTerm σ (.add e₀ e₁)).matchesShape (HType.hil _)
        unfold denotTerm denotTermAux
        simp only [denotTerm] at h_e0 h_e1
        rw [h_e0, h_e1]
        simp [DVal.addAt, DVal.asHil]
        exact DVal.matchesShape_hil_rfl _ _
      · intro x s' hx
        -- (b) For each y, by IH(a) at the rebound env, both subterm denotations
        -- have matchesShape (.hil (denotSpace σ s)) (via FV-irrelevance using
        -- x ∉ Space.fv s — derived from `d_s : SValid ε s` + `ctx.disjoint`).
        -- Then `addAt_atSpace_eq_add` reduces to a pointwise sum, and
        -- `IsLinearMap.add_apply` closes against IH(b) on e₀ and e₁.
        have ih₀_b := (soundness d₀ ctx wf).2 x s' hx
        have ih₁_b := (soundness d₁ ctx wf).2 x s' hx
        dsimp only [LinearAtVar] at ih₀_b ih₁_b ⊢
        have h_x_in_Δ : x ∈ (_ : LCtx) := Finmap.mem_iff.mpr ⟨s', hx⟩
        have h_x_not_ε := ctx.disjoint x h_x_in_Δ
        have h_x_not_fv : x ∉ Space.fv s := fun hin =>
          h_x_not_ε (Finmap.mem_keys.mp (SValid.fv_closure d_s hin))
        have h_eq : ∀ y : (denotSpace σ s').carrier,
            ((denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).addAt
                (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁)).atSpace
                (denotSpace σ s) =
            (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).atSpace
                (denotSpace σ s) +
            (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁).atSpace
                (denotSpace σ s) := by
          intro y
          have wf' : EnvWF (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) _ _ :=
            wf.bind_lin ctx hx y
          have ih₀_a := (soundness d₀ ctx wf').1
          have ih₁_a := (soundness d₁ ctx wf').1
          rw [denotTy_space] at ih₀_a ih₁_a
          have hagree :
              (σ.bind x (.hil ⟨denotSpace σ s', y⟩)).AgreeOn σ (Space.fv s) :=
            DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv
          have hd : denotSpace (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) s =
                    denotSpace σ s := denotSpace_agree s hagree
          rw [hd] at ih₀_a ih₁_a
          exact DVal.addAt_atSpace_eq_add ih₀_a ih₁_a
        have h_fun_eq :
            (fun y : (denotSpace σ s').carrier =>
              ((denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).addAt
                  (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁)).atSpace
                  (denotSpace σ s)) =
            (fun y : (denotSpace σ s').carrier =>
              (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).atSpace
                  (denotSpace σ s) +
              (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁).atSpace
                  (denotSpace σ s)) := funext h_eq
        show IsLinearMap ℝ _
        rw [show (fun y : (denotSpace σ s').carrier =>
              (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) (.add e₀ e₁)).atSpace
                  (denotSpace σ s)) =
            (fun y => ((denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₀).addAt
                  (denotTerm (σ.bind x (.hil ⟨denotSpace σ s', y⟩)) e₁)).atSpace
                  (denotSpace σ s)) from rfl,
            h_fun_eq]
        exact IsLinearMap.add_apply ih₀_b ih₁_b
  | @HasType.promote Δ_outer ε' e τ lin h_disjΔ h_disjε h_fresh d =>
      -- Outer: CtxWF Δ_outer (lin.toNL ∪ ε'), EnvWF σ Δ_outer (lin.toNL ∪ ε').
      -- Inner derivation: HasType (lin ∪ Δ_outer) ε' e τ.
      -- Build CtxWF and EnvWF for the inner context, then invoke soundness on d.
      have ctx_inner : CtxWF (lin ∪ Δ_outer) ε' := {
        disjoint := fun x hx_in hx_ε' => by
          rcases Finmap.mem_union.mp hx_in with hx_lin | hx_Δ
          · -- x ∈ lin → x ∈ lin.toNL → x ∉ ε' by h_disjε
            have hx_toNL : x ∈ lin.toNL := (LCtx.mem_toNL_iff lin x).mpr hx_lin
            exact @h_disjε x hx_toNL hx_ε'
          · -- x ∈ Δ_outer → x ∉ outer ε = lin.toNL ∪ ε' → x ∉ ε'
            exact ctx.disjoint x hx_Δ (Finmap.mem_union.mpr (Or.inr hx_ε'))
        lin_fv_in_ε := fun x s hx y hy => by
          -- x ∈ lin ∪ Δ_outer with binding s. y ∈ Space.fv s. Show y ∈ ε'.
          by_cases hx_lin : x ∈ lin
          · -- x ∈ lin: lin.lookup x = some s'. By toNL_lookup, lin.toNL has (x, .space s').
            have h_lin : lin.lookup x = some s := by
              rw [Finmap.lookup_union_left hx_lin] at hx; exact hx
            have h_outer_ε : (lin.toNL ∪ ε').lookup x = some (.space s) := by
              rw [Finmap.lookup_union_left ((LCtx.mem_toNL_iff lin x).mpr hx_lin)]
              exact LCtx.toNL_lookup lin x s h_lin
            -- ctx.nl_fv_in_ε x (.space s) : ∀ y ∈ Ty.fv (.space s), y ∈ lin.toNL ∪ ε'
            have h_in_outer := ctx.nl_fv_in_ε x (.space s) h_outer_ε y (by simp [Ty.fv]; exact hy)
            -- Want: y ∈ ε'. Need y ∉ lin.toNL.
            rcases Finmap.mem_union.mp h_in_outer with h_lin_y | h_ε'_y
            · -- y ∈ lin.toNL ⇒ y ∈ lin. But fresh_lin says y ∈ lin → y ∉ Space.fv s'.
              have h_y_in_lin : y ∈ lin := (LCtx.mem_toNL_iff lin y).mp h_lin_y
              exact absurd hy (h_fresh.fresh_lin y h_y_in_lin x s h_lin)
            · exact h_ε'_y
          · -- x ∈ Δ_outer: Δ_outer.lookup x = some s.
            have h_Δ : Δ_outer.lookup x = some s := by
              rw [Finmap.lookup_union_right hx_lin] at hx; exact hx
            have h_in_outer := ctx.lin_fv_in_ε x s h_Δ y hy
            rcases Finmap.mem_union.mp h_in_outer with h_lin_y | h_ε'_y
            · have h_y_in_lin : y ∈ lin := (LCtx.mem_toNL_iff lin y).mp h_lin_y
              exact absurd hy (h_fresh.fresh_Δ y h_y_in_lin x s h_Δ)
            · exact h_ε'_y
        nl_fv_in_ε := fun x τ' hx y hy => by
          -- x ∈ ε' with binding τ'. y ∈ Ty.fv τ'. Show y ∈ ε'.
          have hx_not_lin : x ∉ lin.toNL := fun h => @h_disjε x h (Finmap.mem_of_lookup_eq_some hx)
          have h_outer : (lin.toNL ∪ ε').lookup x = some τ' := by
            rw [Finmap.lookup_union_right hx_not_lin]; exact hx
          have h_in_outer := ctx.nl_fv_in_ε x τ' h_outer y hy
          rcases Finmap.mem_union.mp h_in_outer with h_lin_y | h_ε'_y
          · have h_y_in_lin : y ∈ lin := (LCtx.mem_toNL_iff lin y).mp h_lin_y
            exact absurd hy (h_fresh.fresh_ε y h_y_in_lin x τ' hx)
          · exact h_ε'_y
      }
      have wf_inner : EnvWF σ (lin ∪ Δ_outer) ε' := {
        lin_match := fun x s hx => by
          by_cases hx_lin : x ∈ lin
          · have h_lin : lin.lookup x = some s := by
              rw [Finmap.lookup_union_left hx_lin] at hx; exact hx
            have h_outer_ε : (lin.toNL ∪ ε').lookup x = some (.space s) := by
              rw [Finmap.lookup_union_left ((LCtx.mem_toNL_iff lin x).mpr hx_lin)]
              exact LCtx.toNL_lookup lin x s h_lin
            -- wf.nl_match at (x, .space s): matchesShape (denotTy σ (.space s)) = HType.hil (denotSpace σ s).
            obtain ⟨v, h_lookup, h_match⟩ := wf.nl_match x (.space s) h_outer_ε
            exact ⟨v, h_lookup, h_match⟩
          · have h_Δ : Δ_outer.lookup x = some s := by
              rw [Finmap.lookup_union_right hx_lin] at hx; exact hx
            exact wf.lin_match x s h_Δ
        nl_match := fun x τ' hx => by
          have hx_not_lin : x ∉ lin.toNL := fun h => @h_disjε x h (Finmap.mem_of_lookup_eq_some hx)
          have h_outer : (lin.toNL ∪ ε').lookup x = some τ' := by
            rw [Finmap.lookup_union_right hx_not_lin]; exact hx
          exact wf.nl_match x τ' h_outer
      }
      have ih := soundness d ctx_inner wf_inner
      refine ⟨ih.1, ?_⟩
      · -- (b) Restrict linearity claim from (lin ∪ Δ_outer) to Δ_outer.
        intro x s' hx
        have hx_not_lin : x ∉ lin :=
          fun h => @h_disjΔ x h (Finmap.mem_of_lookup_eq_some hx)
        have hx_in_inner : (lin ∪ Δ_outer).lookup x = some s' := by
          rw [Finmap.lookup_union_right hx_not_lin]; exact hx
        exact ih.2 x s' hx_in_inner

end

/-! ## Context-extension helpers (FV-transport boilerplate consolidation).

These two theorems eliminate ~50-100 LOC of repeated context-building
boilerplate in the curry/F evaluation chain. Pattern: given a layer's
linearity helper that needs `CtxWF (Finmap.insert x s Δ) ε` and
`EnvWF (σ.bind x v) (Finmap.insert x s Δ) ε`, build both via these
helpers from the smaller `CtxWF Δ ε` + `EnvWF σ Δ ε` plus freshness/SValid.
-/

namespace CtxWF

/-- Extend `CtxWF Δ ε` with a new linear binder `x : s`. -/
theorem extend_lin {Δ : LCtx} {ε : NLCtx} (ctx : CtxWF Δ ε)
    {x : Name} (h_x_ε : x ∉ ε)
    {s : Space} (sv : SValid ε s) :
    CtxWF (Finmap.insert x s Δ) ε where
  disjoint := fun x'' hx'' hx''_ε => by
    rcases Finmap.mem_insert.mp hx'' with rfl | h
    · exact h_x_ε hx''_ε
    · exact ctx.disjoint x'' h hx''_ε
  lin_fv_in_ε := fun x'' s'' hx'' z hz => by
    by_cases h_eq : x'' = x
    · subst x''
      rw [Finmap.lookup_insert] at hx''
      have h_eq_s : s'' = s := (Option.some.inj hx'').symm
      rw [h_eq_s] at hz
      exact Finmap.mem_keys.mp (SValid.fv_closure sv hz)
    · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
      exact ctx.lin_fv_in_ε x'' s'' hx'' z hz
  nl_fv_in_ε := ctx.nl_fv_in_ε

end CtxWF

namespace EnvWF

/-- Extend `EnvWF σ Δ ε` with a new linear binder `x : s` bound to a
    value `y : (denotSpace σ s).carrier`. The new env is well-formed
    against the extended context. All FV transports handled internally. -/
theorem extend_lin {σ : DEnv} {Δ : LCtx} {ε : NLCtx}
    (wf : EnvWF σ Δ ε) (ctx : CtxWF Δ ε)
    {x : Name} (h_x_ε : x ∉ ε)
    {s : Space} (sv : SValid ε s)
    (y : (denotSpace σ s).carrier) :
    EnvWF (σ.bind x (.hil ⟨denotSpace σ s, y⟩))
      (Finmap.insert x s Δ) ε := by
  have h_x_not_fv_s : x ∉ Space.fv s :=
    fun hin => h_x_ε (Finmap.mem_keys.mp (SValid.fv_closure sv hin))
  set σ' : DEnv := σ.bind x (.hil ⟨denotSpace σ s, y⟩) with hσ'
  have h_denot_s : denotSpace σ' s = denotSpace σ s :=
    denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s)
  have h_v_match : DVal.matchesShape
                    (DVal.hil ⟨denotSpace σ s, y⟩)
                    (HType.hil (denotSpace σ s)) :=
    DVal.matchesShape_hil_rfl _ _
  exact {
    lin_match := fun x'' s'' hx'' => by
      by_cases h_eq : x'' = x
      · subst x''
        rw [Finmap.lookup_insert] at hx''
        have h_eq_s : s'' = s := (Option.some.inj hx'').symm
        rw [h_eq_s]
        refine ⟨.hil ⟨denotSpace σ s, y⟩, ?_, ?_⟩
        · show σ'.vars.lookup x = some _
          simp [σ', DEnv.bind, Finmap.lookup_insert]
        · rw [h_denot_s]; exact h_v_match
      · rw [Finmap.lookup_insert_of_ne _ h_eq] at hx''
        obtain ⟨w, h_lookup, h_match⟩ := wf.lin_match x'' s'' hx''
        have h_x_not_fv_s'' : x ∉ Space.fv s'' := fun hin =>
          h_x_ε (ctx.lin_fv_in_ε x'' s'' hx'' x hin)
        have hd : denotSpace σ' s'' = denotSpace σ s'' :=
          denotSpace_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv_s'')
        refine ⟨w, ?_, ?_⟩
        · show σ'.vars.lookup x'' = some w
          simp [σ', DEnv.bind, Finmap.lookup_insert_of_ne _ h_eq, h_lookup]
        · rw [hd]; exact h_match
    nl_match := fun x'' τ'' hx'' => by
      have h_x_in_ε : x'' ∈ ε := Finmap.mem_iff.mpr ⟨_, hx''⟩
      have h_xne : x ≠ x'' := fun heq => by subst heq; exact h_x_ε h_x_in_ε
      obtain ⟨w, h_lookup, h_match⟩ := wf.nl_match x'' τ'' hx''
      have h_x_not_fv : x ∉ Ty.fv τ'' := fun hin =>
        h_x_ε (ctx.nl_fv_in_ε x'' τ'' hx'' x hin)
      have hd : denotTy σ' τ'' = denotTy σ τ'' :=
        denotTy_agree _ (DEnv.AgreeOn.bind_left_of_not_mem h_x_not_fv)
      refine ⟨w, ?_, ?_⟩
      · show σ'.vars.lookup x'' = some w
        simp [σ', DEnv.bind, Finmap.lookup_insert_of_ne _ h_xne.symm, h_lookup]
      · rw [hd]; exact h_match
  }

/-- Variant of `extend_lin` that takes the binding's HSpace explicitly
    via a propositional equality `h_V : V = denotSpace σ s`. Useful for
    chained extensions where the natural type of `y` is in an earlier
    σ-frame's denotSpace (propositionally — but not always definitionally
    — equal to the current σ's denotSpace via FV-irrelevance). -/
theorem extend_lin_at {σ : DEnv} {Δ : LCtx} {ε : NLCtx}
    (wf : EnvWF σ Δ ε) (ctx : CtxWF Δ ε)
    {x : Name} (h_x_ε : x ∉ ε)
    {s : Space} (sv : SValid ε s)
    {V : HSpace} (h_V : V = denotSpace σ s)
    (y : V.carrier) :
    EnvWF (σ.bind x (.hil ⟨V, y⟩))
      (Finmap.insert x s Δ) ε := by
  subst h_V
  exact wf.extend_lin ctx h_x_ε sv y

end EnvWF

end GLang
