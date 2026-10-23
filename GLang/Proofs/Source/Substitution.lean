

import GLang.Annotated.Binding
import GLang.Proofs.Source.FreeVars
import GLang.Proofs.Source.SourceLN
import GLang.Annotated.Denotation
import GLang.Proofs.Source.FVIrrelevance
import Mathlib.Data.Finmap
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD

namespace GLang

/-! ## DEnv-rebinding helpers (kept; used by `Soundness`). -/

namespace DEnv

theorem bind_comm {σ : DEnv} {x y : Name} (v w : DVal) (h : x ≠ y) :
    (σ.bind x v).bind y w = (σ.bind y w).bind x v := by
  cases σ with
  | mk vars =>
    show DEnv.mk _ = DEnv.mk _
    congr 1
    exact Finmap.insert_insert_of_ne vars h

theorem bind_overwrite (σ : DEnv) (x : Name) (v w : DVal) :
    (σ.bind x v).bind x w = σ.bind x w := by
  cases σ with
  | mk vars =>
    show DEnv.mk _ = DEnv.mk _
    congr 1
    exact Finmap.insert_insert vars

end DEnv

/-! ## `llam`-codomain congruence helper.

The `.llam s₀ s e` denotation matches on the codomain `s` (real vs. tensor). Under
`openRec`/`subst`/env-change the codomain becomes a stuck application (e.g.
`Space.openRec k (.var x) s`), so the inner match cannot fire directly. This helper
abstracts the codomain away: the `.llam` denotation depends on `s` only through its
DENOTATION (`denotSpaceAux … s`) and its REALNESS (`Space.isReal s`), both of which
are preserved by `openRec`/`subst`. Proved once by `cases s <;> cases s'`; reused in
all three binder arms below. -/

/-- `true` iff the space is `ℝ` (the `.llam` codomain match's discriminant). -/
def Space.isReal : Space → Bool
  | .real => true
  | _     => false

theorem Space.isReal_openRec (k : Nat) (u : Term) (s : Space) :
    (Space.openRec k u s).isReal = s.isReal := by
  cases s <;> rfl

theorem Space.isReal_subst (x : Name) (u : Term) (s : Space) :
    (Space.subst x u s).isReal = s.isReal := by
  cases s <;> rfl

/-- Congruence for the `.llam` denotation through its codomain. -/
theorem denotTermAux_llam_congr
    {σ σ' : DEnv} {Δ Δ' : List DVal} {s₀ s s₀' s' : Space} {e e' : Term}
    (h₀ : denotSpaceAux σ Δ s₀ = denotSpaceAux σ' Δ' s₀')
    (hs : denotSpaceAux σ Δ s = denotSpaceAux σ' Δ' s')
    (hreal : s.isReal = s'.isReal)
    (hbody : ∀ v : DVal, denotTermAux σ (v :: Δ) e = denotTermAux σ' (v :: Δ') e') :
    denotTermAux σ Δ (.llam s₀ s e) = denotTermAux σ' Δ' (.llam s₀' s' e') := by
  cases s <;> cases s' <;> simp only [Space.isReal] at hreal <;>
    first
    | exact absurd hreal (by decide)
    | (simp only [denotTermAux]
       rw [h₀]
       exact congrArg (llamRealDVal _) (funext fun v => congrArg (·.atSpace HSpace.real) (hbody v)))
    | (simp only [denotTermAux]
       rw [h₀, hs]
       exact congrArg (llamTensorDVal _ _) (funext hbody))

/-! ## BRIDGE: open-at-fresh-name vs. bound-index, with `Δ` fixed.

`denot*Aux (σ.bind x (Δ.getD k default)) Δ (openRec k (.var x) ·) = denot*Aux σ Δ ·`
when `x ∉ fv`. The bound de Bruijn slot `k` is read off `Δ` and re-presented as a
free `x`-binding in `σ`; `Δ` itself is identical on both sides. The binder arms
push the same fiber value onto `Δ` and recurse at index `k+1`, where
`List.getD_cons_succ` realigns `(v :: Δ).getD (k+1) = Δ.getD k`. -/

mutual

theorem denotSpaceAux_openRec_bind {x : Name} (σ : DEnv) :
    ∀ (Δ : List DVal) (k : Nat) (s : Space), x ∉ Space.fv s →
      denotSpaceAux (σ.bind x (Δ.getD k DVal.default)) Δ (Space.openRec k (.var x) s)
        = denotSpaceAux σ Δ s
  | _, _, .empty, _ => rfl
  | _, _, .real,  _ => rfl
  | Δ, k, .dual s, h => by
      simp only [Space.fv] at h
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s h]
  | Δ, k, .dsum s₀ s₁, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.2]
  | Δ, k, .tprod s₀ s₁, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.2]
  | Δ, k, .ker s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.2,
          denotTermAux_openRec_bind σ Δ k e h.2]
  | Δ, k, .coker s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.2,
          denotTermAux_openRec_bind σ Δ k e h.2]
  | Δ, k, .img s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.2,
          denotTermAux_openRec_bind σ Δ k e h.2]
  | Δ, k, .coimg s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.2,
          denotTermAux_openRec_bind σ Δ k e h.2]

theorem denotTyAux_openRec_bind {x : Name} (σ : DEnv) :
    ∀ (Δ : List DVal) (k : Nat) (τ : Ty), x ∉ Ty.fv τ →
      denotTyAux (σ.bind x (Δ.getD k DVal.default)) Δ (Ty.openRec k (.var x) τ)
        = denotTyAux σ Δ τ
  | Δ, k, .space s, h => by
      simp only [Ty.fv] at h
      simp only [Ty.openRec, denotTyAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s h]
  | Δ, k, .piTy τ₀ τ₁, h => by
      simp only [Ty.fv, Finset.mem_union, not_or] at h
      simp only [Ty.openRec, denotTyAux]
      rw [denotTyAux_openRec_bind σ Δ k τ₀ h.1]
      refine congrArg (HType.sec _) ?_
      funext z
      have hb := denotTyAux_openRec_bind σ ((denotTyAux σ Δ τ₀).embed z :: Δ) (k+1) τ₁ h.2
      simp only [List.getD_cons_succ] at hb
      exact hb

theorem denotTermAux_openRec_bind {x : Name} (σ : DEnv) :
    ∀ (Δ : List DVal) (k : Nat) (e : Term), x ∉ Term.fv e →
      denotTermAux (σ.bind x (Δ.getD k DVal.default)) Δ (Term.openRec k (.var x) e)
        = denotTermAux σ Δ e
  | Δ, k, .bvar n, _ => by
      by_cases hnk : n = k
      · simp only [Term.openRec, hnk, ↓reduceIte, denotTermAux, DEnv.bind,
          Finmap.lookup_insert, Option.getD_some]
      · simp only [Term.openRec, if_neg hnk, denotTermAux]
  | _, _, .real _, _ => rfl
  | Δ, k, .var w, h => by
      simp only [Term.fv, Finset.mem_singleton] at h
      simp only [Term.openRec, denotTermAux, DEnv.bind,
        Finmap.lookup_insert_of_ne _ (Ne.symm h)]
  | Δ, k, .zero s, h => by
      simp only [Term.fv] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s h]
  | Δ, k, .inner s, h => by
      simp only [Term.fv] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s h]
  | Δ, k, .smul e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_openRec_bind σ Δ k e₀ h.1, denotTermAux_openRec_bind σ Δ k e₁ h.2]
  | Δ, k, .add e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_openRec_bind σ Δ k e₀ h.1, denotTermAux_openRec_bind σ Δ k e₁ h.2]
  | Δ, k, .dsumE e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_openRec_bind σ Δ k e₀ h.1, denotTermAux_openRec_bind σ Δ k e₁ h.2]
  | Δ, k, .tprodE e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_openRec_bind σ Δ k e₀ h.1, denotTermAux_openRec_bind σ Δ k e₁ h.2]
  | Δ, k, .appN e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_openRec_bind σ Δ k e₀ h.1, denotTermAux_openRec_bind σ Δ k e₁ h.2]
  | Δ, k, .appL s₀ s₁ e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.1.2,
          denotTermAux_openRec_bind σ Δ k e₀ h.1.2, denotTermAux_openRec_bind σ Δ k e₁ h.2]
  | Δ, k, .appI s e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s h.1.1, denotTermAux_openRec_bind σ Δ k e₀ h.1.2,
          denotTermAux_openRec_bind σ Δ k e₁ h.2]
  | Δ, k, .pinvT s₀ s₁ e, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.2,
          denotTermAux_openRec_bind σ Δ k e h.2]
  | Δ, k, .pinvD s e, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_openRec_bind σ Δ k s h.1, denotTermAux_openRec_bind σ Δ k e h.2]
  | Δ, k, .llam s₀ s e, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec]
      refine denotTermAux_llam_congr
        (denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1)
        (denotSpaceAux_openRec_bind σ Δ k s h.1.2)
        (Space.isReal_openRec k (.var x) s) ?_
      intro v
      have hb := denotTermAux_openRec_bind σ (v :: Δ) (k+1) e h.2
      simp only [List.getD_cons_succ] at hb
      exact hb
  | Δ, k, .nllam τ₀ e, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, denotTermAux]
      rw [denotTyAux_openRec_bind σ Δ k τ₀ h.1]
      refine congrArg (DVal.pi _) ?_
      funext z
      have hb := denotTermAux_openRec_bind σ ((denotTyAux σ Δ τ₀).embed z :: Δ) (k+1) e h.2
      simp only [List.getD_cons_succ] at hb
      exact hb
  | Δ, k, .embed s, h => by
      simp only [Term.fv] at h
      cases s with
      | empty => rfl
      | real => rfl
      | dual _ => rfl
      | dsum _ _ => rfl
      | tprod _ _ => rfl
      | ker s₀ s₁ e =>
          simp only [Space.fv, Finset.mem_union, not_or] at h
          simp only [Term.openRec, Space.openRec, denotTermAux]
          rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.2,
              denotTermAux_openRec_bind σ Δ k e h.2]
      | coker s₀ s₁ e =>
          simp only [Space.fv, Finset.mem_union, not_or] at h
          simp only [Term.openRec, Space.openRec, denotTermAux]
          rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.2,
              denotTermAux_openRec_bind σ Δ k e h.2]
      | img s₀ s₁ e =>
          simp only [Space.fv, Finset.mem_union, not_or] at h
          simp only [Term.openRec, Space.openRec, denotTermAux]
          rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.2,
              denotTermAux_openRec_bind σ Δ k e h.2]
      | coimg s₀ s₁ e =>
          simp only [Space.fv, Finset.mem_union, not_or] at h
          simp only [Term.openRec, Space.openRec, denotTermAux]
          rw [denotSpaceAux_openRec_bind σ Δ k s₀ h.1.1, denotSpaceAux_openRec_bind σ Δ k s₁ h.1.2,
              denotTermAux_openRec_bind σ Δ k e h.2]

end

/-! ## IRREL: a locally-closed term's denotation ignores the local env `Δ`.

`lc e → denotTermAux σ Δ₁ e = denotTermAux σ Δ₂ e`. Induction on the `lc`
derivation. The cofinite binder arms pick a fresh `y` (∉ `L ∪ fv`) and convert
both `Δᵢ`-pushed sides into the SAME opened body `openVar y ·` via BRIDGE, then
apply the IH on the smaller `lc (openVar y ·)` derivation. `σ` is quantified so
the IH can be taken at the BRIDGE-extended env `σ.bind y w`. -/

mutual

theorem denotSpaceAux_lc_irrel :
    ∀ {s : Space}, Space.lc s → ∀ (σ : DEnv) (Δ₁ Δ₂ : List DVal),
      denotSpaceAux σ Δ₁ s = denotSpaceAux σ Δ₂ s
  | _, .empty => fun _ _ _ => rfl
  | _, .real  => fun _ _ _ => rfl
  | _, .dual hs => fun σ Δ₁ Δ₂ => by
      simp only [denotSpaceAux]; rw [denotSpaceAux_lc_irrel hs σ Δ₁ Δ₂]
  | _, .dsum h₀ h₁ => fun σ Δ₁ Δ₂ => by
      simp only [denotSpaceAux]
      rw [denotSpaceAux_lc_irrel h₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel h₁ σ Δ₁ Δ₂]
  | _, .tprod h₀ h₁ => fun σ Δ₁ Δ₂ => by
      simp only [denotSpaceAux]
      rw [denotSpaceAux_lc_irrel h₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel h₁ σ Δ₁ Δ₂]
  | _, .ker hs₀ hs₁ he => fun σ Δ₁ Δ₂ => by
      simp only [denotSpaceAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel he σ Δ₁ Δ₂]
  | _, .coker hs₀ hs₁ he => fun σ Δ₁ Δ₂ => by
      simp only [denotSpaceAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel he σ Δ₁ Δ₂]
  | _, .img hs₀ hs₁ he => fun σ Δ₁ Δ₂ => by
      simp only [denotSpaceAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel he σ Δ₁ Δ₂]
  | _, .coimg hs₀ hs₁ he => fun σ Δ₁ Δ₂ => by
      simp only [denotSpaceAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel he σ Δ₁ Δ₂]

theorem denotTyAux_lc_irrel :
    ∀ {τ : Ty}, Ty.lc τ → ∀ (σ : DEnv) (Δ₁ Δ₂ : List DVal),
      denotTyAux σ Δ₁ τ = denotTyAux σ Δ₂ τ
  | _, .space hs => fun σ Δ₁ Δ₂ => by
      simp only [denotTyAux]; rw [denotSpaceAux_lc_irrel hs σ Δ₁ Δ₂]
  | .piTy τ₀ τ₁, .piTy L hτ₀ hbody => fun σ Δ₁ Δ₂ => by
      simp only [denotTyAux]
      rw [denotTyAux_lc_irrel hτ₀ σ Δ₁ Δ₂]
      refine congrArg (HType.sec _) ?_
      funext z
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv τ₁)
      simp only [Finset.mem_union, not_or] at hy
      set w := (denotTyAux σ Δ₂ τ₀).embed z
      have B1 := denotTyAux_openRec_bind (x := y) σ (w :: Δ₁) 0 τ₁ hy.2
      have B2 := denotTyAux_openRec_bind (x := y) σ (w :: Δ₂) 0 τ₁ hy.2
      simp only [List.getD_cons_zero] at B1 B2
      rw [← B1, ← B2]
      exact denotTyAux_lc_irrel (hbody y hy.1) (σ.bind y w) (w :: Δ₁) (w :: Δ₂)

theorem denotTermAux_lc_irrel :
    ∀ {e : Term}, Term.lc e → ∀ (σ : DEnv) (Δ₁ Δ₂ : List DVal),
      denotTermAux σ Δ₁ e = denotTermAux σ Δ₂ e
  | _, .var  => fun _ _ _ => rfl
  | _, .real => fun _ _ _ => rfl
  | _, .zero hs => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]; rw [denotSpaceAux_lc_irrel hs σ Δ₁ Δ₂]
  | _, .inner hs => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]; rw [denotSpaceAux_lc_irrel hs σ Δ₁ Δ₂]
  | _, .smul h₀ h₁ => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotTermAux_lc_irrel h₀ σ Δ₁ Δ₂, denotTermAux_lc_irrel h₁ σ Δ₁ Δ₂]
  | _, .add h₀ h₁ => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotTermAux_lc_irrel h₀ σ Δ₁ Δ₂, denotTermAux_lc_irrel h₁ σ Δ₁ Δ₂]
  | _, .dsumE h₀ h₁ => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotTermAux_lc_irrel h₀ σ Δ₁ Δ₂, denotTermAux_lc_irrel h₁ σ Δ₁ Δ₂]
  | _, .tprodE h₀ h₁ => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotTermAux_lc_irrel h₀ σ Δ₁ Δ₂, denotTermAux_lc_irrel h₁ σ Δ₁ Δ₂]
  | _, .appN h₀ h₁ => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotTermAux_lc_irrel h₀ σ Δ₁ Δ₂, denotTermAux_lc_irrel h₁ σ Δ₁ Δ₂]
  | _, .appL hs₀ hs₁ h₀ h₁ => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel h₀ σ Δ₁ Δ₂, denotTermAux_lc_irrel h₁ σ Δ₁ Δ₂]
  | _, .appI hs h₀ h₁ => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotSpaceAux_lc_irrel hs σ Δ₁ Δ₂, denotTermAux_lc_irrel h₀ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel h₁ σ Δ₁ Δ₂]
  | _, .pinvT hs₀ hs₁ he => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel he σ Δ₁ Δ₂]
  | _, .pinvD hs he => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotSpaceAux_lc_irrel hs σ Δ₁ Δ₂, denotTermAux_lc_irrel he σ Δ₁ Δ₂]
  | _, .embed .empty => fun _ _ _ => rfl
  | _, .embed .real => fun _ _ _ => rfl
  | _, .embed (.dual _) => fun _ _ _ => rfl
  | _, .embed (.dsum _ _) => fun _ _ _ => rfl
  | _, .embed (.tprod _ _) => fun _ _ _ => rfl
  | _, .embed (.ker hs₀ hs₁ he) => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel he σ Δ₁ Δ₂]
  | _, .embed (.coker hs₀ hs₁ he) => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel he σ Δ₁ Δ₂]
  | _, .embed (.img hs₀ hs₁ he) => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel he σ Δ₁ Δ₂]
  | _, .embed (.coimg hs₀ hs₁ he) => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂, denotSpaceAux_lc_irrel hs₁ σ Δ₁ Δ₂,
          denotTermAux_lc_irrel he σ Δ₁ Δ₂]
  | .llam s₀ s e, .llam L hs₀ hs hbody => fun σ Δ₁ Δ₂ => by
      refine denotTermAux_llam_congr
        (denotSpaceAux_lc_irrel hs₀ σ Δ₁ Δ₂)
        (denotSpaceAux_lc_irrel hs σ Δ₁ Δ₂)
        rfl ?_
      intro v
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Term.fv e)
      simp only [Finset.mem_union, not_or] at hy
      have B1 := denotTermAux_openRec_bind (x := y) σ (v :: Δ₁) 0 e hy.2
      have B2 := denotTermAux_openRec_bind (x := y) σ (v :: Δ₂) 0 e hy.2
      simp only [List.getD_cons_zero] at B1 B2
      rw [← B1, ← B2]
      exact denotTermAux_lc_irrel (hbody y hy.1) (σ.bind y v) (v :: Δ₁) (v :: Δ₂)
  | .nllam τ e, .nllam L hτ hbody => fun σ Δ₁ Δ₂ => by
      simp only [denotTermAux]
      rw [denotTyAux_lc_irrel hτ σ Δ₁ Δ₂]
      refine congrArg (DVal.pi _) ?_
      funext z
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Term.fv e)
      simp only [Finset.mem_union, not_or] at hy
      set w := (denotTyAux σ Δ₂ τ).embed z
      have B1 := denotTermAux_openRec_bind (x := y) σ (w :: Δ₁) 0 e hy.2
      have B2 := denotTermAux_openRec_bind (x := y) σ (w :: Δ₂) 0 e hy.2
      simp only [List.getD_cons_zero] at B1 B2
      rw [← B1, ← B2]
      exact denotTermAux_lc_irrel (hbody y hy.1) (σ.bind y w) (w :: Δ₁) (w :: Δ₂)

end

/-! ## SUBST: the clean unconditional substitution lemma.

`denotTermAux σ Δ (subst x u e) = denotTermAux (σ.bind x ⟦u⟧σΔ) Δ e` for `lc u`.
Structural induction on the syntax (mirrors BRIDGE). The binder arms recurse at
the pushed env `w :: Δ`, where the IH yields the bound value `⟦u⟧σ(w::Δ)`; IRREL
(`lc u`) collapses it back to `⟦u⟧σΔ`. No fresh names, no `NoCapture`. -/

mutual

theorem denotSpaceAux_subst {x : Name} {u : Term} (hu : Term.lc u) (σ : DEnv) :
    ∀ (Δ : List DVal) (s : Space),
      denotSpaceAux σ Δ (Space.subst x u s)
        = denotSpaceAux (σ.bind x (denotTermAux σ Δ u)) Δ s
  | _, .empty => rfl
  | _, .real  => rfl
  | Δ, .dual s => by
      simp only [Space.subst, denotSpaceAux]
      rw [denotSpaceAux_subst hu σ Δ s]
  | Δ, .dsum s₀ s₁ => by
      simp only [Space.subst, denotSpaceAux]
      rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁]
  | Δ, .tprod s₀ s₁ => by
      simp only [Space.subst, denotSpaceAux]
      rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁]
  | Δ, .ker s₀ s₁ e => by
      simp only [Space.subst, denotSpaceAux]
      rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
          denotTermAux_subst hu σ Δ e]
  | Δ, .coker s₀ s₁ e => by
      simp only [Space.subst, denotSpaceAux]
      rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
          denotTermAux_subst hu σ Δ e]
  | Δ, .img s₀ s₁ e => by
      simp only [Space.subst, denotSpaceAux]
      rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
          denotTermAux_subst hu σ Δ e]
  | Δ, .coimg s₀ s₁ e => by
      simp only [Space.subst, denotSpaceAux]
      rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
          denotTermAux_subst hu σ Δ e]

theorem denotTyAux_subst {x : Name} {u : Term} (hu : Term.lc u) (σ : DEnv) :
    ∀ (Δ : List DVal) (τ : Ty),
      denotTyAux σ Δ (Ty.subst x u τ)
        = denotTyAux (σ.bind x (denotTermAux σ Δ u)) Δ τ
  | Δ, .space s => by
      simp only [Ty.subst, denotTyAux]
      rw [denotSpaceAux_subst hu σ Δ s]
  | Δ, .piTy τ₀ τ₁ => by
      simp only [Ty.subst, denotTyAux]
      rw [denotTyAux_subst hu σ Δ τ₀]
      refine congrArg (HType.sec _) ?_
      funext z
      rw [denotTyAux_subst hu σ _ τ₁, denotTermAux_lc_irrel hu σ _ Δ]

theorem denotTermAux_subst {x : Name} {u : Term} (hu : Term.lc u) (σ : DEnv) :
    ∀ (Δ : List DVal) (e : Term),
      denotTermAux σ Δ (Term.subst x u e)
        = denotTermAux (σ.bind x (denotTermAux σ Δ u)) Δ e
  | _, .bvar _ => rfl
  | _, .real _ => rfl
  | Δ, .var y => by
      by_cases hxy : x = y
      · subst hxy
        simp [Term.subst, denotTermAux, DEnv.bind, Finmap.lookup_insert]
      · simp [Term.subst, denotTermAux, DEnv.bind,
              Finmap.lookup_insert_of_ne _ (Ne.symm hxy), hxy]
  | Δ, .zero s => by
      simp only [Term.subst, denotTermAux]
      rw [denotSpaceAux_subst hu σ Δ s]
  | Δ, .inner s => by
      simp only [Term.subst, denotTermAux]
      rw [denotSpaceAux_subst hu σ Δ s]
  | Δ, .smul e₀ e₁ => by
      simp only [Term.subst, denotTermAux]
      rw [denotTermAux_subst hu σ Δ e₀, denotTermAux_subst hu σ Δ e₁]
  | Δ, .add e₀ e₁ => by
      simp only [Term.subst, denotTermAux]
      rw [denotTermAux_subst hu σ Δ e₀, denotTermAux_subst hu σ Δ e₁]
  | Δ, .dsumE e₀ e₁ => by
      simp only [Term.subst, denotTermAux]
      rw [denotTermAux_subst hu σ Δ e₀, denotTermAux_subst hu σ Δ e₁]
  | Δ, .tprodE e₀ e₁ => by
      simp only [Term.subst, denotTermAux]
      rw [denotTermAux_subst hu σ Δ e₀, denotTermAux_subst hu σ Δ e₁]
  | Δ, .appN e₀ e₁ => by
      simp only [Term.subst, denotTermAux]
      rw [denotTermAux_subst hu σ Δ e₀, denotTermAux_subst hu σ Δ e₁]
  | Δ, .appL s₀ s₁ e₀ e₁ => by
      simp only [Term.subst, denotTermAux]
      rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
          denotTermAux_subst hu σ Δ e₀, denotTermAux_subst hu σ Δ e₁]
  | Δ, .appI s e₀ e₁ => by
      simp only [Term.subst, denotTermAux]
      rw [denotSpaceAux_subst hu σ Δ s, denotTermAux_subst hu σ Δ e₀,
          denotTermAux_subst hu σ Δ e₁]
  | Δ, .pinvT s₀ s₁ e => by
      simp only [Term.subst, denotTermAux]
      rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
          denotTermAux_subst hu σ Δ e]
  | Δ, .pinvD s e => by
      simp only [Term.subst, denotTermAux]
      rw [denotSpaceAux_subst hu σ Δ s, denotTermAux_subst hu σ Δ e]
  | Δ, .llam s₀ s e => by
      simp only [Term.subst]
      refine denotTermAux_llam_congr
        (denotSpaceAux_subst hu σ Δ s₀)
        (denotSpaceAux_subst hu σ Δ s)
        (Space.isReal_subst x u s) ?_
      intro v
      rw [denotTermAux_subst hu σ (v :: Δ) e, denotTermAux_lc_irrel hu σ (v :: Δ) Δ]
  | Δ, .nllam τ e => by
      simp only [Term.subst, denotTermAux]
      rw [denotTyAux_subst hu σ Δ τ]
      refine congrArg (DVal.pi _) ?_
      funext z
      rw [denotTermAux_subst hu σ _ e, denotTermAux_lc_irrel hu σ _ Δ]
  | Δ, .embed s => by
      simp only [Term.subst]
      cases s with
      | empty => rfl
      | real => rfl
      | dual _ => rfl
      | dsum _ _ => rfl
      | tprod _ _ => rfl
      | ker s₀ s₁ e =>
          simp only [Space.subst, denotTermAux]
          rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
              denotTermAux_subst hu σ Δ e]
      | coker s₀ s₁ e =>
          simp only [Space.subst, denotTermAux]
          rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
              denotTermAux_subst hu σ Δ e]
      | img s₀ s₁ e =>
          simp only [Space.subst, denotTermAux]
          rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
              denotTermAux_subst hu σ Δ e]
      | coimg s₀ s₁ e =>
          simp only [Space.subst, denotTermAux]
          rw [denotSpaceAux_subst hu σ Δ s₀, denotSpaceAux_subst hu σ Δ s₁,
              denotTermAux_subst hu σ Δ e]

end

/-! ## Closed-term corollaries (`Δ = []`). -/

theorem denotSpace_subst {x : Name} {u : Term} (hu : Term.lc u) (σ : DEnv) (s : Space) :
    denotSpace σ (Space.subst x u s) = denotSpace (σ.bind x (denotTerm σ u)) s :=
  denotSpaceAux_subst hu σ [] s

theorem denotTy_subst {x : Name} {u : Term} (hu : Term.lc u) (σ : DEnv) (τ : Ty) :
    denotTy σ (Ty.subst x u τ) = denotTy (σ.bind x (denotTerm σ u)) τ :=
  denotTyAux_subst hu σ [] τ

theorem denotTerm_subst {x : Name} {u : Term} (hu : Term.lc u) (σ : DEnv) (e : Term) :
    denotTerm σ (Term.subst x u e) = denotTerm (σ.bind x (denotTerm σ u)) e :=
  denotTermAux_subst hu σ [] e

/-! ## Open-bridge corollaries (the form Soundness's binder arms consume).

`denot* (σ.bind y v) (openVar y ·) = denot*Aux σ [v] ·`, i.e. the binder body
"opened at a fresh `y` with `y ↦ v` in `σ`" equals the body denoted under the
single-entry local env `[v]` — which is exactly the fiber produced by the `.pi` /
`.sec` / `llam*DVal` unfolding of the binder's denotation. Combines IRREL (drop
the env from `[]` to `[v]` on the lc-opened body) with BRIDGE (open at index 0).
The `lc (openVar y ·)` hypothesis comes from `Regularity` on the body's typing. -/

theorem denotTy_openVar_bind {σ : DEnv} {y : Name} {v : DVal} {τ : Ty}
    (hlc : Ty.lc (Ty.openVar y τ)) (hy : y ∉ Ty.fv τ) :
    denotTy (σ.bind y v) (Ty.openVar y τ) = denotTyAux σ [v] τ := by
  show denotTyAux (σ.bind y v) [] (Ty.openVar y τ) = denotTyAux σ [v] τ
  rw [denotTyAux_lc_irrel hlc (σ.bind y v) [] [v]]
  have hb := denotTyAux_openRec_bind (x := y) σ [v] 0 τ hy
  simp only [List.getD_cons_zero] at hb
  exact hb

theorem denotTerm_openVar_bind {σ : DEnv} {y : Name} {v : DVal} {e : Term}
    (hlc : Term.lc (Term.openVar y e)) (hy : y ∉ Term.fv e) :
    denotTerm (σ.bind y v) (Term.openVar y e) = denotTermAux σ [v] e := by
  show denotTermAux (σ.bind y v) [] (Term.openVar y e) = denotTermAux σ [v] e
  rw [denotTermAux_lc_irrel hlc (σ.bind y v) [] [v]]
  have hb := denotTermAux_openRec_bind (x := y) σ [v] 0 e hy
  simp only [List.getD_cons_zero] at hb
  exact hb

/-! ## INSTANTIATE bridge: denotation of `openRec`-by-a-general-term.

`denot*Aux σ Δ (openRec Δ.length u ·) = denot*Aux σ (Δ ++ [⟦u⟧σΔ]) ·` for `lc u`:
substituting a (locally-closed) term `u` for the de Bruijn slot at depth `Δ.length`
denotes the same as appending `u`'s value to the local env. This is the
general-term analogue of BRIDGE (which is the `.var`-only case) — the bound de
Bruijn slot lands at the END of `Δ` (index `Δ.length`). At `Δ = []` it yields the
`instantiate` corollaries that `app_nonlinear`'s soundness consumes. Binder arms
use IRREL (lc `u`) to keep `⟦u⟧` fixed across the pushed env. -/

private theorem getD_append_singleton_self (Δ : List DVal) (a : DVal) :
    (Δ ++ [a]).getD Δ.length DVal.default = a := by
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]; rfl

private theorem getD_append_singleton_ne (Δ : List DVal) (a : DVal) {n : Nat}
    (h : n ≠ Δ.length) :
    (Δ ++ [a]).getD n DVal.default = Δ.getD n DVal.default := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_append_right _ _ _ _ (le_of_lt hgt),
        List.getD_eq_default _ _ (le_of_lt hgt)]
    exact List.getD_eq_default _ _ (by simp only [List.length_cons, List.length_nil]; omega)

mutual

theorem denotSpaceAux_inst {u : Term} (hu : Term.lc u) (σ : DEnv) :
    ∀ (Δ : List DVal) (s : Space),
      denotSpaceAux σ Δ (Space.openRec Δ.length u s)
        = denotSpaceAux σ (Δ ++ [denotTermAux σ Δ u]) s
  | _, .empty => rfl
  | _, .real  => rfl
  | Δ, .dual s => by
      simp only [Space.openRec, denotSpaceAux]; rw [denotSpaceAux_inst hu σ Δ s]
  | Δ, .dsum s₀ s₁ => by
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁]
  | Δ, .tprod s₀ s₁ => by
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁]
  | Δ, .ker s₀ s₁ e => by
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
          denotTermAux_inst hu σ Δ e]
  | Δ, .coker s₀ s₁ e => by
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
          denotTermAux_inst hu σ Δ e]
  | Δ, .img s₀ s₁ e => by
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
          denotTermAux_inst hu σ Δ e]
  | Δ, .coimg s₀ s₁ e => by
      simp only [Space.openRec, denotSpaceAux]
      rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
          denotTermAux_inst hu σ Δ e]

theorem denotTyAux_inst {u : Term} (hu : Term.lc u) (σ : DEnv) :
    ∀ (Δ : List DVal) (τ : Ty),
      denotTyAux σ Δ (Ty.openRec Δ.length u τ)
        = denotTyAux σ (Δ ++ [denotTermAux σ Δ u]) τ
  | Δ, .space s => by
      simp only [Ty.openRec, denotTyAux]; rw [denotSpaceAux_inst hu σ Δ s]
  | Δ, .piTy τ₀ τ₁ => by
      simp only [Ty.openRec, denotTyAux]
      rw [denotTyAux_inst hu σ Δ τ₀]
      refine congrArg (HType.sec _) ?_
      funext z
      have hirr : denotTermAux σ ((denotTyAux σ (Δ ++ [denotTermAux σ Δ u]) τ₀).embed z :: Δ) u
                = denotTermAux σ Δ u := denotTermAux_lc_irrel hu σ _ Δ
      have ih := denotTyAux_inst hu σ ((denotTyAux σ (Δ ++ [denotTermAux σ Δ u]) τ₀).embed z :: Δ) τ₁
      rw [hirr] at ih
      exact ih

theorem denotTermAux_inst {u : Term} (hu : Term.lc u) (σ : DEnv) :
    ∀ (Δ : List DVal) (e : Term),
      denotTermAux σ Δ (Term.openRec Δ.length u e)
        = denotTermAux σ (Δ ++ [denotTermAux σ Δ u]) e
  | Δ, .bvar n => by
      by_cases hn : n = Δ.length
      · subst hn
        simp only [Term.openRec, ↓reduceIte, denotTermAux]
        rw [getD_append_singleton_self]
      · simp only [Term.openRec, if_neg hn, denotTermAux]
        rw [getD_append_singleton_ne _ _ hn]
  | _, .real _ => rfl
  | Δ, .var w => by simp only [Term.openRec, denotTermAux]
  | Δ, .zero s => by
      simp only [Term.openRec, denotTermAux]; rw [denotSpaceAux_inst hu σ Δ s]
  | Δ, .inner s => by
      simp only [Term.openRec, denotTermAux]; rw [denotSpaceAux_inst hu σ Δ s]
  | Δ, .smul e₀ e₁ => by
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_inst hu σ Δ e₀, denotTermAux_inst hu σ Δ e₁]
  | Δ, .add e₀ e₁ => by
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_inst hu σ Δ e₀, denotTermAux_inst hu σ Δ e₁]
  | Δ, .dsumE e₀ e₁ => by
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_inst hu σ Δ e₀, denotTermAux_inst hu σ Δ e₁]
  | Δ, .tprodE e₀ e₁ => by
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_inst hu σ Δ e₀, denotTermAux_inst hu σ Δ e₁]
  | Δ, .appN e₀ e₁ => by
      simp only [Term.openRec, denotTermAux]
      rw [denotTermAux_inst hu σ Δ e₀, denotTermAux_inst hu σ Δ e₁]
  | Δ, .appL s₀ s₁ e₀ e₁ => by
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
          denotTermAux_inst hu σ Δ e₀, denotTermAux_inst hu σ Δ e₁]
  | Δ, .appI s e₀ e₁ => by
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_inst hu σ Δ s, denotTermAux_inst hu σ Δ e₀,
          denotTermAux_inst hu σ Δ e₁]
  | Δ, .pinvT s₀ s₁ e => by
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
          denotTermAux_inst hu σ Δ e]
  | Δ, .pinvD s e => by
      simp only [Term.openRec, denotTermAux]
      rw [denotSpaceAux_inst hu σ Δ s, denotTermAux_inst hu σ Δ e]
  | Δ, .llam s₀ s e => by
      simp only [Term.openRec]
      refine denotTermAux_llam_congr
        (denotSpaceAux_inst hu σ Δ s₀)
        (denotSpaceAux_inst hu σ Δ s)
        (Space.isReal_openRec Δ.length u s) ?_
      intro v
      have hirr : denotTermAux σ (v :: Δ) u = denotTermAux σ Δ u :=
        denotTermAux_lc_irrel hu σ _ Δ
      have ih := denotTermAux_inst hu σ (v :: Δ) e
      rw [hirr] at ih
      exact ih
  | Δ, .nllam τ e => by
      simp only [Term.openRec, denotTermAux]
      rw [denotTyAux_inst hu σ Δ τ]
      refine congrArg (DVal.pi _) ?_
      funext z
      have hirr : denotTermAux σ ((denotTyAux σ (Δ ++ [denotTermAux σ Δ u]) τ).embed z :: Δ) u
                = denotTermAux σ Δ u := denotTermAux_lc_irrel hu σ _ Δ
      have ih := denotTermAux_inst hu σ ((denotTyAux σ (Δ ++ [denotTermAux σ Δ u]) τ).embed z :: Δ) e
      rw [hirr] at ih
      exact ih
  | Δ, .embed s => by
      simp only [Term.openRec]
      cases s with
      | empty => rfl
      | real => rfl
      | dual _ => rfl
      | dsum _ _ => rfl
      | tprod _ _ => rfl
      | ker s₀ s₁ e =>
          simp only [Space.openRec, denotTermAux]
          rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
              denotTermAux_inst hu σ Δ e]
      | coker s₀ s₁ e =>
          simp only [Space.openRec, denotTermAux]
          rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
              denotTermAux_inst hu σ Δ e]
      | img s₀ s₁ e =>
          simp only [Space.openRec, denotTermAux]
          rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
              denotTermAux_inst hu σ Δ e]
      | coimg s₀ s₁ e =>
          simp only [Space.openRec, denotTermAux]
          rw [denotSpaceAux_inst hu σ Δ s₀, denotSpaceAux_inst hu σ Δ s₁,
              denotTermAux_inst hu σ Δ e]

end

/-- `instantiate` corollary (Δ=[]): the codomain of a Π-type, instantiated by a
    locally-closed argument `u`, denotes as the codomain under the single-entry
    env `[⟦u⟧σ]`. Consumed by `app_nonlinear`'s soundness. -/
theorem denotTy_instantiate {u : Term} (hu : Term.lc u) (σ : DEnv) (τ : Ty) :
    denotTy σ (Ty.instantiate u τ) = denotTyAux σ [denotTerm σ u] τ := by
  have h := denotTyAux_inst hu σ [] τ
  simpa using h

theorem denotTerm_instantiate {u : Term} (hu : Term.lc u) (σ : DEnv) (e : Term) :
    denotTerm σ (Term.instantiate u e) = denotTermAux σ [denotTerm σ u] e := by
  have h := denotTermAux_inst hu σ [] e
  simpa using h

end GLang
