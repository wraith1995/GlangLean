

import GLang.Annotated.Binding
import GLang.Proofs.Source.FreeVars
import GLang.Annotated.Judgments
import GLang.Annotated.Denotation
import Mathlib.Data.Finmap

namespace GLang

/-- `σ₁ ≈ σ₂` on `S`: agreement on variable lookups inside `S`. -/
structure DEnv.AgreeOn (σ₁ σ₂ : DEnv) (S : Finset Name) : Prop where
  vars  : ∀ x ∈ S, σ₁.vars.lookup x = σ₂.vars.lookup x

namespace DEnv.AgreeOn

variable {σ₁ σ₂ : DEnv}

/-- Weakening: agreement on a larger set implies agreement on a subset. -/
theorem mono {S T : Finset Name} (h : σ₁.AgreeOn σ₂ T) (hST : S ⊆ T) :
    σ₁.AgreeOn σ₂ S :=
  ⟨fun x hx => h.vars x (hST hx)⟩

theorem of_union_left {S T : Finset Name} (h : σ₁.AgreeOn σ₂ (S ∪ T)) :
    σ₁.AgreeOn σ₂ S :=
  h.mono Finset.subset_union_left

theorem of_union_right {S T : Finset Name} (h : σ₁.AgreeOn σ₂ (S ∪ T)) :
    σ₁.AgreeOn σ₂ T :=
  h.mono Finset.subset_union_right

/-- Bind both sides with the same value; the resulting envs agree on `S`
    provided the underlying envs agreed on `S.erase x`. -/
theorem bind_erase {S : Finset Name} {x : Name}
    (h : σ₁.AgreeOn σ₂ (S.erase x)) (v : DVal) :
    (σ₁.bind x v).AgreeOn (σ₂.bind x v) S where
  vars y hy := by
    by_cases hxy : y = x
    · subst hxy; simp [DEnv.bind]
    · simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hxy]
      exact h.vars y (Finset.mem_erase.mpr ⟨hxy, hy⟩)

/-- Reflexivity: σ agrees with itself on any set. -/
theorem refl (σ : DEnv) (S : Finset Name) : σ.AgreeOn σ S :=
  ⟨fun _ _ => rfl⟩

/-- `(σ.bind x v) ≈ σ on S` provided `x ∉ S` — adding a binding for `x`
    is invisible outside `S` when `x` isn't in `S`. -/
theorem bind_left_of_not_mem {σ : DEnv} {S : Finset Name} {x : Name} {v : DVal}
    (hx : x ∉ S) : (σ.bind x v).AgreeOn σ S where
  vars y hy := by
    have hy_ne : y ≠ x := fun heq => hx (heq ▸ hy)
    simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hy_ne]

end DEnv.AgreeOn

/-! ## Main lemma: agreement-on-FV implies equal denotations (Δ-threaded). -/

mutual

theorem denotSpaceAux_agree :
    ∀ {σ₁ σ₂ : DEnv} (Δ : List DVal) (s : Space),
      σ₁.AgreeOn σ₂ (Space.fv s) → denotSpaceAux σ₁ Δ s = denotSpaceAux σ₂ Δ s
  | _, _, _, .empty, _ => rfl
  | _, _, _, .real,  _ => rfl
  | _, _, Δ, .dual s, h => by
      unfold Space.fv at h
      have := denotSpaceAux_agree Δ s h
      unfold denotSpaceAux; rw [this]
  | _, _, Δ, .dsum s₀ s₁, h => by
      unfold Space.fv at h
      have h₀ := denotSpaceAux_agree Δ s₀ h.of_union_left
      have h₁ := denotSpaceAux_agree Δ s₁ h.of_union_right
      unfold denotSpaceAux; rw [h₀, h₁]
  | _, _, Δ, .tprod s₀ s₁, h => by
      unfold Space.fv at h
      have h₀ := denotSpaceAux_agree Δ s₀ h.of_union_left
      have h₁ := denotSpaceAux_agree Δ s₁ h.of_union_right
      unfold denotSpaceAux; rw [h₀, h₁]
  | _, _, Δ, .ker s₀ s₁ e, h => by
      unfold Space.fv at h
      have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
      have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_right
      have h_e  := denotTermAux_agree Δ e h.of_union_right
      unfold denotSpaceAux; rw [h_s₀, h_s₁, h_e]
  | _, _, Δ, .coker s₀ s₁ e, h => by
      unfold Space.fv at h
      have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
      have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_right
      have h_e  := denotTermAux_agree Δ e h.of_union_right
      unfold denotSpaceAux; rw [h_s₀, h_s₁, h_e]
  | _, _, Δ, .img s₀ s₁ e, h => by
      unfold Space.fv at h
      have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
      have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_right
      have h_e  := denotTermAux_agree Δ e h.of_union_right
      unfold denotSpaceAux; rw [h_s₀, h_s₁, h_e]
  | _, _, Δ, .coimg s₀ s₁ e, h => by
      unfold Space.fv at h
      have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
      have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_right
      have h_e  := denotTermAux_agree Δ e h.of_union_right
      unfold denotSpaceAux; rw [h_s₀, h_s₁, h_e]

theorem denotTyAux_agree :
    ∀ {σ₁ σ₂ : DEnv} (Δ : List DVal) (τ : Ty),
      σ₁.AgreeOn σ₂ (Ty.fv τ) → denotTyAux σ₁ Δ τ = denotTyAux σ₂ Δ τ
  | _, _, Δ, .space s, h => by
      unfold Ty.fv at h
      have := denotSpaceAux_agree Δ s h
      unfold denotTyAux; rw [this]
  | _, _, Δ, .piTy τ₀ τ₁, h => by
      unfold Ty.fv at h
      have h_τ₀ := denotTyAux_agree Δ τ₀ h.of_union_left
      unfold denotTyAux
      rw [h_τ₀]
      refine congrArg (HType.sec _) ?_
      funext y
      exact denotTyAux_agree _ τ₁ h.of_union_right

theorem denotTermAux_agree :
    ∀ {σ₁ σ₂ : DEnv} (Δ : List DVal) (e : Term),
      σ₁.AgreeOn σ₂ (Term.fv e) → denotTermAux σ₁ Δ e = denotTermAux σ₂ Δ e
  | _, _, _, .bvar _, _ => rfl
  | _, _, _, .real _, _ => rfl
  | _, _, Δ, .zero s, h => by
      unfold Term.fv at h
      have := denotSpaceAux_agree Δ s h
      unfold denotTermAux; rw [this]
  | _, _, Δ, .inner s, h => by
      unfold Term.fv at h
      have := denotSpaceAux_agree Δ s h
      unfold denotTermAux; rw [this]
  | _, _, Δ, .smul e₀ e₁, h => by
      unfold Term.fv at h
      have h₀ := denotTermAux_agree Δ e₀ h.of_union_left
      have h₁ := denotTermAux_agree Δ e₁ h.of_union_right
      unfold denotTermAux; rw [h₀, h₁]
  | _, _, Δ, .add e₀ e₁, h => by
      unfold Term.fv at h
      have h₀ := denotTermAux_agree Δ e₀ h.of_union_left
      have h₁ := denotTermAux_agree Δ e₁ h.of_union_right
      unfold denotTermAux; rw [h₀, h₁]
  | _, _, Δ, .dsumE e₀ e₁, h => by
      unfold Term.fv at h
      have h₀ := denotTermAux_agree Δ e₀ h.of_union_left
      have h₁ := denotTermAux_agree Δ e₁ h.of_union_right
      unfold denotTermAux; rw [h₀, h₁]
  | _, _, Δ, .tprodE e₀ e₁, h => by
      unfold Term.fv at h
      have h₀ := denotTermAux_agree Δ e₀ h.of_union_left
      have h₁ := denotTermAux_agree Δ e₁ h.of_union_right
      unfold denotTermAux; rw [h₀, h₁]
  | _, _, Δ, .appN e₀ e₁, h => by
      unfold Term.fv at h
      have h₀ := denotTermAux_agree Δ e₀ h.of_union_left
      have h₁ := denotTermAux_agree Δ e₁ h.of_union_right
      unfold denotTermAux; rw [h₀, h₁]
  | _, _, Δ, .appL s₀ s₁ e₀ e₁, h => by
      unfold Term.fv at h
      have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left.of_union_left
      have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_left.of_union_right
      have h_e₀ := denotTermAux_agree Δ e₀ h.of_union_left.of_union_right
      have h_e₁ := denotTermAux_agree Δ e₁ h.of_union_right
      unfold denotTermAux; rw [h_s₀, h_s₁, h_e₀, h_e₁]
  | _, _, Δ, .appI s e₀ e₁, h => by
      unfold Term.fv at h
      have h_s  := denotSpaceAux_agree Δ s h.of_union_left.of_union_left
      have h_e₀ := denotTermAux_agree Δ e₀ h.of_union_left.of_union_right
      have h_e₁ := denotTermAux_agree Δ e₁ h.of_union_right
      unfold denotTermAux; rw [h_s, h_e₀, h_e₁]
  | _, _, Δ, .pinvT s₀ s₁ e, h => by
      unfold Term.fv at h
      have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
      have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_right
      have h_e  := denotTermAux_agree Δ e h.of_union_right
      unfold denotTermAux; rw [h_s₀, h_s₁, h_e]
  | _, _, Δ, .pinvD s e, h => by
      unfold Term.fv at h
      have h_s := denotSpaceAux_agree Δ s h.of_union_left
      have h_e := denotTermAux_agree Δ e h.of_union_right
      unfold denotTermAux; rw [h_s, h_e]
  | _, _, Δ, .var x, h => by
      unfold Term.fv at h
      have hx : x ∈ ({x} : Finset Name) := Finset.mem_singleton.mpr rfl
      have := h.vars x hx
      unfold denotTermAux; rw [this]
  | σ₁, σ₂, Δ, .llam s₀ s e, h => by
      unfold Term.fv at h
      have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
      have h_s  := denotSpaceAux_agree Δ s  h.of_union_left.of_union_right
      have body_agree : ∀ v : DVal, denotTermAux σ₁ (v :: Δ) e = denotTermAux σ₂ (v :: Δ) e :=
        fun v => denotTermAux_agree (v :: Δ) e h.of_union_right
      cases s
      case real =>
        simp only [denotTermAux]
        rw [h_s₀]
        exact congrArg (llamRealDVal _)
          (funext fun v => congrArg (·.atSpace HSpace.real) (body_agree v))
      all_goals (simp only [denotTermAux]
                 rw [h_s₀, h_s]
                 exact congrArg (llamTensorDVal _ _) (funext body_agree))
  | σ₁, σ₂, Δ, .nllam τ₀ e, h => by
      unfold Term.fv at h
      have h_τ₀ := denotTyAux_agree Δ τ₀ h.of_union_left
      unfold denotTermAux
      rw [h_τ₀]
      refine congrArg (DVal.pi _) ?_
      funext y
      exact denotTermAux_agree _ e h.of_union_right
  | _, _, Δ, .embed s, h => by
      unfold Term.fv at h
      cases s with
      | empty => rfl
      | real => rfl
      | dual _ => rfl
      | dsum _ _ => rfl
      | tprod _ _ => rfl
      | ker s₀ s₁ e =>
          unfold Space.fv at h
          have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
          have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_right
          have h_e  := denotTermAux_agree Δ e h.of_union_right
          simp only [denotTermAux]; rw [h_s₀, h_s₁, h_e]
      | coker s₀ s₁ e =>
          unfold Space.fv at h
          have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
          have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_right
          have h_e  := denotTermAux_agree Δ e h.of_union_right
          simp only [denotTermAux]; rw [h_s₀, h_s₁, h_e]
      | img s₀ s₁ e =>
          unfold Space.fv at h
          have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
          have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_right
          have h_e  := denotTermAux_agree Δ e h.of_union_right
          simp only [denotTermAux]; rw [h_s₀, h_s₁, h_e]
      | coimg s₀ s₁ e =>
          unfold Space.fv at h
          have h_s₀ := denotSpaceAux_agree Δ s₀ h.of_union_left.of_union_left
          have h_s₁ := denotSpaceAux_agree Δ s₁ h.of_union_left.of_union_right
          have h_e  := denotTermAux_agree Δ e h.of_union_right
          simp only [denotTermAux]; rw [h_s₀, h_s₁, h_e]

end

/-! ## Closed-term corollaries (`Δ = []`) — the wrapper statements. -/

theorem denotSpace_agree {σ₁ σ₂ : DEnv} (s : Space)
    (h : σ₁.AgreeOn σ₂ (Space.fv s)) : denotSpace σ₁ s = denotSpace σ₂ s :=
  denotSpaceAux_agree [] s h

theorem denotTy_agree {σ₁ σ₂ : DEnv} (τ : Ty)
    (h : σ₁.AgreeOn σ₂ (Ty.fv τ)) : denotTy σ₁ τ = denotTy σ₂ τ :=
  denotTyAux_agree [] τ h

theorem denotTerm_agree {σ₁ σ₂ : DEnv} (e : Term)
    (h : σ₁.AgreeOn σ₂ (Term.fv e)) : denotTerm σ₁ e = denotTerm σ₂ e :=
  denotTermAux_agree [] e h

end GLang
