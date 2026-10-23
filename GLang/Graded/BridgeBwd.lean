import GLang.Graded.Weakening
import GLang.Graded.BridgeFwd

namespace GLang.Graded

open GLang

/-! ## Promotion-free source derivations

The backward bridge visibly has no `HasType.promote` arm.  The predicates below
make that fact precise for the complete mutual source derivation, including
term-typing witnesses nested inside spaces, types, and subtyping derivations.
This hereditary formulation is the one needed by proof-indexed consumers of a
typing derivation; merely ruling out a promotion at the root would be too weak.
-/

mutual

/-- A space-validity derivation contains no nested `HasType.promote` node. -/
def SPromotionFree : {ε : NLCtx} → {s : Space} → SValid ε s → Prop
  | _, _, .empty => True
  | _, _, .real => True
  | _, _, .dual hs => SPromotionFree hs
  | _, _, .dsum hs₀ hs₁ => SPromotionFree hs₀ ∧ SPromotionFree hs₁
  | _, _, .tprod hs₀ hs₁ => SPromotionFree hs₀ ∧ SPromotionFree hs₁
  | _, _, .ker hs₀ hs₁ he =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧ PromotionFree he
  | _, _, .coker hs₀ hs₁ he =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧ PromotionFree he
  | _, _, .img hs₀ hs₁ he =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧ PromotionFree he
  | _, _, .coimg hs₀ hs₁ he =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧ PromotionFree he

/-- A type-validity derivation contains no nested `HasType.promote` node. -/
def TPromotionFree : {ε : NLCtx} → {τ : Ty} → {k : Kind} → TValid ε τ k → Prop
  | _, _, _, .space hs => SPromotionFree hs
  | _, _, _, .piTy L hτ₀ hbody =>
      TPromotionFree hτ₀ ∧ ∀ y (hy : y ∉ L), TPromotionFree (hbody y hy)

/-- A subtyping derivation contains no nested `HasType.promote` node. -/
def SubPromotionFree : {ε : NLCtx} → {s₀ s₁ : Space} → SubType ε s₀ s₁ → Prop
  | _, _, _, .sub_ker hs₀ hs₁ he =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧ PromotionFree he
  | _, _, _, .sub_coker hs₀ hs₁ he =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧ PromotionFree he
  | _, _, _, .sub_img hs₀ hs₁ he =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧ PromotionFree he
  | _, _, _, .sub_coimg hs₀ hs₁ he =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧ PromotionFree he

/-- A complete source typing derivation contains no `HasType.promote` node,
including in its formation and subtyping premises. -/
def PromotionFree : {Δ : LCtx} → {ε : NLCtx} → {e : Term} → {τ : Ty} →
    HasType Δ ε e τ → Prop
  | _, _, _, _, .zero hs => SPromotionFree hs
  | _, _, _, _, .smul hs _ h₀ h₁ =>
      SPromotionFree hs ∧ PromotionFree h₀ ∧ PromotionFree h₁
  | _, _, _, _, .add hs h₀ h₁ =>
      SPromotionFree hs ∧ PromotionFree h₀ ∧ PromotionFree h₁
  | _, _, _, _, .inner hs => SPromotionFree hs
  | _, _, _, _, .real_lit _ => True
  | _, _, _, _, .app_linear hs₀ hs₁ _ h₀ h₁ =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧
        PromotionFree h₀ ∧ PromotionFree h₁
  | _, _, _, _, .app_inner hs _ h₀ h₁ =>
      SPromotionFree hs ∧ PromotionFree h₀ ∧ PromotionFree h₁
  | _, _, _, _, .app_nonlinear h₀ h₁ => PromotionFree h₀ ∧ PromotionFree h₁
  | _, _, _, _, .var_lin => True
  | _, _, _, _, .var_nlin _ => True
  | _, _, _, _, .pinv_tensor hs₀ hs₁ he =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧ PromotionFree he
  | _, _, _, _, .pinv_dual hs he => SPromotionFree hs ∧ PromotionFree he
  | _, _, _, _, .promote _ _ _ _ _ => False
  | _, _, _, _, .dsumE hs₀ hs₁ h₀ h₁ =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧
        PromotionFree h₀ ∧ PromotionFree h₁
  | _, _, _, _, .tprodE hs₀ hs₁ _ h₀ h₁ =>
      SPromotionFree hs₀ ∧ SPromotionFree hs₁ ∧
        PromotionFree h₀ ∧ PromotionFree h₁
  | _, _, _, _, .llam_real L hs hbody =>
      SPromotionFree hs ∧ ∀ y (hy : y ∉ L), PromotionFree (hbody y hy)
  | _, _, _, _, .llam_tensor L _ hs₀ hs hbody =>
      SPromotionFree hs₀ ∧ SPromotionFree hs ∧
        ∀ y (hy : y ∉ L), PromotionFree (hbody y hy)
  | _, _, _, _, .embed hsub => SubPromotionFree hsub
  | _, _, _, _, .nllam L hτ hbody =>
      TPromotionFree hτ ∧ ∀ y (hy : y ∉ L), PromotionFree (hbody y hy)

end

/-! ## An insert-based induction principle for `LCtx`. -/

/-- Key-peeling induction for `LCtx` (via `AList.insertRec`). -/
theorem lctx_insert_induction {C : LCtx → Prop} (hemp : C ∅)
    (hins : ∀ (x : Name) (s : Space) (m : LCtx), x ∉ m → C m → C (Finmap.insert x s m)) :
    ∀ m : LCtx, C m := by
  intro m
  induction m using Finmap.induction_on with
  | _ al =>
    induction al with
    | H0 => exact hemp
    | IH a b l hnm ih =>
        rw [← Finmap.insert_toFinmap]
        exact hins a b (AList.toFinmap l) (by rwa [Finmap.mem_toFinmap]) ih

/-! ## The threading relation. -/

/-- Pointwise `tr`-recovery: `Γ x` is `tr Δ ε x` up to grade-`0` drop / `1→ω` bump /
    ε-add. Like `WkPt` (`Weakening.lean`) but a grade-`0` (inert) source may drop to
    `none` or re-appear as a nonlinear (`≠1`) target. -/
def WkPt0 (a b : Option (GGrade × Ty)) : Prop :=
  match a, b with
  | none, none => True
  | none, some (g', _) => g' ≠ GGrade.one
  | some (GGrade.zero, _), none => True
  | some (GGrade.zero, _), some (g', _) => g' ≠ GGrade.one
  | some (_, _), none => False
  | some (g, τ), some (g', τ') => τ = τ' ∧ GGrade.Wk g g'

/-- `Γ` recovers `tr Δ ε` (up to inert grade-0 / `1→ω` / ε-add). -/
def TrGe (Γ : GCtx) (Δ : LCtx) (ε : NLCtx) : Prop := ∀ x, WkPt0 (Γ x) (tr Δ ε x)

/-- `tr Δ ε` recovers itself. -/
theorem TrGe.refl_tr (Δ : LCtx) (ε : NLCtx) : TrGe (tr Δ ε) Δ ε := by
  intro x
  simp only [tr]
  cases hΔ : Δ.lookup x with
  | some s => exact ⟨rfl, GGrade.Wk.refl _⟩
  | none =>
    cases hε : ε.lookup x with
    | some τ => exact ⟨rfl, GGrade.Wk.refl _⟩
    | none => trivial

/-! ## Pointwise split recovery. -/

/-- `WkPt0 none c` whenever the target `c` is not a fresh LINEAR var. -/
theorem wkpt0_none {c : Option (GGrade × Ty)} (hc : ∀ τ, c ≠ some (GGrade.one, τ)) :
    WkPt0 none c := by
  rcases c with _ | ⟨gc, τc⟩
  · trivial
  · intro h; exact hc τc (by rw [h])

/-- `WkPt0 (some (0, τ)) c` whenever the target `c` is not a fresh LINEAR var. -/
theorem wkpt0_zero {τ : Ty} {c : Option (GGrade × Ty)} (hc : ∀ τ', c ≠ some (GGrade.one, τ')) :
    WkPt0 (some (GGrade.zero, τ)) c := by
  rcases c with _ | ⟨gc, τc⟩
  · trivial
  · intro h; exact hc τc (by rw [h])

/-- At a NON-LINEAR (ε / absent) target the split distributes: if the SUM recovers `c`
    and the branches type-agree, EACH branch recovers `c`. -/
theorem splitBack_np {a b c : Option (GGrade × Ty)}
    (hc : ∀ τ, c ≠ some (GGrade.one, τ))
    (hta : ∀ ga τa gb τb, a = some (ga, τa) → b = some (gb, τb) → τa = τb)
    (hw : WkPt0 (gadd a b) c) : WkPt0 a c ∧ WkPt0 b c := by
  rcases a with _ | ⟨ga, τa⟩ <;> rcases b with _ | ⟨gb, τb⟩
  · exact ⟨wkpt0_none hc, wkpt0_none hc⟩
  · simp only [gadd] at hw; exact ⟨wkpt0_none hc, hw⟩
  · simp only [gadd] at hw; exact ⟨hw, wkpt0_none hc⟩
  · have hτ : τa = τb := hta ga τa gb τb rfl rfl
    subst hτ
    simp only [gadd] at hw
    rcases c with _ | ⟨gc, τc⟩ <;>
      · cases ga <;> cases gb <;>
          simp_all [WkPt0, GGrade.add, GGrade.Wk]

/-- From `WkPt0 (gadd a b) (some (1, σ))` the sum is EXACTLY `some (1, σ)`. -/
theorem gadd_eq_of_wkpt0_one {a b : Option (GGrade × Ty)} {σ : Ty}
    (hw : WkPt0 (gadd a b) (some (GGrade.one, σ))) : gadd a b = some (GGrade.one, σ) := by
  rcases hg : gadd a b with _ | ⟨g, τ⟩
  · rw [hg] at hw; exact absurd rfl hw
  · rw [hg] at hw
    cases g <;> simp_all [WkPt0, GGrade.Wk]

/-- A grade-`1` sum routes ENTIRELY to one branch; the other branch is inert at `x`
    (`none` or grade-`0`), i.e. `WkPt0 · none`. Uses point `TypeAgree` to fix the type. -/
theorem gadd_one_route {a b : Option (GGrade × Ty)} {σ : Ty}
    (hta : ∀ ga τa gb τb, a = some (ga, τa) → b = some (gb, τb) → τa = τb)
    (h : gadd a b = some (GGrade.one, σ)) :
    (a = some (GGrade.one, σ) ∧ WkPt0 b none) ∨ (b = some (GGrade.one, σ) ∧ WkPt0 a none) := by
  rcases a with _ | ⟨ga, τa⟩ <;> rcases b with _ | ⟨gb, τb⟩
  · simp only [gadd] at h; exact absurd h (by simp)
  · simp only [gadd] at h; exact Or.inr ⟨h, trivial⟩
  · simp only [gadd] at h; exact Or.inl ⟨h, trivial⟩
  · have hτ := hta ga τa gb τb rfl rfl; subst hτ
    simp only [gadd, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hadd, hτeq⟩ := h; subst hτeq
    cases ga <;> cases gb <;> simp only [GGrade.add] at hadd <;>
      first
        | exact absurd hadd (by decide)
        | exact Or.inl ⟨rfl, trivial⟩
        | exact Or.inr ⟨rfl, trivial⟩

/-- **`splitBack`.** Recover a disjoint linear partition from a graded split. -/
theorem splitBack {ε : NLCtx} :
    ∀ (Δ : LCtx) (Γ₀ Γ₁ : GCtx),
      (∀ x, WkPt0 (gadd (Γ₀ x) (Γ₁ x)) (tr Δ ε x)) → TypeAgree Γ₀ Γ₁ → CtxDisj Δ ε →
      ∃ Δ₀ Δ₁ : LCtx, Δ₀ ∪ Δ₁ = Δ ∧ Finmap.Disjoint Δ₀ Δ₁ ∧
        CtxDisj Δ₀ ε ∧ CtxDisj Δ₁ ε ∧ TrGe Γ₀ Δ₀ ε ∧ TrGe Γ₁ Δ₁ ε := by
  refine lctx_insert_induction ?_ ?_
  · -- Δ = ∅
    intro Γ₀ Γ₁ hpt hta _hcd
    refine ⟨∅, ∅, by simp, Finmap.disjoint_empty _, CtxDisj.empty ε, CtxDisj.empty ε, ?_, ?_⟩
    · intro x
      have hc : ∀ τ, tr (∅ : LCtx) ε x ≠ some (GGrade.one, τ) := by
        intro τ h; exact (tr_emptyΔ_no_lin ε) x τ h
      exact (splitBack_np hc (fun ga τa gb τb h0 h1 => hta x ga τa gb τb h0 h1) (hpt x)).1
    · intro x
      have hc : ∀ τ, tr (∅ : LCtx) ε x ≠ some (GGrade.one, τ) := by
        intro τ h; exact (tr_emptyΔ_no_lin ε) x τ h
      exact (splitBack_np hc (fun ga τa gb τb h0 h1 => hta x ga τa gb τb h0 h1) (hpt x)).2
  · -- Δ = insert x s Δ'
    intro x s Δ' hxΔ' IH Γ₀ Γ₁ hpt hta hcd
    -- x is LINEAR in the conclusion; recover its routing.
    have hxε : x ∉ ε := hcd x (Finmap.mem_insert.mpr (Or.inl rfl))
    have htrx : tr (Finmap.insert x s Δ') ε x = some (GGrade.one, .space s) := by
      rw [tr_insert, Function.update_self]
    have hsumx : gadd (Γ₀ x) (Γ₁ x) = some (GGrade.one, .space s) :=
      gadd_eq_of_wkpt0_one (by rw [← htrx]; exact hpt x)
    -- Peel x from both branches.
    set Γ₀' := Function.update Γ₀ x none with hΓ₀'
    set Γ₁' := Function.update Γ₁ x none with hΓ₁'
    have hpt' : ∀ y, WkPt0 (gadd (Γ₀' y) (Γ₁' y)) (tr Δ' ε y) := by
      intro y
      rcases eq_or_ne y x with rfl | hyx
      · rw [hΓ₀', hΓ₁', Function.update_self, Function.update_self]
        simp only [gadd]
        rw [tr, Finmap.lookup_eq_none.mpr hxΔ', Finmap.lookup_eq_none.mpr hxε]
        trivial
      · rw [hΓ₀', hΓ₁', Function.update_of_ne hyx, Function.update_of_ne hyx]
        have : tr Δ' ε y = tr (Finmap.insert x s Δ') ε y := by
          rw [tr_insert, Function.update_of_ne hyx]
        rw [this]; exact hpt y
    have hta' : TypeAgree Γ₀' Γ₁' := by
      intro y g0 τ0 g1 τ1 h0 h1
      rcases eq_or_ne y x with rfl | hyx
      · rw [hΓ₀', Function.update_self] at h0; exact absurd h0 (by simp)
      · rw [hΓ₀', Function.update_of_ne hyx] at h0
        rw [hΓ₁', Function.update_of_ne hyx] at h1
        exact hta y g0 τ0 g1 τ1 h0 h1
    have hcd' : CtxDisj Δ' ε := fun y hy => hcd y (Finmap.mem_insert.mpr (Or.inr hy))
    obtain ⟨Δ₀', Δ₁', hun', hdis', hcd0', hcd1', htr0', htr1'⟩ := IH Γ₀' Γ₁' hpt' hta' hcd'
    have hxΔ0' : x ∉ Δ₀' := fun h => hxΔ' (by rw [← hun']; exact Finmap.mem_union.mpr (Or.inl h))
    have hxΔ1' : x ∉ Δ₁' := fun h => hxΔ' (by rw [← hun']; exact Finmap.mem_union.mpr (Or.inr h))
    -- Route x by which branch grades it 1.
    rcases gadd_one_route (fun ga τa gb τb h0 h1 => hta x ga τa gb τb h0 h1) hsumx with
      ⟨hL, hR⟩ | ⟨hR, hL⟩
    · -- x routes LEFT: Γ₀ x = some (1, .space s), Γ₁ x inert.
      refine ⟨Finmap.insert x s Δ₀', Δ₁', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← Finmap.insert_union, hun']
      · intro y hy hy1
        rcases Finmap.mem_insert.mp hy with rfl | hy0
        · exact hxΔ1' hy1
        · exact hdis' y hy0 hy1
      · intro y hy
        rcases Finmap.mem_insert.mp hy with rfl | hy0
        · exact hxε
        · exact hcd0' y hy0
      · exact hcd1'
      · intro y
        rcases eq_or_ne y x with rfl | hyx
        · rw [hL, tr_insert, Function.update_self]; exact ⟨rfl, GGrade.Wk.refl _⟩
        · have h := htr0' y
          rw [hΓ₀', Function.update_of_ne hyx] at h
          rw [tr_insert, Function.update_of_ne hyx]; exact h
      · intro y
        rcases eq_or_ne y x with rfl | hyx
        · rw [tr, Finmap.lookup_eq_none.mpr hxΔ1', Finmap.lookup_eq_none.mpr hxε]; exact hR
        · have h := htr1' y
          rw [hΓ₁', Function.update_of_ne hyx] at h; exact h
    · -- x routes RIGHT: Γ₁ x = some (1, .space s), Γ₀ x inert.
      refine ⟨Δ₀', Finmap.insert x s Δ₁', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · apply Finmap.ext_lookup; intro y
        rcases eq_or_ne y x with rfl | hyx
        · rw [Finmap.lookup_union_right hxΔ0', Finmap.lookup_insert, Finmap.lookup_insert]
        · rw [Finmap.lookup_insert_of_ne _ hyx]
          by_cases hy0 : y ∈ Δ₀'
          · rw [Finmap.lookup_union_left hy0, ← hun', Finmap.lookup_union_left hy0]
          · rw [Finmap.lookup_union_right hy0, Finmap.lookup_insert_of_ne _ hyx,
                ← hun', Finmap.lookup_union_right hy0]
      · intro y hy hy1
        rcases Finmap.mem_insert.mp hy1 with rfl | hy1'
        · exact hxΔ0' hy
        · exact hdis' y hy hy1'
      · exact hcd0'
      · intro y hy
        rcases Finmap.mem_insert.mp hy with rfl | hy1
        · exact hxε
        · exact hcd1' y hy1
      · intro y
        rcases eq_or_ne y x with rfl | hyx
        · rw [tr, Finmap.lookup_eq_none.mpr hxΔ0', Finmap.lookup_eq_none.mpr hxε]; exact hL
        · have h := htr0' y
          rw [hΓ₀', Function.update_of_ne hyx] at h; exact h
      · intro y
        rcases eq_or_ne y x with rfl | hyx
        · rw [hR, tr_insert, Function.update_self]; exact ⟨rfl, GGrade.Wk.refl _⟩
        · have h := htr1' y
          rw [hΓ₁', Function.update_of_ne hyx] at h
          rw [tr_insert, Function.update_of_ne hyx]; exact h

/-! ## Type-context recovery and leaf/var shape lemmas. -/

/-- The ω-view of `Γ` is contained in `asTypeCtx ε`: a grade-`ω` var of `Γ` maps to an
    ε var of the same type (`ω` cannot drop, and `tr` gives `ω` only on ε). -/
theorem typeCtxOmega_submap {Γ : GCtx} {Δ : LCtx} {ε : NLCtx}
    (htr : TrGe Γ Δ ε) : SubMap (typeCtxOmega Γ) (asTypeCtx ε) := by
  intro x τ hx
  have hΓ : Γ x = some (GGrade.omega, τ) := by
    simp only [typeCtxOmega] at hx
    rcases hg : Γ x with _ | ⟨g, τg⟩
    · rw [hg] at hx; simp at hx
    · rw [hg] at hx; cases g <;> simp_all
  have hw := htr x; rw [hΓ] at hw
  rcases htrx : tr Δ ε x with _ | ⟨g', τ'⟩
  · rw [htrx] at hw; exact hw.elim
  · rw [htrx] at hw
    obtain ⟨hτ, hwk⟩ := hw
    simp only [asTypeCtx]
    simp only [tr] at htrx
    rcases hΔ : Δ.lookup x with _ | s
    · rw [hΔ] at htrx
      rcases hεl : ε.lookup x with _ | τε
      · rw [hεl] at htrx; simp at htrx
      · rw [hεl] at htrx
        simp only [Option.some.injEq, Prod.mk.injEq] at htrx
        first
          | rw [hεl, hτ, htrx.2]
          | rw [hτ, htrx.2]
    · rw [hΔ] at htrx
      simp only [Option.some.injEq, Prod.mk.injEq] at htrx
      rw [← htrx.1] at hwk
      simp [GGrade.Wk] at hwk

theorem noLin_trge_empty {Γ : GCtx} {Δ : LCtx} {ε : NLCtx}
    (hnl : NoLin Γ) (htr : TrGe Γ Δ ε) : Δ = ∅ := by
  apply Finmap.ext_lookup
  intro x
  rw [Finmap.lookup_empty]
  rcases hΔ : Δ.lookup x with _ | s
  · rfl
  · exfalso
    have htrx : tr Δ ε x = some (GGrade.one, .space s) := by simp only [tr, hΔ]
    have hw := htr x; rw [htrx] at hw
    have hxΓ : Γ x = some (GGrade.one, .space s) := by
      rcases hg : Γ x with _ | ⟨gz, τz⟩
      · rw [hg] at hw; exact absurd rfl hw
      · rw [hg] at hw; cases gz <;> simp_all [WkPt0, GGrade.Wk]
    exact hnl x (.space s) hxΓ

private def gvarShapeData
    {Γ : GCtx} {Δ : LCtx} {ε : NLCtx} {x : Name} {g : GGrade} {τ : Ty}
    (htr : TrGe Γ Δ ε) (hx : Γ x = some (g, τ)) (hg : g ≠ GGrade.zero)
    (haff : ∀ y, y ≠ x → ∀ τy, Γ y ≠ some (GGrade.one, τy)) :
    {ht : HasType Δ ε (.var x) τ // PromotionFree ht} := by
  have hsub : ∀ z, z ≠ x → Δ.lookup z = none := by
    intro z hzx
    rcases hΔz : Δ.lookup z with _ | sz
    · rfl
    · exfalso
      have htrz : tr Δ ε z = some (GGrade.one, .space sz) := by simp only [tr, hΔz]
      have hw := htr z; rw [htrz] at hw
      have : Γ z = some (GGrade.one, .space sz) := by
        rcases hgz : Γ z with _ | ⟨gz, τz⟩
        · rw [hgz] at hw; exact absurd rfl hw
        · rw [hgz] at hw; cases gz <;> simp_all [WkPt0, GGrade.Wk]
      exact haff z hzx (.space sz) this
  rcases hΔx : Δ.lookup x with _ | s
  · have hΔempty : Δ = ∅ := by
      apply Finmap.ext_lookup; intro y; rw [Finmap.lookup_empty]
      rcases eq_or_ne y x with rfl | hyx
      · exact hΔx
      · exact hsub y hyx
    subst hΔempty
    have hw := htr x; rw [hx] at hw
    have hεx : ε.lookup x = some τ := by
      rcases hε : ε.lookup x with _ | τε
      · exfalso
        have htx : tr (∅ : LCtx) ε x = none := by simp only [tr, Finmap.lookup_empty, hε]
        rw [htx] at hw; cases g <;> simp_all [WkPt0]
      · have htx : tr (∅ : LCtx) ε x = some (GGrade.omega, τε) := by
          simp only [tr, Finmap.lookup_empty, hε]
        rw [htx] at hw
        have hττ : τ = τε := by cases g <;> simp_all [WkPt0, GGrade.Wk]
        first
          | rw [hε, hττ]
          | rw [hττ]
    exact ⟨HasType.var_nlin hεx, True.intro⟩
  · have hΔsingle : Δ = Finmap.singleton x s := by
      apply Finmap.ext_lookup; intro y
      rcases eq_or_ne y x with rfl | hyx
      · rw [hΔx, Finmap.lookup_singleton_eq]
      · rw [hsub y hyx, Finmap.lookup_eq_none.mpr (by rw [Finmap.mem_singleton]; exact hyx)]
    have hw := htr x; rw [hx] at hw
    have htrx : tr Δ ε x = some (GGrade.one, .space s) := by simp only [tr, hΔx]
    rw [htrx] at hw
    have hτ : τ = .space s := by cases g <;> simp_all [WkPt0, GGrade.Wk]
    subst hτ; rw [hΔsingle]
    exact ⟨HasType.var_lin, True.intro⟩

/-- **`gvar` inverts to `var_lin` / `var_nlin`.** The affine leaf condition forces
    `Δ ⊆ {x}`; then `x ∈ Δ` gives `var_lin` (singleton), `x ∉ Δ` gives `var_nlin`. -/
def gvar_shape {Γ : GCtx} {Δ : LCtx} {ε : NLCtx} {x : Name} {g : GGrade} {τ : Ty}
    (htr : TrGe Γ Δ ε) (hx : Γ x = some (g, τ)) (hg : g ≠ GGrade.zero)
    (haff : ∀ y, y ≠ x → ∀ τy, Γ y ≠ some (GGrade.one, τy)) :
    HasType Δ ε (.var x) τ :=
  (gvarShapeData htr hx hg haff).1

/-- The source variable derivation recovered from a graded variable has no
`HasType.promote` node. -/
theorem gvar_shape_promotionFree
    {Γ : GCtx} {Δ : LCtx} {ε : NLCtx} {x : Name} {g : GGrade} {τ : Ty}
    (htr : TrGe Γ Δ ε) (hx : Γ x = some (g, τ)) (hg : g ≠ GGrade.zero)
    (haff : ∀ y, y ≠ x → ∀ τy, Γ y ≠ some (GGrade.one, τy)) :
    PromotionFree (gvar_shape htr hx hg haff) :=
  (gvarShapeData htr hx hg haff).2

/-! ## `TrGe` under binders and at FFS witnesses. -/

/-- Linear binder: extend `Γ` by a fresh grade-`1` vector and `Δ` by `y : s`. -/
theorem TrGe.insert_lin {Γ : GCtx} {Δ : LCtx} {ε : NLCtx} (htr : TrGe Γ Δ ε)
    (y : Name) (s : Space) :
    TrGe (Function.update Γ y (some (GGrade.one, .space s))) (Finmap.insert y s Δ) ε := by
  intro z
  rcases eq_or_ne z y with rfl | hzy
  · rw [Function.update_self, tr_insert, Function.update_self]; exact ⟨rfl, GGrade.Wk.refl _⟩
  · rw [Function.update_of_ne hzy, tr_insert, Function.update_of_ne hzy]; exact htr z

/-- ω binder (over an empty `Δ`): extend `Γ` by a fresh grade-`ω` var and `ε` by `y : τ₀`. -/
theorem TrGe.insert_omega {Γ : GCtx} {ε : NLCtx} (htr : TrGe Γ (∅ : LCtx) ε)
    (y : Name) (τ₀ : Ty) :
    TrGe (Function.update Γ y (some (GGrade.omega, τ₀))) (∅ : LCtx) (Finmap.insert y τ₀ ε) := by
  intro z
  rcases eq_or_ne z y with rfl | hzy
  · rw [Function.update_self, tr_insert_nl, Function.update_self]; exact ⟨rfl, GGrade.Wk.refl _⟩
  · rw [Function.update_of_ne hzy, tr_insert_nl, Function.update_of_ne hzy]; exact htr z

/-- The FFS-witness context `resurrect f` recovers `(∅, ε)` when `f ⊑ asTypeCtx ε`. -/
theorem TrGe.resurrect_of_submap {f : Name → Option Ty} {ε : NLCtx}
    (h : SubMap f (asTypeCtx ε)) : TrGe (resurrect f) (∅ : LCtx) ε := by
  intro x
  rcases hf : f x with _ | τ
  · have : resurrect f x = none := by simp only [resurrect, hf, Option.map_none]
    rw [this]
    refine wkpt0_none (fun τ' hτ' => ?_)
    simp only [tr, Finmap.lookup_empty] at hτ'
    rcases hε : ε.lookup x with _ | τε
    · rw [hε] at hτ'; simp at hτ'
    · rw [hε] at hτ'; simp only [Option.some.injEq, Prod.mk.injEq] at hτ'
      exact absurd hτ'.1 (by decide)
  · have hru : resurrect f x = some (GGrade.omega, τ) := by
      simp only [resurrect, hf, Option.map_some]
    have hε : ε.lookup x = some τ := h x τ hf
    rw [hru, show tr (∅ : LCtx) ε x = some (GGrade.omega, τ) by
      simp only [tr, Finmap.lookup_empty, hε]]
    exact ⟨rfl, GGrade.Wk.refl _⟩

/-! ## `splitBack` as data (via choice), for the split arms of the mutual. -/

/-- The linear partition recovered by `splitBack`, packaged as data. -/
structure SplitData (Γ₀ Γ₁ : GCtx) (Δ : LCtx) (ε : NLCtx) : Type where
  Δ₀ : LCtx
  Δ₁ : LCtx
  hun : Δ₀ ∪ Δ₁ = Δ
  hdis : Finmap.Disjoint Δ₀ Δ₁
  hcd0 : CtxDisj Δ₀ ε
  hcd1 : CtxDisj Δ₁ ε
  htr0 : TrGe Γ₀ Δ₀ ε
  htr1 : TrGe Γ₁ Δ₁ ε

/-- `splitBack`'s existential, realized as `SplitData` (uses choice; noncomputable). -/
noncomputable def splitBackData {Γ Γ₀ Γ₁ : GCtx} {Δ : LCtx} {ε : NLCtx}
    (hsp : ∀ x, Γ x = gadd (Γ₀ x) (Γ₁ x)) (htr : TrGe Γ Δ ε)
    (hta : TypeAgree Γ₀ Γ₁) (hcd : CtxDisj Δ ε) : SplitData Γ₀ Γ₁ Δ ε := by
  have hpt : ∀ x, WkPt0 (gadd (Γ₀ x) (Γ₁ x)) (tr Δ ε x) := fun x => hsp x ▸ htr x
  choose Δ₀ Δ₁ hun hdis hcd0 hcd1 htr0 htr1 using splitBack Δ Γ₀ Γ₁ hpt hta hcd
  exact ⟨Δ₀, Δ₁, hun, hdis, hcd0, hcd1, htr0, htr1⟩

mutual

/-- `GSValid (asTypeCtx ε) s → SValid ε s` (via `SubMap` to `asTypeCtx ε`). -/
noncomputable def svalidBwd : {f : Name → Option Ty} → {s : Space} → GSValid f s →
    {ε : NLCtx} → SubMap f (asTypeCtx ε) → SValid ε s
  | _, _, .empty, _, _ => .empty
  | _, _, .real, _, _ => .real
  | _, _, .dual d, _, hsm => .dual (svalidBwd d hsm)
  | _, _, .dsum d₀ d₁, _, hsm => .dsum (svalidBwd d₀ hsm) (svalidBwd d₁ hsm)
  | _, _, .tprod d₀ d₁, _, hsm => .tprod (svalidBwd d₀ hsm) (svalidBwd d₁ hsm)
  | _, _, .ker hs₀ hs₁ he, _, hsm =>
      .ker (svalidBwd hs₀ hsm) (svalidBwd hs₁ hsm)
           (hasTypeBwd he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _))
  | _, _, .coker hs₀ hs₁ he, _, hsm =>
      .coker (svalidBwd hs₀ hsm) (svalidBwd hs₁ hsm)
             (hasTypeBwd he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _))
  | _, _, .img hs₀ hs₁ he, _, hsm =>
      .img (svalidBwd hs₀ hsm) (svalidBwd hs₁ hsm)
           (hasTypeBwd he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _))
  | _, _, .coimg hs₀ hs₁ he, _, hsm =>
      .coimg (svalidBwd hs₀ hsm) (svalidBwd hs₁ hsm)
             (hasTypeBwd he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _))

/-- `GTValid (asTypeCtx ε) τ k → TValid ε τ k`. -/
noncomputable def tvalidBwd : {f : Name → Option Ty} → {τ : Ty} → {k : Kind} → GTValid f τ k →
    {ε : NLCtx} → SubMap f (asTypeCtx ε) → TValid ε τ k
  | _, _, _, .space hs, _, hsm => .space (svalidBwd hs hsm)
  | _, _, _, .piTy L hτ₀ hbody, ε, hsm =>
      .piTy (L ∪ ε.keys) (tvalidBwd hτ₀ hsm)
        (fun y hy => by
          simp only [Finset.mem_union, not_or] at hy
          exact tvalidBwd (hbody y hy.1)
            (by rw [asTypeCtx_insert]; exact submap_update hsm y (some _)))

/-- `GSubType (asTypeCtx ε) s₀ s₁ → SubType ε s₀ s₁`. -/
noncomputable def subtypeBwd : {f : Name → Option Ty} → {s₀ s₁ : Space} → GSubType f s₀ s₁ →
    {ε : NLCtx} → SubMap f (asTypeCtx ε) → SubType ε s₀ s₁
  | _, _, _, .sub_ker hs₀ hs₁ he, _, hsm =>
      .sub_ker (svalidBwd hs₀ hsm) (svalidBwd hs₁ hsm)
               (hasTypeBwd he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _))
  | _, _, _, .sub_coker hs₀ hs₁ he, _, hsm =>
      .sub_coker (svalidBwd hs₀ hsm) (svalidBwd hs₁ hsm)
                 (hasTypeBwd he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _))
  | _, _, _, .sub_img hs₀ hs₁ he, _, hsm =>
      .sub_img (svalidBwd hs₀ hsm) (svalidBwd hs₁ hsm)
               (hasTypeBwd he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _))
  | _, _, _, .sub_coimg hs₀ hs₁ he, _, hsm =>
      .sub_coimg (svalidBwd hs₀ hsm) (svalidBwd hs₁ hsm)
                 (hasTypeBwd he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _))

/-- **The backward bridge.** `GHasType (tr Δ ε) e τ → HasType Δ ε e τ`, generalized to
    a `TrGe`-related context so the induction goes through. -/
noncomputable def hasTypeBwd : {Γ : GCtx} → {e : Term} → {τ : Ty} → GHasType Γ e τ →
    {Δ : LCtx} → {ε : NLCtx} → TrGe Γ Δ ε → CtxDisj Δ ε → HasType Δ ε e τ
  | _, _, _, .gzero hs, _, _, htr, _ =>
      .zero (svalidBwd hs (typeCtxOmega_submap htr))
  | _, _, _, .gsmul hs hsp hta h₀ h₁, _, _, htr, hcd => by
      obtain ⟨Δ₀, Δ₁, hun, hdis, hcd0, hcd1, htr0, htr1⟩ := splitBackData hsp htr hta hcd
      rw [← hun]
      exact .smul (svalidBwd hs (typeCtxOmega_submap htr)) hdis
        (hasTypeBwd h₀ htr0 hcd0) (hasTypeBwd h₁ htr1 hcd1)
  | _, _, _, .gadd hs h₀ h₁, _, _, htr, hcd =>
      .add (svalidBwd hs (typeCtxOmega_submap htr))
        (hasTypeBwd h₀ htr hcd) (hasTypeBwd h₁ htr hcd)
  | _, _, _, .ginner hs hnl, _, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr; subst hΔ
      exact .inner (svalidBwd hs (typeCtxOmega_submap htr))
  | _, _, _, .greal_lit r hnl, _, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr; subst hΔ
      exact .real_lit r
  | _, _, _, .gapp_linear hs₀ hs₁ hsp hta h₀ h₁, _, _, htr, hcd => by
      obtain ⟨Δ₀, Δ₁, hun, hdis, hcd0, hcd1, htr0, htr1⟩ := splitBackData hsp htr hta hcd
      rw [← hun]
      exact .app_linear (svalidBwd hs₀ (typeCtxOmega_submap htr))
        (svalidBwd hs₁ (typeCtxOmega_submap htr)) hdis
        (hasTypeBwd h₀ htr0 hcd0) (hasTypeBwd h₁ htr1 hcd1)
  | _, _, _, .gapp_inner hs hsp hta h₀ h₁, _, _, htr, hcd => by
      obtain ⟨Δ₀, Δ₁, hun, hdis, hcd0, hcd1, htr0, htr1⟩ := splitBackData hsp htr hta hcd
      rw [← hun]
      exact .app_inner (svalidBwd hs (typeCtxOmega_submap htr)) hdis
        (hasTypeBwd h₀ htr0 hcd0) (hasTypeBwd h₁ htr1 hcd1)
  | _, _, _, .gapp_nonlinear hnl h₀ h₁, _, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr; subst hΔ
      exact .app_nonlinear (hasTypeBwd h₀ htr (CtxDisj.empty _))
        (hasTypeBwd h₁ htr (CtxDisj.empty _))
  | _, _, _, .gvar hx hg hlin, _, _, htr, _ => gvar_shape htr hx hg hlin
  | _, _, _, .gpinv_tensor hs₀ hs₁ hnl he, _, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr; subst hΔ
      exact .pinv_tensor (svalidBwd hs₀ (typeCtxOmega_submap htr))
        (svalidBwd hs₁ (typeCtxOmega_submap htr)) (hasTypeBwd he htr (CtxDisj.empty _))
  | _, _, _, .gpinv_dual hs hnl he, _, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr; subst hΔ
      exact .pinv_dual (svalidBwd hs (typeCtxOmega_submap htr))
        (hasTypeBwd he htr (CtxDisj.empty _))
  | _, _, _, .gdsumE hs₀ hs₁ h₀ h₁, _, _, htr, hcd =>
      .dsumE (svalidBwd hs₀ (typeCtxOmega_submap htr))
        (svalidBwd hs₁ (typeCtxOmega_submap htr))
        (hasTypeBwd h₀ htr hcd) (hasTypeBwd h₁ htr hcd)
  | _, _, _, .gtprodE hs₀ hs₁ hsp hta h₀ h₁, _, _, htr, hcd => by
      obtain ⟨Δ₀, Δ₁, hun, hdis, hcd0, hcd1, htr0, htr1⟩ := splitBackData hsp htr hta hcd
      rw [← hun]
      exact .tprodE (svalidBwd hs₀ (typeCtxOmega_submap htr))
        (svalidBwd hs₁ (typeCtxOmega_submap htr)) hdis
        (hasTypeBwd h₀ htr0 hcd0) (hasTypeBwd h₁ htr1 hcd1)
  | _, _, _, .gllam_real L hs hbody, _, ε, htr, hcd =>
      .llam_real (L ∪ ε.keys) (svalidBwd hs (typeCtxOmega_submap htr))
        (fun y hy => by
          simp only [Finset.mem_union, not_or] at hy
          have hyε : y ∉ ε := fun h => hy.2 (Finmap.mem_keys.mpr h)
          exact hasTypeBwd (hbody y hy.1) (TrGe.insert_lin htr y _) (CtxDisj.insert' hcd hyε))
  | _, _, _, .gllam_tensor L hne hs₀ hs hbody, _, ε, htr, hcd =>
      .llam_tensor (L ∪ ε.keys) hne (svalidBwd hs₀ (typeCtxOmega_submap htr))
        (svalidBwd hs (typeCtxOmega_submap htr))
        (fun y hy => by
          simp only [Finset.mem_union, not_or] at hy
          have hyε : y ∉ ε := fun h => hy.2 (Finmap.mem_keys.mpr h)
          exact hasTypeBwd (hbody y hy.1) (TrGe.insert_lin htr y _) (CtxDisj.insert' hcd hyε))
  | _, _, _, .gembed hsub hnl, _, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr; subst hΔ
      exact .embed (subtypeBwd hsub (typeCtxOmega_submap htr))
  | _, _, _, .gnllam L htv hnl hbody, _, ε, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr; subst hΔ
      exact .nllam (L ∪ ε.keys) (tvalidBwd htv (typeCtxOmega_submap htr))
        (fun y hy => by
          simp only [Finset.mem_union, not_or] at hy
          exact hasTypeBwd (hbody y hy.1) (TrGe.insert_omega htr y _) (CtxDisj.empty _))

end

/-! ## The backward bridge is hereditarily promotion-free -/

mutual

/-- `svalidBwd` introduces no promotion in an FFS term witness. -/
noncomputable def svalidBwd_promotionFree : {f : Name → Option Ty} → {s : Space} →
    (h : GSValid f s) → {ε : NLCtx} → (hsm : SubMap f (asTypeCtx ε)) →
    SPromotionFree (svalidBwd h hsm)
  | _, _, .empty, _, _ => True.intro
  | _, _, .real, _, _ => True.intro
  | _, _, .dual hs, _, hsm => svalidBwd_promotionFree hs hsm
  | _, _, .dsum hs₀ hs₁, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm⟩
  | _, _, .tprod hs₀ hs₁, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm⟩
  | _, _, .ker hs₀ hs₁ he, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm,
        hasTypeBwd_promotionFree he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _)⟩
  | _, _, .coker hs₀ hs₁ he, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm,
        hasTypeBwd_promotionFree he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _)⟩
  | _, _, .img hs₀ hs₁ he, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm,
        hasTypeBwd_promotionFree he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _)⟩
  | _, _, .coimg hs₀ hs₁ he, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm,
        hasTypeBwd_promotionFree he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _)⟩

/-- `tvalidBwd` introduces no promotion in any nested FFS term witness. -/
noncomputable def tvalidBwd_promotionFree : {f : Name → Option Ty} → {τ : Ty} →
    {k : Kind} → (h : GTValid f τ k) → {ε : NLCtx} →
    (hsm : SubMap f (asTypeCtx ε)) → TPromotionFree (tvalidBwd h hsm)
  | _, _, _, .space hs, _, hsm => svalidBwd_promotionFree hs hsm
  | _, _, _, .piTy L h₀ hbody, ε, hsm =>
      ⟨tvalidBwd_promotionFree h₀ hsm, fun y hy => by
        simp only [Finset.mem_union, not_or] at hy
        exact tvalidBwd_promotionFree (hbody y hy.1)
          (by rw [asTypeCtx_insert]; exact submap_update hsm y (some _))⟩

/-- `subtypeBwd` introduces no promotion in its FFS term witness. -/
noncomputable def subtypeBwd_promotionFree : {f : Name → Option Ty} →
    {s₀ s₁ : Space} → (h : GSubType f s₀ s₁) → {ε : NLCtx} →
    (hsm : SubMap f (asTypeCtx ε)) → SubPromotionFree (subtypeBwd h hsm)
  | _, _, _, .sub_ker hs₀ hs₁ he, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm,
        hasTypeBwd_promotionFree he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _)⟩
  | _, _, _, .sub_coker hs₀ hs₁ he, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm,
        hasTypeBwd_promotionFree he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _)⟩
  | _, _, _, .sub_img hs₀ hs₁ he, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm,
        hasTypeBwd_promotionFree he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _)⟩
  | _, _, _, .sub_coimg hs₀ hs₁ he, _, hsm =>
      ⟨svalidBwd_promotionFree hs₀ hsm, svalidBwd_promotionFree hs₁ hsm,
        hasTypeBwd_promotionFree he (TrGe.resurrect_of_submap hsm) (CtxDisj.empty _)⟩

/-- The generalized backward bridge reconstructs a complete source derivation
without any `HasType.promote` node. -/
noncomputable def hasTypeBwd_promotionFree : {Γ : GCtx} → {e : Term} → {τ : Ty} →
    (h : GHasType Γ e τ) → {Δ : LCtx} → {ε : NLCtx} →
    (htr : TrGe Γ Δ ε) → (hdisj : CtxDisj Δ ε) →
    PromotionFree (hasTypeBwd h htr hdisj)
  | _, _, _, .gzero hs, _, _, htr, _ =>
      svalidBwd_promotionFree hs (typeCtxOmega_submap htr)
  | _, _, _, .gsmul hs hsp hta h₀ h₁, Δ, ε, htr, hcd => by
      unfold hasTypeBwd
      generalize hsd : splitBackData hsp htr hta hcd = sd
      rcases sd with ⟨Δ₀, Δ₁, hun, _, hcd₀, hcd₁, htr₀, htr₁⟩
      cases hun
      exact ⟨svalidBwd_promotionFree hs (typeCtxOmega_submap htr),
        hasTypeBwd_promotionFree h₀ htr₀ hcd₀,
        hasTypeBwd_promotionFree h₁ htr₁ hcd₁⟩
  | _, _, _, .gadd hs h₀ h₁, _, _, htr, hcd =>
      ⟨svalidBwd_promotionFree hs (typeCtxOmega_submap htr),
        hasTypeBwd_promotionFree h₀ htr hcd, hasTypeBwd_promotionFree h₁ htr hcd⟩
  | _, _, _, .ginner hs hnl, Δ, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr
      subst Δ
      exact svalidBwd_promotionFree hs (typeCtxOmega_submap htr)
  | _, _, _, .greal_lit _ hnl, Δ, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr
      subst Δ
      exact True.intro
  | _, _, _, .gapp_linear hs₀ hs₁ hsp hta h₀ h₁, Δ, ε, htr, hcd => by
      unfold hasTypeBwd
      generalize hsd : splitBackData hsp htr hta hcd = sd
      rcases sd with ⟨Δ₀, Δ₁, hun, _, hcd₀, hcd₁, htr₀, htr₁⟩
      cases hun
      exact ⟨svalidBwd_promotionFree hs₀ (typeCtxOmega_submap htr),
        svalidBwd_promotionFree hs₁ (typeCtxOmega_submap htr),
        hasTypeBwd_promotionFree h₀ htr₀ hcd₀,
        hasTypeBwd_promotionFree h₁ htr₁ hcd₁⟩
  | _, _, _, .gapp_inner hs hsp hta h₀ h₁, Δ, ε, htr, hcd => by
      unfold hasTypeBwd
      generalize hsd : splitBackData hsp htr hta hcd = sd
      rcases sd with ⟨Δ₀, Δ₁, hun, _, hcd₀, hcd₁, htr₀, htr₁⟩
      cases hun
      exact ⟨svalidBwd_promotionFree hs (typeCtxOmega_submap htr),
        hasTypeBwd_promotionFree h₀ htr₀ hcd₀,
        hasTypeBwd_promotionFree h₁ htr₁ hcd₁⟩
  | _, _, _, .gapp_nonlinear hnl h₀ h₁, Δ, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr
      subst Δ
      exact ⟨hasTypeBwd_promotionFree h₀ htr (CtxDisj.empty _),
        hasTypeBwd_promotionFree h₁ htr (CtxDisj.empty _)⟩
  | _, _, _, .gvar hx hg hlin, _, _, htr, _ =>
      gvar_shape_promotionFree htr hx hg hlin
  | _, _, _, .gpinv_tensor hs₀ hs₁ hnl he, Δ, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr
      subst Δ
      exact ⟨svalidBwd_promotionFree hs₀ (typeCtxOmega_submap htr),
        svalidBwd_promotionFree hs₁ (typeCtxOmega_submap htr),
        hasTypeBwd_promotionFree he htr (CtxDisj.empty _)⟩
  | _, _, _, .gpinv_dual hs hnl he, Δ, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr
      subst Δ
      exact ⟨svalidBwd_promotionFree hs (typeCtxOmega_submap htr),
        hasTypeBwd_promotionFree he htr (CtxDisj.empty _)⟩
  | _, _, _, .gdsumE hs₀ hs₁ h₀ h₁, _, _, htr, hcd =>
      ⟨svalidBwd_promotionFree hs₀ (typeCtxOmega_submap htr),
        svalidBwd_promotionFree hs₁ (typeCtxOmega_submap htr),
        hasTypeBwd_promotionFree h₀ htr hcd, hasTypeBwd_promotionFree h₁ htr hcd⟩
  | _, _, _, .gtprodE hs₀ hs₁ hsp hta h₀ h₁, Δ, ε, htr, hcd => by
      unfold hasTypeBwd
      generalize hsd : splitBackData hsp htr hta hcd = sd
      rcases sd with ⟨Δ₀, Δ₁, hun, _, hcd₀, hcd₁, htr₀, htr₁⟩
      cases hun
      exact ⟨svalidBwd_promotionFree hs₀ (typeCtxOmega_submap htr),
        svalidBwd_promotionFree hs₁ (typeCtxOmega_submap htr),
        hasTypeBwd_promotionFree h₀ htr₀ hcd₀,
        hasTypeBwd_promotionFree h₁ htr₁ hcd₁⟩
  | _, _, _, .gllam_real L hs hbody, _, ε, htr, hcd => by
      simp only [hasTypeBwd, PromotionFree]
      refine ⟨svalidBwd_promotionFree hs (typeCtxOmega_submap htr), ?_⟩
      intro y hy
      simp only [Finset.mem_union, not_or] at hy
      exact hasTypeBwd_promotionFree (hbody y hy.1) (TrGe.insert_lin htr y _)
        (CtxDisj.insert' hcd (fun h => hy.2 (Finmap.mem_keys.mpr h)))
  | _, _, _, .gllam_tensor L hne hs₀ hs hbody, _, ε, htr, hcd => by
      simp only [hasTypeBwd, PromotionFree]
      refine ⟨svalidBwd_promotionFree hs₀ (typeCtxOmega_submap htr),
        svalidBwd_promotionFree hs (typeCtxOmega_submap htr), ?_⟩
      intro y hy
      simp only [Finset.mem_union, not_or] at hy
      exact hasTypeBwd_promotionFree (hbody y hy.1) (TrGe.insert_lin htr y _)
        (CtxDisj.insert' hcd (fun h => hy.2 (Finmap.mem_keys.mpr h)))
  | _, _, _, .gembed hsub hnl, Δ, _, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr
      subst Δ
      exact subtypeBwd_promotionFree hsub (typeCtxOmega_submap htr)
  | _, _, _, .gnllam L htv hnl hbody, Δ, ε, htr, _ => by
      have hΔ := noLin_trge_empty hnl htr
      subst Δ
      refine ⟨tvalidBwd_promotionFree htv (typeCtxOmega_submap htr), ?_⟩
      intro y hy
      simp only [Finset.mem_union, not_or] at hy
      exact hasTypeBwd_promotionFree (hbody y hy.1) (TrGe.insert_omega htr y _)
        (CtxDisj.empty _)

end

/-! ## The public backward bridge + the packaged equivalence. -/

noncomputable def hasTypeBridgeBwd {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (hcd : CtxDisj Δ ε) (h : GHasType (tr Δ ε) e τ) : HasType Δ ε e τ :=
  hasTypeBwd h (TrGe.refl_tr Δ ε) hcd

/-- The public backward bridge reconstructs a source derivation with no
`HasType.promote` node anywhere in its mutual derivation tree. -/
theorem hasTypeBridgeBwd_promotionFree
    {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (hcd : CtxDisj Δ ε) (h : GHasType (tr Δ ε) e τ) :
    PromotionFree (hasTypeBridgeBwd hcd h) :=
  hasTypeBwd_promotionFree h (TrGe.refl_tr Δ ε) hcd

theorem hasTypeEquiv {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (hcd : CtxDisj Δ ε) : Nonempty (GHasType (tr Δ ε) e τ) ↔ Nonempty (HasType Δ ε e τ) :=
  ⟨fun ⟨h⟩ => ⟨hasTypeBridgeBwd hcd h⟩, fun ⟨h⟩ => ⟨hasTypeBridge hcd h⟩⟩

end GLang.Graded
