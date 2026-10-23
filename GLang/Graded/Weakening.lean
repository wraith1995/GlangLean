import GLang.Graded.Typing

namespace GLang.Graded

open GLang

/-! ## The pointwise / whole-context weakening relation `GWk`. -/

/-- Pointwise graded weakening: `none → none`; add an unused NON-linear var
    (`none → some (g', _)` with `g' ≠ 1`); grade-weaken an existing var
    (`some (g,τ) → some (g',τ)`); never drop (`some → none` forbidden). -/
def WkPt (a a' : Option (GGrade × Ty)) : Prop :=
  match a, a' with
  | none, none => True
  | none, some (g', _) => g' ≠ GGrade.one
  | some (g, τ), some (g', τ') => τ = τ' ∧ GGrade.Wk g g'
  | some _, none => False

/-- Whole-context graded weakening. Like `GCtx.Wk` but may ADD an unused
    non-linear variable (needed for the FFS cross-link; see the header note). -/
def GWk (Γ Γ' : GCtx) : Prop := ∀ x, WkPt (Γ x) (Γ' x)

/-- `GCtx.Wk` (no new vars) is a special case of `GWk`. -/
theorem GWk.of_wk {Γ Γ' : GCtx} (h : GCtx.Wk Γ Γ') : GWk Γ Γ' := by
  intro x
  cases hΓ : Γ x with
  | none =>
    cases hΓ' : Γ' x with
    | none => trivial
    | some p => have hx := h x; rw [hΓ, hΓ'] at hx; exact hx.elim
  | some p =>
    obtain ⟨g, τ⟩ := p
    cases hΓ' : Γ' x with
    | none => have hx := h x; rw [hΓ, hΓ'] at hx; exact hx.elim
    | some q =>
      obtain ⟨g', τ'⟩ := q
      have hx := h x; rw [hΓ, hΓ'] at hx
      exact hx

/-! ## Small helpers on the type-context and `resurrect`. -/

/-- `typeCtxOmega` inverts `resurrect` (grade-0 vars are type-visible). -/
theorem typeCtxOmega_resurrect (f : Name → Option Ty) :
    typeCtxOmega (resurrect f) = f := by
  funext x
  simp only [typeCtxOmega, resurrect]
  cases f x <;> rfl

/-- `SubMap` lifts through `Function.update` with a fixed value. -/
theorem submap_update {f f' : Name → Option Ty} (h : SubMap f f')
    (y : Name) (v : Option Ty) :
    SubMap (Function.update f y v) (Function.update f' y v) := by
  intro x τ hx
  rcases eq_or_ne x y with rfl | hxy
  · rw [Function.update_self] at hx ⊢; exact hx
  · rw [Function.update_of_ne hxy] at hx ⊢; exact h x τ hx

/-- `GWk` lifts through `Function.update` with a fixed value (fresh var ↦ itself). -/
theorem gwk_update {Γ Γ' : GCtx} (h : GWk Γ Γ') (y : Name) (v : Option (GGrade × Ty)) :
    GWk (Function.update Γ y v) (Function.update Γ' y v) := by
  intro x
  rcases eq_or_ne x y with rfl | hxy
  · rw [Function.update_self, Function.update_self]
    cases v with
    | none => trivial
    | some p => obtain ⟨g, τ⟩ := p; exact ⟨rfl, GGrade.Wk.refl _⟩
  · rw [Function.update_of_ne hxy, Function.update_of_ne hxy]; exact h x

/-- A `1 → ω` bump makes a linear var newly type-visible: the ω-only type view
    only GROWS under `GWk`. -/
theorem typeCtxOmega_mono_gwk {Γ Γ' : GCtx} (hw : GWk Γ Γ') :
    SubMap (typeCtxOmega Γ) (typeCtxOmega Γ') := by
  intro x τ hx
  have hwx := hw x
  simp only [typeCtxOmega] at hx ⊢
  cases hΓ : Γ x with
  | none => rw [hΓ] at hx; simp at hx
  | some p =>
    obtain ⟨g, τg⟩ := p
    rw [hΓ] at hx hwx
    cases hΓ' : Γ' x with
    | none => rw [hΓ'] at hwx; exact hwx.elim
    | some q =>
      obtain ⟨g', τ'⟩ := q
      rw [hΓ'] at hwx
      simp only [WkPt] at hwx
      obtain ⟨hτ, hwk⟩ := hwx
      subst hτ
      cases g with
      | one => simp at hx
      | zero =>
        rcases hwk with rfl | ⟨h1, _⟩
        · exact hx
        · exact absurd h1 (by decide)
      | omega =>
        rcases hwk with rfl | ⟨h1, _⟩
        · exact hx
        · exact absurd h1 (by decide)

/-- `resurrect` is monotone: `SubMap → GWk` (added vars land at grade `ω ≠ 1`). -/
theorem resurrect_mono {f f' : Name → Option Ty} (h : SubMap f f') :
    GWk (resurrect f) (resurrect f') := by
  intro x
  cases hf : f x with
  | none =>
    cases hf' : f' x with
    | none => simp [WkPt, resurrect, hf, hf']
    | some τ' =>
      show WkPt (resurrect f x) (resurrect f' x)
      rw [resurrect, resurrect, hf, hf']
      exact (by decide : GGrade.omega ≠ GGrade.one)
  | some τ =>
    have hff := h x τ hf
    show WkPt (resurrect f x) (resurrect f' x)
    rw [resurrect, resurrect, hf, hff]
    exact ⟨rfl, GGrade.Wk.refl _⟩

/-! ## The `+`-monotone split.

Given `Γ = Γ₀ + Γ₁` (pointwise `gadd`) and `GWk Γ Γ'`, distribute the weakening:
`Γ' = Γ₀' + Γ₁'` with `GWk Γ₀ Γ₀'`, `GWk Γ₁ Γ₁'`. A grade-`1` sum forces exactly
one summand present, so a `1 → ω` bump lands on that side; an added var goes left.
-/

/-- The grade a `1 → ω` bump assigns to the LEFT summand of `add g₀ g₁ ⊑ G'`. -/
def bumpL (g₀ g₁ G' : GGrade) : GGrade :=
  if G' = GGrade.add g₀ g₁ then g₀ else if g₀ = GGrade.one then GGrade.omega else g₀

/-- The grade a `1 → ω` bump assigns to the RIGHT summand of `add g₀ g₁ ⊑ G'`. -/
def bumpR (g₀ g₁ G' : GGrade) : GGrade :=
  if G' = GGrade.add g₀ g₁ then g₁ else if g₀ = GGrade.one then g₁ else GGrade.omega

/-- The bump is a valid split: it reproduces `G'` and weakens each summand. -/
theorem bump_spec {g₀ g₁ G' : GGrade} (hw : GGrade.Wk (GGrade.add g₀ g₁) G') :
    GGrade.add (bumpL g₀ g₁ G') (bumpR g₀ g₁ G') = G'
    ∧ GGrade.Wk g₀ (bumpL g₀ g₁ G') ∧ GGrade.Wk g₁ (bumpR g₀ g₁ G') := by
  rcases hw with rfl | ⟨hsum, rfl⟩
  · simp only [bumpL, bumpR]
    exact ⟨rfl, GGrade.Wk.refl _, GGrade.Wk.refl _⟩
  · have hne : GGrade.omega ≠ GGrade.add g₀ g₁ := by rw [hsum]; decide
    simp only [bumpL, bumpR, if_neg hne]
    cases g₀ <;> cases g₁ <;> simp_all [GGrade.add, GGrade.Wk]

/-- Left summand of the weakened split (pointwise, on `Option` values). -/
def wkSplitL' (a b c : Option (GGrade × Ty)) : Option (GGrade × Ty) :=
  match a, b, c with
  | _, none, _ => c
  | none, some _, _ => none
  | some (g₀, τ₀), some (g₁, _), some (G', _) => some (bumpL g₀ g₁ G', τ₀)
  | some (_, τ₀), some _, none => some (GGrade.one, τ₀)  -- unreachable

/-- Right summand of the weakened split (pointwise, on `Option` values). -/
def wkSplitR' (a b c : Option (GGrade × Ty)) : Option (GGrade × Ty) :=
  match a, b, c with
  | _, none, _ => none
  | none, some _, _ => c
  | some (g₀, _), some (g₁, τ₁), some (G', _) => some (bumpR g₀ g₁ G', τ₁)
  | some _, some (_, τ₁), none => some (GGrade.one, τ₁)  -- unreachable

/-- Pointwise correctness of the weakened split. -/
theorem wkSplit_point (a b c : Option (GGrade × Ty)) (hw : WkPt (gadd a b) c) :
    c = gadd (wkSplitL' a b c) (wkSplitR' a b c)
    ∧ WkPt a (wkSplitL' a b c) ∧ WkPt b (wkSplitR' a b c) := by
  rcases a with _ | ⟨g₀, τ₀⟩ <;> rcases b with _ | ⟨g₁, τ₁⟩ <;> rcases c with _ | ⟨G', τc⟩
  · exact ⟨rfl, trivial, trivial⟩
  · exact ⟨rfl, hw, trivial⟩
  · exact hw.elim
  · exact ⟨rfl, trivial, hw⟩
  · exact hw.elim
  · exact ⟨rfl, hw, trivial⟩
  · exact hw.elim
  · obtain ⟨hτ, hwk⟩ := hw
    obtain ⟨hadd, hL, hR⟩ := bump_spec hwk
    refine ⟨?_, ?_, ?_⟩
    · show some (G', τc) = some (GGrade.add (bumpL g₀ g₁ G') (bumpR g₀ g₁ G'), τ₀)
      rw [hadd, hτ]
    · show WkPt (some (g₀, τ₀)) (some (bumpL g₀ g₁ G', τ₀))
      exact ⟨rfl, hL⟩
    · show WkPt (some (g₁, τ₁)) (some (bumpR g₀ g₁ G', τ₁))
      exact ⟨rfl, hR⟩

/-- Left context of the weakened split. -/
def wkSplitL (Γ₀ Γ₁ Γ' : GCtx) : GCtx := fun x => wkSplitL' (Γ₀ x) (Γ₁ x) (Γ' x)

/-- Right context of the weakened split. -/
def wkSplitR (Γ₀ Γ₁ Γ' : GCtx) : GCtx := fun x => wkSplitR' (Γ₀ x) (Γ₁ x) (Γ' x)

/-- The `+`-monotone split: distribute `GWk Γ Γ'` across `Γ = Γ₀ + Γ₁`. -/
theorem wkSplit_spec {Γ Γ₀ Γ₁ Γ' : GCtx}
    (hsplit : ∀ x, Γ x = gadd (Γ₀ x) (Γ₁ x)) (hw : GWk Γ Γ') :
    (∀ x, Γ' x = gadd (wkSplitL Γ₀ Γ₁ Γ' x) (wkSplitR Γ₀ Γ₁ Γ' x))
    ∧ GWk Γ₀ (wkSplitL Γ₀ Γ₁ Γ') ∧ GWk Γ₁ (wkSplitR Γ₀ Γ₁ Γ') := by
  have key : ∀ x, WkPt (gadd (Γ₀ x) (Γ₁ x)) (Γ' x) := by
    intro x; rw [← hsplit x]; exact hw x
  refine ⟨fun x => ?_, fun x => ?_, fun x => ?_⟩
  · exact (wkSplit_point (Γ₀ x) (Γ₁ x) (Γ' x) (key x)).1
  · exact (wkSplit_point (Γ₀ x) (Γ₁ x) (Γ' x) (key x)).2.1
  · exact (wkSplit_point (Γ₀ x) (Γ₁ x) (Γ' x) (key x)).2.2

/-- **`TypeAgree` survives the weakened split.** `wkSplitL`/`wkSplitR` only ever
    bump GRADES (`bumpL`/`bumpR`) — the TYPE at each present position is copied
    verbatim from `Γ₀`/`Γ₁`. So a var present in BOTH split-images is present in both
    `Γ₀` and `Γ₁` at the same types, and `TypeAgree Γ₀ Γ₁` pins them equal. Holds
    unconditionally in `Γ'` (weakening preserves types). -/
theorem wkSplit_typeagree {Γ₀ Γ₁ Γ' : GCtx} (hta : TypeAgree Γ₀ Γ₁) :
    TypeAgree (wkSplitL Γ₀ Γ₁ Γ') (wkSplitR Γ₀ Γ₁ Γ') := by
  intro x g₀ τ₀ g₁ τ₁ hL hR
  have hLx : wkSplitL' (Γ₀ x) (Γ₁ x) (Γ' x) = some (g₀, τ₀) := hL
  have hRx : wkSplitR' (Γ₀ x) (Γ₁ x) (Γ' x) = some (g₁, τ₁) := hR
  rcases ha : Γ₀ x with _ | ⟨ga, τa⟩ <;> rcases hb : Γ₁ x with _ | ⟨gb, τb⟩ <;>
    rcases hc : Γ' x with _ | ⟨gc, τc⟩ <;>
    rw [ha, hb, hc] at hLx hRx <;>
    simp only [wkSplitL', wkSplitR', reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hLx hRx
  -- Only the `some/some/·` cases survive; there `τa = τ₀`, `τb = τ₁`, and `TypeAgree` pins `τa = τb`.
  all_goals
    (obtain ⟨-, hτa⟩ := hLx; obtain ⟨-, hτb⟩ := hRx; rw [← hτa, ← hτb]; exact hta x ga τa gb τb ha hb)

/-! ## The `gvar` arm (affine-leaf preservation). -/

/-- `GWk` never creates a fresh linear (`1`) variable, so the affine-leaf side
    condition of `gvar` survives weakening. -/
theorem affine_leaf_gwk {Γ Γ' : GCtx} (hw : GWk Γ Γ') {x : Name}
    (hc : ∀ y, y ≠ x → ∀ τy, Γ y ≠ some (GGrade.one, τy)) :
    ∀ y, y ≠ x → ∀ τy, Γ' y ≠ some (GGrade.one, τy) := by
  intro y hy τy hcontra
  have hwy := hw y
  rw [hcontra] at hwy
  cases hΓ : Γ y with
  | none => rw [hΓ] at hwy; simp only [WkPt] at hwy; exact hwy rfl
  | some p =>
    obtain ⟨g, τ⟩ := p
    rw [hΓ] at hwy
    simp only [WkPt] at hwy
    obtain ⟨hτ, hwk⟩ := hwy
    subst hτ
    have hg1 : g = GGrade.one := by rcases hwk with h | ⟨h, _⟩ <;> exact h
    subst hg1
    exact hc y hy τ hΓ

/-- **`NoLin` is preserved by weakening.** A `1 → ω` bump (or keeping a grade)
    never CREATES a fresh grade-`1`, so the affine-leaf premise of the `∅`-Δ leaf
    rules survives `GWk`. (This is `affine_leaf_gwk` without the `y ≠ x` exclusion.) -/
theorem NoLin.wk {Γ Γ' : GCtx} (hw : GWk Γ Γ') (h : NoLin Γ) : NoLin Γ' := by
  intro y τy hcontra
  have hwy := hw y
  rw [hcontra] at hwy
  cases hΓ : Γ y with
  | none => rw [hΓ] at hwy; simp only [WkPt] at hwy; exact hwy rfl
  | some p =>
    obtain ⟨g, τ⟩ := p
    rw [hΓ] at hwy
    simp only [WkPt] at hwy
    obtain ⟨hτ, hwk⟩ := hwy
    subst hτ
    have hg1 : g = GGrade.one := by rcases hwk with h | ⟨h, _⟩ <;> exact h
    subst hg1
    exact h y τ hΓ

/-- Reconstruct `gvar` at the weakened context (type preserved; grade may bump).
    The affine-leaf discipline AND the standard-QTT `g ≠ 0` premise both survive:
    a `GGrade.Wk` step (`1 → ω` or keep) never lowers a nonzero grade to `0`. -/
def gvar_wk {Γ Γ' : GCtx} {x : Name} {g : GGrade} {τ : Ty}
    (hx : Γ x = some (g, τ))
    (hg : g ≠ GGrade.zero)
    (hlin : ∀ y, y ≠ x → ∀ τy, Γ y ≠ some (GGrade.one, τy))
    (hw : GWk Γ Γ') : GHasType Γ' (.var x) τ := by
  have hwx := hw x
  rw [hx] at hwx
  cases hΓ' : Γ' x with
  | none => rw [hΓ'] at hwx; exact hwx.elim
  | some p =>
    obtain ⟨g', τ'⟩ := p
    rw [hΓ'] at hwx
    simp only [WkPt] at hwx
    obtain ⟨hτ, hwk⟩ := hwx
    subst hτ
    have hg' : g' ≠ GGrade.zero := by
      rcases hwk with rfl | ⟨rfl, rfl⟩
      · exact hg
      · decide
    exact GHasType.gvar hΓ' hg' (affine_leaf_gwk hw hlin)

/-! ## The core 4-way mutual weakening. -/

mutual

/-- Weakening for `GSValid` under `SubMap`. -/
def gsvalid_wk : {f : Name → Option Ty} → {s : Space} → GSValid f s →
    {f' : Name → Option Ty} → SubMap f f' → GSValid f' s
  | _, _, .empty, _, _ => .empty
  | _, _, .real, _, _ => .real
  | _, _, .dual d, _, hsub => .dual (gsvalid_wk d hsub)
  | _, _, .dsum d₀ d₁, _, hsub => .dsum (gsvalid_wk d₀ hsub) (gsvalid_wk d₁ hsub)
  | _, _, .tprod d₀ d₁, _, hsub => .tprod (gsvalid_wk d₀ hsub) (gsvalid_wk d₁ hsub)
  | _, _, .ker hs₀ hs₁ he, _, hsub =>
      .ker (gsvalid_wk hs₀ hsub) (gsvalid_wk hs₁ hsub)
           (gradeWeaken he (resurrect_mono hsub))
  | _, _, .coker hs₀ hs₁ he, _, hsub =>
      .coker (gsvalid_wk hs₀ hsub) (gsvalid_wk hs₁ hsub)
             (gradeWeaken he (resurrect_mono hsub))
  | _, _, .img hs₀ hs₁ he, _, hsub =>
      .img (gsvalid_wk hs₀ hsub) (gsvalid_wk hs₁ hsub)
           (gradeWeaken he (resurrect_mono hsub))
  | _, _, .coimg hs₀ hs₁ he, _, hsub =>
      .coimg (gsvalid_wk hs₀ hsub) (gsvalid_wk hs₁ hsub)
             (gradeWeaken he (resurrect_mono hsub))

/-- Weakening for `GTValid` under `SubMap`. -/
def gtvalid_wk : {f : Name → Option Ty} → {τ : Ty} → {k : Kind} → GTValid f τ k →
    {f' : Name → Option Ty} → SubMap f f' → GTValid f' τ k
  | _, _, _, .space hs, _, hsub => .space (gsvalid_wk hs hsub)
  | _, _, _, .piTy L hτ₀ hbody, _, hsub =>
      .piTy L (gtvalid_wk hτ₀ hsub)
        (fun y hy => gtvalid_wk (hbody y hy) (submap_update hsub y _))

/-- Weakening for `GSubType` under `SubMap`. -/
def gsubtype_wk : {f : Name → Option Ty} → {s₀ s₁ : Space} → GSubType f s₀ s₁ →
    {f' : Name → Option Ty} → SubMap f f' → GSubType f' s₀ s₁
  | _, _, _, .sub_ker hs₀ hs₁ he, _, hsub =>
      .sub_ker (gsvalid_wk hs₀ hsub) (gsvalid_wk hs₁ hsub)
               (gradeWeaken he (resurrect_mono hsub))
  | _, _, _, .sub_coker hs₀ hs₁ he, _, hsub =>
      .sub_coker (gsvalid_wk hs₀ hsub) (gsvalid_wk hs₁ hsub)
                 (gradeWeaken he (resurrect_mono hsub))
  | _, _, _, .sub_img hs₀ hs₁ he, _, hsub =>
      .sub_img (gsvalid_wk hs₀ hsub) (gsvalid_wk hs₁ hsub)
               (gradeWeaken he (resurrect_mono hsub))
  | _, _, _, .sub_coimg hs₀ hs₁ he, _, hsub =>
      .sub_coimg (gsvalid_wk hs₀ hsub) (gsvalid_wk hs₁ hsub)
                 (gradeWeaken he (resurrect_mono hsub))

/-- **Promote is admissible grade-weakening.** `GHasType` weakens under `GWk`. -/
def gradeWeaken : {Γ : GCtx} → {e : Term} → {τ : Ty} → GHasType Γ e τ →
    {Γ' : GCtx} → GWk Γ Γ' → GHasType Γ' e τ
  | _, _, _, .gzero hs, _, hw => .gzero (gsvalid_wk hs (typeCtxOmega_mono_gwk hw))
  | _, _, _, .gsmul hs hsp hta h₀ h₁, _, hw =>
      let sp := wkSplit_spec hsp hw
      .gsmul (gsvalid_wk hs (typeCtxOmega_mono_gwk hw)) sp.1 (wkSplit_typeagree hta)
             (gradeWeaken h₀ sp.2.1) (gradeWeaken h₁ sp.2.2)
  | _, _, _, .gadd hs h₀ h₁, _, hw =>
      .gadd (gsvalid_wk hs (typeCtxOmega_mono_gwk hw))
            (gradeWeaken h₀ hw) (gradeWeaken h₁ hw)
  | _, _, _, .ginner hs hnl, _, hw =>
      .ginner (gsvalid_wk hs (typeCtxOmega_mono_gwk hw)) (NoLin.wk hw hnl)
  | _, _, _, .greal_lit r hnl, _, hw => .greal_lit r (NoLin.wk hw hnl)
  | _, _, _, .gapp_linear hs₀ hs₁ hsp hta h₀ h₁, _, hw =>
      let sp := wkSplit_spec hsp hw
      .gapp_linear (gsvalid_wk hs₀ (typeCtxOmega_mono_gwk hw))
                   (gsvalid_wk hs₁ (typeCtxOmega_mono_gwk hw)) sp.1 (wkSplit_typeagree hta)
                   (gradeWeaken h₀ sp.2.1) (gradeWeaken h₁ sp.2.2)
  | _, _, _, .gapp_inner hs hsp hta h₀ h₁, _, hw =>
      let sp := wkSplit_spec hsp hw
      .gapp_inner (gsvalid_wk hs (typeCtxOmega_mono_gwk hw)) sp.1 (wkSplit_typeagree hta)
                  (gradeWeaken h₀ sp.2.1) (gradeWeaken h₁ sp.2.2)
  | _, _, _, .gapp_nonlinear hnl h₀ h₁, _, hw =>
      .gapp_nonlinear (NoLin.wk hw hnl) (gradeWeaken h₀ hw) (gradeWeaken h₁ hw)
  | _, _, _, .gvar hx hg hlin, _, hw => gvar_wk hx hg hlin hw
  | _, _, _, .gpinv_tensor hs₀ hs₁ hnl he, _, hw =>
      .gpinv_tensor (gsvalid_wk hs₀ (typeCtxOmega_mono_gwk hw))
                    (gsvalid_wk hs₁ (typeCtxOmega_mono_gwk hw)) (NoLin.wk hw hnl)
                    (gradeWeaken he hw)
  | _, _, _, .gpinv_dual hs hnl he, _, hw =>
      .gpinv_dual (gsvalid_wk hs (typeCtxOmega_mono_gwk hw)) (NoLin.wk hw hnl)
                  (gradeWeaken he hw)
  | _, _, _, .gdsumE hs₀ hs₁ h₀ h₁, _, hw =>
      .gdsumE (gsvalid_wk hs₀ (typeCtxOmega_mono_gwk hw))
              (gsvalid_wk hs₁ (typeCtxOmega_mono_gwk hw))
              (gradeWeaken h₀ hw) (gradeWeaken h₁ hw)
  | _, _, _, .gtprodE hs₀ hs₁ hsp hta h₀ h₁, _, hw =>
      let sp := wkSplit_spec hsp hw
      .gtprodE (gsvalid_wk hs₀ (typeCtxOmega_mono_gwk hw))
               (gsvalid_wk hs₁ (typeCtxOmega_mono_gwk hw)) sp.1 (wkSplit_typeagree hta)
               (gradeWeaken h₀ sp.2.1) (gradeWeaken h₁ sp.2.2)
  | _, _, _, .gllam_real L hs hbody, _, hw =>
      .gllam_real L (gsvalid_wk hs (typeCtxOmega_mono_gwk hw))
        (fun y hy => gradeWeaken (hbody y hy) (gwk_update hw y _))
  | _, _, _, .gllam_tensor L hne hs₀ hs hbody, _, hw =>
      .gllam_tensor L hne (gsvalid_wk hs₀ (typeCtxOmega_mono_gwk hw))
        (gsvalid_wk hs (typeCtxOmega_mono_gwk hw))
        (fun y hy => gradeWeaken (hbody y hy) (gwk_update hw y _))
  | _, _, _, .gembed hsub hnl, _, hw =>
      .gembed (gsubtype_wk hsub (typeCtxOmega_mono_gwk hw)) (NoLin.wk hw hnl)
  | _, _, _, .gnllam L htv hnl hbody, _, hw =>
      .gnllam L (gtvalid_wk htv (typeCtxOmega_mono_gwk hw)) (NoLin.wk hw hnl)
        (fun y hy => gradeWeaken (hbody y hy) (gwk_update hw y _))

end

/-! ## The payoff: `promote` admissible. -/

/-- **`promote` is admissible grade-weakening.** Moving `lin` from linear to
    nonlinear (`1 → ω`) is exactly a `GWk`; the FFS type-formation obligations
    transport by the ω-only monotone weakening. No `PromoteFresh`, no transport
    lemma. -/
def promote_admissible {lin Δ : LCtx} {ε' : NLCtx} {e : Term} {τ : Ty}
    (hdisjΔ : Finmap.Disjoint lin Δ)
    (h : GHasType (tr (lin ∪ Δ) ε') e τ) :
    GHasType (tr Δ (lin.toNL ∪ ε')) e τ :=
  gradeWeaken h (GWk.of_wk (tr_promote_wk lin Δ ε' hdisjΔ))

end GLang.Graded
