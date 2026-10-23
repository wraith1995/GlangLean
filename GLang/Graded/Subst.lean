import GLang.Graded.Weakening
import GLang.Graded.BridgeFwd

namespace GLang.Graded

open GLang

/-! ## The substituted contexts. -/

/-- Rewrite the type at each `Option (GGrade × Ty)` entry by `Ty.subst y e₁`
    (grade untouched). -/
@[reducible] def mapSubstTy (y : Name) (e₁ : Term) :
    Option (GGrade × Ty) → Option (GGrade × Ty) :=
  Option.map (fun p => (p.1, Ty.subst y e₁ p.2))

/-- The result context of GHasType substitution: drop `y`, merge the ambient
    `Nε := tr ∅ ε` (all-`ω`, idempotent, disjoint from linear names), rewrite types. -/
def gsubstCtx (y : Name) (e₁ : Term) (ε : NLCtx) (Γ : GCtx) : GCtx :=
  fun z => if z = y then none
           else mapSubstTy y e₁ (gadd (Γ z) (tr (∅ : LCtx) ε z))

/-- The result context of TYPE-FORMATION substitution (`GSValid`/`GTValid`/
    `GSubType` live over a grade-free type-context): drop `y`, RESTORE the ambient
    `ε` (via `orElse`), rewrite types. The `ε`-restore mirrors `gsubstCtx`'s
    `Nε`-merge, so the resurrection bridge holds UNCONDITIONALLY. -/
def tsubstCtx (y : Name) (e₁ : Term) (ε : NLCtx) (f : Name → Option Ty) : Name → Option Ty :=
  fun z => if z = y then none
           else (Option.orElse (f z) (fun _ => ε.lookup z)).map (Ty.subst y e₁)

/-- Ambient TYPE-consistency (graded side): wherever both `ε` and `Γ` bind `z`, the
    types agree. Survives splits (via `TypeAgree`) and binders (fresh var ∉ ε); lets
    `gadd` (keeps the LEFT type) agree with `argTyped`'s `ε`-types at `var y` leaves. -/
def NEAgree (ε : NLCtx) (Γ : GCtx) : Prop :=
  ∀ z τ, ε.lookup z = some τ → ∀ g τ', Γ z = some (g, τ') → τ = τ'

/-- Ambient TYPE-consistency (type-formation side): `f` agrees with `ε` on shared
    vars. Weaker than presence; all that the resurrection witness recursion needs. -/
def TNEAgree (ε : NLCtx) (f : Name → Option Ty) : Prop :=
  ∀ z τ, ε.lookup z = some τ → ∀ τ', f z = some τ' → τ = τ'

/-! ## The threaded substitution data. -/

/-- Constant data for the substitution recursion (a `Type`: carries a `GHasType`). -/
structure GSubstData (y : Name) (e₁ : Term) (ε : NLCtx) (τ₀ : Ty) : Type where
  /-- `e₁` locally closed — drives `subst_openRec` in the binder arms. -/
  lc       : Term.lc e₁
  /-- The argument typing (weakened at each `var y` leaf). -/
  argTyped : GHasType (tr (∅ : LCtx) ε) e₁ τ₀
  /-- A variable does not occur in its own type. -/
  yfvτ0    : y ∉ Ty.fv τ₀
  /-- `y` is the freshly-substituted var, not an ambient one (`Nε y = none`). -/
  ynε      : ε.lookup y = none
  /-- The ambient `ε`-types are `y`-fresh (so `subst y e₁` is the identity on them). -/
  εfresh   : ∀ z τ, ε.lookup z = some τ → y ∉ Ty.fv τ

/-! ## Pure `Option`/context algebra of `gsubstCtx`. -/

/-- `mapSubstTy` distributes over `gadd` (it only rewrites the type, and `gadd`
    keeps the LEFT type + adds grades). -/
theorem mapSubstTy_gadd (y : Name) (e₁ : Term) (a b : Option (GGrade × Ty)) :
    mapSubstTy y e₁ (gadd a b) = gadd (mapSubstTy y e₁ a) (mapSubstTy y e₁ b) := by
  rcases a with _ | ⟨ga, τa⟩ <;> rcases b with _ | ⟨gb, τb⟩ <;> rfl

/-- The ambient-merged additive identity: `(a + b) + n = (a + n) + (b + n)` when
    `n` is idempotent (`n = none` or `n = some (ω, _)`) and, where `b` and `n` are
    both present, their types agree (`hbn`). The engine of split reassembly. -/
theorem gadd_amb_reassoc {a b n : Option (GGrade × Ty)}
    (hn : n = none ∨ ∃ τn, n = some (GGrade.omega, τn))
    (hbn : ∀ gb τb τn, b = some (gb, τb) → n = some (GGrade.omega, τn) → τb = τn) :
    gadd (gadd a b) n = gadd (gadd a n) (gadd b n) := by
  rcases hn with rfl | ⟨τn, rfl⟩
  · rcases a with _ | ⟨ga, τa⟩ <;> rcases b with _ | ⟨gb, τb⟩ <;> rfl
  · rcases a with _ | ⟨ga, τa⟩ <;> rcases b with _ | ⟨gb, τb⟩
    · rfl
    · have : τb = τn := hbn gb τb τn rfl rfl
      subst this; simp only [gadd, GGrade.add_omega]
    · simp only [gadd, GGrade.add_omega]
    · simp only [gadd, GGrade.add_omega]

/-- `gadd _ none = _`. -/
theorem gadd_none (a : Option (GGrade × Ty)) : gadd a none = a := by
  cases a <;> rfl

/-- The ambient `Nε = tr ∅ ε` is `none` or `some (ω, τ)` with `τ` its `ε`-type. -/
theorem trEmpty_apply (ε : NLCtx) (z : Name) :
    tr (∅ : LCtx) ε z = (ε.lookup z).map (fun τ => (GGrade.omega, τ)) := by
  simp only [tr, Finmap.lookup_empty]
  cases ε.lookup z <;> rfl

theorem trEmpty_shape (ε : NLCtx) (z : Name) :
    tr (∅ : LCtx) ε z = none
    ∨ ∃ τn, tr (∅ : LCtx) ε z = some (GGrade.omega, τn) ∧ ε.lookup z = some τn := by
  rw [trEmpty_apply]
  cases h : ε.lookup z with
  | none => exact Or.inl rfl
  | some τ => exact Or.inr ⟨τ, rfl, rfl⟩

/-- The weak (no `ε`-witness) shape, as consumed by the additive lemmas. -/
theorem trEmpty_hn (ε : NLCtx) (z : Name) :
    tr (∅ : LCtx) ε z = none ∨ ∃ τn, tr (∅ : LCtx) ε z = some (GGrade.omega, τn) :=
  (trEmpty_shape ε z).imp id (fun ⟨τn, h, _⟩ => ⟨τn, h⟩)

/-! ## `NEAgree` / `AmbPres` preservation. -/

theorem NEAgree.split {ε : NLCtx} {Γ Γ₀ Γ₁ : GCtx}
    (hsplit : ∀ x, Γ x = gadd (Γ₀ x) (Γ₁ x)) (hta : TypeAgree Γ₀ Γ₁)
    (h : NEAgree ε Γ) : NEAgree ε Γ₀ ∧ NEAgree ε Γ₁ := by
  constructor
  · intro z τ hz g τ' hΓ₀
    have hΓ : ∃ g'', Γ z = some (g'', τ') := by
      rw [hsplit z, hΓ₀]
      cases Γ₁ z with
      | none => exact ⟨g, rfl⟩
      | some p => exact ⟨GGrade.add g p.1, rfl⟩
    obtain ⟨g'', hΓ⟩ := hΓ
    exact h z τ hz g'' τ' hΓ
  · intro z τ hz g τ' hΓ₁
    cases hΓ₀ : Γ₀ z with
    | none =>
        have hΓ : Γ z = some (g, τ') := by rw [hsplit z, hΓ₀, hΓ₁]; rfl
        exact h z τ hz _ _ hΓ
    | some p =>
        obtain ⟨g₀, τ₀'⟩ := p
        have htyeq : τ₀' = τ' := hta z g₀ τ₀' g τ' hΓ₀ hΓ₁
        subst htyeq
        have hΓ : Γ z = some (GGrade.add g₀ g, τ₀') := by rw [hsplit z, hΓ₀, hΓ₁]; rfl
        exact h z τ hz _ _ hΓ

theorem NEAgree.update {ε : NLCtx} {Γ : GCtx} {y' : Name} {v : Option (GGrade × Ty)}
    (hy'ε : ε.lookup y' = none) (h : NEAgree ε Γ) :
    NEAgree ε (Function.update Γ y' v) := by
  intro z τ hz g τ' hupd
  rcases eq_or_ne z y' with rfl | hzy'
  · rw [hz] at hy'ε; exact absurd hy'ε (by simp)
  · rw [Function.update_of_ne hzy'] at hupd; exact h z τ hz g τ' hupd

/-- `TNEAgree` survives a fresh non-ambient binder extension. -/
theorem TNEAgree.update {ε : NLCtx} {f : Name → Option Ty} {y' : Name} {τ₀ : Ty}
    (hy'ε : ε.lookup y' = none) (h : TNEAgree ε f) :
    TNEAgree ε (Function.update f y' (some τ₀)) := by
  intro z τ hz τ' hupd
  rcases eq_or_ne z y' with rfl | hzy'
  · rw [hz] at hy'ε; exact absurd hy'ε (by simp)
  · rw [Function.update_of_ne hzy'] at hupd; exact h z τ hz τ' hupd

/-- `NEAgree ε Γ` gives `TNEAgree` of `Γ`'s ω-view (for the GHasType arm's GSValid premises). -/
theorem NEAgree.toTypeCtx {ε : NLCtx} {Γ : GCtx} (h : NEAgree ε Γ) :
    TNEAgree ε (typeCtxOmega Γ) := by
  intro z τ hz τ' hf
  simp only [typeCtxOmega] at hf
  cases hΓ : Γ z with
  | none => rw [hΓ] at hf; simp at hf
  | some p =>
      obtain ⟨g, τg⟩ := p; rw [hΓ] at hf
      cases g with
      | zero => simp at hf
      | one => simp at hf
      | omega =>
          simp only [Option.some.injEq] at hf
          rw [← hf]; exact h z τ hz GGrade.omega τg hΓ

/-- `TNEAgree ε f` gives `NEAgree ε (resurrect f)` (for the FFS witness recursion). -/
theorem TNEAgree.toResurrect {ε : NLCtx} {f : Name → Option Ty} (h : TNEAgree ε f) :
    NEAgree ε (resurrect f) := by
  intro z τ hz g τ' hr
  simp only [resurrect] at hr
  cases hf : f z with
  | none => rw [hf] at hr; simp at hr
  | some τf =>
      rw [hf] at hr; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]; exact h z τ hz τf hf

/-! ## `gsubstCtx` reassembly / update / resurrect / `NoLin`. -/

/-- **Split reassembly.** `gsubstCtx` distributes over a `gadd`-split (needs the
    right branch's `NEAgree` so the merged ambient types line up). -/
theorem gsubstCtx_gadd {y : Name} {e₁ : Term} {ε : NLCtx} {Γ Γ₀ Γ₁ : GCtx}
    (hsplit : ∀ x, Γ x = gadd (Γ₀ x) (Γ₁ x)) (hne1 : NEAgree ε Γ₁) :
    ∀ z, gsubstCtx y e₁ ε Γ z
        = gadd (gsubstCtx y e₁ ε Γ₀ z) (gsubstCtx y e₁ ε Γ₁ z) := by
  intro z
  simp only [gsubstCtx]
  rcases eq_or_ne z y with rfl | hzy
  · simp only [if_pos rfl]; rfl
  · simp only [if_neg hzy, hsplit z]
    rw [← mapSubstTy_gadd]
    congr 1
    apply gadd_amb_reassoc (trEmpty_hn ε z)
    intro gb τb τn hb hn
    have hε : ε.lookup z = some τn := by
      rcases trEmpty_shape ε z with h0 | ⟨τn', hn', hε'⟩
      · rw [hn] at h0; exact absurd h0 (by simp)
      · rw [hn] at hn'; simp only [Option.some.injEq, Prod.mk.injEq] at hn'
        rw [hn'.2]; exact hε'
    exact (hne1 z τn hε gb τb hb).symm

/-- The PRE-substitution type of a present `gsubstCtx` entry: it is `subst y e₁ τ'`
    where `τ'` comes from `Γ z` (if present) or from the ambient `ε`-type (else). -/
theorem gsubstCtx_ty {y : Name} {e₁ : Term} {ε : NLCtx} {Γ : GCtx} {z : Name}
    {g : GGrade} {τ : Ty} (hzy : z ≠ y)
    (h : gsubstCtx y e₁ ε Γ z = some (g, τ)) :
    ∃ τ', τ = Ty.subst y e₁ τ'
      ∧ ((∃ g', Γ z = some (g', τ')) ∨ (Γ z = none ∧ ε.lookup z = some τ')) := by
  simp only [gsubstCtx, if_neg hzy, mapSubstTy] at h
  cases hΓ : Γ z with
  | some p =>
      obtain ⟨g', τ'⟩ := p
      refine ⟨τ', ?_, Or.inl ⟨g', rfl⟩⟩
      rw [hΓ] at h
      cases hn : tr (∅ : LCtx) ε z with
      | none =>
          rw [hn] at h
          simp only [gadd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.symm
      | some q =>
          obtain ⟨gn, τn⟩ := q; rw [hn] at h
          simp only [gadd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          exact h.2.symm
  | none =>
      rw [hΓ] at h
      cases hn : tr (∅ : LCtx) ε z with
      | none => rw [hn] at h; simp [gadd] at h
      | some q =>
          obtain ⟨gn, τn⟩ := q; rw [hn] at h
          simp only [gadd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          refine ⟨τn, h.2.symm, Or.inr ⟨rfl, ?_⟩⟩
          rcases trEmpty_shape ε z with h0 | ⟨τn', hn', hε'⟩
          · rw [hn] at h0; exact absurd h0 (by simp)
          · rw [hn] at hn'; simp only [Option.some.injEq, Prod.mk.injEq] at hn'
            rw [hn'.2]; exact hε'

/-- **`TypeAgree` survives substitution** (needs both branches' `NEAgree`). -/
theorem gsubstCtx_typeagree {y : Name} {e₁ : Term} {ε : NLCtx} {Γ₀ Γ₁ : GCtx}
    (hta : TypeAgree Γ₀ Γ₁) (hne0 : NEAgree ε Γ₀) (hne1 : NEAgree ε Γ₁) :
    TypeAgree (gsubstCtx y e₁ ε Γ₀) (gsubstCtx y e₁ ε Γ₁) := by
  intro z g₀ τ₀ g₁ τ₁ h0 h1
  have hzy : z ≠ y := by rintro rfl; simp only [gsubstCtx, ↓reduceIte, reduceCtorEq] at h0
  obtain ⟨a₀, rfl, hcase0⟩ := gsubstCtx_ty hzy h0
  obtain ⟨a₁, rfl, hcase1⟩ := gsubstCtx_ty hzy h1
  suffices h : a₀ = a₁ by rw [h]
  rcases hcase0 with ⟨g0', hΓ0⟩ | ⟨hΓ0none, hε0⟩ <;>
    rcases hcase1 with ⟨g1', hΓ1⟩ | ⟨hΓ1none, hε1⟩
  · exact hta z g0' a₀ g1' a₁ hΓ0 hΓ1
  · exact (hne0 z a₁ hε1 g0' a₀ hΓ0).symm
  · exact hne1 z a₀ hε0 g1' a₁ hΓ1
  · rw [hε0] at hε1; simp only [Option.some.injEq] at hε1; exact hε1

/-- Substitution commutes with a fresh non-ambient binder update (`y' ≠ y`, `y' ∉ ε`). -/
theorem gsubstCtx_update {y : Name} {e₁ : Term} {ε : NLCtx} {Γ : GCtx}
    {y' : Name} {v : Option (GGrade × Ty)} (hy'y : y' ≠ y) (hy'ε : ε.lookup y' = none) :
    gsubstCtx y e₁ ε (Function.update Γ y' v)
      = Function.update (gsubstCtx y e₁ ε Γ) y' (mapSubstTy y e₁ v) := by
  funext z
  rcases eq_or_ne z y' with rfl | hzy'
  · rw [Function.update_self]
    simp only [gsubstCtx, if_neg hy'y, Function.update_self]
    rw [trEmpty_apply, hy'ε]
    simp only [Option.map_none, gadd_none]
  · rw [Function.update_of_ne hzy']
    simp only [gsubstCtx]
    rcases eq_or_ne z y with rfl | hzy
    · simp only [↓reduceIte]
    · simp only [if_neg hzy, Function.update_of_ne hzy']

theorem gsubstCtx_resurrect {y : Name} {e₁ : Term} {ε : NLCtx} {f : Name → Option Ty} :
    gsubstCtx y e₁ ε (resurrect f) = resurrect (tsubstCtx y e₁ ε f) := by
  funext z
  simp only [gsubstCtx, resurrect, tsubstCtx, mapSubstTy]
  rcases eq_or_ne z y with rfl | hzy
  · simp only [↓reduceIte, Option.map_none]
  · simp only [if_neg hzy]
    rw [trEmpty_apply]
    cases hf : f z with
    | none =>
        cases hεz : ε.lookup z with
        | none => simp [gadd]
        | some τe => simp [gadd]
    | some τf =>
        cases hεz : ε.lookup z with
        | none => simp [gadd]
        | some τe => simp [gadd, GGrade.add_omega]

/-- A `gadd` of a non-linear `a` with the idempotent ambient `n ∈ {none, (ω,·)}`
    never has grade `1`. -/
theorem gadd_noLin_grade {a n : Option (GGrade × Ty)} {τ' : Ty}
    (ha : ∀ g τ, a = some (g, τ) → g ≠ GGrade.one)
    (hn : n = none ∨ ∃ τn, n = some (GGrade.omega, τn))
    (h : gadd a n = some (GGrade.one, τ')) : False := by
  rcases hn with rfl | ⟨τn, rfl⟩
  · rw [gadd_none] at h; exact ha _ _ h rfl
  · rcases a with _ | ⟨g, τ⟩
    · simp only [gadd, Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by decide)
    · simp only [gadd, Option.some.injEq, Prod.mk.injEq, GGrade.add_omega] at h
      exact absurd h.1 (by decide)

/-- `NoLin` survives substitution: the `Nε`-merge only produces grades in `{0, ω}`. -/
theorem NoLin.gsubst {y : Name} {e₁ : Term} {ε : NLCtx} {Γ : GCtx}
    (h : NoLin Γ) : NoLin (gsubstCtx y e₁ ε Γ) := by
  intro z τz hcon
  rcases eq_or_ne z y with rfl | hzy
  · simp only [gsubstCtx, ↓reduceIte, reduceCtorEq] at hcon
  · rw [gsubstCtx, if_neg hzy, mapSubstTy] at hcon
    rcases hh : gadd (Γ z) (tr (∅ : LCtx) ε z) with _ | ⟨g', τ'⟩
    · rw [hh] at hcon; simp at hcon
    · rw [hh] at hcon
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcon
      refine gadd_noLin_grade ?_ (trEmpty_hn ε z) (by rw [hh, hcon.1])
      intro g τ hgt hc
      subst hc
      exact h z τ hgt

/-- The GHasType arm's GSValid-premise view: substituting the ω-view equals the
    ω-view of the substituted context (needs `NEAgree`). -/
theorem tsubstCtx_typeCtxOmega {y : Name} {e₁ : Term} {ε : NLCtx} {Γ : GCtx}
    (hne : NEAgree ε Γ) :
    tsubstCtx y e₁ ε (typeCtxOmega Γ) = typeCtxOmega (gsubstCtx y e₁ ε Γ) := by
  funext z
  simp only [typeCtxOmega, tsubstCtx, gsubstCtx, mapSubstTy]
  rcases eq_or_ne z y with rfl | hzy
  · simp only [↓reduceIte]
  · simp only [if_neg hzy, trEmpty_apply]
    cases hΓ : Γ z with
    | none =>
        cases he : ε.lookup z with
        | none => simp [gadd, hΓ, he]
        | some τe => simp [gadd, hΓ, he]
    | some p =>
        obtain ⟨g, τg⟩ := p
        cases he : ε.lookup z with
        | none => cases g <;> simp [gadd, hΓ, he]
        | some τe =>
            have hteq : τe = τg := hne z τe he g τg hΓ
            subst hteq
            cases g <;> simp [gadd, hΓ, he, GGrade.add_omega]

/-- Top-level: substituting a fresh `y` in `asTypeCtx ε` is the identity (`ε`-types
    are `y`-fresh, `y ∉ ε`). -/
theorem tsubstCtx_asTypeCtx {y : Name} {e₁ : Term} {ε : NLCtx}
    (hynε : ε.lookup y = none)
    (hεfresh : ∀ z τ, ε.lookup z = some τ → y ∉ Ty.fv τ) :
    tsubstCtx y e₁ ε (asTypeCtx ε) = asTypeCtx ε := by
  funext z
  simp only [tsubstCtx, asTypeCtx]
  rcases eq_or_ne z y with rfl | hzy
  · rw [if_pos rfl, hynε]
  · rw [if_neg hzy]
    cases he : ε.lookup z with
    | none => simp [he]
    | some τe => simp only [he, Option.orElse_some, Option.map_some,
        Ty.subst_fresh y e₁ τe (hεfresh z τe he)]

/-! ## The threaded substitution invariants (bundle `NEAgree` with the `y`-type pin). -/

/-- GHasType-side invariant: `ε`-types agree, and `y` (wherever present in `Γ`) has
    type `τ₀` — needed so the `var y` leaf plants `e₁ : τ₀`. -/
def GInv (y : Name) (τ₀ : Ty) (ε : NLCtx) (Γ : GCtx) : Prop :=
  NEAgree ε Γ ∧ ∀ g τ, Γ y = some (g, τ) → τ = τ₀

/-- Type-formation-side invariant. -/
def TInv (y : Name) (τ₀ : Ty) (ε : NLCtx) (f : Name → Option Ty) : Prop :=
  TNEAgree ε f ∧ ∀ τ, f y = some τ → τ = τ₀

theorem GInv.split {y : Name} {τ₀ : Ty} {ε : NLCtx} {Γ Γ₀ Γ₁ : GCtx}
    (hsplit : ∀ x, Γ x = gadd (Γ₀ x) (Γ₁ x)) (hta : TypeAgree Γ₀ Γ₁)
    (h : GInv y τ₀ ε Γ) : GInv y τ₀ ε Γ₀ ∧ GInv y τ₀ ε Γ₁ := by
  obtain ⟨hne, hyt⟩ := h
  obtain ⟨hne0, hne1⟩ := NEAgree.split hsplit hta hne
  refine ⟨⟨hne0, ?_⟩, ⟨hne1, ?_⟩⟩
  · intro g τ hΓ₀
    have : ∃ g'', Γ y = some (g'', τ) := by
      rw [hsplit y, hΓ₀]; cases Γ₁ y with
      | none => exact ⟨g, rfl⟩
      | some p => exact ⟨GGrade.add g p.1, rfl⟩
    obtain ⟨g'', hΓ⟩ := this; exact hyt g'' τ hΓ
  · intro g τ hΓ₁
    cases hΓ₀ : Γ₀ y with
    | none => exact hyt g τ (by rw [hsplit y, hΓ₀, hΓ₁]; rfl)
    | some p =>
        obtain ⟨g₀, τ₀'⟩ := p
        have : τ₀' = τ := hta y g₀ τ₀' g τ hΓ₀ hΓ₁
        subst this
        exact hyt _ _ (by rw [hsplit y, hΓ₀, hΓ₁]; rfl)

theorem GInv.update {y : Name} {τ₀ : Ty} {ε : NLCtx} {Γ : GCtx}
    {y' : Name} {v : Option (GGrade × Ty)} (hy'y : y' ≠ y) (hy'ε : ε.lookup y' = none)
    (h : GInv y τ₀ ε Γ) : GInv y τ₀ ε (Function.update Γ y' v) := by
  obtain ⟨hne, hyt⟩ := h
  refine ⟨NEAgree.update hy'ε hne, ?_⟩
  intro g τ hupd
  rw [Function.update_of_ne (Ne.symm hy'y)] at hupd
  exact hyt g τ hupd

theorem GInv.toTInv {y : Name} {τ₀ : Ty} {ε : NLCtx} {Γ : GCtx}
    (h : GInv y τ₀ ε Γ) : TInv y τ₀ ε (typeCtxOmega Γ) := by
  obtain ⟨hne, hyt⟩ := h
  refine ⟨hne.toTypeCtx, ?_⟩
  intro τ hf
  simp only [typeCtxOmega] at hf
  cases hΓ : Γ y with
  | none => rw [hΓ] at hf; simp at hf
  | some p =>
      obtain ⟨g, τg⟩ := p; rw [hΓ] at hf
      cases g with
      | zero => simp at hf
      | one => simp at hf
      | omega => simp only [Option.some.injEq] at hf; rw [← hf]; exact hyt GGrade.omega τg hΓ

theorem TInv.toResurrect {y : Name} {τ₀ : Ty} {ε : NLCtx} {f : Name → Option Ty}
    (h : TInv y τ₀ ε f) : GInv y τ₀ ε (resurrect f) := by
  obtain ⟨htne, hyt⟩ := h
  refine ⟨htne.toResurrect, ?_⟩
  intro g τ hr
  simp only [resurrect] at hr
  cases hf : f y with
  | none => rw [hf] at hr; simp at hr
  | some τf =>
      rw [hf] at hr; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]; exact hyt τf hf

theorem TInv.update {y : Name} {τ₀ : Ty} {ε : NLCtx} {f : Name → Option Ty}
    {y' : Name} {τ' : Ty} (hy'y : y' ≠ y) (hy'ε : ε.lookup y' = none)
    (h : TInv y τ₀ ε f) : TInv y τ₀ ε (Function.update f y' (some τ')) := by
  obtain ⟨htne, hyt⟩ := h
  refine ⟨TNEAgree.update hy'ε htne, ?_⟩
  intro τ hupd
  rw [Function.update_of_ne (Ne.symm hy'y)] at hupd
  exact hyt τ hupd

/-! ## Syntactic `subst`/`openVar` commutation (from the shared LN kit). -/

theorem Term.subst_openVar_ne {y y' : Name} {e₁ e : Term}
    (hlc : Term.lc e₁) (hne : y' ≠ y) :
    Term.subst y e₁ (Term.openVar y' e) = Term.openVar y' (Term.subst y e₁ e) := by
  simp only [Term.openVar, Term.subst_openRec y e₁ hlc e 0 (.var y'), Term.subst,
    if_neg (Ne.symm hne)]

theorem Ty.subst_openVar_ne {y y' : Name} {e₁ : Term} {τ : Ty}
    (hlc : Term.lc e₁) (hne : y' ≠ y) :
    Ty.subst y e₁ (Ty.openVar y' τ) = Ty.openVar y' (Ty.subst y e₁ τ) := by
  simp only [Ty.openVar, Ty.subst_openRec y e₁ hlc τ 0 (.var y'), Term.subst,
    if_neg (Ne.symm hne)]

/-- Substitution commutes with a fresh non-ambient binder extension (type-formation). -/
theorem tsubstCtx_update {y : Name} {e₁ : Term} {ε : NLCtx} {f : Name → Option Ty}
    {y' : Name} {τ' : Ty} (hy'y : y' ≠ y) :
    tsubstCtx y e₁ ε (Function.update f y' (some τ'))
      = Function.update (tsubstCtx y e₁ ε f) y' (some (Ty.subst y e₁ τ')) := by
  funext z
  rcases eq_or_ne z y' with rfl | hzy'
  · rw [Function.update_self]
    simp only [tsubstCtx, if_neg hy'y, Function.update_self, Option.orElse_some, Option.map_some]
  · rw [Function.update_of_ne hzy']
    simp only [tsubstCtx]
    rcases eq_or_ne z y with rfl | hzy
    · simp only [↓reduceIte]
    · simp only [if_neg hzy, Function.update_of_ne hzy']

/-- `gsubstCtx` on a `var x` (`x ≠ y`): still present at a nonzero grade, type substituted.
    A `def` returning a `Subtype` so it can be destructured in the `Type`-valued arm. -/
def gsubstCtx_var {y : Name} {e₁ : Term} {ε : NLCtx} {Γ : GCtx}
    {x : Name} {g : GGrade} {τ : Ty}
    (hxy : x ≠ y) (hx : Γ x = some (g, τ)) (hg : g ≠ GGrade.zero) :
    { g' : GGrade // gsubstCtx y e₁ ε Γ x = some (g', Ty.subst y e₁ τ) ∧ g' ≠ GGrade.zero } := by
  cases htr : tr (∅ : LCtx) ε x with
  | none => exact ⟨g, by simp only [gsubstCtx, if_neg hxy, mapSubstTy, hx, htr, gadd_none,
      Option.map_some], hg⟩
  | some p =>
      obtain ⟨gn, τn⟩ := p
      have hgn : gn = GGrade.omega := by
        have ht := trEmpty_apply ε x; rw [htr] at ht
        cases hl : ε.lookup x with
        | none => rw [hl] at ht; simp at ht
        | some τe => rw [hl] at ht
                     simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ht
                     exact ht.1
      subst hgn
      exact ⟨GGrade.omega, by simp only [gsubstCtx, if_neg hxy, mapSubstTy, hx, htr, gadd,
        Option.map_some, GGrade.add_omega], by decide⟩

/-- The affine-leaf side condition survives substitution (the `Nε`-merge never makes a `1`). -/
theorem gsubstCtx_affineLeaf {y : Name} {e₁ : Term} {ε : NLCtx} {Γ : GCtx} {x : Name}
    (hlin : ∀ w, w ≠ x → ∀ τw, Γ w ≠ some (GGrade.one, τw)) :
    ∀ w, w ≠ x → ∀ τw, gsubstCtx y e₁ ε Γ w ≠ some (GGrade.one, τw) := by
  intro w hwx τw hcon
  rcases eq_or_ne w y with rfl | hwy
  · simp only [gsubstCtx, ↓reduceIte, reduceCtorEq] at hcon
  · rw [gsubstCtx, if_neg hwy, mapSubstTy] at hcon
    rcases hh : gadd (Γ w) (tr (∅ : LCtx) ε w) with _ | ⟨g', τ'⟩
    · rw [hh] at hcon; simp at hcon
    · rw [hh] at hcon
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hcon
      refine gadd_noLin_grade ?_ (trEmpty_hn ε w) (by rw [hh, hcon.1])
      intro g τ hgt hc; subst hc; exact hlin w hwx τ hgt

/-- Substitution preserves `≠ .real` on spaces (the head constructor is untouched). -/
theorem space_subst_ne_real (y : Name) (e₁ : Term) {s : Space} (h : s ≠ Space.real) :
    Space.subst y e₁ s ≠ Space.real := by cases s <;> simp_all [Space.subst]

/-- `y' ∉ ε.keys ⇒ ε.lookup y' = none`. -/
theorem lookup_eq_none_of_notMem_keys {ε : NLCtx} {y' : Name} (h : y' ∉ ε.keys) :
    ε.lookup y' = none :=
  Finmap.lookup_eq_none.mpr (fun hm => h (Finmap.mem_keys.mpr hm))

theorem term_subst_var_self (y : Name) (e₁ : Term) : Term.subst y e₁ (.var y) = e₁ := by
  simp [Term.subst]

theorem term_subst_var_ne {y x : Name} (e₁ : Term) (h : y ≠ x) :
    Term.subst y e₁ (.var x) = .var x := by
  simp [Term.subst, h]

/-! ## The `var y` leaf: `argTyped` weakens into the substituted context. -/

/-- At a `var y` leaf (`y` the only linear var), the argument context `tr ∅ ε`
    `GWk`-weakens into `gsubstCtx y e₁ ε Γ` (the `Nε`-merge restores `ε` at `ω`). -/
theorem gwk_var_leaf {y : Name} {e₁ : Term} {ε : NLCtx} {Γ : GCtx}
    (hne : NEAgree ε Γ) (hynε : ε.lookup y = none)
    (hεfresh : ∀ z τ, ε.lookup z = some τ → y ∉ Ty.fv τ)
    (hlin : ∀ w, w ≠ y → ∀ τw, Γ w ≠ some (GGrade.one, τw)) :
    GWk (tr (∅ : LCtx) ε) (gsubstCtx y e₁ ε Γ) := by
  intro w
  rcases eq_or_ne w y with rfl | hwy
  · rw [trEmpty_apply, hynε]
    simp only [gsubstCtx, ↓reduceIte, Option.map_none, WkPt]
  · simp only [gsubstCtx, if_neg hwy, mapSubstTy]
    rcases trEmpty_shape ε w with h0 | ⟨τw, hn, hεw⟩
    · rw [h0]
      cases hΓ : Γ w with
      | none => simp only [gadd_none, Option.map_none, WkPt]
      | some p =>
          obtain ⟨g, τ⟩ := p
          have hg1 : g ≠ GGrade.one := fun hc => hlin w hwy τ (by rw [hΓ, hc])
          rw [gadd_none]
          simp only [Option.map_some, WkPt]
          exact hg1
    · rw [hn]
      have hτw : Ty.subst y e₁ τw = τw := Ty.subst_fresh y e₁ τw (hεfresh w τw hεw)
      cases hΓ : Γ w with
      | none =>
          simp only [gadd, Option.map_some, hτw]
          exact ⟨rfl, GGrade.Wk.refl _⟩
      | some p =>
          obtain ⟨g, τ⟩ := p
          have hτeq : τ = τw := (hne w τw hεw g τ hΓ).symm
          subst hτeq
          simp only [gadd, Option.map_some, GGrade.add_omega, hτw]
          exact ⟨rfl, GGrade.Wk.refl _⟩

/-! ## The 4-way mutual substitution metatheorem. -/

mutual

/-- **(GSValid substitution).** -/
def gsvalid_subst {y : Name} {e₁ : Term} {ε : NLCtx} {τ₀ : Ty}
    (sd : GSubstData y e₁ ε τ₀) :
    {f : Name → Option Ty} → {s : Space} → TInv y τ₀ ε f → GSValid f s →
    GSValid (tsubstCtx y e₁ ε f) (Space.subst y e₁ s)
  | _, _, _, .empty => .empty
  | _, _, _, .real => .real
  | _, _, htinv, .dual h => .dual (gsvalid_subst sd htinv h)
  | _, _, htinv, .dsum h₀ h₁ => .dsum (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
  | _, _, htinv, .tprod h₀ h₁ => .tprod (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
  | _, _, htinv, .ker h₀ h₁ he =>
      .ker (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
        (by have hw := ghastype_subst sd htinv.toResurrect he
            rw [gsubstCtx_resurrect] at hw; simpa only [Ty.subst, Space.subst] using hw)
  | _, _, htinv, .coker h₀ h₁ he =>
      .coker (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
        (by have hw := ghastype_subst sd htinv.toResurrect he
            rw [gsubstCtx_resurrect] at hw; simpa only [Ty.subst, Space.subst] using hw)
  | _, _, htinv, .img h₀ h₁ he =>
      .img (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
        (by have hw := ghastype_subst sd htinv.toResurrect he
            rw [gsubstCtx_resurrect] at hw; simpa only [Ty.subst, Space.subst] using hw)
  | _, _, htinv, .coimg h₀ h₁ he =>
      .coimg (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
        (by have hw := ghastype_subst sd htinv.toResurrect he
            rw [gsubstCtx_resurrect] at hw; simpa only [Ty.subst, Space.subst] using hw)

/-- **(GTValid substitution).** -/
def gtvalid_subst {y : Name} {e₁ : Term} {ε : NLCtx} {τ₀ : Ty}
    (sd : GSubstData y e₁ ε τ₀) :
    {f : Name → Option Ty} → {τ : Ty} → {k : Kind} → TInv y τ₀ ε f → GTValid f τ k →
    GTValid (tsubstCtx y e₁ ε f) (Ty.subst y e₁ τ) k
  | _, _, _, htinv, .space hs => .space (gsvalid_subst sd htinv hs)
  | _, _, _, htinv, .piTy L h₀ hcod => by
      refine GTValid.piTy (L ∪ {y} ∪ ε.keys) (gtvalid_subst sd htinv h₀) ?_
      intro y' hy'
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy'
      obtain ⟨⟨hy'L, hy'y⟩, hy'εk⟩ := hy'
      have hy'εlk := lookup_eq_none_of_notMem_keys hy'εk
      have hrec := gtvalid_subst sd (htinv.update hy'y hy'εlk) (hcod y' hy'L)
      rw [tsubstCtx_update hy'y, Ty.subst_openVar_ne sd.lc hy'y] at hrec
      exact hrec

/-- **(GSubType substitution).** -/
def gsubtype_subst {y : Name} {e₁ : Term} {ε : NLCtx} {τ₀ : Ty}
    (sd : GSubstData y e₁ ε τ₀) :
    {f : Name → Option Ty} → {s₀ s₁ : Space} → TInv y τ₀ ε f → GSubType f s₀ s₁ →
    GSubType (tsubstCtx y e₁ ε f) (Space.subst y e₁ s₀) (Space.subst y e₁ s₁)
  | _, _, _, htinv, .sub_ker h₀ h₁ he =>
      .sub_ker (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
        (by have hw := ghastype_subst sd htinv.toResurrect he
            rw [gsubstCtx_resurrect] at hw; simpa only [Ty.subst, Space.subst] using hw)
  | _, _, _, htinv, .sub_coker h₀ h₁ he =>
      .sub_coker (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
        (by have hw := ghastype_subst sd htinv.toResurrect he
            rw [gsubstCtx_resurrect] at hw; simpa only [Ty.subst, Space.subst] using hw)
  | _, _, _, htinv, .sub_img h₀ h₁ he =>
      .sub_img (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
        (by have hw := ghastype_subst sd htinv.toResurrect he
            rw [gsubstCtx_resurrect] at hw; simpa only [Ty.subst, Space.subst] using hw)
  | _, _, _, htinv, .sub_coimg h₀ h₁ he =>
      .sub_coimg (gsvalid_subst sd htinv h₀) (gsvalid_subst sd htinv h₁)
        (by have hw := ghastype_subst sd htinv.toResurrect he
            rw [gsubstCtx_resurrect] at hw; simpa only [Ty.subst, Space.subst] using hw)

def ghastype_subst {y : Name} {e₁ : Term} {ε : NLCtx} {τ₀ : Ty}
    (sd : GSubstData y e₁ ε τ₀) :
    {Γ : GCtx} → {e : Term} → {τ : Ty} → GInv y τ₀ ε Γ → GHasType Γ e τ →
    GHasType (gsubstCtx y e₁ ε Γ) (Term.subst y e₁ e) (Ty.subst y e₁ τ)
  | _, _, _, hinv, .gzero hs => by
      exact .gzero ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs)
  | _, _, _, hinv, .gsmul hs hsp hta h₀ h₁ => by
      obtain ⟨hinv0, hinv1⟩ := GInv.split hsp hta hinv
      exact .gsmul ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs)
        (gsubstCtx_gadd hsp hinv1.1) (gsubstCtx_typeagree hta hinv0.1 hinv1.1)
        (ghastype_subst sd hinv0 h₀) (ghastype_subst sd hinv1 h₁)
  | _, _, _, hinv, .gadd hs h₀ h₁ => by
      exact .gadd ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs)
        (ghastype_subst sd hinv h₀) (ghastype_subst sd hinv h₁)
  | _, _, _, hinv, .ginner hs hnl => by
      exact .ginner ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs)
        (NoLin.gsubst hnl)
  | _, _, _, _, .greal_lit r hnl => .greal_lit r (NoLin.gsubst hnl)
  | _, _, _, hinv, .gapp_linear hs₀ hs₁ hsp hta h₀ h₁ => by
      obtain ⟨hinv0, hinv1⟩ := GInv.split hsp hta hinv
      exact .gapp_linear ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs₀)
        ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs₁)
        (gsubstCtx_gadd hsp hinv1.1) (gsubstCtx_typeagree hta hinv0.1 hinv1.1)
        (ghastype_subst sd hinv0 h₀) (ghastype_subst sd hinv1 h₁)
  | _, _, _, hinv, .gapp_inner hs hsp hta h₀ h₁ => by
      obtain ⟨hinv0, hinv1⟩ := GInv.split hsp hta hinv
      exact .gapp_inner ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs)
        (gsubstCtx_gadd hsp hinv1.1) (gsubstCtx_typeagree hta hinv0.1 hinv1.1)
        (ghastype_subst sd hinv0 h₀) (ghastype_subst sd hinv1 h₁)
  | _, _, _, hinv, @GHasType.gapp_nonlinear _ e₀ earg τ₀' τ₁ hnl h₀ h₁ => by
      have hcomm : Ty.subst y e₁ (Ty.instantiate earg τ₁)
          = Ty.instantiate (Term.subst y e₁ earg) (Ty.subst y e₁ τ₁) :=
        Ty.subst_openRec y e₁ sd.lc τ₁ 0 earg
      rw [hcomm]
      exact .gapp_nonlinear (NoLin.gsubst hnl)
        (ghastype_subst sd hinv h₀) (ghastype_subst sd hinv h₁)
  | _, _, _, hinv, @GHasType.gvar _ x g τ hx hg hlin =>
      if hxy : x = y then by
        rw [hxy] at hx hlin
        have hτ : τ = τ₀ := hinv.2 g τ hx
        rw [hxy, hτ, term_subst_var_self, Ty.subst_fresh y e₁ τ₀ sd.yfvτ0]
        exact gradeWeaken sd.argTyped (gwk_var_leaf hinv.1 sd.ynε sd.εfresh hlin)
      else by
        rw [term_subst_var_ne e₁ (Ne.symm hxy)]
        obtain ⟨g', hx', hg'⟩ := gsubstCtx_var hxy hx hg
        exact .gvar hx' hg' (gsubstCtx_affineLeaf hlin)
  | _, _, _, hinv, .gpinv_tensor hs₀ hs₁ hnl he => by
      exact .gpinv_tensor ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs₀)
        ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs₁)
        (NoLin.gsubst hnl) (ghastype_subst sd hinv he)
  | _, _, _, hinv, .gpinv_dual hs hnl he => by
      exact .gpinv_dual ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs)
        (NoLin.gsubst hnl) (ghastype_subst sd hinv he)
  | _, _, _, hinv, .gdsumE hs₀ hs₁ h₀ h₁ => by
      exact .gdsumE ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs₀)
        ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs₁)
        (ghastype_subst sd hinv h₀) (ghastype_subst sd hinv h₁)
  | _, _, _, hinv, .gtprodE hs₀ hs₁ hsp hta h₀ h₁ => by
      obtain ⟨hinv0, hinv1⟩ := GInv.split hsp hta hinv
      exact .gtprodE ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs₀)
        ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs₁)
        (gsubstCtx_gadd hsp hinv1.1) (gsubstCtx_typeagree hta hinv0.1 hinv1.1)
        (ghastype_subst sd hinv0 h₀) (ghastype_subst sd hinv1 h₁)
  | _, _, _, hinv, .gllam_real L hs hbody => by
      refine GHasType.gllam_real (L ∪ {y} ∪ ε.keys)
        ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs) ?_
      intro y' hy'
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy'
      obtain ⟨⟨hy'L, hy'y⟩, hy'εk⟩ := hy'
      have hy'εlk := lookup_eq_none_of_notMem_keys hy'εk
      have hrec := ghastype_subst sd (hinv.update hy'y hy'εlk) (hbody y' hy'L)
      rw [gsubstCtx_update hy'y hy'εlk, Term.subst_openVar_ne sd.lc hy'y] at hrec
      exact hrec
  | _, _, _, hinv, .gllam_tensor L hne hs₀ hs hbody => by
      refine GHasType.gllam_tensor (L ∪ {y} ∪ ε.keys) (space_subst_ne_real y e₁ hne)
        ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs₀)
        ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsvalid_subst sd hinv.toTInv hs) ?_
      intro y' hy'
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy'
      obtain ⟨⟨hy'L, hy'y⟩, hy'εk⟩ := hy'
      have hy'εlk := lookup_eq_none_of_notMem_keys hy'εk
      have hrec := ghastype_subst sd (hinv.update hy'y hy'εlk) (hbody y' hy'L)
      rw [gsubstCtx_update hy'y hy'εlk, Term.subst_openVar_ne sd.lc hy'y] at hrec
      exact hrec
  | _, _, _, hinv, .gembed hsub hnl => by
      exact .gembed ((tsubstCtx_typeCtxOmega hinv.1) ▸ gsubtype_subst sd hinv.toTInv hsub)
        (NoLin.gsubst hnl)
  | _, _, _, hinv, .gnllam L htv hnl hbody => by
      refine GHasType.gnllam (L ∪ {y} ∪ ε.keys)
        ((tsubstCtx_typeCtxOmega hinv.1) ▸ gtvalid_subst sd hinv.toTInv htv)
        (NoLin.gsubst hnl) ?_
      intro y' hy'
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy'
      obtain ⟨⟨hy'L, hy'y⟩, hy'εk⟩ := hy'
      have hy'εlk := lookup_eq_none_of_notMem_keys hy'εk
      have hrec := ghastype_subst sd (hinv.update hy'y hy'εlk) (hbody y' hy'L)
      rw [gsubstCtx_update hy'y hy'εlk, Term.subst_openVar_ne sd.lc hy'y,
        Ty.subst_openVar_ne sd.lc hy'y] at hrec
      exact hrec

end

/-! ## Top-level lemmas for discharging `GTVInst`. -/

/-- Substituting a fresh `y` out of `update (asTypeCtx ε) y τ₀` restores `asTypeCtx ε`. -/
theorem tsubstCtx_update_asTypeCtx {y : Name} {e₁ : Term} {ε : NLCtx} {τ₀ : Ty}
    (hynε : ε.lookup y = none)
    (hεfresh : ∀ z τ, ε.lookup z = some τ → y ∉ Ty.fv τ) :
    tsubstCtx y e₁ ε (Function.update (asTypeCtx ε) y (some τ₀)) = asTypeCtx ε := by
  funext z
  simp only [tsubstCtx, asTypeCtx]
  rcases eq_or_ne z y with rfl | hzy
  · rw [if_pos rfl, hynε]
  · rw [if_neg hzy, Function.update_of_ne hzy]
    cases he : ε.lookup z with
    | none => simp [asTypeCtx, he]
    | some τe => simp [asTypeCtx, he, Ty.subst_fresh y e₁ τe (hεfresh z τe he)]

/-- Substitution-intro: `subst y e₁ (openVar y τ) = instantiate e₁ τ` for `y ∉ fv τ`. -/
theorem ty_subst_intro (y : Name) (e₁ : Term) (τ : Ty) (hlc : Term.lc e₁)
    (hy : y ∉ Ty.fv τ) :
    Ty.subst y e₁ (Ty.openVar y τ) = Ty.instantiate e₁ τ := by
  show Ty.subst y e₁ (Ty.openRec 0 (.var y) τ) = Ty.openRec 0 e₁ τ
  rw [Ty.subst_openRec y e₁ hlc τ 0 (.var y), term_subst_var_self, Ty.subst_fresh y e₁ τ hy]

end GLang.Graded
