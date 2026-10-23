import GLang.Graded.BridgeBwd
import GLang.Proofs.Source.Soundness

/-!
# Context support for graded strengthening

These lemmas package the invariant needed when erasing a name from a dependent
graded derivation: every *other* context entry has a type that is fresh for the
erased name.  `CtxWF` supplies exactly this invariant for the translation of a
fresh nonlinear source extension.
-/

namespace GLang.Graded

open GLang

/-- Remove one coordinate from a graded context. -/
def eraseName (Γ : GCtx) (x : Name) : GCtx := Function.update Γ x none

/-- Every binding other than `x` has an `x`-fresh type. -/
def TypeFreshAt (Γ : GCtx) (x : Name) : Prop :=
  ∀ z g τ, z ≠ x → Γ z = some (g, τ) → x ∉ Ty.fv τ

/-- Function-valued type-context version of `TypeFreshAt`. -/
def TypeViewFreshAt (f : Name → Option Ty) (x : Name) : Prop :=
  ∀ z τ, z ≠ x → f z = some τ → x ∉ Ty.fv τ

@[simp] theorem eraseName_self (Γ : GCtx) (x : Name) : eraseName Γ x x = none := by
  simp [eraseName]

theorem eraseName_of_ne (Γ : GCtx) {x z : Name} (hzx : z ≠ x) :
    eraseName Γ x z = Γ z := by
  simp [eraseName, Function.update_of_ne hzx]

theorem eraseName_update_comm (Γ : GCtx) {x y : Name}
    (v : Option (GGrade × Ty)) (hxy : x ≠ y) :
    eraseName (Function.update Γ y v) x =
      Function.update (eraseName Γ x) y v := by
  simpa only [eraseName] using Function.update_comm (f := Γ) hxy.symm v none

theorem typeCtxOmega_eraseName (Γ : GCtx) (x : Name) :
    typeCtxOmega (eraseName Γ x) = Function.update (typeCtxOmega Γ) x none := by
  funext z
  rcases eq_or_ne z x with rfl | hzx
  · simp [eraseName, typeCtxOmega]
  · simp [eraseName, typeCtxOmega, Function.update_of_ne hzx]

theorem resurrect_erase (f : Name → Option Ty) (x : Name) :
    resurrect (Function.update f x none) = eraseName (resurrect f) x := by
  funext z
  rcases eq_or_ne z x with rfl | hzx
  · simp [resurrect, eraseName]
  · simp [resurrect, eraseName, Function.update_of_ne hzx]

theorem eraseName_tr_empty_insert {Γ : NLCtx} {x : Name} {τx : Ty} (hxΓ : x ∉ Γ) :
    eraseName (tr (∅ : LCtx) (Finmap.insert x τx Γ)) x = tr ∅ Γ := by
  funext z
  rcases eq_or_ne z x with rfl | hzx
  · simp [eraseName, tr, Finmap.lookup_eq_none.mpr hxΓ]
  · simp [eraseName, tr, Function.update_of_ne hzx, Finmap.lookup_insert_of_ne _ hzx]

theorem typeFreshAt_tr_empty_insert {Γ : NLCtx} {x : Name} {τx : Ty}
    (hctx : CtxWF ∅ Γ) (hxΓ : x ∉ Γ) :
    TypeFreshAt (tr (∅ : LCtx) (Finmap.insert x τx Γ)) x := by
  intro z g τ hzx hz
  simp only [tr, Finmap.lookup_empty, Finmap.lookup_insert_of_ne _ hzx] at hz
  cases hΓz : Γ.lookup z with
  | none => rw [hΓz] at hz; simp at hz
  | some τz =>
      rw [hΓz] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at hz
      obtain ⟨_, rfl⟩ := hz
      intro hxτ
      exact hxΓ (hctx.nl_fv_in_ε z τz hΓz x hxτ)

theorem typeViewFreshAt_insert {Γ : NLCtx} {x : Name} {τx : Ty}
    (hctx : CtxWF ∅ Γ) (hxΓ : x ∉ Γ) :
    TypeViewFreshAt (asTypeCtx (Finmap.insert x τx Γ)) x := by
  intro z τ hzx hz
  simp only [asTypeCtx, Finmap.lookup_insert_of_ne _ hzx] at hz
  intro hxτ
  exact hxΓ (hctx.nl_fv_in_ε z τ hz x hxτ)

theorem TypeFreshAt.typeCtxOmega {Γ : GCtx} {x : Name} (hf : TypeFreshAt Γ x) :
    TypeViewFreshAt (typeCtxOmega Γ) x := by
  intro z τ hzx hz
  change (match Γ z with
    | some (.omega, τ') => some τ'
    | _ => none) = some τ at hz
  cases hΓz : Γ z with
  | none => rw [hΓz] at hz; simp at hz
  | some p =>
      obtain ⟨g, τz⟩ := p
      rw [hΓz] at hz
      cases g with
      | zero => simp at hz
      | one => simp at hz
      | omega =>
          simp only [Option.some.injEq] at hz
          subst τz
          exact hf z GGrade.omega τ hzx hΓz

theorem TypeViewFreshAt.resurrect {f : Name → Option Ty} {x : Name}
    (hf : TypeViewFreshAt f x) : TypeFreshAt (resurrect f) x := by
  intro z g τ hzx hz
  change (f z).map (fun τ' => (GGrade.omega, τ')) = some (g, τ) at hz
  cases hfz : f z with
  | none => rw [hfz] at hz; simp at hz
  | some τz =>
      rw [hfz] at hz
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hz
      obtain ⟨_, rfl⟩ := hz
      exact hf z τz hzx hfz

theorem TypeViewFreshAt.update {f : Name → Option Ty} {x y : Name} {τ : Ty}
    (hf : TypeViewFreshAt f x) (hyx : y ≠ x) (hτ : x ∉ Ty.fv τ) :
    TypeViewFreshAt (Function.update f y (some τ)) x := by
  intro z τz hzx hz
  rcases eq_or_ne z y with rfl | hzy
  · rw [Function.update_self] at hz
    simp only [Option.some.injEq] at hz
    exact hz ▸ hτ
  · apply hf z τz hzx
    simpa [Function.update_of_ne hzy] using hz

/-- A split branch inherits type freshness from the conclusion context. -/
theorem TypeFreshAt.of_split_left {Γ Γ₀ Γ₁ : GCtx} {x : Name}
    (hf : TypeFreshAt Γ x) (hsp : ∀ z, Γ z = gadd (Γ₀ z) (Γ₁ z))
    (hta : TypeAgree Γ₀ Γ₁) : TypeFreshAt Γ₀ x := by
  intro z g τ hzx hz
  have hΓ : ∃ g', Γ z = some (g', τ) := by
    cases h₁ : Γ₁ z with
    | none =>
        refine ⟨g, ?_⟩
        rw [hsp z, hz, h₁]; rfl
    | some p =>
        obtain ⟨g₁, τ₁⟩ := p
        have hτ : τ = τ₁ := hta z g τ g₁ τ₁ hz h₁
        subst τ₁
        refine ⟨GGrade.add g g₁, ?_⟩
        rw [hsp z, hz, h₁]; rfl
  obtain ⟨g', hΓ⟩ := hΓ
  exact hf z g' τ hzx hΓ

theorem TypeFreshAt.of_split_right {Γ Γ₀ Γ₁ : GCtx} {x : Name}
    (hf : TypeFreshAt Γ x) (hsp : ∀ z, Γ z = gadd (Γ₀ z) (Γ₁ z))
    (hta : TypeAgree Γ₀ Γ₁) : TypeFreshAt Γ₁ x := by
  intro z g τ hzx hz
  have hΓ : ∃ g', Γ z = some (g', τ) := by
    cases h₀ : Γ₀ z with
    | none =>
        refine ⟨g, ?_⟩
        rw [hsp z, h₀, hz]; rfl
    | some p =>
        obtain ⟨g₀, τ₀⟩ := p
        have hτ : τ₀ = τ := hta z g₀ τ₀ g τ h₀ hz
        subst τ₀
        refine ⟨GGrade.add g₀ g, ?_⟩
        rw [hsp z, h₀, hz]; rfl
  obtain ⟨g', hΓ⟩ := hΓ
  exact hf z g' τ hzx hΓ

theorem split_eraseName {Γ Γ₀ Γ₁ : GCtx} (x : Name)
    (hsp : ∀ z, Γ z = gadd (Γ₀ z) (Γ₁ z)) :
    ∀ z, eraseName Γ x z = gadd (eraseName Γ₀ x z) (eraseName Γ₁ x z) := by
  intro z
  rcases eq_or_ne z x with rfl | hzx
  · simp [eraseName, gadd]
  · simpa [eraseName, Function.update_of_ne hzx] using hsp z

theorem typeAgree_eraseName {Γ₀ Γ₁ : GCtx} (x : Name) (h : TypeAgree Γ₀ Γ₁) :
    TypeAgree (eraseName Γ₀ x) (eraseName Γ₁ x) := by
  intro z g₀ τ₀ g₁ τ₁ hz₀ hz₁
  rcases eq_or_ne z x with rfl | hzx
  · simp [eraseName] at hz₀
  · exact h z g₀ τ₀ g₁ τ₁
      (by simpa [eraseName, Function.update_of_ne hzx] using hz₀)
      (by simpa [eraseName, Function.update_of_ne hzx] using hz₁)

theorem NoLin.eraseName {Γ : GCtx} (x : Name) (h : NoLin Γ) :
    NoLin (eraseName Γ x) := by
  intro y τ hy
  rcases eq_or_ne y x with rfl | hyx
  · rw [eraseName_self] at hy
    exact absurd hy (by simp)
  · rw [eraseName_of_ne Γ hyx] at hy
    exact h y τ hy

/-- Extending at a distinct binder preserves freshness when the binder type is
itself fresh. -/
theorem TypeFreshAt.update {Γ : GCtx} {x y : Name} {g : GGrade} {τ : Ty}
    (hf : TypeFreshAt Γ x) (hyx : y ≠ x) (hτ : x ∉ Ty.fv τ) :
    TypeFreshAt (Function.update Γ y (some (g, τ))) x := by
  intro z gz τz hzx hz
  rcases eq_or_ne z y with rfl | hzy
  · rw [Function.update_self] at hz
    simp only [Option.some.injEq, Prod.mk.injEq] at hz
    exact hz.2 ▸ hτ
  · apply hf z gz τz hzx
    simpa [Function.update_of_ne hzy] using hz

/-! ## Result-type freshness

This is the dependent regularity fact used by the erasure induction.  A term
that does not mention `x`, typed in a context whose other binding types do not
mention `x`, cannot acquire an `x`-dependent result type merely through hidden
intermediate annotations.  The `appN`, `embed`, and `nllam` cases are the
substantive ones.
-/

mutual

/-- The ambient side of graded subtyping is fresh whenever its syntactic
subspace side is fresh.  Each of the four constructors exposes both component
spaces and its witness term in the source FFS syntax. -/
def GSubType.ambient_fresh {f : Name → Option Ty} {s₀ s₁ : Space}
    (h : GSubType f s₀ s₁) {x : Name} (hx : x ∉ Space.fv s₀) :
    x ∉ Space.fv s₁ := by
  cases h <;> simp only [Space.fv, Finset.mem_union, not_or] at hx
  · exact hx.1.1
  · exact hx.1.1
  · exact hx.1.2
  · exact hx.1.2

/-- A graded typing derivation cannot hide dependence on `x` in its result
type when the term and every other context binding are `x`-fresh. -/
def GHasType.result_fresh : {Γ : GCtx} → {e : Term} → {τ : Ty} →
    GHasType Γ e τ → ∀ {x : Name}, TypeFreshAt Γ x → x ∉ Term.fv e →
      x ∉ Ty.fv τ
  | _, _, _, .gzero _, _, _, he => by simpa [Term.fv, Ty.fv] using he
  | _, _, _, .gsmul _ hsp hta _ h₁, x, hf, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      exact GHasType.result_fresh h₁ (hf.of_split_right hsp hta) he.2
  | _, _, _, .gadd _ h₀ _, x, hf, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      exact GHasType.result_fresh h₀ hf he.1
  | _, _, _, .ginner _ _, _, _, he => by
      intro hm
      simp only [Ty.fv, Space.fv, Finset.mem_union] at hm
      exact hm.elim he he
  | _, _, _, .greal_lit _ _, _, _, _ => by simp [Ty.fv, Space.fv]
  | _, _, _, .gapp_linear _ _ _ _ _ _, _, _, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      simpa [Ty.fv] using he.1.1.2
  | _, _, _, .gapp_inner _ _ _ _ _, _, _, _ => by simp [Ty.fv, Space.fv]
  | _, _, _, .gapp_nonlinear _ h₀ h₁, x, hf, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      have hfpi := GHasType.result_fresh h₀ hf he.1
      simp only [Ty.fv, Finset.mem_union, not_or] at hfpi
      have hfarg := GHasType.result_fresh h₁ hf he.2
      intro hm
      have hm' := Ty.fv_openRec_subset 0 _ _ hm
      rcases Finset.mem_union.mp hm' with hm' | hm'
      · exact hfpi.2 hm'
      · exact he.2 hm'
  | _, _, _, @GHasType.gvar Γ z g τ hz _ _, x, hf, he => by
      have hzx : z ≠ x := by
        intro h; subst z
        exact he (by simp [Term.fv])
      exact hf z g τ hzx hz
  | _, _, _, .gpinv_tensor _ _ _ _, _, _, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      simpa [Ty.fv, Space.fv] using ⟨he.1.2, he.1.1⟩
  | _, _, _, .gpinv_dual _ _ _, _, _, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      simpa [Ty.fv, Space.fv] using he.1
  | _, _, _, .gdsumE _ _ h₀ h₁, x, hf, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      have hf₀ := GHasType.result_fresh h₀ hf he.1
      have hf₁ := GHasType.result_fresh h₁ hf he.2
      simpa [Ty.fv, Space.fv] using ⟨hf₀, hf₁⟩
  | _, _, _, .gtprodE _ _ hsp hta h₀ h₁, x, hf, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      have hf₀ := GHasType.result_fresh h₀ (hf.of_split_left hsp hta) he.1
      have hf₁ := GHasType.result_fresh h₁ (hf.of_split_right hsp hta) he.2
      simpa [Ty.fv, Space.fv] using ⟨hf₀, hf₁⟩
  | _, _, _, .gllam_real _ _ _, _, _, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      simpa [Ty.fv, Space.fv] using he.1.1
  | _, _, _, .gllam_tensor _ _ _ _ _, _, _, he => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      simpa [Ty.fv, Space.fv] using ⟨he.1.1, he.1.2⟩
  | _, _, _, .gembed hsub _, _, _, he => by
      simp only [Term.fv] at he
      have hamb := hsub.ambient_fresh he
      simpa [Ty.fv, Space.fv] using ⟨he, hamb⟩
  | _, _, _, .gnllam L _ _ hbody, x, hf, he => by
      rename_i Γctx τdom τcod kdom kcod e htv hnl
      simp only [Term.fv, Finset.mem_union, not_or] at he
      have hex := Infinite.exists_notMem_finset (L ∪ {x})
      let y := hex.choose
      have hy : y ∉ L ∪ {x} := hex.choose_spec
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
      have hyx : y ≠ x := hy.2
      have hbodyfresh : x ∉ Term.fv (Term.openVar y e) := by
        intro hm
        have hm' := Term.fv_openRec_subset 0 (.var y) e hm
        rcases Finset.mem_union.mp hm' with hm' | hm'
        · exact he.2 hm'
        · have hxy : x = y := by simpa [Term.fv] using hm'
          exact hyx hxy.symm
      have hctxfresh := hf.update (g := GGrade.omega) hyx he.1
      have hcodopen := GHasType.result_fresh (hbody y hy.1) hctxfresh hbodyfresh
      have hcod : x ∉ Ty.fv τcod := by
        intro hm
        exact hcodopen (Ty.fv_subset_openRec (v := .var y) hm)
      simpa [Ty.fv] using ⟨he.1, hcod⟩

end

end GLang.Graded
