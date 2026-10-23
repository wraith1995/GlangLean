import GLang.Proofs.Adequacy.Foundations.Agree
import GLang.Proofs.Adequacy.Foundations.Foundations
import GLang.Proofs.Adequacy.Foundations.Erasure
import GLang.Graded.SourceWeaken
import GLang.Proofs.Source.Wellformed
import GLang.Proofs.Source.FVIrrelevance

namespace GLang

open Basis (BasisValid)

/-! ## Basis validity: fv-closure and fresh nonlinear weakening -/

/-- Cofinite FV closure for a basis binder body (local copy of the retired
    `ValueAdequacyFullCore.Basis.fv_openVar_body_subset`). -/
theorem Basis.fv_subset_of_openVar_body {b : Basis} {L A : Finset Name}
    (h : ∀ y, y ∉ L → ∀ z, z ∈ Basis.fv (Basis.openVar y b) → z = y ∨ z ∈ A) :
    Basis.fv b ⊆ A := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Basis.fv b)
  simp only [Finset.mem_union, not_or] at hy
  intro z hz
  rcases h y hy.1 z (Basis.fv_subset_openRec hz) with rfl | hzA
  · exact absurd hz hy.2
  · exact hzA

theorem Basis.BasisValid.fv_subset_keys {Γ : NLCtx} {b : Basis}
    (h : BasisValid Γ b) : Basis.fv b ⊆ Γ.keys := by
  induction h with
  | empty | one => simp [Basis.fv]
  | dual _ _ ih => simpa only [Basis.fv] using ih
  | dsum _ _ _ _ ih0 ih1 | tprod _ _ _ _ ih0 ih1 =>
      simpa only [Basis.fv] using Finset.union_subset ih0 ih1
  | proj_ker hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid (Basis.BasisValid.proj_ker hb0 hb1 hs0 hs1 htype)).some
  | proj_coker hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid (Basis.BasisValid.proj_coker hb0 hb1 hs0 hs1 htype)).some
  | proj_img hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid (Basis.BasisValid.proj_img hb0 hb1 hs0 hs1 htype)).some
  | proj_coimg hb0 hb1 hs0 hs1 htype ih0 ih1 =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih0) ih1
      exact SValid.fv_closure
        (Basis.BasisValid.sof_valid (Basis.BasisValid.proj_coimg hb0 hb1 hs0 hs1 htype)).some
  | image _ _ _ ih => simpa only [Basis.fv] using ih
  | terms hb hs hsv hterms _ ih =>
      simp only [Basis.fv]
      refine Finset.union_subset (Finset.union_subset ?_ ih) ?_
      · exact SValid.fv_closure hsv.some
      · intro z hz
        obtain ⟨e, he, hze⟩ := Term.mem_fvList.mp hz
        have hzctx := HasType.fv_closure (hterms e he).some hze
        simpa only [Finmap.keys_empty, Finset.empty_union] using hzctx
  | frame L hb0 hbody ih0 ihbody =>
      simp only [Basis.fv]
      refine Finset.union_subset ih0 ?_
      apply Basis.fv_subset_of_openVar_body (L := L)
      intro y hy z hz
      have hzctx := ihbody y hy hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hzctx
      exact hzctx

/-- A valid basis does not mention a name outside its context. -/
theorem Basis.BasisValid.not_mem_fv_of_not_mem {Γ : NLCtx} {b : Basis} {x : Name}
    (h : BasisValid Γ b) (hx : x ∉ Γ) : x ∉ Basis.fv b :=
  fun hm => hx (Finmap.mem_keys.mp (h.fv_subset_keys hm))

private theorem asTypeCtx_submap_insert' (Γ : NLCtx) (y : Name) (τ : Ty) (hyΓ : y ∉ Γ) :
    Graded.SubMap (Graded.asTypeCtx Γ) (Graded.asTypeCtx (Finmap.insert y τ Γ)) := by
  intro x σ hx
  by_cases hxy : x = y
  · subst x
    simp only [Graded.asTypeCtx, Finmap.lookup_eq_none.mpr hyΓ] at hx
    contradiction
  · simpa only [Graded.asTypeCtx, Finmap.lookup_insert_of_ne _ hxy] using hx

/-- Fresh nonlinear weakening of `SValid` (via the graded bridges). -/
noncomputable def SValid.weakenInsertNL {Γ : NLCtx} {s : Space}
    (y : Name) (τ : Ty) (hyΓ : y ∉ Γ) (h : SValid Γ s) :
    SValid (Finmap.insert y τ Γ) s :=
  Graded.svalidBwd (Graded.gsvalid_wk (Graded.svalidBridge h)
    (asTypeCtx_submap_insert' Γ y τ hyΓ))
    (by exact fun _ _ h => h)

/-- Fresh nonlinear weakening of `TValid` (via the graded bridges). -/
noncomputable def TValid.weakenInsertNL {Γ : NLCtx} {t : Ty} {k : Kind}
    (y : Name) (τ : Ty) (hyΓ : y ∉ Γ) (h : TValid Γ t k) :
    TValid (Finmap.insert y τ Γ) t k :=
  Graded.tvalidBwd (Graded.gtvalid_wk (Graded.tvalidBridge h)
    (asTypeCtx_submap_insert' Γ y τ hyΓ))
    (by exact fun _ _ h => h)

theorem Basis.BasisValid.weakenInsertNL
    {Γ : NLCtx} {b : Basis} {y : Name} {τ : Ty}
    (hyΓ : y ∉ Γ) (hyb : y ∉ Basis.fv b)
    (hb : BasisValid Γ b) :
    BasisValid (Finmap.insert y τ Γ) b := by
  induction hb generalizing y τ with
  | empty => exact .empty
  | one => exact .one
  | dual hb htof ih =>
      exact .dual (ih hyΓ (by simpa [Basis.fv] using hyb)) htof
  | dsum hb₀ hb₁ htof₀ htof₁ ih₀ ih₁ =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hyb
      exact .dsum (ih₀ hyΓ hyb.1) (ih₁ hyΓ hyb.2) htof₀ htof₁
  | tprod hb₀ hb₁ htof₀ htof₁ ih₀ ih₁ =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hyb
      exact .tprod (ih₀ hyΓ hyb.1) (ih₁ hyΓ hyb.2) htof₀ htof₁
  | proj_ker hb₀ hb₁ hsof₀ hsof₁ hterm ih₀ ih₁ =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hyb
      refine .proj_ker (ih₀ hyΓ hyb.1.2) (ih₁ hyΓ hyb.2) hsof₀ hsof₁ ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyΓ hterm.some⟩
  | proj_coker hb₀ hb₁ hsof₀ hsof₁ hterm ih₀ ih₁ =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hyb
      refine .proj_coker (ih₀ hyΓ hyb.1.2) (ih₁ hyΓ hyb.2) hsof₀ hsof₁ ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyΓ hterm.some⟩
  | proj_img hb₀ hb₁ hsof₀ hsof₁ hterm ih₀ ih₁ =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hyb
      refine .proj_img (ih₀ hyΓ hyb.1.2) (ih₁ hyΓ hyb.2) hsof₀ hsof₁ ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyΓ hterm.some⟩
  | proj_coimg hb₀ hb₁ hsof₀ hsof₁ hterm ih₀ ih₁ =>
      simp only [Basis.fv, Space.fv, Finset.mem_union, not_or] at hyb
      refine .proj_coimg (ih₀ hyΓ hyb.1.2) (ih₁ hyΓ hyb.2) hsof₀ hsof₁ ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyΓ hterm.some⟩
  | image hb hsof hterm ih =>
      simp only [Basis.fv] at hyb
      refine .image (ih hyΓ hyb) hsof ?_
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyΓ hterm.some⟩
  | terms hb htof hsv hes hne ih =>
      simp only [Basis.fv, Finset.mem_union, Finset.mem_biUnion,
        Finset.mem_image, not_or] at hyb
      refine .terms (ih hyΓ hyb.1.2) htof ⟨hsv.some.weakenInsertNL y τ hyΓ⟩ ?_ hne
      intro e he
      exact ⟨Graded.hasType_weaken_insert (Graded.CtxDisj.empty _)
        (Finmap.lookup_eq_none.mp (Finmap.lookup_empty y)) hyΓ
        (hes e he).some⟩
  | @frame Γ b₀ b₁ L hb₀ hbody ih₀ ihbody =>
      simp only [Basis.fv, Finset.mem_union, not_or] at hyb
      refine .frame (L ∪ {y}) (ih₀ hyΓ hyb.1) ?_
      intro z hz
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
      have hzy : z ≠ y := hz.2
      have hyz : y ≠ z := Ne.symm hzy
      have hyΓz : y ∉ Finmap.insert z (Basis.tof b₀) Γ := by
        simp [Finmap.mem_insert, hyΓ, hyz]
      have hyopen : y ∉ Basis.fv (Basis.openVar z b₁) := by
        intro hm
        have hs := Basis.fv_openRec_subset 0 (.var z) b₁ hm
        simp only [Finset.mem_union, Term.fv, Finset.mem_singleton] at hs
        exact hs.elim hyb.2 hyz
      have hw := ihbody z hz.1 (τ := τ) hyΓz hyopen
      have hcomm :
          Finmap.insert z (Basis.tof b₀) (Finmap.insert y τ Γ) =
            Finmap.insert y τ (Finmap.insert z (Basis.tof b₀) Γ) := by
        apply Finmap.ext_lookup
        intro w
        by_cases hwz : w = z
        · subst w
          simp [Finmap.lookup_insert, hzy]
        · by_cases hwy : w = y
          · subst w
            simp [Finmap.lookup_insert, hyz]
          · simp [Finmap.lookup_insert_of_ne, hwz, hwy]
      rw [hcomm]
      exact hw

/-! ## `EvalCtx.extend` membership -/

/-- Membership in an extended evaluation context. -/
theorem EvalCtx.mem_extend {Ψ : EvalCtx} {x x' : VName} {b b' : Basis} {v : ValExpr} :
    (x', b') ∈ Ψ.extend x b v ↔ (x' = x ∧ b' = b) ∨ (x', b') ∈ Ψ := by
  simp only [EvalCtx.extend, Finmap.mem_insert, Prod.mk.injEq]

/-- A name is bound (at some basis) in an extended evaluation context iff it is the new name
    or was bound before. -/
theorem EvalCtx.exists_mem_extend {Ψ : EvalCtx} {x x' : VName} {b : Basis} {v : ValExpr} :
    (∃ b', (x', b') ∈ Ψ.extend x b v) ↔ x' = x ∨ ∃ b', (x', b') ∈ Ψ := by
  constructor
  · rintro ⟨b', hb'⟩
    rcases EvalCtx.mem_extend.mp hb' with ⟨rfl, _⟩ | h
    · exact Or.inl rfl
    · exact Or.inr ⟨b', h⟩
  · rintro (rfl | ⟨b', h⟩)
    · exact ⟨b, EvalCtx.mem_extend.mpr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨b', EvalCtx.mem_extend.mpr (Or.inr h)⟩

/-! ## The telescope's name discipline -/

theorem LegacyConsistent.mem_iff {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ) :
    (∀ x, (x ∈ Δ ∨ x ∈ Γ) ↔ ∃ b, (x, b) ∈ Ψ) ∧
    (∀ x, x ∈ Γv ↔ ∃ b, (x, b) ∈ Ψ) ∧
    (∀ x, x ∈ σ.vars ↔ ∃ b, (x, b) ∈ Ψ) := by
  induction h with
  | empty =>
      refine ⟨fun x' => ?_, fun x' => ?_, fun x' => ?_⟩ <;> simp [Finmap.notMem_empty]
  | @extend_lin Δ Γ Ψ Γv σ ρ x b v τv xs s yv _ hx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      refine ⟨fun x' => ?_, fun x' => ?_, fun x' => ?_⟩
      · rw [Finmap.mem_insert, EvalCtx.exists_mem_extend, ← ih.1 x']; tauto
      · rw [Finmap.mem_insert, EvalCtx.exists_mem_extend, ← ih.2.1 x']
      · show x' ∈ σ.vars.insert x xs ↔ _
        rw [Finmap.mem_insert, EvalCtx.exists_mem_extend, ← ih.2.2 x']
  | @extend_nl Δ Γ Ψ Γv σ ρ x b v τv xs yv _ hx _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      refine ⟨fun x' => ?_, fun x' => ?_, fun x' => ?_⟩
      · rw [Finmap.mem_insert, EvalCtx.exists_mem_extend, ← ih.1 x']; tauto
      · rw [Finmap.mem_insert, EvalCtx.exists_mem_extend, ← ih.2.1 x']
      · show x' ∈ σ.vars.insert x xs ↔ _
        rw [Finmap.mem_insert, EvalCtx.exists_mem_extend, ← ih.2.2 x']

/-- A name fresh for `Ψ` is fresh for `Γv`. -/
theorem LegacyConsistent.not_mem_valCtx {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ) {y : VName}
    (hy : ∀ b, (y, b) ∉ Ψ) : y ∉ Γv :=
  fun hm => by obtain ⟨b, hb⟩ := (h.mem_iff.2.1 y).mp hm; exact hy b hb

theorem LegacyConsistent.ctxWF {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ) :
    CtxWF Δ Γ := by
  induction h with
  | empty =>
      exact ⟨fun x hx => absurd hx Finmap.notMem_empty,
        fun x s hx => absurd hx (by simp),
        fun x τ hx => absurd hx (by simp)⟩
  | @extend_lin Δ Γ Ψ Γv σ ρ x b v τv xs s yv _ hx htof hb _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      have hfv : Ty.fv (Basis.tof b) ⊆ Γ.keys :=
        (Basis.fv_tof_subset b).trans hb.fv_subset_keys
      refine ⟨fun y hy => ?_, fun y s' hy => ?_, ih.nl_fv_in_ε⟩
      · rcases Finmap.mem_insert.mp hy with rfl | hy
        · exact hx.2.1
        · exact ih.disjoint y hy
      · by_cases hyx : y = x
        · subst hyx
          rw [Finmap.lookup_insert] at hy
          obtain rfl := Option.some.inj hy
          intro z hz
          have : z ∈ Ty.fv (Basis.tof b) := by rw [htof]; exact hz
          exact Finmap.mem_keys.mp (hfv this)
        · rw [Finmap.lookup_insert_of_ne _ hyx] at hy
          exact ih.lin_fv_in_ε y s' hy
  | @extend_nl Δ Γ Ψ Γv σ ρ x b v τv xs yv _ hx hb _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      have hfv : Ty.fv (Basis.tof b) ⊆ Γ.keys :=
        (Basis.fv_tof_subset b).trans hb.fv_subset_keys
      refine ⟨fun y hy => ?_, fun y s' hy z hz => ?_, fun y τ hy => ?_⟩
      · intro hmem
        rcases Finmap.mem_insert.mp hmem with rfl | hmem
        · exact hx.1 hy
        · exact ih.disjoint y hy hmem
      · exact Finmap.mem_insert.mpr (Or.inr (ih.lin_fv_in_ε y s' hy z hz))
      · by_cases hyx : y = x
        · subst hyx
          rw [Finmap.lookup_insert] at hy
          obtain rfl := Option.some.inj hy
          intro z hz
          exact Finmap.mem_insert.mpr (Or.inr (Finmap.mem_keys.mp (hfv hz)))
        · rw [Finmap.lookup_insert_of_ne _ hyx] at hy
          intro z hz
          exact Finmap.mem_insert.mpr (Or.inr (ih.nl_fv_in_ε y τ hy z hz))

/-- `CtxWF ∅ Γ` — the form `denotBasis_isBasis` (`BasisSoundnessTodo.lean`) consumes. -/
theorem LegacyConsistent.ctxWF_nl {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ) :
    CtxWF ∅ Γ :=
  ⟨fun x hx => absurd hx Finmap.notMem_empty,
   fun x s hx => absurd hx (by simp),
   h.ctxWF.nl_fv_in_ε⟩

/-- Every space bound in `Δ` has its free names in `Γ`; every type bound in `Γ` likewise
    (the FV facts the environment lemmas transport along). -/
theorem LegacyConsistent.fv_lin_subset {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ)
    {x : Name} {s : Space} (hx : Δ.lookup x = some s) {y : Name} (hy : y ∉ Γ) :
    y ∉ Space.fv s :=
  fun hm => hy (h.ctxWF.lin_fv_in_ε x s hx y hm)

theorem LegacyConsistent.fv_nl_subset {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ)
    {x : Name} {τ : Ty} (hx : Γ.lookup x = some τ) {y : Name} (hy : y ∉ Γ) :
    y ∉ Ty.fv τ :=
  fun hm => hy (h.ctxWF.nl_fv_in_ε x τ hx y hm)

theorem LegacyConsistent.envWF {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ) :
    EnvWF σ Δ Γ := by
  induction h with
  | empty =>
      exact ⟨fun x s hx => absurd hx (by simp), fun x τ hx => absurd hx (by simp)⟩
  | @extend_lin Δ Γ Ψ Γv σ ρ x b v τv xs s yv hc hx htof hb _ _ _ _ _ _ _ _ hxs _ _ _ _ ih =>
      have hfv : Ty.fv (Basis.tof b) ⊆ Γ.keys :=
        (Basis.fv_tof_subset b).trans hb.fv_subset_keys
      have hxΓ : x ∉ Γ.keys := fun hm => hx.2.1 (Finmap.mem_keys.mp hm)
      have hxs' : xs.matchesShape (HType.hil (denotSpace σ s)) := by
        rw [htof, denotTy_space] at hxs; exact hxs
      have hxfvs : x ∉ Space.fv s := by
        intro hm; apply hxΓ; apply hfv; rw [htof]; exact hm
      refine ⟨fun y s' hy => ?_, fun y τ hy => ?_⟩
      · by_cases hyx : y = x
        · rw [hyx] at hy ⊢
          rw [Finmap.lookup_insert] at hy
          have hss : s' = s := (Option.some.inj hy).symm
          rw [hss]
          refine ⟨xs, by simp [DEnv.bind, Finmap.lookup_insert], ?_⟩
          rw [denotSpace_agree s (DEnv.AgreeOn.bind_left_of_not_mem hxfvs)]
          exact hxs'
        · rw [Finmap.lookup_insert_of_ne _ hyx] at hy
          obtain ⟨w, hw, hshape⟩ := ih.lin_match y s' hy
          refine ⟨w, by simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hyx, hw], ?_⟩
          have hxfv : x ∉ Space.fv s' := hc.fv_lin_subset hy hx.2.1
          rw [denotSpace_agree s' (DEnv.AgreeOn.bind_left_of_not_mem hxfv)]
          exact hshape
      · obtain ⟨w, hw, hshape⟩ := ih.nl_match y τ hy
        have hyx : y ≠ x := fun e => hx.2.1 (e ▸ Finmap.mem_of_lookup_eq_some hy)
        refine ⟨w, by simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hyx, hw], ?_⟩
        have hxfv : x ∉ Ty.fv τ := hc.fv_nl_subset hy hx.2.1
        rw [denotTy_agree τ (DEnv.AgreeOn.bind_left_of_not_mem hxfv)]
        exact hshape
  | @extend_nl Δ Γ Ψ Γv σ ρ x b v τv xs yv hc hx hb _ _ _ _ _ _ _ _ hxs _ _ _ _ ih =>
      have hfv : Ty.fv (Basis.tof b) ⊆ Γ.keys :=
        (Basis.fv_tof_subset b).trans hb.fv_subset_keys
      have hxΓ : x ∉ Γ.keys := fun hm => hx.2.1 (Finmap.mem_keys.mp hm)
      have hxfvb : x ∉ Ty.fv (Basis.tof b) := fun hm => hxΓ (hfv hm)
      refine ⟨fun y s' hy => ?_, fun y τ hy => ?_⟩
      · obtain ⟨w, hw, hshape⟩ := ih.lin_match y s' hy
        have hyx : y ≠ x := fun e => hx.1 (e ▸ Finmap.mem_of_lookup_eq_some hy)
        refine ⟨w, by simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hyx, hw], ?_⟩
        have hxfv : x ∉ Space.fv s' := hc.fv_lin_subset hy hx.2.1
        rw [denotSpace_agree s' (DEnv.AgreeOn.bind_left_of_not_mem hxfv)]
        exact hshape
      · by_cases hyx : y = x
        · rw [hyx] at hy ⊢
          rw [Finmap.lookup_insert] at hy
          have hττ : τ = Basis.tof b := (Option.some.inj hy).symm
          rw [hττ]
          refine ⟨xs, by simp [DEnv.bind, Finmap.lookup_insert], ?_⟩
          rw [denotTy_agree _ (DEnv.AgreeOn.bind_left_of_not_mem hxfvb)]
          exact hxs
        · rw [Finmap.lookup_insert_of_ne _ hyx] at hy
          obtain ⟨w, hw, hshape⟩ := ih.nl_match y τ hy
          refine ⟨w, by simp [DEnv.bind, Finmap.lookup_insert_of_ne _ hyx, hw], ?_⟩
          have hxfv : x ∉ Ty.fv τ := hc.fv_nl_subset hy hx.2.1
          rw [denotTy_agree τ (DEnv.AgreeOn.bind_left_of_not_mem hxfv)]
          exact hshape

/-- `EnvWF σ ∅ Γ` — the form `denotBasis_isBasis` consumes. -/
theorem LegacyConsistent.envWF_nl {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ) :
    EnvWF σ ∅ Γ :=
  ⟨fun x s hx => absurd hx (by simp), h.envWF.nl_match⟩

theorem LegacyConsistent.basisValid_of_mem {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx}
    {Ψ : EvalCtx} {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ) :
    ∀ x b, (x, b) ∈ Ψ → BasisValid Γ b := by
  induction h with
  | empty => intro x b hx; exact absurd hx Finmap.notMem_empty
  | @extend_lin Δ Γ Ψ Γv σ ρ x b v τv xs s yv _ hx _ hb _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro y b' hy
      rcases EvalCtx.mem_extend.mp hy with ⟨rfl, rfl⟩ | hy
      · exact hb
      · exact ih y b' hy
  | @extend_nl Δ Γ Ψ Γv σ ρ x b v τv xs yv _ hx hb _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
      intro y b' hy
      rcases EvalCtx.mem_extend.mp hy with ⟨rfl, rfl⟩ | hy
      · exact hb.weakenInsertNL hx.2.1 (hb.not_mem_fv_of_not_mem hx.2.1)
      · exact (ih y b' hy).weakenInsertNL hx.2.1 ((ih y b' hy).not_mem_fv_of_not_mem hx.2.1)

theorem LegacyConsistent.typingImplyEval {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ) :
    GLang.V2.TypingImplyEval Δ Γ Ψ := by
  refine ⟨h.mem_iff.1, ?_, ?_, h.basisValid_of_mem⟩
  · -- clause 2: linear bindings
    induction h with
    | empty => intro x s b hx; simp at hx
    | @extend_lin Δ Γ Ψ Γv σ ρ x b v τv xs s yv _ hx htof _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
        intro y s' b' hy hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · rw [Finmap.lookup_insert] at hy
          obtain rfl := Option.some.inj hy
          exact htof
        · have hyx : y ≠ x := fun e => hx.2.2 b' (e ▸ hmem)
          rw [Finmap.lookup_insert_of_ne _ hyx] at hy
          exact ih y s' b' hy hmem
    | @extend_nl Δ Γ Ψ Γv σ ρ x b v τv xs yv _ hx _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
        intro y s' b' hy hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · exact absurd (Finmap.mem_of_lookup_eq_some hy) hx.1
        · exact ih y s' b' hy hmem
  · -- clause 3: nonlinear bindings
    induction h with
    | empty => intro x τ b hx; simp at hx
    | @extend_lin Δ Γ Ψ Γv σ ρ x b v τv xs s yv _ hx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
        intro y τ b' hy hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · exact absurd (Finmap.mem_of_lookup_eq_some hy) hx.2.1
        · exact ih y τ b' hy hmem
    | @extend_nl Δ Γ Ψ Γv σ ρ x b v τv xs yv _ hx _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
        intro y τ b' hy hmem
        rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem
        · rw [Finmap.lookup_insert] at hy
          exact Option.some.inj hy
        · have hyx : y ≠ x := fun e => hx.2.2 b' (e ▸ hmem)
          rw [Finmap.lookup_insert_of_ne _ hyx] at hy
          exact ih y τ b' hy hmem

/-! ## Recovering a stored binding -/

structure LegacyConsistent.Stored (orc : FFSOracleSem) (x : VName) (b : Basis) (v : ValExpr)
    (τv : ValTy) (xs : DVal) (Δ₀ : LCtx) (Γ₀ : NLCtx) (Ψ₀ : EvalCtx) (Γv₀ : ValCtx)
    (σ₀ : DEnv) (ρ₀ : ValEnvSem) : Prop where
  prefix_consistent : LegacyConsistent orc Δ₀ Γ₀ Ψ₀ Γv₀ σ₀ ρ₀
  fresh : x ∉ Δ₀ ∧ x ∉ Γ₀ ∧ ∀ b', (x, b') ∉ Ψ₀
  hb : BasisValid Γ₀ b
  hfvb : Basis.fv b ⊆ Ψ₀.keyNames
  hτv : ValTy.EvalT Ψ₀ (Basis.tof b) τv
  hinfer : ValExpr.inferType v = τv
  hinferSpace : ValExpr.inferSpaceCtx [] v = ValTy.spaceOf τv
  hfvv : ValExpr.fv v ⊆ (Ψ₀.extend x b v).keyNames
  hlc : ValExpr.lc v
  hanchor : ∀ b₀ b₁ τv₀ τv₁ body,
    b = .frame b₀ b₁ → v = .vlam τv₀ τv₁ body →
    ∃ L : Finset VName, ∀ y, y ∉ L →
      ValTy.EvalT (Ψ₀.extend x b v |>.extend y b₀ (.var y τv₀))
        (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁)
  hxs : xs.matchesShape (denotTy σ₀ (Basis.tof b))
  hresult : LegacyResultAgree orc σ₀ ρ₀ [] [] [] (Basis.tof b) τv
    (denotBasis σ₀ b) xs (denotValB_semS orc ρ₀ [] [] v)
  hdims : LegacyAgreeDims orc σ₀ ρ₀ [] [] [] (Basis.tof b) τv
  hcert : ∃ Γcert, NLCtxIncl Γcert Γ₀ ∧ S.Ty Γcert Ψ₀ (Basis.tof b) τv

/-- Look a binding up in a consistent telescope: recover the stored value expression `v`,
    its value type `τv`, the source value `xs`, the prefix environments and the full record of
    `LegacyConsistent.Stored`, together with the CURRENT lookups (`Ψ`, `Γv`, `σ`, `ρ` all still map
    `x` to what was recorded) and the typing-context side (`x` is linear at `s` with
    `tof b = .space s`, or nonlinear at `tof b`).  The returned denotation equation is
    explicitly successful and identifies its payload with the current store entry `ρ x`. -/
theorem LegacyConsistent.lookup {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ)
    {x : VName} {b : Basis} (hmem : (x, b) ∈ Ψ) :
    ∃ (v : ValExpr) (τv : ValTy) (xs : DVal) (Δ₀ : LCtx) (Γ₀ : NLCtx) (Ψ₀ : EvalCtx)
      (Γv₀ : ValCtx) (σ₀ : DEnv) (ρ₀ : ValEnvSem),
      LegacyConsistent.Stored orc x b v τv xs Δ₀ Γ₀ Ψ₀ Γv₀ σ₀ ρ₀ ∧
      NLCtxIncl Γ₀ Γ ∧
      EvalCtx.lookup Ψ (x, b) = some v ∧
      Γv.lookup x = some τv ∧
      σ.vars.lookup x = some xs ∧
      denotValB_semS orc ρ₀ [] [] v = .ok (ρ x) ∧
      ((∃ s, Δ.lookup x = some s ∧ Basis.tof b = .space s) ∨ Γ.lookup x = some (Basis.tof b)) := by
  induction h with
  | empty => exact absurd hmem Finmap.notMem_empty
  | @extend_lin Δ Γ Ψ Γv σ ρ x' b' v' τv' xs' s yv' hc hx htof hb hfvb hτv hv hvspace hfvv hlc _ hanchor hxs hden hagree
      hdims hcert ih =>
      rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · refine ⟨v', τv', xs', Δ, Γ, Ψ, Γv, σ, ρ,
          ⟨hc, hx, hb, hfvb, hτv, hv, hvspace, hfvv, hlc, hanchor, hxs,
            ⟨yv', hden, hagree⟩, hdims,
            hcert⟩, NLCtxIncl.refl Γ, ?_, ?_, ?_, ?_, ?_⟩
        · simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert]
        · simp [Finmap.lookup_insert]
        · simp [DEnv.bind, Finmap.lookup_insert]
        · simpa [ValEnvSem.update_same] using hden
        · exact Or.inl ⟨s, by simp [Finmap.lookup_insert], htof⟩
      · obtain ⟨v, τv, xs, Δ₀, Γ₀, Ψ₀, Γv₀, σ₀, ρ₀, hst, hΓincl, hΨ, hΓv, hσ, hρ, hctx⟩ := ih hmem'
        have hxx : x ≠ x' := fun e => hx.2.2 b (e ▸ hmem')
        refine ⟨v, τv, xs, Δ₀, Γ₀, Ψ₀, Γv₀, σ₀, ρ₀, hst, hΓincl, ?_, ?_, ?_, ?_, ?_⟩
        · have hne : (x, b) ≠ (x', b') := fun e => hxx (Prod.mk.inj e).1
          simpa [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hne] using hΨ
        · simpa [Finmap.lookup_insert_of_ne _ hxx] using hΓv
        · simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hxx] using hσ
        · simpa [ValEnvSem.update_other _ _ _ _ hxx] using hρ
        · rcases hctx with ⟨s', hs', htof'⟩ | hΓ
          · exact Or.inl ⟨s', by simpa [Finmap.lookup_insert_of_ne _ hxx] using hs', htof'⟩
          · exact Or.inr hΓ
  | @extend_nl Δ Γ Ψ Γv σ ρ x' b' v' τv' xs' yv' hc hx hb hfvb hτv hv hvspace hfvv hlc _ hanchor hxs hden hagree hdims hcert ih =>
      rcases EvalCtx.mem_extend.mp hmem with ⟨rfl, rfl⟩ | hmem'
      · refine ⟨v', τv', xs', Δ, Γ, Ψ, Γv, σ, ρ,
          ⟨hc, hx, hb, hfvb, hτv, hv, hvspace, hfvv, hlc, hanchor, hxs,
            ⟨yv', hden, hagree⟩, hdims,
            hcert⟩, (NLCtxIncl.refl Γ).insert_right hx.2.1 (Basis.tof b),
            ?_, ?_, ?_, ?_, ?_⟩
        · simp [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert]
        · simp [Finmap.lookup_insert]
        · simp [DEnv.bind, Finmap.lookup_insert]
        · simpa [ValEnvSem.update_same] using hden
        · exact Or.inr (by simp [Finmap.lookup_insert])
      · obtain ⟨v, τv, xs, Δ₀, Γ₀, Ψ₀, Γv₀, σ₀, ρ₀, hst, hΓincl, hΨ, hΓv, hσ, hρ, hctx⟩ := ih hmem'
        have hxx : x ≠ x' := fun e => hx.2.2 b (e ▸ hmem')
        refine ⟨v, τv, xs, Δ₀, Γ₀, Ψ₀, Γv₀, σ₀, ρ₀, hst,
          hΓincl.insert_right hx.2.1 (Basis.tof b'), ?_, ?_, ?_, ?_, ?_⟩
        · have hne : (x, b) ≠ (x', b') := fun e => hxx (Prod.mk.inj e).1
          simpa [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hne] using hΨ
        · simpa [Finmap.lookup_insert_of_ne _ hxx] using hΓv
        · simpa [DEnv.bind, Finmap.lookup_insert_of_ne _ hxx] using hσ
        · simpa [ValEnvSem.update_other _ _ _ _ hxx] using hρ
        · rcases hctx with ⟨s', hs', htof'⟩ | hΓ
          · exact Or.inl ⟨s', hs', htof'⟩
          · exact Or.inr (by simpa [Finmap.lookup_insert_of_ne _ hxx] using hΓ)

/-- `LegacyConsistent.lookup` in the form `OpStep.var` consumes: a stored key has a value. -/
theorem LegacyConsistent.lookup_isSome {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ)
    {x : VName} {b : Basis} (hmem : (x, b) ∈ Ψ) : ∃ v, EvalCtx.lookup Ψ (x, b) = some v := by
  obtain ⟨v, _, _, _, _, _, _, _, _, _, _, hΨ, _⟩ := h.lookup hmem
  exact ⟨v, hΨ⟩

theorem ValExpr.fv_var_subset_keyNames_extend {Ψ : EvalCtx} {y : VName} {b₀ : Basis}
    {τv₀ : ValTy} (hfvτ : ValTy.fv τv₀ ⊆ Ψ.keyNames) :
    ValExpr.fv (.var y τv₀) ⊆ (Ψ.extend y b₀ (.var y τv₀)).keyNames := by
  rw [GLang.V2.keyNames_extend]
  simp only [ValExpr.fv]
  exact Finset.insert_subset_insert _ hfvτ

/-- **Binder extension, non-linear side** (definitions §7.1): a name `y` fresh for the
    telescope, a valid scoped basis `b₀` with realization `τv₀` of `tof b₀` (whose free names
    are scoped in `Ψ` and which is locally closed), and an agreeing pair `(x', y')` of
    elements, extend a consistent telescope by `y : tof b₀` / `(y, b₀) ↦ .var y τv₀`.
    Hypothesis `hρ`: see the section header. -/
theorem LegacyConsistent.extend_binder_nl {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ)
    {y : VName} (hy : y ∉ Δ ∧ y ∉ Γ ∧ ∀ b', (y, b') ∉ Ψ)
    {b₀ : Basis} (hb₀ : BasisValid Γ b₀) (hfvb : Basis.fv b₀ ⊆ Ψ.keyNames)
    {τv₀ : ValTy} (hτ₀ : S.Ty Γ Ψ (Basis.tof b₀) τv₀)
    (hfvτ : ValTy.fv τv₀ ⊆ Ψ.keyNames) (hlc : ValTy.lc τv₀)
    (x' : (denotTy σ (Basis.tof b₀)).El) (y' : (denotValTyS orc ρ [] [] τv₀).El)
    (hρ : ρ y = ValValSem.fromEl _ y')
    (hagree : LegacyAgree orc σ ρ [] [] [] (Basis.tof b₀) τv₀ (denotBasis σ b₀)
                ((denotTy σ (Basis.tof b₀)).embed x') (ValValSem.fromEl _ y'))
    (hdims : LegacyAgreeDims orc σ ρ [] [] [] (Basis.tof b₀) τv₀) :
    LegacyConsistent orc Δ (Finmap.insert y (Basis.tof b₀) Γ) (Ψ.extend y b₀ (.var y τv₀))
      (Finmap.insert y τv₀ Γv) (σ.bind y ((denotTy σ (Basis.tof b₀)).embed x'))
      (ρ.update y (ValValSem.fromEl _ y')) := by
  have hden : denotValB_semS orc ρ [] [] (.var y τv₀) = .ok (ValValSem.fromEl _ y') := by
    rw [denotValB_semS.eq_2, hρ]
  have hc := LegacyConsistent.extend_nl h hy hb₀ hfvb hτ₀.toEvalT (by simp) (by simp [ValExpr.inferSpaceCtx])
    (ValExpr.fv_var_subset_keyNames_extend hfvτ) (.var hlc) (Or.inr ⟨_, rfl⟩)
    (by intro _ _ _ _ _ _ hv; exact nomatch hv)
    (HType.embed_matchesShape _ _)
    hden hagree hdims ⟨Γ, NLCtxIncl.refl Γ, hτ₀⟩
  exact hc

/-- **Binder extension, linear side** (`llam_assemble`'s `Δ` extension shape, with the
    `.var` placeholder): as `extend_binder_nl`, with `tof b₀ = .space s` and `y : s` in `Δ`. -/
theorem LegacyConsistent.extend_binder_lin {orc : FFSOracleSem} {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {Γv : ValCtx} {σ : DEnv} {ρ : ValEnvSem} (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ)
    {y : VName} (hy : y ∉ Δ ∧ y ∉ Γ ∧ ∀ b', (y, b') ∉ Ψ)
    {b₀ : Basis} {s : GLang.Space} (htof : Basis.tof b₀ = .space s)
    (hb₀ : BasisValid Γ b₀) (hfvb : Basis.fv b₀ ⊆ Ψ.keyNames)
    {τv₀ : ValTy} (hτ₀ : S.Ty Γ Ψ (Basis.tof b₀) τv₀)
    (hfvτ : ValTy.fv τv₀ ⊆ Ψ.keyNames) (hlc : ValTy.lc τv₀)
    (x' : (denotTy σ (Basis.tof b₀)).El) (y' : (denotValTyS orc ρ [] [] τv₀).El)
    (hρ : ρ y = ValValSem.fromEl _ y')
    (hagree : LegacyAgree orc σ ρ [] [] [] (Basis.tof b₀) τv₀ (denotBasis σ b₀)
                ((denotTy σ (Basis.tof b₀)).embed x') (ValValSem.fromEl _ y'))
    (hdims : LegacyAgreeDims orc σ ρ [] [] [] (Basis.tof b₀) τv₀) :
    LegacyConsistent orc (Finmap.insert y s Δ) Γ (Ψ.extend y b₀ (.var y τv₀))
      (Finmap.insert y τv₀ Γv) (σ.bind y ((denotTy σ (Basis.tof b₀)).embed x'))
      (ρ.update y (ValValSem.fromEl _ y')) := by
  have hden : denotValB_semS orc ρ [] [] (.var y τv₀) = .ok (ValValSem.fromEl _ y') := by
    rw [denotValB_semS.eq_2, hρ]
  have hc := LegacyConsistent.extend_lin h hy htof hb₀ hfvb hτ₀.toEvalT (by simp)
    (by simp [ValExpr.inferSpaceCtx])
    (ValExpr.fv_var_subset_keyNames_extend hfvτ) (.var hlc) (Or.inr ⟨_, rfl⟩)
    (by intro _ _ _ _ _ _ hv; exact nomatch hv)
    (HType.embed_matchesShape _ _)
    hden hagree hdims ⟨Γ, NLCtxIncl.refl Γ, hτ₀⟩
  exact hc

end GLang
