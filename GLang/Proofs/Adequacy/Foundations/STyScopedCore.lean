import GLang.Proofs.Adequacy.Foundations.Strengthened
import GLang.Proofs.Preservation.ValuePreservationV2

namespace GLang

open Basis (BasisValid)

/-- **Scoped evaluation context**: every stored value mentions only key-names of `Ψ`
    (clause 1 of `GLang.V2.EvalCtxValidPlus`, alone). -/
def EvalCtxScoped (Ψ : EvalCtx) : Prop :=
  ∀ x b v, EvalCtx.lookup Ψ (x, b) = some v → ValExpr.fv v ⊆ Ψ.keyNames

/-- Membership in an evaluation context's name projection is witnessed by
membership of a pair key at some basis. -/
theorem EvalCtx.mem_keyNames_iff_exists_basis
    {Psi : EvalCtx} {x : VName} :
    x ∈ Psi.keyNames ↔ ∃ b, (x, b) ∈ Psi := by
  rw [EvalCtx.keyNames, Finset.mem_image]
  constructor
  · rintro ⟨⟨x', b⟩, hp, rfl⟩
    exact ⟨b, Finmap.mem_keys.mp hp⟩
  · rintro ⟨b, hb⟩
    exact ⟨(x, b), Finmap.mem_keys.mpr hb, rfl⟩

/-- Extending an evaluation context adds exactly the installed source name
to its name projection. -/
theorem EvalCtx.keyNames_extend_core
    (Psi : EvalCtx) (y : VName) (b : Basis) (v : ValExpr) :
    (Psi.extend y b v).keyNames = insert y Psi.keyNames := by
  apply Finset.Subset.antisymm
  · intro z hz
    rw [EvalCtx.keyNames, Finset.mem_image] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    simp only [EvalCtx.extend, Finmap.mem_keys, Finmap.mem_insert] at hp
    rcases hp with rfl | hp
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finmap.mem_keys.mpr hp))
  · intro z hz
    rw [EvalCtx.keyNames, Finset.mem_image]
    rcases Finset.mem_insert.mp hz with rfl | hz
    · refine ⟨(z, b), ?_, rfl⟩
      simp only [Finmap.mem_keys, EvalCtx.extend]
      exact Finmap.mem_insert.mpr (Or.inl rfl)
    · rw [EvalCtx.keyNames, Finset.mem_image] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      refine ⟨p, ?_, rfl⟩
      simp only [Finmap.mem_keys, EvalCtx.extend]
      exact Finmap.mem_insert.mpr (Or.inr (Finmap.mem_keys.mp hp))

/-- The empty context is scoped. -/
theorem EvalCtxScoped.empty : EvalCtxScoped ∅ := by
  intro x b v h
  simp only [EvalCtx.lookup, Finmap.lookup_empty] at h
  exact nomatch h

theorem EvalCtxScoped.extend {Ψ : EvalCtx} (hΨ : EvalCtxScoped Ψ) {y : VName} {b : Basis}
    {w : ValExpr} (hw : ValExpr.fv w ⊆ insert y Ψ.keyNames) :
    EvalCtxScoped (Ψ.extend y b w) := by
  intro x b' v hlk
  rw [EvalCtx.keyNames_extend_core]
  simp only [EvalCtx.extend, EvalCtx.lookup] at hlk
  by_cases hk : (x, b') = (y, b)
  · rw [hk, Finmap.lookup_insert, Option.some.injEq] at hlk
    subst hlk; exact hw
  · rw [Finmap.lookup_insert_of_ne _ hk] at hlk
    exact (hΨ x b' v hlk).trans (Finset.subset_insert _ _)

/-- Binder extension by a placeholder variable `(y,b₀) ↦ .var y τv₀`. -/
theorem EvalCtxScoped.extend_var {Ψ : EvalCtx} (hΨ : EvalCtxScoped Ψ) {y : VName} {b₀ : Basis}
    {τv₀ : ValTy} (hτ : ValTy.fv τv₀ ⊆ Ψ.keyNames) :
    EvalCtxScoped (Ψ.extend y b₀ (.var y τv₀)) :=
  hΨ.extend (by simp only [ValExpr.fv]; exact Finset.insert_subset_insert _ hτ)

/-- Binder extension by a basis vector `(y,b') ↦ .delta i sv'` (the `llam_assemble` family). -/
theorem EvalCtxScoped.extend_delta {Ψ : EvalCtx} (hΨ : EvalCtxScoped Ψ) {y : VName} {b' : Basis}
    {i : Nat} {sv' : ValSpace} (hsv : ValSpace.fv sv' ⊆ Ψ.keyNames) :
    EvalCtxScoped (Ψ.extend y b' (.delta i sv')) :=
  hΨ.extend (by simp only [ValExpr.fv]; exact hsv.trans (Finset.subset_insert _ _))

/-! ## Binder fv-drop helpers -/

/-- Drop a fresh name from a `⊆ insert y K` bound. -/
theorem subset_of_subset_insert_of_notMem {S K : Finset VName} {y : VName}
    (hsub : S ⊆ insert y K) (hy : y ∉ S) : S ⊆ K :=
  fun _ ha => (Finset.mem_insert.mp (hsub ha)).resolve_left (fun h => hy (h ▸ ha))

/-- Codomain TYPE of a cofinite binder: from the opened IH at a name outside `fv τv₁`. -/
theorem EvalCtxScoped.drop_ty {Ψ : EvalCtx} {b₀ : Basis} {τv₀ τv₁ : ValTy} {L : Finset VName}
    (ih : ∀ y, y ∉ L → EvalCtxScoped (Ψ.extend y b₀ (.var y τv₀)) →
      ValTy.fv (ValTy.openVar y τv₀ τv₁) ⊆ (Ψ.extend y b₀ (.var y τv₀)).keyNames)
    (hΨ : EvalCtxScoped Ψ) (hfv₀ : ValTy.fv τv₀ ⊆ Ψ.keyNames) :
    ValTy.fv τv₁ ⊆ Ψ.keyNames := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ ValTy.fv τv₁)
  rw [Finset.mem_union, not_or] at hy
  have h := ih y hy.1 (hΨ.extend_var hfv₀)
  rw [EvalCtx.keyNames_extend_core] at h
  exact subset_of_subset_insert_of_notMem
    (fun w hw => h (ValTy.fv_subset_openRec hw)) hy.2

/-- Body VALUE of a cofinite binder (opened with a `.var`). -/
theorem EvalCtxScoped.drop_expr {Ψ : EvalCtx} {b₀ : Basis} {τv₀ : ValTy} {env : ValExpr}
    {L : Finset VName}
    (ih : ∀ y, y ∉ L → EvalCtxScoped (Ψ.extend y b₀ (.var y τv₀)) →
      ValExpr.fv (ValExpr.openVar y τv₀ env) ⊆ (Ψ.extend y b₀ (.var y τv₀)).keyNames)
    (hΨ : EvalCtxScoped Ψ) (hfv₀ : ValTy.fv τv₀ ⊆ Ψ.keyNames) :
    ValExpr.fv env ⊆ Ψ.keyNames := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ ValExpr.fv env)
  rw [Finset.mem_union, not_or] at hy
  have h := ih y hy.1 (hΨ.extend_var hfv₀)
  rw [EvalCtx.keyNames_extend_core] at h
  exact subset_of_subset_insert_of_notMem
    (fun w hw => h (ValExpr.fv_subset_openRec hw)) hy.2

/-- `llam_assemble` family: each `env i` is `y`-independent, so the fresh `.delta` binder drops. -/
theorem EvalCtxScoped.drop_family {Ψ : EvalCtx} {b' : Basis} {sv' : ValSpace} {n : Nat}
    {env : Fin n → ValExpr} {L : Finset VName}
    (ih : ∀ y, y ∉ L → ∀ i : Fin n, EvalCtxScoped (Ψ.extend y b' (.delta i.val sv')) →
      ValExpr.fv (env i) ⊆ (Ψ.extend y b' (.delta i.val sv')).keyNames)
    (hΨ : EvalCtxScoped Ψ) (hfvsv' : ValSpace.fv sv' ⊆ Ψ.keyNames) :
    ∀ i : Fin n, ValExpr.fv (env i) ⊆ Ψ.keyNames := by
  intro i
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ ValExpr.fv (env i))
  rw [Finset.mem_union, not_or] at hy
  have h := ih y hy.1 i (hΨ.extend_delta hfvsv')
  rw [EvalCtx.keyNames_extend_core] at h
  exact subset_of_subset_insert_of_notMem h hy.2

/-- `fvList` of a `List.ofFn` family, from a per-member bound. -/
theorem ValExpr.fvList_ofFn_subset {n : Nat} {f : Fin n → ValExpr} {K : Finset VName}
    (h : ∀ i, ValExpr.fv (f i) ⊆ K) : ValExpr.fvList (List.ofFn f) ⊆ K := by
  intro w hw
  obtain ⟨el, hel, hwel⟩ := ValExpr.mem_fvList.mp hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hel
  exact h i hwel

/-- Empty-context inferred spaces introduce no names beyond their operand.
This absorption form lets the generic strengthened-scoping arm normalize the
source annotation recorded by `S.Cob.image_svds`. -/
private theorem ValExpr.fv_inferSpaceCtx_nil_union_fv (e : ValExpr) :
    ValSpace.fv (ValExpr.inferSpaceCtx [] e) ∪ ValExpr.fv e = ValExpr.fv e := by
  rw [ValExpr.inferSpaceCtx_nil]
  exact Finset.union_eq_right.mpr (ValExpr.fv_inferSpace_subset e)

/-- The complete source-space annotation used by `image_svds` has exactly the
free names of its operand. -/
private theorem ValExpr.fv_inferSpaceCtx_nil_svds (e : ValExpr) :
    ValSpace.fv (ValExpr.inferSpaceCtx [] (.svds e)) = ValExpr.fv e := by
  simp only [ValExpr.inferSpaceCtx, ValSpace.fv,
    ValExpr.fv_inferSpaceCtx_nil_union_fv, Finset.union_self]

/-! ## The joint induction -/

/-- Generic arm closer: unfold `fv`, split the unions, discharge each piece from an IH
    specialized at the (unchanged) context, or from the stored-value clause (`var` arms). -/
macro "sfv_generic" : tactic => `(tactic| (
  intros
  intro hΨ
  try simp_all only [ValExpr.reshapBase, ValExpr.fv, ValTy.fv, ValSpace.fv,
    ValExpr.fv_inferSpaceCtx_nil_union_fv,
    ValExpr.fv_inferSpaceCtx_nil_svds,
    Finset.union_subset_iff,
    Finset.empty_subset, true_and, and_true, and_self]
  first
  | done
  | exact hΨ _ _ _ ‹EvalCtx.lookup _ _ = some _›))

/-- The shared recursor call
    (`S.Space`/`S.Ty`/`S.TyAt`/`S.Cob`/`S.Term` all use it). -/
macro "sfv_rec" h:term : tactic => `(tactic| (
  refine ($h).rec
    (motive_1 := fun _ Ψ _ sv _ => EvalCtxScoped Ψ → ValSpace.fv sv ⊆ Ψ.keyNames)
    (motive_2 := fun _ Ψ _ τv _ => EvalCtxScoped Ψ → ValTy.fv τv ⊆ Ψ.keyNames)
    (motive_3 := fun _ Ψ _ τv _ => EvalCtxScoped Ψ → ValTy.fv τv ⊆ Ψ.keyNames)
    (motive_4 := fun _ Ψ _ env _ _ => EvalCtxScoped Ψ → ValExpr.fv env ⊆ Ψ.keyNames)
    (motive_5 := fun _ _ Ψ _ _ v τv _ =>
      EvalCtxScoped Ψ → ValExpr.fv v ⊆ Ψ.keyNames ∧ ValTy.fv τv ⊆ Ψ.keyNames)
    -- S.Space (9)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    -- S.Ty (2)
    ?_ ?_
    -- S.TyAt (2)
    ?_ ?_
    -- S.Cob (13)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    -- S.Term (28)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  all_goals try (sfv_generic; done)
  -- Remaining, in constructor order: S.Ty.piTy, S.TyAt.frame, image_svds, nllam,
  -- frame_reanchor, frame_eta, llam_assemble, llam_assemble_real.
  · -- S.Ty.piTy
    intro Γ Ψ b₀ τ₀ τ₁ τv₀ τv₁ k₀ k₁ ht hb hbv h₀ L h₁ ih₀ ih₁ hΨ
    have hfv₀ := ih₀ hΨ
    simp only [ValTy.fv]
    exact Finset.union_subset hfv₀ (EvalCtxScoped.drop_ty ih₁ hΨ hfv₀)
  · -- S.TyAt.frame
    intro Γ Ψ b₀ b₁ τv₀ τv₁ hbv hdom L hcod ihdom ihcod hΨ
    have hfv₀ := ihdom hΨ
    simp only [ValTy.fv]
    exact Finset.union_subset hfv₀ (EvalCtxScoped.drop_ty ihcod hΨ hfv₀)
  · -- S.Cob.image_svds: the canonical coordinate composition is scoped.
    intro Γ Ψ b₀ b₁ e leev s₀ s₁ svb hbS hbT hs₀ hs₁ hb₀ hb₁ hsvb he ihsvb ihe hΨ
    have hspace := ihsvb hΨ
    have hvalue := (ihe hΨ).1
    have hcoords := (ValExpr.imageCoords_fv svb leev).trans
      (Finset.union_subset hspace hvalue)
    have hinfer : ValSpace.fv (ValExpr.inferSpaceCtx [] (.imageCoords svb leev))
        ⊆ Ψ.keyNames := by
      rw [ValExpr.inferSpaceCtx_nil]
      exact (ValExpr.fv_inferSpace_subset _).trans hcoords
    simp only [ValExpr.fv, ValTy.fv, ValSpace.fv, ValExpr.reshapBase]
    repeat' apply Finset.union_subset
    all_goals assumption
  · -- nllam
    intro Γ Ψ b₀ b₁ τ₀ τ₁ e τv₀ τv₁ env hb₀ hb₁ ht hbv hτv h₀ L he h₁ ihτv ih₀ ihe ih₁ hΨ
    refine ⟨?_, ihτv hΨ⟩
    have hfv₀ := ih₀ hΨ
    have hfvτ₁ := EvalCtxScoped.drop_ty ih₁ hΨ hfv₀
    have hfvenv := EvalCtxScoped.drop_expr (fun y hy hΨ' => (ihe y hy hΨ').1) hΨ hfv₀
    simp only [ValExpr.fv, ValTy.fv]
    exact Finset.union_subset (Finset.union_subset hfv₀ hfvτ₁)
      (Finset.union_subset (Finset.union_subset hfvenv hfvτ₁) hfvτ₁)
  · -- dependent application: conversions add only inferred or explicit type names.
    intro Γ Ψ b₀ b₁ f a vf va d c ta out ht hb hout hf ha ihout ihf iha hΨ
    exact ⟨(ValExpr.fv_applyAt_subset _ _ _).trans
      (Finset.union_subset (Finset.union_subset (ihf hΨ).1 (iha hΨ).1) (ihout hΨ)), ihout hΨ⟩
  · -- frame_reanchor
    intro Γ Ψ b₀ b₀' b₁ n₀ leev env₁ τv₀ τv₀' τv₁ τv₁' htof ht hbv hτv h₀ hfn hdom L hx hcod
      ihτv ih₀ ihfn ihdom ihx ihcod hΨ
    refine ⟨?_, ihτv hΨ⟩
    have hfv₀ := ih₀ hΨ
    have hfvτ₁' := EvalCtxScoped.drop_ty ihcod hΨ hfv₀
    have hfvenv₁ := EvalCtxScoped.drop_expr (fun y hy hΨ' => (ihx y hy hΨ').1) hΨ hfv₀
    have hfvleev := (ihfn hΨ).1
    have hfvτv₀' := ihdom hΨ
    have hcall := (ValExpr.fv_applyValue_subset leev (.reshap env₁ τv₀' τv₀')).trans
      (Finset.union_subset hfvleev
        (Finset.union_subset (Finset.union_subset hfvenv₁ hfvτv₀') hfvτv₀'))
    exact Finset.union_subset (Finset.union_subset hfv₀ hfvτ₁')
      (Finset.union_subset (Finset.union_subset hcall hfvτ₁') hfvτ₁')
  · -- frame_eta
    intro Γ Ψ b₀ b₁ n₀ τv₀ τv₁ env ht hbv hτv h₀ L he h₁ ihτv ih₀ ihe ih₁ hΨ
    refine ⟨?_, ihτv hΨ⟩
    have hfv₀ := ih₀ hΨ
    have hfvτ₁ := EvalCtxScoped.drop_ty ih₁ hΨ hfv₀
    have hfvenv := EvalCtxScoped.drop_expr (fun y hy hΨ' => (ihe y hy hΨ').1) hΨ hfv₀
    simp only [ValExpr.fv, ValTy.fv]
    exact Finset.union_subset (Finset.union_subset hfv₀ hfvτ₁)
      (Finset.union_subset (Finset.union_subset hfvenv hfvτ₁) hfvτ₁)
  · -- llam_assemble (S1 may wrap the `.vsum` in a `.reshap … (.space (.tprod sv' sv))`; the
    -- closing `first` already covers the extra `fv sv' ∪ fv sv` pieces)
    intro Δ Γ Ψ b' b e sv' sv env htof' ht hbv hτv hsv' hsv L hfam ihτv ihsv' ihsv ihfam hΨ
    refine ⟨?_, ihτv hΨ⟩
    have hfvsv' := ihsv' hΨ
    have hfvsv := ihsv hΨ
    have hfvenv := EvalCtxScoped.drop_family (fun y hy i hΨ' => (ihfam y hy i hΨ').1) hΨ hfvsv'
    have hlist : ValExpr.fvList (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
        ValExpr.tprodE (.delta i.val sv')
          (.reshap (env i) (.space sv) (.space sv))) ⊆ Ψ.keyNames :=
      ValExpr.fvList_ofFn_subset fun i => by
        simp only [ValExpr.fv, ValTy.fv]
        exact Finset.union_subset hfvsv'
          (Finset.union_subset (Finset.union_subset (hfvenv i) hfvsv) hfvsv)
    have hfvtgt : ValTy.fv (.space (.tprod sv' sv)) ⊆ Ψ.keyNames := by
      simp only [ValTy.fv, ValSpace.fv]
      exact Finset.union_subset hfvsv' hfvsv
    simp only [ValExpr.fv_sumAt, ValExpr.reshapBase, ValExpr.fv]
    exact Finset.union_subset (Finset.union_subset (Finset.union_subset hfvsv' hlist) hfvtgt)
      hfvtgt
  · -- llam_assemble_real
    intro Δ Γ Ψ b' e sv' env htof' ht hbv hτv hsv' L hfam ihτv ihsv' ihfam hΨ
    refine ⟨?_, ihτv hΨ⟩
    have hfvsv' := ihsv' hΨ
    have hfvenv := EvalCtxScoped.drop_family (fun y hy i hΨ' => (ihfam y hy i hΨ').1) hΨ hfvsv'
    have hlist : ValExpr.fvList (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
        ValExpr.scale (.reshap (env i) (.space .real) (.space .real))
          (.delta i.val sv')) ⊆ Ψ.keyNames :=
      ValExpr.fvList_ofFn_subset fun i => by
        simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
        exact Finset.union_subset
          (Finset.union_subset (Finset.union_subset (hfvenv i) (Finset.empty_subset _))
            (Finset.empty_subset _)) hfvsv'
    have hfvtgt : ValTy.fv (.space sv') ⊆ Ψ.keyNames := by
      simp only [ValTy.fv]
      exact hfvsv'
    simp only [ValExpr.fv_sumAt, ValExpr.reshapBase, ValExpr.fv]
    exact Finset.union_subset (Finset.union_subset (Finset.union_subset hfvsv' hlist) hfvtgt)
      hfvtgt))

/-- **`S.Ty` realizations are scoped** at any scoped context (the strong, `LegacyConsistent`-free
    form of `STyScoped`, under the explicit `EvalCtxScoped Ψ`). -/
theorem S.Ty.fv_subset_keyNames {Γ : NLCtx} {Ψ : EvalCtx} {τ : GLang.Ty} {τv : ValTy}
    (h : S.Ty Γ Ψ τ τv) (hΨ : EvalCtxScoped Ψ) : ValTy.fv τv ⊆ Ψ.keyNames := by
  revert hΨ; sfv_rec h

/-- **Basis-indexed `S.TyAt` realizations are scoped** at any scoped
    evaluation context. -/
theorem S.TyAt.fv_subset_keyNames {Γ : NLCtx} {Ψ : EvalCtx} {b : Basis} {τv : ValTy}
    (h : S.TyAt Γ Ψ b τv) (hΨ : EvalCtxScoped Ψ) : ValTy.fv τv ⊆ Ψ.keyNames := by
  revert hΨ; sfv_rec h

/-- **`S.Space` realizations are scoped.** -/
theorem S.Space.fv_subset_keyNames {Γ : NLCtx} {Ψ : EvalCtx} {s : GLang.Space} {sv : ValSpace}
    (h : S.Space Γ Ψ s sv) (hΨ : EvalCtxScoped Ψ) : ValSpace.fv sv ⊆ Ψ.keyNames := by
  revert hΨ; sfv_rec h

/-- **`S.Cob` change-of-basis values are scoped.** -/
theorem S.Cob.fv_subset_keyNames {Γ : NLCtx} {Ψ : EvalCtx} {b₀ b₁ : Basis} {env : ValExpr}
    (h : S.Cob Γ Ψ b₀ env b₁) (hΨ : EvalCtxScoped Ψ) : ValExpr.fv env ⊆ Ψ.keyNames := by
  revert hΨ; sfv_rec h

/-- **`S.Term` values AND their types are scoped** (joint form; the type half is needed by
    the induction itself — `appL_lin`/`appI_lin` read the contraction space off the operand's
    type). -/
theorem S.Term.fv_subset_keyNames_joint {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {e : GLang.Term}
    {b : Basis} {v : ValExpr} {τv : ValTy} (h : S.Term Δ Γ Ψ e b v τv) (hΨ : EvalCtxScoped Ψ) :
    ValExpr.fv v ⊆ Ψ.keyNames ∧ ValTy.fv τv ⊆ Ψ.keyNames := by
  revert hΨ; sfv_rec h

/-- **`S.Term` values are scoped.** -/
theorem S.Term.fv_subset_keyNames {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {e : GLang.Term} {b : Basis}
    {v : ValExpr} {τv : ValTy} (h : S.Term Δ Γ Ψ e b v τv) (hΨ : EvalCtxScoped Ψ) :
    ValExpr.fv v ⊆ Ψ.keyNames :=
  (h.fv_subset_keyNames_joint hΨ).1

/-- The produced value's TYPE is scoped too. -/
theorem S.Term.fv_ty_subset_keyNames {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {e : GLang.Term}
    {b : Basis} {v : ValExpr} {τv : ValTy} (h : S.Term Δ Γ Ψ e b v τv) (hΨ : EvalCtxScoped Ψ) :
    ValTy.fv τv ⊆ Ψ.keyNames :=
  (h.fv_subset_keyNames_joint hΨ).2

end GLang
