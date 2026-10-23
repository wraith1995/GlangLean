

import GLang.Proofs.Preservation.PreservationV2_EvalTSubst
import GLang.Proofs.Preservation.PreservationV2Helpers

namespace GLang

/-! ## The full ambient name-set of an `EvalCtx`: `avoid` + key-basis fv.

`EvalCtx.avoid` collects key NAMES and entry-value fv, but the rename transport also
substitutes through the stored KEY BASES (`ESubst.fwd` re-keys `(z, b)` to
`(z, Basis.subst y₀ (.var y) b)`), so the renamed-away name must be fresh for those
too. -/

/-- `EvalCtx.avoid Ψ` plus the free names of every key's basis component. A name
    outside `avoidB Ψ` is fresh for every name `Ψ` mentions: key names, stored
    values, AND stored key bases. -/
noncomputable def EvalCtx.avoidB (Ψ : EvalCtx) : Finset VName :=
  EvalCtx.avoid Ψ ∪ Ψ.keys.biUnion (fun kb => Basis.fv kb.2)

/-- Avoiding `avoidB Ψ` yields the three freshness facts the rename transport needs:
    fresh key name, fresh in every entry value, fresh in every key basis. -/
theorem EvalCtx.avoidB_spec {Ψ : EvalCtx} {y : VName} (hy : y ∉ EvalCtx.avoidB Ψ) :
    (∀ b, (y, b) ∉ Ψ) ∧
    (∀ k v, EvalCtx.lookup Ψ k = some v → y ∉ ValExpr.fv v) ∧
    (∀ z b, (z, b) ∈ Ψ → y ∉ Basis.fv b) := by
  rw [EvalCtx.avoidB, Finset.mem_union, not_or] at hy
  obtain ⟨hav, hbases⟩ := hy
  obtain ⟨hkeys, hvals⟩ := EvalCtx.avoid_spec hav
  refine ⟨hkeys, hvals, fun z b hmem hfv => ?_⟩
  exact hbases (Finset.mem_biUnion.mpr ⟨(z, b), Finmap.mem_keys.mpr hmem, hfv⟩)

/-! ## Lemma kit (5b): open-after-close is renaming-substitution.

`openRec k (.var y τ) v = v → openRec k (.var y τ) (closeRec k y₀ v) = subst y₀ (.var y τ) v`.

The companion of ValueLN kit (5) (`close_openVar`). The hypothesis (no `bvar k`
exposed at level `k`, in the precise form "opening with `.var y τ` at `k` is the
identity") is what `openRec_lc` supplies on locally-closed values. Both pipelines
replace an annotated occurrence `.var y₀ σ` by the SAME `.var y τ` (close forgets
`σ` and re-opening pins `τ`; `subst` discards `σ` wholesale), so no per-occurrence
annotation agreement is needed. -/

mutual

theorem ValSpace.openRec_closeRec_subst (y₀ y : VName) (τ : ValTy) :
    ∀ (s : ValSpace) (k : Nat), ValSpace.openRec k (.var y τ) s = s →
      ValSpace.openRec k (.var y τ) (ValSpace.closeRec k y₀ s)
        = ValSpace.subst y₀ (.var y τ) s
  | .empty, _, _ => rfl
  | .real, _, _ => rfl
  | .dsum s₀ s₁, k, h => by
      simp only [ValSpace.openRec, ValSpace.dsum.injEq] at h
      simp only [ValSpace.openRec, ValSpace.closeRec, ValSpace.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s₀ k h.1,
        ValSpace.openRec_closeRec_subst y₀ y τ s₁ k h.2]
  | .tprod s₀ s₁, k, h => by
      simp only [ValSpace.openRec, ValSpace.tprod.injEq] at h
      simp only [ValSpace.openRec, ValSpace.closeRec, ValSpace.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s₀ k h.1,
        ValSpace.openRec_closeRec_subst y₀ y τ s₁ k h.2]
  | .ffs p s e, k, h => by
      simp only [ValSpace.openRec, ValSpace.ffs.injEq, true_and] at h
      simp only [ValSpace.openRec, ValSpace.closeRec, ValSpace.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h.2]

theorem ValTy.openRec_closeRec_subst (y₀ y : VName) (τ : ValTy) :
    ∀ (σ : ValTy) (k : Nat), ValTy.openRec k (.var y τ) σ = σ →
      ValTy.openRec k (.var y τ) (ValTy.closeRec k y₀ σ) = ValTy.subst y₀ (.var y τ) σ
  | .space s, k, h => by
      simp only [ValTy.openRec, ValTy.space.injEq] at h
      simp only [ValTy.openRec, ValTy.closeRec, ValTy.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s k h]
  | .piTy τ₀ τ₁, k, h => by
      simp only [ValTy.openRec, ValTy.piTy.injEq] at h
      simp only [ValTy.openRec, ValTy.closeRec, ValTy.subst,
        ValTy.openRec_closeRec_subst y₀ y τ τ₀ k h.1,
        ValTy.openRec_closeRec_subst y₀ y τ τ₁ (k+1) h.2]

theorem ValExpr.openRec_closeRec_subst (y₀ y : VName) (τ : ValTy) :
    ∀ (e : ValExpr) (k : Nat), ValExpr.openRec k (.var y τ) e = e →
      ValExpr.openRec k (.var y τ) (ValExpr.closeRec k y₀ e)
        = ValExpr.subst y₀ (.var y τ) e
  | .bvar i, k, h => by
      by_cases hik : i = k
      · subst hik
        simp only [ValExpr.openRec] at h
        exact absurd h (by simp)
      · simp only [ValExpr.closeRec, ValExpr.openRec, if_neg hik, ValExpr.subst]
  | .var z σ, k, h => by
      simp only [ValExpr.openRec, ValExpr.var.injEq, true_and] at h
      by_cases hz : z = y₀
      · subst hz
        simp only [ValExpr.closeRec, ValExpr.openRec, ValExpr.subst, ↓reduceIte]
      · simp only [ValExpr.closeRec, ValExpr.openRec, ValExpr.subst,
          if_neg hz, ValExpr.var.injEq, true_and]
        exact ValTy.openRec_closeRec_subst y₀ y τ σ k h
  | .vlam τ₀ τ₁ e, k, h => by
      simp only [ValExpr.openRec, ValExpr.vlam.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValTy.openRec_closeRec_subst y₀ y τ τ₀ k h.1,
        ValTy.openRec_closeRec_subst y₀ y τ τ₁ (k+1) h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e (k+1) h.2.2]
  | .zero s, k, h => by
      simp only [ValExpr.openRec, ValExpr.zero.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s k h]
  | .rlit _, _, _ => rfl
  | .scale e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.scale.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2]
  | .vadd s e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.vadd.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2.2]
  | .dsumE e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.dsumE.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2]
  | .tprodE e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.tprodE.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2]
  | .delta n s, k, h => by
      simp only [ValExpr.openRec, ValExpr.delta.injEq, true_and] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s k h]
  | .idelta s, k, h => by
      simp only [ValExpr.openRec, ValExpr.idelta.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s k h]
  | .vsum s es, k, h => by
      simp only [ValExpr.openRec, ValExpr.vsum.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s k h.1,
        ValExpr.openList_closeList_subst y₀ y τ es k h.2]
  | .ttv s e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.ttv.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2.2]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.mtm.injEq, true_and] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValSpace.openRec_closeRec_subst y₀ y τ s₀ k h.1,
        ValSpace.openRec_closeRec_subst y₀ y τ s₁ k h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.2.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2.2.2]
  | .appV e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.appV.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2]
  | .vkrn e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.vkrn.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2]
  | .vblk e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.vblk.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2]
  | .reshap e σ σ₀, k, h => by
      simp only [ValExpr.openRec, ValExpr.reshap.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h.1,
        ValTy.openRec_closeRec_subst y₀ y τ σ k h.2.1,
        ValTy.openRec_closeRec_subst y₀ y τ σ₀ k h.2.2]
  | .vtrans e, k, h => by
      simp only [ValExpr.openRec, ValExpr.vtrans.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h]
  | .gsvdS e a b, k, h => by
      simp only [ValExpr.openRec, ValExpr.gsvdS.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ a k h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ b k h.2.2]
  | .gsvdU e a b, k, h => by
      simp only [ValExpr.openRec, ValExpr.gsvdU.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ a k h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ b k h.2.2]
  | .gsvdUI e a b, k, h => by
      simp only [ValExpr.openRec, ValExpr.gsvdUI.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ a k h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ b k h.2.2]
  | .gsvdV e a b, k, h => by
      simp only [ValExpr.openRec, ValExpr.gsvdV.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ a k h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ b k h.2.2]
  | .gsvdVI e a b, k, h => by
      simp only [ValExpr.openRec, ValExpr.gsvdVI.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ a k h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ b k h.2.2]
  | .pinv e, k, h => by
      simp only [ValExpr.openRec, ValExpr.pinv.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h]
  | .gpinv e a b, k, h => by
      simp only [ValExpr.openRec, ValExpr.gpinv.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ a k h.2.1,
        ValExpr.openRec_closeRec_subst y₀ y τ b k h.2.2]
  | .rrefRep e₀ e₁, k, h => by
      simp only [ValExpr.openRec, ValExpr.rrefRep.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e₀ k h.1,
        ValExpr.openRec_closeRec_subst y₀ y τ e₁ k h.2]
  | .inv e, k, h => by
      simp only [ValExpr.openRec, ValExpr.inv.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h]
  | .svds e, k, h => by
      simp only [ValExpr.openRec, ValExpr.svds.injEq] at h
      simp only [ValExpr.openRec, ValExpr.closeRec, ValExpr.subst,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h]

theorem ValExpr.openList_closeList_subst (y₀ y : VName) (τ : ValTy) :
    ∀ (es : List ValExpr) (k : Nat), ValExpr.openRecList k (.var y τ) es = es →
      ValExpr.openRecList k (.var y τ) (ValExpr.closeRecList k y₀ es)
        = ValExpr.substList y₀ (.var y τ) es
  | [], _, _ => rfl
  | e :: es, k, h => by
      simp only [ValExpr.openRecList, List.cons.injEq] at h
      simp only [ValExpr.openRecList, ValExpr.closeRecList, ValExpr.substList,
        ValExpr.openRec_closeRec_subst y₀ y τ e k h.1,
        ValExpr.openList_closeList_subst y₀ y τ es k h.2]

end

/-- `openVar`-form corollary on locally-closed value types: re-opening the
    `y₀`-closure of `σ` at `y` IS the renaming substitution. -/
theorem ValTy.openVar_closeRec_of_lc (y₀ y : VName) (τ : ValTy) {σ : ValTy}
    (h : ValTy.lc σ) :
    ValTy.openVar y τ (ValTy.closeRec 0 y₀ σ) = ValTy.subst y₀ (.var y τ) σ :=
  ValTy.openRec_closeRec_subst y₀ y τ σ 0 (ValTy.openRec_lc h 0 _)

/-- `openVar`-form corollary on locally-closed value expressions. -/
theorem ValExpr.openVar_closeRec_of_lc (y₀ y : VName) (τ : ValTy) {e : ValExpr}
    (h : ValExpr.lc e) :
    ValExpr.openVar y τ (ValExpr.closeRec 0 y₀ e) = ValExpr.subst y₀ (.var y τ) e :=
  ValExpr.openRec_closeRec_subst y₀ y τ e 0 (ValExpr.openRec_lc h 0 _)

/-! ## The rename `ESubst`: `y₀ ↦ y` as a context substitution. -/

/-- **Renaming as `ESubst`** (the P3 risk-retirement result): discharging the
    placeholder `(y₀, b₀) ↦ .var y₀ τv₀` by substituting `y₀ ↦ .var y` (source) /
    `.var y τv₀` (value) is an `ESubst` into the context re-keyed at `y`. The
    variable cut is `OpStep.var` at the fresh `(y, b₀)` binding; the boundary is
    transported by `subst_fresh` (`y₀` fresh for everything `Ψ` mentions, via
    `avoidB`). `y = y₀` is allowed (the transport degenerates to the identity). -/
theorem ESubst.rename {Ψ : EvalCtx} {b₀ : Basis} {τv₀ : ValTy} {y₀ y : VName}
    (hy₀ : y₀ ∉ EvalCtx.avoidB Ψ) (hy : y ∉ EvalCtx.avoidB Ψ)
    (hy₀b₀ : y₀ ∉ Basis.fv b₀) (hy₀τv₀ : y₀ ∉ ValTy.fv τv₀)
    (hlcτv₀ : ValTy.lc τv₀) :
    ESubst y₀ b₀ τv₀ (.var y) (.var y τv₀)
      (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀))
      (EvalCtx.extend Ψ y b₀ (.var y τv₀)) := by
  obtain ⟨hy₀keys, hy₀vals, hy₀bases⟩ := EvalCtx.avoidB_spec hy₀
  obtain ⟨hykeys, -, -⟩ := EvalCtx.avoidB_spec hy
  refine ⟨?_, ?_, ?_, ?_, .var, .var hlcτv₀, ?_, ?_⟩
  · -- xbind: the placeholder is the inserted binding.
    rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert]
  · -- xonly: `y₀` is not a key name of `Ψ`, so only the inserted binding matches.
    intro b' v' hl
    by_cases hk : ((y₀ : VName), b') = (y₀, b₀)
    · exact (Prod.mk.inj hk).2
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      exact absurd (Finmap.mem_of_lookup_eq_some hl) (hy₀keys b')
  · -- hcut: `.var y` realizes at `b₀` via the freshly inserted binding.
    rw [Basis.subst_fresh y₀ (.var y) b₀ hy₀b₀]
    exact .var (by rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert])
  · -- fwd: boundary bindings are `y₀`-free (keys AND values), so they transport
    -- unchanged; their key name differs from `y` (fresh key name).
    intro z b v hzx hl
    rw [EvalCtx.extend, EvalCtx.lookup,
      Finmap.lookup_insert_of_ne _ (fun hk => hzx (congrArg Prod.fst hk))] at hl
    have hmem := Finmap.mem_of_lookup_eq_some hl
    have hzy : z ≠ y := fun hzy => hykeys b (hzy ▸ hmem)
    rw [Basis.subst_fresh y₀ (.var y) b (hy₀bases z b hmem),
      ValExpr.subst_fresh y₀ (.var y τv₀) v (hy₀vals (z, b) v hl),
      EvalCtx.extend, EvalCtx.lookup,
      Finmap.lookup_insert_of_ne _ (fun hk => hzy (congrArg Prod.fst hk))]
    exact hl
  · -- hinfer: placeholder via `spaceOf` fv-projection; boundary via fv-freshness.
    intro z b v hl
    by_cases hk : ((z : VName), b) = (y₀, b₀)
    · rw [hk] at hl
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      simp only [ValExpr.subst, ↓reduceIte, ValExpr.inferSpace]
      rw [ValSpace.subst_fresh y₀ (.var y τv₀) (ValTy.spaceOf τv₀)
        (fun hmem => hy₀τv₀ (ValSpace.fv_spaceOf_subset τv₀ hmem))]
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      have hy₀v : y₀ ∉ ValExpr.fv v := hy₀vals (z, b) v hl
      rw [ValExpr.subst_fresh y₀ (.var y τv₀) v hy₀v,
        ValSpace.subst_fresh y₀ (.var y τv₀) (ValExpr.inferSpace v)
          (fun hmem => hy₀v (ValExpr.fv_inferSpace_subset v hmem))]

  · intro z b v hl
    unfold InferTypeSubstAt
    by_cases hk : ((z : VName), b) = (y₀, b₀)
    · rw [hk] at hl
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      simp only [ValExpr.subst, ↓reduceIte, ValExpr.inferType]
      exact (ValTy.subst_fresh y₀ (.var y τv₀) τv₀ hy₀τv₀).symm
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      have hy₀v : y₀ ∉ ValExpr.fv v := hy₀vals (z, b) v hl
      rw [ValExpr.subst_fresh y₀ (.var y τv₀) v hy₀v,
        ValTy.subst_fresh y₀ (.var y τv₀) (ValExpr.inferType v)
          (fun hmem => hy₀v (ValExpr.fv_inferType_subset v hmem))]

/-- Discharge a fresh symbolic linear variable to a concrete coordinate.
    The source context stores `.var x (.space sv)` so the ordinary progress
    induction can evaluate the body once.  The target context stores
    `.delta i sv`; substituting that delta for `x` turns the one symbolic run
    into the `i`-th concrete column. -/
theorem ESubst.delta {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    {x y : VName} {i : Nat}
    (hx : x ∉ EvalCtx.avoidB Ψ) (hy : y ∉ EvalCtx.avoidB Ψ)
    (hxb : x ∉ Basis.fv b) (hxsv : x ∉ ValSpace.fv sv)
    (hlcsv : ValSpace.lc sv) :
    ESubst x b (.space sv) (.var y) (.delta i sv)
      (EvalCtx.extend Ψ x b (.var x (.space sv)))
      (EvalCtx.extend Ψ y b (.delta i sv)) := by
  obtain ⟨hxkeys, hxvals, hxbases⟩ := EvalCtx.avoidB_spec hx
  obtain ⟨hykeys, -, -⟩ := EvalCtx.avoidB_spec hy
  refine ⟨?_, ?_, ?_, ?_, .var, .delta hlcsv, ?_, ?_⟩
  · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert]
  · intro b' v' hl
    by_cases hk : ((x : VName), b') = (x, b)
    · exact (Prod.mk.inj hk).2
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      exact absurd (Finmap.mem_of_lookup_eq_some hl) (hxkeys b')
  · rw [Basis.subst_fresh x (.var y) b hxb]
    exact .var (by rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert])
  · intro z b' v hzx hl
    rw [EvalCtx.extend, EvalCtx.lookup,
      Finmap.lookup_insert_of_ne _ (fun hk => hzx (congrArg Prod.fst hk))] at hl
    have hmem := Finmap.mem_of_lookup_eq_some hl
    have hzy : z ≠ y := fun hzy => hykeys b' (hzy ▸ hmem)
    rw [Basis.subst_fresh x (.var y) b' (hxbases z b' hmem),
      ValExpr.subst_fresh x (.delta i sv) v (hxvals (z, b') v hl),
      EvalCtx.extend, EvalCtx.lookup,
      Finmap.lookup_insert_of_ne _ (fun hk => hzy (congrArg Prod.fst hk))]
    exact hl
  · intro z b' v hl
    by_cases hk : ((z : VName), b') = (x, b)
    · rw [hk] at hl
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      simp only [ValExpr.subst, ↓reduceIte, ValExpr.inferSpace, ValTy.spaceOf]
      exact (ValSpace.subst_fresh x (.delta i sv) sv hxsv).symm
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      have hxv : x ∉ ValExpr.fv v := hxvals (z, b') v hl
      rw [ValExpr.subst_fresh x (.delta i sv) v hxv,
        ValSpace.subst_fresh x (.delta i sv) (ValExpr.inferSpace v)
          (fun hmem => hxv (ValExpr.fv_inferSpace_subset v hmem))]

  · intro z b' v hl
    unfold InferTypeSubstAt
    by_cases hk : ((z : VName), b') = (x, b)
    · rw [hk] at hl
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      simp only [ValExpr.subst, ↓reduceIte, ValExpr.inferType, ValTy.subst]
      exact congrArg ValTy.space (ValSpace.subst_fresh x (.delta i sv) sv hxsv).symm
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      have hxv : x ∉ ValExpr.fv v := hxvals (z, b') v hl
      rw [ValExpr.subst_fresh x (.delta i sv) v hxv,
        ValTy.subst_fresh x (.delta i sv) (ValExpr.inferType v)
          (fun hmem => hxv (ValExpr.fv_inferType_subset v hmem))]

/-! ## Single-name rename transports (subst form). -/

/-- Rename the binder key of an `EvalT` derivation under an extended context:
    `y₀ → y`, substituting throughout. Subst-form; the packaging lemmas below
    restore the `openVar` shapes. -/
theorem evalT_rename_of_fresh {Ψ : EvalCtx} {b₀ : Basis} {τv₀ : ValTy}
    {τ : Ty} {τv : ValTy} {y₀ y : VName}
    (h : ValTy.EvalT (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀)) τ τv)
    (hy₀ : y₀ ∉ EvalCtx.avoidB Ψ) (hy : y ∉ EvalCtx.avoidB Ψ)
    (hy₀b₀ : y₀ ∉ Basis.fv b₀) (hy₀τv₀ : y₀ ∉ ValTy.fv τv₀)
    (hlcτv₀ : ValTy.lc τv₀) :
    ValTy.EvalT (EvalCtx.extend Ψ y b₀ (.var y τv₀))
      (Ty.subst y₀ (.var y) τ) (ValTy.subst y₀ (.var y τv₀) τv) :=
  evalT_substC h (ESubst.rename hy₀ hy hy₀b₀ hy₀τv₀ hlcτv₀)

/-- Rename the binder key of an `OpStep` derivation under an extended context. -/
theorem opStep_rename_of_fresh {Ψ : EvalCtx} {b₀ : Basis} {τv₀ : ValTy}
    {e : Term} {b : Basis} {v : ValExpr} {y₀ y : VName}
    (h : ValExpr.OpStep (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀)) e b v)
    (hy₀ : y₀ ∉ EvalCtx.avoidB Ψ) (hy : y ∉ EvalCtx.avoidB Ψ)
    (hy₀b₀ : y₀ ∉ Basis.fv b₀) (hy₀τv₀ : y₀ ∉ ValTy.fv τv₀)
    (hlcτv₀ : ValTy.lc τv₀) :
    ValExpr.OpStep (EvalCtx.extend Ψ y b₀ (.var y τv₀))
      (Term.subst y₀ (.var y) e) (Basis.subst y₀ (.var y) b)
      (ValExpr.subst y₀ (.var y τv₀) v) :=
  opStep_substC h (ESubst.rename hy₀ hy hy₀b₀ hy₀τv₀ hlcτv₀)

/-- Turn one symbolic linear-body evaluation into a concrete coordinate
    evaluation.  Unlike alpha-renaming a concrete-delta run, the output is
    allowed to mention the symbolic variable: substituting `.delta i sv`
    produces the fixed `i`-th column result. -/
theorem ValExpr.OpStep.delta_of_placeholder
    {Ψ : EvalCtx} {x y : VName} {b bout : Basis} {sv : ValSpace}
    {i : Nat} {e : Term} {v : ValExpr}
    (h : ValExpr.OpStep (EvalCtx.extend Ψ x b (.var x (.space sv)))
      (Term.openVar x e) bout v)
    (hxΨ : x ∉ EvalCtx.avoidB Ψ) (hyΨ : y ∉ EvalCtx.avoidB Ψ)
    (hxb : x ∉ Basis.fv b) (hxsv : x ∉ ValSpace.fv sv)
    (hxe : x ∉ Term.fv e) (hxo : x ∉ Basis.fv bout)
    (hlcsv : ValSpace.lc sv) :
    ValExpr.OpStep (EvalCtx.extend Ψ y b (.delta i sv))
      (Term.openVar y e) bout (ValExpr.subst x (.delta i sv) v) := by
  have hrec := opStep_substC h
    (ESubst.delta (i := i) hxΨ hyΨ hxb hxsv hlcsv)
  rw [show Term.subst x (.var y) (Term.openVar x e) = Term.openVar y e from
      (Term.subst_intro x (.var y) e hxe 0).symm,
    Basis.subst_fresh x (.var y) bout hxo] at hrec
  exact hrec

/-! ## Tier-1 packaging: `EvalT` exists-fresh → cofinite (what `EvalT.piTy`'s `h₁`
and `OpStep.nllam`/`frame_eta`'s `h₁` consume). -/

/-- **`EvalT` cofinite packaging.** From a realization of the `y₀`-opened codomain
    at the single fresh name `y₀`, produce the cofinite premise of
    `ValTy.EvalT.piTy` (and of `OpStep.nllam`/`frame_eta`'s `h₁`, with
    `τ₁ := Basis.tof b₁`), with body `ValTy.closeRec 0 y₀ τv₁`.

    Avoid set for `y₀`: `EvalCtx.avoidB Ψ` (key names + entry values + key bases)
    plus the fv of the participants `b₀`, `τv₀`, `τ₁`. The `lc` side conditions
    are discharged by the caller from `realize_lc_joint`. -/
theorem evalT_cofinite_of_fresh {Ψ : EvalCtx} {b₀ : Basis} {τv₀ τv₁ : ValTy}
    {τ₁ : Ty} {y₀ : VName}
    (h : ValTy.EvalT (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀)) (Ty.openVar y₀ τ₁) τv₁)
    (hy₀Ψ : y₀ ∉ EvalCtx.avoidB Ψ) (hy₀b₀ : y₀ ∉ Basis.fv b₀)
    (hy₀τv₀ : y₀ ∉ ValTy.fv τv₀) (hy₀τ₁ : y₀ ∉ Ty.fv τ₁)
    (hlcτv₀ : ValTy.lc τv₀) (hlcτv₁ : ValTy.lc τv₁) :
    ∃ L : Finset VName, ∀ y, y ∉ L →
      ValTy.EvalT (EvalCtx.extend Ψ y b₀ (.var y τv₀)) (Ty.openVar y τ₁)
        (ValTy.openVar y τv₀ (ValTy.closeRec 0 y₀ τv₁)) := by
  refine ⟨EvalCtx.avoidB Ψ, fun y hy => ?_⟩
  have hrec := evalT_rename_of_fresh h hy₀Ψ hy hy₀b₀ hy₀τv₀ hlcτv₀
  rw [show Ty.subst y₀ (.var y) (Ty.openVar y₀ τ₁) = Ty.openVar y τ₁ from
    (Ty.subst_intro y₀ (.var y) τ₁ hy₀τ₁ 0).symm] at hrec
  rw [ValTy.openVar_closeRec_of_lc y₀ y τv₀ hlcτv₁]
  exact hrec

/-! ## Tier-2 packaging: `OpStep` exists-fresh → cofinite (the `he` premises of
`OpStep.nllam` and `OpStep.frame_eta`). -/

/-- **`OpStep` cofinite packaging, `nllam` shape.** From a single-fresh-`y₀`
    realization of the opened body `Term.openVar y₀ e` at the opened codomain
    basis `Basis.openVar y₀ b₁`, produce `OpStep.nllam`'s cofinite `he` premise,
    with body `ValExpr.closeRec 0 y₀ v`. -/
theorem opStep_nllam_cofinite_of_fresh {Ψ : EvalCtx} {b₀ b₁ : Basis} {τv₀ : ValTy}
    {e : Term} {v : ValExpr} {y₀ : VName}
    (h : ValExpr.OpStep (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀))
      (Term.openVar y₀ e) (Basis.openVar y₀ b₁) v)
    (hy₀Ψ : y₀ ∉ EvalCtx.avoidB Ψ) (hy₀b₀ : y₀ ∉ Basis.fv b₀)
    (hy₀τv₀ : y₀ ∉ ValTy.fv τv₀) (hy₀e : y₀ ∉ Term.fv e) (hy₀b₁ : y₀ ∉ Basis.fv b₁)
    (hlcτv₀ : ValTy.lc τv₀) (hlcv : ValExpr.lc v) :
    ∃ L : Finset VName, ∀ y, y ∉ L →
      ValExpr.OpStep (EvalCtx.extend Ψ y b₀ (.var y τv₀))
        (Term.openVar y e) (Basis.openVar y b₁)
        (ValExpr.openVar y τv₀ (ValExpr.closeRec 0 y₀ v)) := by
  refine ⟨EvalCtx.avoidB Ψ, fun y hy => ?_⟩
  have hrec := opStep_rename_of_fresh h hy₀Ψ hy hy₀b₀ hy₀τv₀ hlcτv₀
  rw [show Term.subst y₀ (.var y) (Term.openVar y₀ e) = Term.openVar y e from
      (Term.subst_intro y₀ (.var y) e hy₀e 0).symm,
    show Basis.subst y₀ (.var y) (Basis.openVar y₀ b₁) = Basis.openVar y b₁ from
      (Basis.subst_intro y₀ (.var y) b₁ hy₀b₁ 0).symm] at hrec
  rw [ValExpr.openVar_closeRec_of_lc y₀ y τv₀ hlcv]
  exact hrec

/-- **`OpStep` cofinite packaging, `frame_eta` shape.** From a single-fresh-`y₀`
    evaluation of the η-application `n₀ (.var y₀)` at the opened codomain basis,
    produce `OpStep.frame_eta`'s cofinite `he` premise. -/
theorem opStep_frame_eta_cofinite_of_fresh {Ψ : EvalCtx} {b₀ b₁ : Basis}
    {τv₀ : ValTy} {n₀ : Term} {v : ValExpr} {y₀ : VName}
    (h : ValExpr.OpStep (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀))
      (.appN n₀ (.var y₀)) (Basis.openVar y₀ b₁) v)
    (hy₀Ψ : y₀ ∉ EvalCtx.avoidB Ψ) (hy₀b₀ : y₀ ∉ Basis.fv b₀)
    (hy₀τv₀ : y₀ ∉ ValTy.fv τv₀) (hy₀n₀ : y₀ ∉ Term.fv n₀) (hy₀b₁ : y₀ ∉ Basis.fv b₁)
    (hlcτv₀ : ValTy.lc τv₀) (hlcv : ValExpr.lc v) :
    ∃ L : Finset VName, ∀ y, y ∉ L →
      ValExpr.OpStep (EvalCtx.extend Ψ y b₀ (.var y τv₀))
        (.appN n₀ (.var y)) (Basis.openVar y b₁)
        (ValExpr.openVar y τv₀ (ValExpr.closeRec 0 y₀ v)) := by
  refine ⟨EvalCtx.avoidB Ψ, fun y hy => ?_⟩
  have hrec := opStep_rename_of_fresh h hy₀Ψ hy hy₀b₀ hy₀τv₀ hlcτv₀
  rw [show Term.subst y₀ (.var y) (.appN n₀ (.var y₀)) = Term.appN n₀ (.var y) by
      simp only [Term.subst, ↓reduceIte, Term.subst_fresh y₀ (.var y) n₀ hy₀n₀],
    show Basis.subst y₀ (.var y) (Basis.openVar y₀ b₁) = Basis.openVar y b₁ from
      (Basis.subst_intro y₀ (.var y) b₁ hy₀b₁ 0).symm] at hrec
  rw [ValExpr.openVar_closeRec_of_lc y₀ y τv₀ hlcv]
  exact hrec

end GLang
