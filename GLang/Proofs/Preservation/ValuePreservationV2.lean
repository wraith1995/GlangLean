

import GLang.Proofs.Value.Typing.ValueValidC
import GLang.Operational.Ordinary
import GLang.Annotated.Judgments
import GLang.Proofs.Source.FreeVars
import GLang.Proofs.Basis.Binding
import GLang.Proofs.Preservation.EvalTKind
import GLang.Proofs.Source.SourceTypingInv
import GLang.Proofs.Value.Binding.ValueWeakening
import GLang.Proofs.Preservation.PreservationV2Helpers
import GLang.Proofs.Preservation.PreservationV2_DsumTprod
import GLang.Proofs.Preservation.PreservationV2_Reshape
import GLang.Proofs.Preservation.PreservationV2_FFS
import GLang.Proofs.Preservation.PreservationV2_EvalBBCross
import GLang.Proofs.Preservation.PreservationV2_EvalTSubst
import GLang.Proofs.Value.Typing.ValueRealizeLc
import GLang.Proofs.Source.Soundness

namespace GLang

/-- The variable names bound by `Ψ` (project the `VName` out of `(VName × Basis)`). -/
noncomputable def EvalCtx.keyNames (Ψ : EvalCtx) : Finset VName :=
  Ψ.keys.image Prod.fst

end GLang

namespace GLang.V2

abbrev ValScope := Finset VName

/-! ## The five environment judgments (all explicit; see the plan §3). -/

structure CtxWF' (Δ : LCtx) (Γ : NLCtx) : Prop where
  disjoint  : ∀ x, x ∈ Δ → x ∉ Γ
  lin_fv    : ∀ x s, Δ.lookup x = some s → Space.fv s ⊆ Γ.keys
  nl_fv     : ∀ x τ, Γ.lookup x = some τ → Ty.fv τ ⊆ Γ.keys
  lin_valid : ∀ x s, Δ.lookup x = some s → Nonempty (SValid Γ s)
  nl_valid  : ∀ x τ, Γ.lookup x = some τ → ∃ k, Nonempty (TValid Γ τ k)

def EvalCtxValid (Ψ : EvalCtx) : Prop :=
  ∀ x b v, EvalCtx.lookup Ψ (x, b) = some v →
        Basis.fv b ⊆ Ψ.keyNames
      ∧ ValExpr.fv v ⊆ Ψ.keyNames
      ∧ ValTy.EvalT Ψ (Basis.tof b) (ValExpr.inferType v)

def EvalCtxLamAnchored (Ψ : EvalCtx) : Prop :=
  ∀ x b₀ b₁ τv₀ τv₁ body,
    EvalCtx.lookup Ψ (x, .frame b₀ b₁) = some (.vlam τv₀ τv₁ body) →
    ∃ L : Finset VName, ∀ y, y ∉ L →
      ValTy.EvalT (EvalCtx.extend Ψ y b₀ (.var y τv₀))
        (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁)

def EvalCtxValidPlus (Ψ : EvalCtx) : Prop :=
  ∀ x b v, EvalCtx.lookup Ψ (x, b) = some v →
        ValExpr.fv v ⊆ Ψ.keyNames
      ∧ ValTy.EvalT Ψ (Basis.tof b) (ValExpr.inferType v)
      ∧ ValTy.fv (ValExpr.inferType v) ⊆ Ψ.keyNames
      ∧ ValExpr.lc v
      ∧ (∀ b₀ b₁ τv₀ τv₁ body, b = .frame b₀ b₁ → v = .vlam τv₀ τv₁ body →
          ∃ L : Finset VName, ∀ y, y ∉ L →
            ValTy.EvalT (EvalCtx.extend Ψ y b₀ (.var y τv₀))
              (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁))

/-- `EvalCtxValidPlus` stores `lc` values — the threaded form of `EvalCtxLc`. -/
theorem EvalCtxValidPlus.toEvalCtxLc {Ψ : EvalCtx} (h : EvalCtxValidPlus Ψ) :
    EvalCtxLc Ψ := fun k v hlk => (h k.1 k.2 v (by simpa using hlk)).2.2.2.1

def RhoValid (Ψ : EvalCtx) (ρ : ValScope) : Prop :=
  ∀ x b v, x ∈ ρ → EvalCtx.lookup Ψ (x, b) = some v →
        ValTyOk (ValExpr.inferType v)                 -- ⊢ τv
      ∧ ValTy.fv (ValExpr.inferType v) ⊆ ρ            -- fv(τv) ⊆ ρ   (telescope)
      ∧ ValExpr.fv v ⊆ ρ                              -- v ∈ ⟦τv⟧ρ    (syntactic)

/-- Operational-context typing. The `tof b = τ` clauses relate the inferred value type to the source type. -/
def TypingImplyEval (Δ : LCtx) (Γ : NLCtx) (Ψ : EvalCtx) : Prop :=
      (∀ x, (x ∈ Δ ∨ x ∈ Γ) ↔ ∃ b, (x, b) ∈ Ψ)
    ∧ (∀ x s b, Δ.lookup x = some s → (x, b) ∈ Ψ → Basis.tof b = .space s)
    ∧ (∀ x τ b, Γ.lookup x = some τ → (x, b) ∈ Ψ → Basis.tof b = τ)
    ∧ (∀ x b, (x, b) ∈ Ψ → Basis.BasisValid Γ b)

def ScopeImplyVal (Δ : LCtx) (Γ : NLCtx) (ρ : ValScope) : Prop :=
  ∀ x, (x ∈ Δ ∨ x ∈ Γ) ↔ x ∈ ρ

/-- The THREADABLE scope fragment (R5): `keyNames Ψ ⊆ ρ`. This is `Ψ`/`ρ`-only —
    it has NO `Δ`/`Γ` dependence, so it survives linear-context splitting and
    `promote` *trivially* (those don't touch `Ψ` or `ρ`), and even binder
    extension (`Ψ` and `ρ` grow by the same name). The var leaf gets `x ∈ ρ` from
    its value's `Ψ`-lookup (`x ∈ keyNames Ψ`) — no source-context membership
    needed. Both `TypingImplyEval` and `ScopeImplyVal` (and `CtxWF'`) are dropped
    from the motive; `KeyScope` is derived from them at the boundary. -/
def KeyScope (Ψ : EvalCtx) (ρ : ValScope) : Prop := Ψ.keyNames ⊆ ρ

/-- Boundary derivation: the strong `Γ⊢Ψ` + `Γ,Ψ⊢ρ` give `keyNames Ψ ⊆ ρ`. -/
theorem keyScope_of {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {ρ : ValScope}
    (hΓΨ : TypingImplyEval Δ Γ Ψ) (hΓΨρ : ScopeImplyVal Δ Γ ρ) : KeyScope Ψ ρ := by
  intro x hx
  rw [EvalCtx.keyNames, Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact (hΓΨρ p.1).mp ((hΓΨ.1 p.1).mpr ⟨p.2, by simpa using Finmap.mem_keys.mp hp⟩)

/-- A bound key-name is in `keyNames`. -/
theorem mem_keyNames_of_lookup {Ψ : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
    (hlk : EvalCtx.lookup Ψ (x, b) = some v) : x ∈ Ψ.keyNames :=
  Finset.mem_image.mpr
    ⟨(x, b), Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hlk), rfl⟩

theorem evalCtxValidPlus_of {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {ρ : ValScope}
    (hΨ : EvalCtxValid Ψ) (hΨlc : EvalCtxLc Ψ) (hanch : EvalCtxLamAnchored Ψ)
    (hρ : RhoValid Ψ ρ)
    (hΓΨ : TypingImplyEval Δ Γ Ψ) (hΓΨρ : ScopeImplyVal Δ Γ ρ) :
    EvalCtxValidPlus Ψ := by
  have hsup : ρ ⊆ Ψ.keyNames := by
    intro x hx
    obtain ⟨b, hb⟩ := (hΓΨ.1 x).mp ((hΓΨρ x).mpr hx)
    exact Finset.mem_image.mpr ⟨(x, b), Finmap.mem_keys.mpr hb, rfl⟩
  intro x b v hlk
  obtain ⟨_, hvfv, hevT⟩ := hΨ x b v hlk
  have hxρ : x ∈ ρ := (keyScope_of hΓΨ hΓΨρ) (mem_keyNames_of_lookup hlk)
  obtain ⟨_, hτfv, _⟩ := hρ x b v hxρ hlk
  exact ⟨hvfv, hevT, hτfv.trans hsup, hΨlc (x, b) v hlk,
    fun b₀ b₁ τv₀ τv₁ body hb hv => hanch x b₀ b₁ τv₀ τv₁ body (hb ▸ hv ▸ hlk)⟩

/-! ## The statements.

The four `preservation_*` parts live BELOW `preservation_master` (the shared
four-conjunct induction) as corollaries — see the end of this file. -/

/-- `tof b = .space s ⟹ sof b = s` (only `.frame` has a non-`.space` `tof`). -/
theorem sof_of_tof_eq_space {b : Basis} {s : Space}
    (h : Basis.tof b = .space s) : Basis.sof b = s := by
  cases b <;> simp_all [Basis.tof]

/-- `x ∈ ρ` for a variable whose value `Ψ` binds, via `KeyScope`. -/
theorem mem_scope_of_lookup {Ψ : EvalCtx} {ρ : ValScope} {x : VName} {b : Basis}
    {v : ValExpr} (hkey : KeyScope Ψ ρ) (hlk : EvalCtx.lookup Ψ (x, b) = some v) :
    x ∈ ρ :=
  hkey (Finset.mem_image_of_mem Prod.fst
    (Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some hlk)))

/-! ## Binder-extension helpers (for the `piTy`/`nllam` arms). -/

/-- `keyNames` after a binder extension grows by exactly the new name. -/
theorem keyNames_extend (Ψ : EvalCtx) (y : VName) (b : Basis) (v : ValExpr) :
    EvalCtx.keyNames (EvalCtx.extend Ψ y b v) = insert y (EvalCtx.keyNames Ψ) := by
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

/-- `EvalCtxValidPlus` survives extension by an arbitrary well-formed stored entry.
    The final premise is precisely the new entry's local frame anchoring obligation;
    surviving entries are weakened and their anchors transported past the fresh insert. -/
theorem evalCtxValidPlus_extend_value {Ψ : EvalCtx} {y : VName} {b₀ : Basis}
    {v₀ : ValExpr} (hΨ : EvalCtxValidPlus Ψ) (hfresh : (y, b₀) ∉ Ψ)
    (hvfv : ValExpr.fv v₀ ⊆ (EvalCtx.extend Ψ y b₀ v₀).keyNames)
    (hev : ValTy.EvalT Ψ (Basis.tof b₀) (ValExpr.inferType v₀))
    (hτfv : ValTy.fv (ValExpr.inferType v₀) ⊆ Ψ.keyNames)
    (hlc : ValExpr.lc v₀)
    (hanchor : ∀ c₀ c₁ τw₀ τw₁ body,
      b₀ = .frame c₀ c₁ → v₀ = .vlam τw₀ τw₁ body →
      ∃ L : Finset VName, ∀ z, z ∉ L →
        ValTy.EvalT (EvalCtx.extend (EvalCtx.extend Ψ y b₀ v₀) z c₀ (.var z τw₀))
          (Ty.openVar z (Basis.tof c₁)) (ValTy.openVar z τw₀ τw₁)) :
    EvalCtxValidPlus (EvalCtx.extend Ψ y b₀ v₀) := by
  have hkn := keyNames_extend Ψ y b₀ v₀
  intro x b v hlk
  simp only [EvalCtx.extend, EvalCtx.lookup] at hlk
  by_cases hk : (x, b) = (y, b₀)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
    rw [Finmap.lookup_insert, Option.some.injEq] at hlk
    subst hlk
    refine ⟨hvfv, evalT_wk hev hfresh, ?_, hlc, hanchor⟩
    rw [hkn]
    exact hτfv.trans (Finset.subset_insert _ _)
  · rw [Finmap.lookup_insert_of_ne _ hk] at hlk
    obtain ⟨hvfv', hevT, hτfv, hlc', hanch⟩ := hΨ x b v hlk
    rw [hkn]
    refine ⟨hvfv'.trans (Finset.subset_insert _ _), evalT_wk hevT hfresh,
      hτfv.trans (Finset.subset_insert _ _), hlc', ?_⟩
    intro c₀ c₁ τw₀ τw₁ body hbf hvf
    obtain ⟨L, hL⟩ := hanch c₀ c₁ τw₀ τw₁ body hbf hvf
    refine ⟨insert y L, fun z hz => ?_⟩
    rw [Finset.mem_insert, not_or] at hz
    have hne : (y, b₀) ≠ (z, c₀) := fun h => hz.1 (congrArg Prod.fst h).symm
    have hfresh' : (y, b₀) ∉ EvalCtx.extend Ψ z c₀ (.var z τw₀) := by
      rw [EvalCtx.extend]
      exact fun h => (Finmap.mem_insert.mp h).elim hne hfresh
    exact evalctx_extend_comm hne ▸ evalT_wk (hL z hz.2) hfresh'

/-- `EvalCtxValidPlus` survives a fresh, valid binder extension `(y,b₀) ↦ .var y τv₀`. -/
theorem evalCtxValidPlus_extend {Ψ : EvalCtx} {y : VName} {b₀ : Basis} {τv₀ : ValTy}
    (hΨ : EvalCtxValidPlus Ψ) (hfresh : (y, b₀) ∉ Ψ)
    (hτv₀ : ValTy.fv τv₀ ⊆ Ψ.keyNames)
    (hev : ValTy.EvalT Ψ (Basis.tof b₀) τv₀) :
    EvalCtxValidPlus (EvalCtx.extend Ψ y b₀ (.var y τv₀)) := by
  have hkn := keyNames_extend Ψ y b₀ (.var y τv₀)
  intro x b v hlk
  simp only [EvalCtx.extend, EvalCtx.lookup] at hlk
  by_cases hk : (x, b) = (y, b₀)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
    rw [Finmap.lookup_insert, Option.some.injEq] at hlk
    subst hlk
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hkn]; simp only [ValExpr.fv]; exact Finset.insert_subset_insert _ hτv₀
    · rw [ValExpr.inferType_var]; exact evalT_wk hev hfresh
    · rw [ValExpr.inferType_var, hkn]; exact hτv₀.trans (Finset.subset_insert _ _)
    · -- `lc (.var y τv₀)`: the domain type is `lc` by `evalT_lc` (stored values `lc`).
      exact .var (evalT_lc hev hΨ.toEvalCtxLc)
    · -- anchoring: a `.var` is not a `.vlam`.
      intro _ _ _ _ _ _ hv
      exact nomatch hv
  · rw [Finmap.lookup_insert_of_ne _ hk] at hlk
    obtain ⟨hvfv, hevT, hτfv, hlc, hanch⟩ := hΨ x b v hlk
    rw [hkn]
    refine ⟨hvfv.trans (Finset.subset_insert _ _), evalT_wk hevT hfresh,
           hτfv.trans (Finset.subset_insert _ _), hlc, ?_⟩
    -- anchoring of the surviving binding: re-instantiate its cofinite codomain at
    -- a fresh `y' ≠ y`, weaken past `(y,b₀)`, insert-commute under the binder.
    intro c₀ c₁ τw₀ τw₁ body hbf hvf
    obtain ⟨L, hL⟩ := hanch c₀ c₁ τw₀ τw₁ body hbf hvf
    refine ⟨insert y L, fun y' hy' => ?_⟩
    rw [Finset.mem_insert, not_or] at hy'
    obtain ⟨hy'y, hy'L⟩ := hy'
    have hne : (y, b₀) ≠ (y', c₀) := fun h => hy'y (congrArg Prod.fst h).symm
    have hfresh' : (y, b₀) ∉ EvalCtx.extend Ψ y' c₀ (.var y' τw₀) := by
      rw [EvalCtx.extend]
      exact fun h => (Finmap.mem_insert.mp h).elim hne hfresh
    exact evalctx_extend_comm hne ▸ evalT_wk (hL y' hy'L) hfresh'

theorem evalCtxValidPlus_extend_delta {Ψ : EvalCtx} {y : VName} {b' : Basis}
    {i : Nat} {sv' : ValSpace}
    (hΨ : EvalCtxValidPlus Ψ) (hfresh : (y, b') ∉ Ψ)
    (hsvfv : ValSpace.fv sv' ⊆ Ψ.keyNames)
    (hsvlc : ValSpace.lc sv')
    (hev : ValTy.EvalT Ψ (Basis.tof b') (.space sv')) :
    EvalCtxValidPlus (EvalCtx.extend Ψ y b' (.delta i sv')) := by
  have hkn := keyNames_extend Ψ y b' (.delta i sv')
  intro x b v hlk
  simp only [EvalCtx.extend, EvalCtx.lookup] at hlk
  by_cases hk : (x, b) = (y, b')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
    rw [Finmap.lookup_insert, Option.some.injEq] at hlk
    subst hlk
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hkn]; exact hsvfv.trans (Finset.subset_insert _ _)
    · exact evalT_wk hev hfresh
    · rw [hkn]; exact hsvfv.trans (Finset.subset_insert _ _)
    · exact .delta hsvlc
    · intro _ _ _ _ _ _ hv
      exact nomatch hv
  · rw [Finmap.lookup_insert_of_ne _ hk] at hlk
    obtain ⟨hvfv, hevT, hτfv, hlc, hanch⟩ := hΨ x b v hlk
    rw [hkn]
    refine ⟨hvfv.trans (Finset.subset_insert _ _), evalT_wk hevT hfresh,
           hτfv.trans (Finset.subset_insert _ _), hlc, ?_⟩
    intro c₀ c₁ τw₀ τw₁ body hbf hvf
    obtain ⟨L, hL⟩ := hanch c₀ c₁ τw₀ τw₁ body hbf hvf
    refine ⟨insert y L, fun y' hy' => ?_⟩
    rw [Finset.mem_insert, not_or] at hy'
    obtain ⟨hy'y, hy'L⟩ := hy'
    have hne : (y, b') ≠ (y', c₀) := fun h => hy'y (congrArg Prod.fst h).symm
    have hfresh' : (y, b') ∉ EvalCtx.extend Ψ y' c₀ (.var y' τw₀) := by
      rw [EvalCtx.extend]
      exact fun h => (Finmap.mem_insert.mp h).elim hne hfresh
    exact evalctx_extend_comm hne ▸ evalT_wk (hL y' hy'L) hfresh'

/-- `KeyScope` survives the binder extension (scope grows by `y` too). -/
theorem keyScope_extend {Ψ : EvalCtx} {y : VName} {b₀ : Basis} {τv₀ : ValTy}
    {ρ : ValScope} (hkey : KeyScope Ψ ρ) :
    KeyScope (EvalCtx.extend Ψ y b₀ (.var y τv₀)) (insert y ρ) := by
  rw [KeyScope, keyNames_extend]; exact Finset.insert_subset_insert _ hkey

/-- `RhoValid` survives a fresh, valid binder extension (scope `insert y ρ`). -/
theorem rhoValid_extend {Ψ : EvalCtx} {y : VName} {b₀ : Basis} {τv₀ : ValTy}
    {ρ : ValScope} (hρ : RhoValid Ψ ρ) (hfreshk : y ∉ Ψ.keyNames)
    (hkey : Ψ.keyNames ⊆ ρ) (hok : ValTyOk τv₀) (hτv₀ : ValTy.fv τv₀ ⊆ Ψ.keyNames) :
    RhoValid (EvalCtx.extend Ψ y b₀ (.var y τv₀)) (insert y ρ) := by
  intro x b v _hxρ hlk
  simp only [EvalCtx.extend, EvalCtx.lookup] at hlk
  by_cases hk : (x, b) = (y, b₀)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
    rw [Finmap.lookup_insert, Option.some.injEq] at hlk; subst hlk
    refine ⟨hok, ?_, ?_⟩
    · rw [ValExpr.inferType_var]
      exact hτv₀.trans (hkey.trans (Finset.subset_insert _ _))
    · simp only [ValExpr.fv]
      exact Finset.insert_subset_insert _ (hτv₀.trans hkey)
  · rw [Finmap.lookup_insert_of_ne _ hk] at hlk
    have hxk : x ∈ Ψ.keyNames := mem_keyNames_of_lookup hlk
    obtain ⟨hok', hτf, hvf⟩ := hρ x b v (hkey hxk) hlk
    exact ⟨hok', hτf.trans (Finset.subset_insert _ _),
           hvf.trans (Finset.subset_insert _ _)⟩

/-! ## Operational fv-scoping (mutual, via the shared 4-way eval recursor).

A realized value / value-space / value-type / COB-witness has all its free names
bound by `Ψ` (`fv ⊆ Ψ.keyNames`), purely operationally given `EvalCtxValidPlus Ψ`.
The four motives all land in `Prop` (`fv ⊆ …`), so no `Nonempty` wrapping is
needed. Proven with `ValSpace.EvalS.rec` over the 4-way mutual eval block, one
recursor call per entry-point (the `evalT_valid` style), with all four motives kept
real so cross-judgment premises (e.g. EvalS.ker's `OpStep` witness) get usable IHs.
The two binder arms (`OpStep.nllam` / `EvalT.piTy`) are factored into the shared
helpers `nllam_codomain_fv_drop` / `nllam_body_fv_drop` below. -/

/-- Drop a fresh binder name from a `⊆ insert y K` fact. -/
private theorem fv_drop_fresh {S K : Finset VName} {y : VName}
    (hsub : S ⊆ insert y K) (hy : y ∉ S) : S ⊆ K :=
  fun a ha => (Finset.mem_insert.mp (hsub ha)).resolve_left (fun h => hy (h ▸ ha))

/-- **Binder fv-drop (codomain TYPE).** From the cofinite opened-codomain IH plus
    the domain's fv-scoping and `EvalT`, recover `fv τv₁ ⊆ Ψ.keyNames`. Shared by the
    `EvalT.piTy` and `OpStep.nllam` arms of the four fv theorems. -/
private theorem nllam_codomain_fv_drop {Ψ : EvalCtx} {b₀ : Basis} {τv₀ τv₁ : ValTy}
    {L : Finset VName}
    (ih₁ : ∀ y, y ∉ L → (EvalCtxValidPlus (EvalCtx.extend Ψ y b₀ (.var y τv₀)) →
            ValTy.fv (ValTy.openVar y τv₀ τv₁) ⊆ (EvalCtx.extend Ψ y b₀ (.var y τv₀)).keyNames))
    (hfv₀ : ValTy.fv τv₀ ⊆ Ψ.keyNames)
    (hev0 : ValTy.EvalT Ψ (Basis.tof b₀) τv₀)
    (hΨ : EvalCtxValidPlus Ψ) : ValTy.fv τv₁ ⊆ Ψ.keyNames := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Ψ.keyNames ∪ ValTy.fv τv₁)
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at hy
  obtain ⟨⟨hyL, hykn⟩, hyfv⟩ := hy
  have hfresh : (y, b₀) ∉ Ψ :=
    fun hc => hykn (Finset.mem_image_of_mem Prod.fst (Finmap.mem_keys.mpr hc))
  have hΨ'' := evalCtxValidPlus_extend hΨ hfresh hfv₀ hev0
  have hcod := ih₁ y hyL hΨ''
  rw [keyNames_extend] at hcod
  intro w hw
  have hw' : w ∈ ValTy.fv (ValTy.openVar y τv₀ τv₁) := ValTy.fv_subset_openRec hw
  exact (Finset.mem_insert.mp (hcod hw')).resolve_left (fun h => hyfv (h ▸ hw))

/-- **Binder fv-drop (body VALUE).** Mirror of `nllam_codomain_fv_drop` for the
    `OpStep.nllam` body `env` (its cofinite opened IH). Recovers `fv env ⊆ keyNames`. -/
private theorem nllam_body_fv_drop {Ψ : EvalCtx} {b₀ : Basis} {τv₀ : ValTy}
    {env : ValExpr} {L : Finset VName}
    (ihe : ∀ y, y ∉ L → (EvalCtxValidPlus (EvalCtx.extend Ψ y b₀ (.var y τv₀)) →
            ValExpr.fv (ValExpr.openVar y τv₀ env) ⊆ (EvalCtx.extend Ψ y b₀ (.var y τv₀)).keyNames))
    (hfv₀ : ValTy.fv τv₀ ⊆ Ψ.keyNames)
    (hev0 : ValTy.EvalT Ψ (Basis.tof b₀) τv₀)
    (hΨ : EvalCtxValidPlus Ψ) : ValExpr.fv env ⊆ Ψ.keyNames := by
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Ψ.keyNames ∪ ValExpr.fv env)
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at hy
  obtain ⟨⟨hyL, hykn⟩, hyfv⟩ := hy
  have hfresh : (y, b₀) ∉ Ψ :=
    fun hc => hykn (Finset.mem_image_of_mem Prod.fst (Finmap.mem_keys.mpr hc))
  have hΨ'' := evalCtxValidPlus_extend hΨ hfresh hfv₀ hev0
  have hbody := ihe y hyL hΨ''
  rw [keyNames_extend] at hbody
  intro w hw
  have hw' : w ∈ ValExpr.fv (ValExpr.openVar y τv₀ env) := ValExpr.fv_subset_openRec hw
  exact (Finset.mem_insert.mp (hbody hw')).resolve_left (fun h => hyfv (h ▸ hw))

/-- The four operational fv-scoping motives (shared by every entry-point). -/
private def fvMotive1 : EvalCtx → Space → ValSpace → Prop → Prop :=
  fun Ψ _ sv _ => EvalCtxValidPlus Ψ → ValSpace.fv sv ⊆ Ψ.keyNames
private def fvMotive2 : EvalCtx → Ty → ValTy → Prop → Prop :=
  fun Ψ _ τv _ => EvalCtxValidPlus Ψ → ValTy.fv τv ⊆ Ψ.keyNames
private def fvMotive3 : EvalCtx → Basis → ValExpr → Basis → Prop → Prop :=
  fun Ψ _ env _ _ => EvalCtxValidPlus Ψ → ValExpr.fv env ⊆ Ψ.keyNames
private def fvMotive4 : EvalCtx → Term → Basis → ValExpr → Prop → Prop :=
  fun Ψ _ _ v _ => EvalCtxValidPlus Ψ → ValExpr.fv v ⊆ Ψ.keyNames

/-! ### The 50 arms (one per eval constructor). Each unfolds the produced value's
    `fv` and discharges every union piece from the matching IH (`ih hΨ`) or from
    `EvalCtxValidPlus` (the `.var` leaf). -/

-- EvalS arms (9).
private theorem evalFv_eReal {Ψ : EvalCtx} : fvMotive1 Ψ .real .real True := by
  intro _; exact Finset.empty_subset _
private theorem evalFv_eEmpty {Ψ : EvalCtx} : fvMotive1 Ψ .empty .empty True := by
  intro _; exact Finset.empty_subset _
private theorem evalFv_eDual {Ψ : EvalCtx} {s : Space} {sv : ValSpace}
    (_h : ValSpace.EvalS Ψ s sv) (ih : fvMotive1 Ψ s sv True) :
    fvMotive1 Ψ (.dual s) sv True := ih
private theorem evalFv_eKer {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {b : Basis}
    {leev : ValExpr} {svb : ValSpace}
    (_he : ValExpr.OpStep Ψ e b leev) (_hb : Basis.sof b = .tprod (.dual s₀) s₁)
    (_hcompat : Basis.FFSMatrixCompatible b)
    (_hsvb : ValSpace.EvalS Ψ (Basis.sof b) svb)
    (ih_he : fvMotive4 Ψ e b leev True) (ih_svb : fvMotive1 Ψ (Basis.sof b) svb True) :
    fvMotive1 Ψ (.ker s₀ s₁ e)
      (.ffs .kernel svb (.reshap leev (.space svb) (.space svb))) True := by
  intro hΨ; simp only [ValSpace.fv, ValExpr.fv, ValTy.fv]
  exact Finset.union_subset (ih_svb hΨ)
    (Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_svb hΨ)) (ih_svb hΨ))
private theorem evalFv_eCoker {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {b : Basis}
    {leev : ValExpr} {svb : ValSpace}
    (_he : ValExpr.OpStep Ψ e b leev) (_hb : Basis.sof b = .tprod (.dual s₀) s₁)
    (_hcompat : Basis.FFSMatrixCompatible b)
    (_hsvb : ValSpace.EvalS Ψ (Basis.sof b) svb)
    (ih_he : fvMotive4 Ψ e b leev True) (ih_svb : fvMotive1 Ψ (Basis.sof b) svb True) :
    fvMotive1 Ψ (.coker s₀ s₁ e)
      (.ffs .cokernel svb (.reshap leev (.space svb) (.space svb))) True := by
  intro hΨ; simp only [ValSpace.fv, ValExpr.fv, ValTy.fv]
  exact Finset.union_subset (ih_svb hΨ)
    (Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_svb hΨ)) (ih_svb hΨ))
private theorem evalFv_eImg {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {b : Basis}
    {leev : ValExpr} {svb : ValSpace}
    (_he : ValExpr.OpStep Ψ e b leev) (_hb : Basis.sof b = .tprod (.dual s₀) s₁)
    (_hcompat : Basis.FFSMatrixCompatible b)
    (_hsvb : ValSpace.EvalS Ψ (Basis.sof b) svb)
    (ih_he : fvMotive4 Ψ e b leev True) (ih_svb : fvMotive1 Ψ (Basis.sof b) svb True) :
    fvMotive1 Ψ (.img s₀ s₁ e)
      (.ffs .image svb (.reshap leev (.space svb) (.space svb))) True := by
  intro hΨ; simp only [ValSpace.fv, ValExpr.fv, ValTy.fv]
  exact Finset.union_subset (ih_svb hΨ)
    (Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_svb hΨ)) (ih_svb hΨ))
private theorem evalFv_eCoimg {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {b : Basis}
    {leev : ValExpr} {svb : ValSpace}
    (_he : ValExpr.OpStep Ψ e b leev) (_hb : Basis.sof b = .tprod (.dual s₀) s₁)
    (_hcompat : Basis.FFSMatrixCompatible b)
    (_hsvb : ValSpace.EvalS Ψ (Basis.sof b) svb)
    (ih_he : fvMotive4 Ψ e b leev True) (ih_svb : fvMotive1 Ψ (Basis.sof b) svb True) :
    fvMotive1 Ψ (.coimg s₀ s₁ e)
      (.ffs .coimage svb (.reshap leev (.space svb) (.space svb))) True := by
  intro hΨ; simp only [ValSpace.fv, ValExpr.fv, ValTy.fv]
  exact Finset.union_subset (ih_svb hΨ)
    (Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_svb hΨ)) (ih_svb hΨ))
private theorem evalFv_eTprod {Ψ : EvalCtx} {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace}
    (_h₀ : ValSpace.EvalS Ψ s₀ sv₀) (_h₁ : ValSpace.EvalS Ψ s₁ sv₁)
    (ih₀ : fvMotive1 Ψ s₀ sv₀ True) (ih₁ : fvMotive1 Ψ s₁ sv₁ True) :
    fvMotive1 Ψ (.tprod s₀ s₁) (.tprod sv₀ sv₁) True := by
  intro hΨ; simp only [ValSpace.fv]; exact Finset.union_subset (ih₀ hΨ) (ih₁ hΨ)
private theorem evalFv_eDsum {Ψ : EvalCtx} {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace}
    (_h₀ : ValSpace.EvalS Ψ s₀ sv₀) (_h₁ : ValSpace.EvalS Ψ s₁ sv₁)
    (ih₀ : fvMotive1 Ψ s₀ sv₀ True) (ih₁ : fvMotive1 Ψ s₁ sv₁ True) :
    fvMotive1 Ψ (.dsum s₀ s₁) (.dsum sv₀ sv₁) True := by
  intro hΨ; simp only [ValSpace.fv]; exact Finset.union_subset (ih₀ hΨ) (ih₁ hΨ)

-- EvalT arms (2).
private theorem evalFv_eTspace {Ψ : EvalCtx} {s : Space} {sv : ValSpace}
    (_h : ValSpace.EvalS Ψ s sv) (ih : fvMotive1 Ψ s sv True) :
    fvMotive2 Ψ (.space s) (.space sv) True := by
  intro hΨ; simp only [ValTy.fv]; exact ih hΨ
private theorem evalFv_eTpiTy {Ψ : EvalCtx} {b₀ : Basis} {τ₀ τ₁ : Ty}
    {τv₀ τv₁ : ValTy} (_h₀ : ValTy.EvalT Ψ τ₀ τv₀) (hb : Basis.tof b₀ = τ₀)
    (L : Finset VName)
    (_h₁ : ∀ y, y ∉ L → ValTy.EvalT (Ψ.extend y b₀ (.var y τv₀))
              (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁))
    (ih₀ : fvMotive2 Ψ τ₀ τv₀ True)
    (ih₁ : ∀ y, y ∉ L → fvMotive2 (Ψ.extend y b₀ (.var y τv₀))
              (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁) True) :
    fvMotive2 Ψ (.piTy τ₀ τ₁) (.piTy τv₀ τv₁) True := by
  intro hΨ
  have hev0 : ValTy.EvalT Ψ (Basis.tof b₀) τv₀ := hb ▸ _h₀
  have hfv₀ := ih₀ hΨ
  simp only [ValTy.fv]
  exact Finset.union_subset hfv₀ (nllam_codomain_fv_drop ih₁ hfv₀ hev0 hΨ)

-- EvalBB arms (9).
private theorem evalFv_bInv {Ψ : EvalCtx} {b₀ b₁ : Basis} {leev : ValExpr}
    (_h : Basis.EvalBB Ψ b₁ leev b₀) (ih : fvMotive3 Ψ b₁ leev b₀ True) :
    fvMotive3 Ψ b₀ (.inv leev) b₁ True := by
  intro hΨ; simp only [ValExpr.fv]; exact ih hΨ
private theorem evalFv_bTrans {Ψ : EvalCtx} {b₀ b₁ b₂ : Basis} {env₀ env₁ : ValExpr}
    {sv : ValSpace} (_h₀ : Basis.EvalBB Ψ b₀ env₀ b₁) (_h₁ : Basis.EvalBB Ψ b₁ env₁ b₂)
    (_hsv : ValSpace.EvalS Ψ (Basis.sof b₀) sv)
    (ih₀ : fvMotive3 Ψ b₀ env₀ b₁ True) (ih₁ : fvMotive3 Ψ b₁ env₁ b₂ True)
    (ih_sv : fvMotive1 Ψ (Basis.sof b₀) sv True) :
    fvMotive3 Ψ b₀ (.mtm 0 0 sv sv env₁ (.reshapBase env₀ (.tprod sv sv))) b₂ True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first | exact ih_sv hΨ | exact ih₀ hΨ | exact ih₁ hΨ
private theorem evalFv_bTprod {Ψ : EvalCtx} {b₀ b₁ b₀' b₁' : Basis} {env₀ env₁ : ValExpr}
    (_h₀ : Basis.EvalBB Ψ b₀' env₀ b₀) (_h₁ : Basis.EvalBB Ψ b₁' env₁ b₁)
    (ih₀ : fvMotive3 Ψ b₀' env₀ b₀ True) (ih₁ : fvMotive3 Ψ b₁' env₁ b₁ True) :
    fvMotive3 Ψ (.tprod b₀' b₁') (.vkrn env₀ env₁) (.tprod b₀ b₁) True := by
  intro hΨ; simp only [ValExpr.fv]; exact Finset.union_subset (ih₀ hΨ) (ih₁ hΨ)
private theorem evalFv_bDsum {Ψ : EvalCtx} {b₀ b₁ b₀' b₁' : Basis} {env₀ env₁ : ValExpr}
    (_h₀ : Basis.EvalBB Ψ b₀' env₀ b₀) (_h₁ : Basis.EvalBB Ψ b₁' env₁ b₁)
    (ih₀ : fvMotive3 Ψ b₀' env₀ b₀ True) (ih₁ : fvMotive3 Ψ b₁' env₁ b₁ True) :
    fvMotive3 Ψ (.dsum b₀' b₁') (.vblk env₀ env₁) (.dsum b₀ b₁) True := by
  intro hΨ; simp only [ValExpr.fv]; exact Finset.union_subset (ih₀ hΨ) (ih₁ hΨ)
private theorem evalFv_bDualStd {Ψ : EvalCtx} {b₀ : Basis} {leev : ValExpr}
    (_htof : Basis.tof b₀ = .space (Basis.sof b₀))
    (_hb₁ : Basis.EvalBB Ψ b₀ leev (Basis.std (Basis.tof b₀)))
    (ih : fvMotive3 Ψ b₀ leev (Basis.std (Basis.tof b₀)) True) :
    fvMotive3 Ψ (.dual b₀) (.vtrans (.inv leev)) (Basis.std (Basis.tof (.dual b₀))) True := by
  intro hΨ; simp only [ValExpr.fv]; exact ih hΨ
private theorem evalFv_bImage {Ψ : EvalCtx} {b₀ b₀' : Basis} {leev : ValExpr}
    (_hcoker : ∃ s₀ s₁ e, Basis.sof b₀ = .coker s₀ s₁ e)
    (_h : Basis.EvalBB Ψ b₀ leev b₀') (ih : fvMotive3 Ψ b₀ leev b₀' True) :
    fvMotive3 Ψ (.image b₀) leev (.image b₀') True := ih
private theorem evalFv_bImageSvds {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
    {leev : ValExpr} {s₀ s₁ : Space} {svb : ValSpace}
    (_hs₀ : Basis.sof b₀ = s₀) (_hs₁ : Basis.sof b₁ = s₁)
    (_hb₀ : Basis.isStd b₀) (_hb₁ : Basis.isStd b₁)
    (_he : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) leev)
    (_hsvb : ValSpace.EvalS Ψ (Basis.sof (.tprod (.dual b₀) b₁)) svb)
    (ih_he : fvMotive4 Ψ e (.tprod (.dual b₀) b₁) leev True)
    (ih_hsvb : fvMotive1 Ψ (Basis.sof (.tprod (.dual b₀) b₁)) svb True) :
    fvMotive3 Ψ (.image (.proj (.coker s₀ s₁ e) b₀ b₁))
      (.reshap (.imageCoords svb leev)
        (.space (.tprod
          (.ffs .cokernel svb (.reshap leev (.space svb) (.space svb)))
          (.ffs .image svb (.reshap leev (.space svb) (.space svb)))))
        (.space (ValExpr.inferSpaceCtx [] (.imageCoords svb leev))))
      (.proj (.img s₀ s₁ e) b₀ b₁) True := by
  intro hΨ
  have hcoordsFv : (ValExpr.imageCoords svb leev).fv ⊆ Ψ.keyNames :=
    (ValExpr.imageCoords_fv svb leev).trans (Finset.union_subset (ih_hsvb hΨ) (ih_he hΨ))
  have hinferFv : ValSpace.fv (ValExpr.inferSpaceCtx [] (ValExpr.imageCoords svb leev)) ⊆ Ψ.keyNames := by
    rw [ValExpr.inferSpaceCtx_nil]
    exact (ValExpr.fv_inferSpace_subset _).trans hcoordsFv
  simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first | exact ih_he hΨ | exact ih_hsvb hΨ | exact hinferFv | exact hcoordsFv
private theorem evalFv_bProjKC {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {s : Space}
    {b₀ b₁ b₀' : Basis} {env₁ env₂ env₃ : ValExpr} {sv₀ sv₁ sv sv' sv₀' : ValSpace}
    (_hs : s = Space.ker s₀ s₁ e ∨ s = Space.coker s₀ s₁ e)
    (_hsofb₀ : Basis.sof b₀ = s₀) (_hsofb₁ : Basis.sof b₁ = s₁)
    (_hsv₀ : ValSpace.EvalS Ψ (Basis.sof b₀) sv₀) (_hsv₁ : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
    (_hsv : ValSpace.EvalS Ψ s sv) (_hsv' : ValSpace.EvalS Ψ s sv')
    (_hsv₀' : ValSpace.EvalS Ψ (Basis.sof b₀') sv₀')
    (_hcob : Basis.EvalBB Ψ b₀ env₂ b₀')
    (_hembd : ValExpr.OpStep Ψ (Term.lembd s) (.tprod (.dual (.proj s b₀ b₁)) b₀) env₃)
    (_hproj : ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₀'))
                (.tprod (.dual b₀') (.proj s b₀' b₁)) env₁)
    (ih_sv₀ : fvMotive1 Ψ (Basis.sof b₀) sv₀ True) (ih_sv₁ : fvMotive1 Ψ (Basis.sof b₁) sv₁ True)
    (ih_sv : fvMotive1 Ψ s sv True) (ih_sv' : fvMotive1 Ψ s sv' True)
    (ih_sv₀' : fvMotive1 Ψ (Basis.sof b₀') sv₀' True)
    (ih_cob : fvMotive3 Ψ b₀ env₂ b₀' True)
    (ih_embd : fvMotive4 Ψ (Term.lembd s) (.tprod (.dual (.proj s b₀ b₁)) b₀) env₃ True)
    (ih_proj : fvMotive4 Ψ (Term.lproj s (Basis.sof b₀'))
                (.tprod (.dual b₀') (.proj s b₀' b₁)) env₁ True) :
    fvMotive3 Ψ (.proj s b₀ b₁)
      (.mtm 0 0 sv₀' sv₀'
        (.reshap env₁ (.space (.tprod sv₀' sv')) (.space (.tprod sv₀' sv')))
        (.mtm 0 0 sv₀ sv₀ (.reshapBase env₂ (.tprod sv₀ sv₀'))
          (.reshap env₃ (.space (.tprod sv sv₀)) (.space (.tprod sv sv₀)))))
      (.proj s b₀' b₁) True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first
    | exact ih_sv₀ hΨ | exact ih_sv₁ hΨ | exact ih_sv hΨ | exact ih_sv' hΨ
    | exact ih_sv₀' hΨ | exact ih_cob hΨ | exact ih_embd hΨ | exact ih_proj hΨ
private theorem evalFv_bProjIC {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {s : Space}
    {b₀ b₁ b₁' : Basis} {env₁ env₂ env₃ : ValExpr} {sv₀ sv₁ sv sv' sv₁' : ValSpace}
    (_hs : s = Space.img s₀ s₁ e ∨ s = Space.coimg s₀ s₁ e)
    (_hsofb₀ : Basis.sof b₀ = s₀) (_hsofb₁ : Basis.sof b₁ = s₁)
    (_hsv₀ : ValSpace.EvalS Ψ (Basis.sof b₀) sv₀) (_hsv₁ : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
    (_hsv : ValSpace.EvalS Ψ s sv) (_hsv' : ValSpace.EvalS Ψ s sv')
    (_hsv₁' : ValSpace.EvalS Ψ (Basis.sof b₁') sv₁')
    (_hcob : Basis.EvalBB Ψ b₁ env₂ b₁')
    (_hembd : ValExpr.OpStep Ψ (Term.lembd s) (.tprod (.dual (.proj s b₀ b₁)) b₁) env₃)
    (_hproj : ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₁'))
                (.tprod (.dual b₁') (.proj s b₀ b₁')) env₁)
    (ih_sv₀ : fvMotive1 Ψ (Basis.sof b₀) sv₀ True) (ih_sv₁ : fvMotive1 Ψ (Basis.sof b₁) sv₁ True)
    (ih_sv : fvMotive1 Ψ s sv True) (ih_sv' : fvMotive1 Ψ s sv' True)
    (ih_sv₁' : fvMotive1 Ψ (Basis.sof b₁') sv₁' True)
    (ih_cob : fvMotive3 Ψ b₁ env₂ b₁' True)
    (ih_embd : fvMotive4 Ψ (Term.lembd s) (.tprod (.dual (.proj s b₀ b₁)) b₁) env₃ True)
    (ih_proj : fvMotive4 Ψ (Term.lproj s (Basis.sof b₁'))
                (.tprod (.dual b₁') (.proj s b₀ b₁')) env₁ True) :
    fvMotive3 Ψ (.proj s b₀ b₁)
      (.mtm 0 0 sv₁' sv₁'
        (.reshap env₁ (.space (.tprod sv₁' sv')) (.space (.tprod sv₁' sv')))
        (.mtm 0 0 sv₁ sv₁ (.reshapBase env₂ (.tprod sv₁ sv₁'))
          (.reshap env₃ (.space (.tprod sv sv₁)) (.space (.tprod sv sv₁)))))
      (.proj s b₀ b₁') True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first
    | exact ih_sv₀ hΨ | exact ih_sv₁ hΨ | exact ih_sv hΨ | exact ih_sv' hΨ
    | exact ih_sv₁' hΨ | exact ih_cob hΨ | exact ih_embd hΨ | exact ih_proj hΨ

private theorem evalFv_bTermsRref {Ψ : EvalCtx} {b b' : Basis} {e : Term}
    {es : List Term} {env₀ env₁ : ValExpr} {sv : ValSpace}
    (_hbb : Basis.EvalBB Ψ b env₁ b')
    (_hch : ValExpr.OpStep Ψ (Term.dsumChain e es) (Basis.dsumChain b' es.length) env₀)
    (_hsv : ValSpace.EvalS Ψ (Basis.sof b) sv)
    (ih_bb : fvMotive3 Ψ b env₁ b' True)
    (ih_ch : fvMotive4 Ψ (Term.dsumChain e es) (Basis.dsumChain b' es.length) env₀ True)
    (ih_sv : fvMotive1 Ψ (Basis.sof b) sv True) :
    fvMotive3 Ψ b
      (.reshap (.rrefRep env₀ (.reshapBase env₁ (.tprod sv sv)))
        (.space (.tprod sv sv)) (.space (.tprod sv sv)))
      (.terms (Basis.sof b') (e :: es) b') True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first | exact ih_bb hΨ | exact ih_ch hΨ | exact ih_sv hΨ

private theorem evalFv_bRefl {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    (_htof : Basis.tof b = .space (Basis.sof b))
    (_hsv : ValSpace.EvalS Ψ (Basis.sof b) sv)
    (ih_hsv : fvMotive1 Ψ (Basis.sof b) sv True) :
    fvMotive3 Ψ b
      (.reshap (.idelta sv) (.space (.tprod sv sv)) (.space (.tprod sv sv))) b True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals exact ih_hsv hΨ

private theorem evalFv_bProjKCCod {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {s : Space}
    {b₀ b₁ b₁' : Basis} {env₁ env₃ : ValExpr} {sv₀ sv sv' : ValSpace}
    (_hs : s = Space.ker s₀ s₁ e ∨ s = Space.coker s₀ s₁ e)
    (_hsofb₀ : Basis.sof b₀ = s₀) (_hsofb₁ : Basis.sof b₁ = s₁)
    (_hsofb₁' : Basis.sof b₁' = s₁)
    (_hsv₀ : ValSpace.EvalS Ψ (Basis.sof b₀) sv₀)
    (_hsv : ValSpace.EvalS Ψ s sv) (_hsv' : ValSpace.EvalS Ψ s sv')
    (_hembd : ValExpr.OpStep Ψ (Term.lembd s) (.tprod (.dual (.proj s b₀ b₁)) b₀) env₃)
    (_hproj : ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₀))
                (.tprod (.dual b₀) (.proj s b₀ b₁')) env₁)
    (ih_sv₀ : fvMotive1 Ψ (Basis.sof b₀) sv₀ True)
    (ih_sv : fvMotive1 Ψ s sv True) (ih_sv' : fvMotive1 Ψ s sv' True)
    (ih_embd : fvMotive4 Ψ (Term.lembd s) (.tprod (.dual (.proj s b₀ b₁)) b₀) env₃ True)
    (ih_proj : fvMotive4 Ψ (Term.lproj s (Basis.sof b₀))
                (.tprod (.dual b₀) (.proj s b₀ b₁')) env₁ True) :
    fvMotive3 Ψ (.proj s b₀ b₁)
      (.mtm 0 0 sv₀ sv₀
        (.reshap env₁ (.space (.tprod sv₀ sv')) (.space (.tprod sv₀ sv')))
        (.reshap env₃ (.space (.tprod sv sv₀)) (.space (.tprod sv sv₀))))
      (.proj s b₀ b₁') True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first
    | exact ih_sv₀ hΨ | exact ih_sv hΨ | exact ih_sv' hΨ
    | exact ih_embd hΨ | exact ih_proj hΨ

private theorem evalFv_bProjICDom {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {s : Space}
    {b₀ b₁ b₀' : Basis} {env₁ env₃ : ValExpr} {sv₁ sv sv' : ValSpace}
    (_hs : s = Space.img s₀ s₁ e ∨ s = Space.coimg s₀ s₁ e)
    (_hsofb₀ : Basis.sof b₀ = s₀) (_hsofb₁ : Basis.sof b₁ = s₁)
    (_hsofb₀' : Basis.sof b₀' = s₀)
    (_hsv₁ : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
    (_hsv : ValSpace.EvalS Ψ s sv) (_hsv' : ValSpace.EvalS Ψ s sv')
    (_hembd : ValExpr.OpStep Ψ (Term.lembd s) (.tprod (.dual (.proj s b₀ b₁)) b₁) env₃)
    (_hproj : ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₁))
                (.tprod (.dual b₁) (.proj s b₀' b₁)) env₁)
    (ih_sv₁ : fvMotive1 Ψ (Basis.sof b₁) sv₁ True)
    (ih_sv : fvMotive1 Ψ s sv True) (ih_sv' : fvMotive1 Ψ s sv' True)
    (ih_embd : fvMotive4 Ψ (Term.lembd s) (.tprod (.dual (.proj s b₀ b₁)) b₁) env₃ True)
    (ih_proj : fvMotive4 Ψ (Term.lproj s (Basis.sof b₁))
                (.tprod (.dual b₁) (.proj s b₀' b₁)) env₁ True) :
    fvMotive3 Ψ (.proj s b₀ b₁)
      (.mtm 0 0 sv₁ sv₁
        (.reshap env₁ (.space (.tprod sv₁ sv')) (.space (.tprod sv₁ sv')))
        (.reshap env₃ (.space (.tprod sv sv₁)) (.space (.tprod sv sv₁))))
      (.proj s b₀' b₁) True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first
    | exact ih_sv₁ hΨ | exact ih_sv hΨ | exact ih_sv' hΨ
    | exact ih_embd hΨ | exact ih_proj hΨ

-- OpStep arms (26).
private theorem evalFv_oVar {Ψ : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
    (h : EvalCtx.lookup Ψ (x, b) = some v) : fvMotive4 Ψ (.var x) b v True :=
  fun hΨ => (hΨ _ _ _ h).1
private theorem evalFv_oCob {Ψ : EvalCtx} {e : Term} {b₀ b₁ : Basis}
    {v env₀ : ValExpr} {sv : ValSpace}
    (_htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
    (_htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
    (_he : ValExpr.OpStep Ψ e b₁ v) (_hbb : Basis.EvalBB Ψ b₁ env₀ b₀)
    (_hes : ValSpace.EvalS Ψ (Basis.sof b₀) sv)
    (ih_he : fvMotive4 Ψ e b₁ v True) (ih_bb : fvMotive3 Ψ b₁ env₀ b₀ True)
    (ih_es : fvMotive1 Ψ (Basis.sof b₀) sv True) :
    fvMotive4 Ψ e b₀
      (.ttv sv (.reshapBase env₀ (.tprod sv sv)) (.reshapBase v sv)) True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first | exact ih_es hΨ | exact ih_bb hΨ | exact ih_he hΨ
private theorem evalFv_oScale {Ψ : EvalCtx} {e₀ e₁ : Term} {b : Basis} {v₀ v₁ : ValExpr}
    (_he₀ : ValExpr.OpStep Ψ e₀ .one v₀) (_he₁ : ValExpr.OpStep Ψ e₁ b v₁)
    (ih₀ : fvMotive4 Ψ e₀ .one v₀ True) (ih₁ : fvMotive4 Ψ e₁ b v₁ True) :
    fvMotive4 Ψ (.smul e₀ e₁) b (.scale v₀ v₁) True := by
  intro hΨ; simp only [ValExpr.fv]; exact Finset.union_subset (ih₀ hΨ) (ih₁ hΨ)
private theorem evalFv_oAdd {Ψ : EvalCtx} {e₀ e₁ : Term} {b : Basis}
    {sv : ValSpace} {v₀ v₁ : ValExpr}
    (_htof : Basis.tof b = .space (Basis.sof b))
    (_hsv : ValSpace.EvalS Ψ (Basis.sof b) sv)
    (_he₀ : ValExpr.OpStep Ψ e₀ b v₀) (_he₁ : ValExpr.OpStep Ψ e₁ b v₁)
    (ih_sv : fvMotive1 Ψ (Basis.sof b) sv True)
    (ih₀ : fvMotive4 Ψ e₀ b v₀ True) (ih₁ : fvMotive4 Ψ e₁ b v₁ True) :
    fvMotive4 Ψ (.add e₀ e₁) b (.vadd sv v₀ v₁) True := by
  intro hΨ
  simp only [ValExpr.fv]
  repeat' apply Finset.union_subset
  all_goals first | exact ih_sv hΨ | exact ih₀ hΨ | exact ih₁ hΨ
private theorem evalFv_oDsumE {Ψ : EvalCtx} {e₀ e₁ : Term} {b₀ b₁ : Basis} {v₀ v₁ : ValExpr}
    (_he₀ : ValExpr.OpStep Ψ e₀ b₀ v₀) (_he₁ : ValExpr.OpStep Ψ e₁ b₁ v₁)
    (_htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
    (_htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
    (ih₀ : fvMotive4 Ψ e₀ b₀ v₀ True) (ih₁ : fvMotive4 Ψ e₁ b₁ v₁ True) :
    fvMotive4 Ψ (.dsumE e₀ e₁) (.dsum b₀ b₁) (.dsumE v₀ v₁) True := by
  intro hΨ; simp only [ValExpr.fv]; exact Finset.union_subset (ih₀ hΨ) (ih₁ hΨ)
private theorem evalFv_oTprodE {Ψ : EvalCtx} {e₀ e₁ : Term} {b₀ b₁ : Basis} {v₀ v₁ : ValExpr}
    (_he₀ : ValExpr.OpStep Ψ e₀ b₀ v₀) (_he₁ : ValExpr.OpStep Ψ e₁ b₁ v₁)
    (_htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
    (_htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
    (ih₀ : fvMotive4 Ψ e₀ b₀ v₀ True) (ih₁ : fvMotive4 Ψ e₁ b₁ v₁ True) :
    fvMotive4 Ψ (.tprodE e₀ e₁) (.tprod b₀ b₁) (.tprodE v₀ v₁) True := by
  intro hΨ; simp only [ValExpr.fv]; exact Finset.union_subset (ih₀ hΨ) (ih₁ hΨ)
private theorem evalFv_oPinvTStd {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term} {v : ValExpr}
    (_he : ValExpr.OpStep Ψ e (.tprod (.dual b₁) b₀) v)
    (_hb₀ : Basis.isStd b₀) (_hb₁ : Basis.isStd b₁)
    (ih_he : fvMotive4 Ψ e (.tprod (.dual b₁) b₀) v True) :
    fvMotive4 Ψ (.pinvT (Basis.sof b₁) (Basis.sof b₀) e) (.tprod (.dual b₀) b₁) (.pinv v) True := by
  intro hΨ; simp only [ValExpr.fv]; exact ih_he hΨ
private theorem evalFv_oPinvTGpinv {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
    {v env₀ env₁ : ValExpr}
    (_he : ValExpr.OpStep Ψ e (.tprod (.dual b₁) b₀) v)
    (_hi₀ : ValExpr.OpStep Ψ (.inner (Basis.sof b₀)) (.tprod (.dual b₀) (.dual b₀)) env₀)
    (_hi₁ : ValExpr.OpStep Ψ (.inner (Basis.sof b₁)) (.tprod (.dual b₁) (.dual b₁)) env₁)
    (ih_he : fvMotive4 Ψ e (.tprod (.dual b₁) b₀) v True)
    (ih_i₀ : fvMotive4 Ψ (.inner (Basis.sof b₀)) (.tprod (.dual b₀) (.dual b₀)) env₀ True)
    (ih_i₁ : fvMotive4 Ψ (.inner (Basis.sof b₁)) (.tprod (.dual b₁) (.dual b₁)) env₁ True) :
    fvMotive4 Ψ (.pinvT (Basis.sof b₁) (Basis.sof b₀) e) (.tprod (.dual b₀) b₁)
      (.gpinv v env₁ env₀) True := by
  intro hΨ; simp only [ValExpr.fv]
  exact Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_i₁ hΨ)) (ih_i₀ hΨ)
private theorem evalFv_oPinvDStd {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term} {v : ValExpr}
    {sv₁ : ValSpace}
    (_he : ValExpr.OpStep Ψ e (.dual b₁) v) (_hsofb₀ : Basis.sof b₀ = .real)
    (_hb₀ : Basis.isStd b₀) (_hb₁ : Basis.isStd b₁)
    (_hsv₁ : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
    (ih_he : fvMotive4 Ψ e (.dual b₁) v True)
    (ih_sv : fvMotive1 Ψ (Basis.sof b₁) sv₁ True) :
    fvMotive4 Ψ (.pinvD (Basis.sof b₁) e) (.tprod (.dual b₀) b₁)
      (.pinv (.reshap v (.space (.tprod sv₁ .real)) (.space sv₁))) True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first | exact ih_he hΨ | exact ih_sv hΨ | exact Finset.empty_subset _
private theorem evalFv_oPinvDGpinv {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
    {v env₀ env₁ : ValExpr} {sv₁ : ValSpace}
    (_he : ValExpr.OpStep Ψ e (.dual b₁) v) (_hsofb₀ : Basis.sof b₀ = .real)
    (_hb₀ : Basis.isStd b₀)
    (_hi₀ : ValExpr.OpStep Ψ (.inner (Basis.sof b₀)) (.tprod (.dual b₀) (.dual b₀)) env₀)
    (_hi₁ : ValExpr.OpStep Ψ (.inner (Basis.sof b₁)) (.tprod (.dual b₁) (.dual b₁)) env₁)
    (_hsv₁ : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
    (ih_he : fvMotive4 Ψ e (.dual b₁) v True)
    (ih_i₀ : fvMotive4 Ψ (.inner (Basis.sof b₀)) (.tprod (.dual b₀) (.dual b₀)) env₀ True)
    (ih_i₁ : fvMotive4 Ψ (.inner (Basis.sof b₁)) (.tprod (.dual b₁) (.dual b₁)) env₁ True)
    (ih_sv : fvMotive1 Ψ (Basis.sof b₁) sv₁ True) :
    fvMotive4 Ψ (.pinvD (Basis.sof b₁) e) (.tprod (.dual b₀) b₁)
      (.gpinv (.reshap v (.space (.tprod sv₁ .real)) (.space sv₁)) env₁ env₀) True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first | exact ih_he hΨ | exact ih_sv hΨ | exact ih_i₀ hΨ | exact ih_i₁ hΨ | exact Finset.empty_subset _
private theorem evalFv_oInnerStd {Ψ : EvalCtx} {b₀ : Basis} {s : Space} {sv : ValSpace}
    (_hb₀ : Basis.isStd b₀) (_hsv : ValSpace.EvalS Ψ s sv) (_hsof : Basis.sof b₀ = s)
    (ih_sv : fvMotive1 Ψ s sv True) :
    fvMotive4 Ψ (.inner s) (.tprod (.dual b₀) (.dual b₀)) (.idelta sv) True := by
  intro hΨ; simp only [ValExpr.fv]; exact ih_sv hΨ
private theorem evalFv_oEmbedKer {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
    {v env₀ env₁ : ValExpr} {s₀ s₁ : Space}
    (_hs₀ : Basis.sof b₀ = s₀) (_hs₁ : Basis.sof b₁ = s₁)
    (_hi₀ : ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀)
    (_hi₁ : ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁)
    (_he : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v)
    (ih_i₀ : fvMotive4 Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀ True)
    (ih_i₁ : fvMotive4 Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁ True)
    (ih_he : fvMotive4 Ψ e (.tprod (.dual b₀) b₁) v True) :
    fvMotive4 Ψ (.embed (Space.ker s₀ s₁ e))
      (.tprod (.dual (.proj (.ker s₀ s₁ e) b₀ b₁)) b₀) (.vtrans (.gsvdUI v env₀ env₁)) True := by
  intro hΨ; simp only [ValExpr.fv]
  exact Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_i₀ hΨ)) (ih_i₁ hΨ)
private theorem evalFv_oEmbedCoker {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
    {v env₀ env₁ : ValExpr} {s₀ s₁ : Space}
    (_hs₀ : Basis.sof b₀ = s₀) (_hs₁ : Basis.sof b₁ = s₁)
    (_hi₀ : ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀)
    (_hi₁ : ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁)
    (_he : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v)
    (ih_i₀ : fvMotive4 Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀ True)
    (ih_i₁ : fvMotive4 Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁ True)
    (ih_he : fvMotive4 Ψ e (.tprod (.dual b₀) b₁) v True) :
    fvMotive4 Ψ (.embed (Space.coker s₀ s₁ e))
      (.tprod (.dual (.proj (.coker s₀ s₁ e) b₀ b₁)) b₀) (.vtrans (.gsvdU v env₀ env₁)) True := by
  intro hΨ; simp only [ValExpr.fv]
  exact Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_i₀ hΨ)) (ih_i₁ hΨ)
private theorem evalFv_oEmbedImg {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
    {v env₀ env₁ : ValExpr} {s₀ s₁ : Space}
    (_hs₀ : Basis.sof b₀ = s₀) (_hs₁ : Basis.sof b₁ = s₁)
    (_hi₀ : ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀)
    (_hi₁ : ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁)
    (_he : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v)
    (ih_i₀ : fvMotive4 Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀ True)
    (ih_i₁ : fvMotive4 Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁ True)
    (ih_he : fvMotive4 Ψ e (.tprod (.dual b₀) b₁) v True) :
    fvMotive4 Ψ (.embed (Space.img s₀ s₁ e))
      (.tprod (.dual (.proj (.img s₀ s₁ e) b₀ b₁)) b₁) (.vtrans (.gsvdV v env₀ env₁)) True := by
  intro hΨ; simp only [ValExpr.fv]
  exact Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_i₀ hΨ)) (ih_i₁ hΨ)
private theorem evalFv_oEmbedCoimg {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
    {v env₀ env₁ : ValExpr} {s₀ s₁ : Space}
    (_hs₀ : Basis.sof b₀ = s₀) (_hs₁ : Basis.sof b₁ = s₁)
    (_hi₀ : ValExpr.OpStep Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀)
    (_hi₁ : ValExpr.OpStep Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁)
    (_he : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v)
    (ih_i₀ : fvMotive4 Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀ True)
    (ih_i₁ : fvMotive4 Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁ True)
    (ih_he : fvMotive4 Ψ e (.tprod (.dual b₀) b₁) v True) :
    fvMotive4 Ψ (.embed (Space.coimg s₀ s₁ e))
      (.tprod (.dual (.proj (.coimg s₀ s₁ e) b₀ b₁)) b₁) (.vtrans (.gsvdVI v env₀ env₁)) True := by
  intro hΨ; simp only [ValExpr.fv]
  exact Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_i₀ hΨ)) (ih_i₁ hΨ)
private theorem evalFv_oAppL {Ψ : EvalCtx} {b₀ b₁ : Basis} {n₀ n₁ : Term}
    {env₀ env₁ : ValExpr} {sv₀ sv₁ : ValSpace}
    (_h₀ : ValExpr.OpStep Ψ n₀ (.tprod (.dual b₀) b₁) env₀)
    (_hsv₀ : ValSpace.EvalS Ψ (Basis.sof b₀) sv₀)
    (_h₁ : ValExpr.OpStep Ψ n₁ b₀ env₁)
    (_hsv₁ : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
    (_htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
    (ih₀ : fvMotive4 Ψ n₀ (.tprod (.dual b₀) b₁) env₀ True)
    (ih_sv₀ : fvMotive1 Ψ (Basis.sof b₀) sv₀ True)
    (ih₁ : fvMotive4 Ψ n₁ b₀ env₁ True)
    (ih_sv₁ : fvMotive1 Ψ (Basis.sof b₁) sv₁ True) :
    fvMotive4 Ψ (.appL (Basis.sof b₀) (Basis.sof b₁) n₀ n₁) b₁
      (ValExpr.reshapBase (.ttv sv₀ env₀ env₁) sv₁) True := by
  intro hΨ
  simp only [ValExpr.reshapBase, ValExpr.fv, ValTy.fv]
  repeat' apply Finset.union_subset
  all_goals first
    | exact ih_sv₀ hΨ
    | exact ih_sv₁ hΨ
    | exact ih₀ hΨ
    | exact ih₁ hΨ
    | exact Finset.empty_subset _
private theorem evalFv_oAppI {Ψ : EvalCtx} {b₀ : Basis} {n₀ n₁ : Term}
    {env₀ env₁ : ValExpr} {sv : ValSpace}
    (_h₀ : ValExpr.OpStep Ψ n₀ (.dual b₀) env₀)
    (_hsv : ValSpace.EvalS Ψ (Basis.sof b₀) sv) (_h₁ : ValExpr.OpStep Ψ n₁ b₀ env₁)
    (ih₀ : fvMotive4 Ψ n₀ (.dual b₀) env₀ True)
    (ih_sv : fvMotive1 Ψ (Basis.sof b₀) sv True)
    (ih₁ : fvMotive4 Ψ n₁ b₀ env₁ True) :
    fvMotive4 Ψ (.appI (Basis.sof b₀) n₀ n₁) .one
      (.ttv sv (.reshap env₀ (.space (.tprod sv .real)) (.space sv)) env₁) True := by
  intro hΨ; simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
  repeat' apply Finset.union_subset
  all_goals first | exact ih_sv hΨ | exact ih₀ hΨ | exact ih₁ hΨ | exact Finset.empty_subset _
private theorem evalFv_oNllam {Ψ : EvalCtx} {b₀ b₁ : Basis} {τ₀ τ₁ : Ty}
    {e : Term} {τv₀ τv₁ : ValTy} {env : ValExpr}
    (hb₀ : Basis.tof b₀ = τ₀) (_hb₁ : Basis.tof b₁ = τ₁) (_h₀ : ValTy.EvalT Ψ τ₀ τv₀)
    (L : Finset VName)
    (_he : ∀ y, y ∉ L → ValExpr.OpStep (Ψ.extend y b₀ (.var y τv₀))
              (Term.openVar y e) (Basis.openVar y b₁) (ValExpr.openVar y τv₀ env))
    (_h₁ : ∀ y, y ∉ L → ValTy.EvalT (Ψ.extend y b₀ (.var y τv₀))
              (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁))
    (ih_h₀ : fvMotive2 Ψ τ₀ τv₀ True)
    (ih_he : ∀ y, y ∉ L → fvMotive4 (Ψ.extend y b₀ (.var y τv₀))
              (Term.openVar y e) (Basis.openVar y b₁)
              (ValExpr.openVar y τv₀ env) True)
    (ih_h₁ : ∀ y, y ∉ L → fvMotive2 (Ψ.extend y b₀ (.var y τv₀))
              (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁) True) :
    fvMotive4 Ψ (.nllam τ₀ e) (.frame b₀ b₁)
      (.vlam τv₀ τv₁ (.reshap env τv₁ τv₁)) True := by
  intro hΨ
  have hev0 : ValTy.EvalT Ψ (Basis.tof b₀) τv₀ := hb₀ ▸ _h₀
  have hfv₀ := ih_h₀ hΨ
  have hfvτ₁ := nllam_codomain_fv_drop ih_h₁ hfv₀ hev0 hΨ
  have hfvenv := nllam_body_fv_drop ih_he hfv₀ hev0 hΨ
  simp only [ValExpr.fv, ValTy.fv]
  exact Finset.union_subset (Finset.union_subset hfv₀ hfvτ₁)
    (Finset.union_subset (Finset.union_subset hfvenv hfvτ₁) hfvτ₁)
private theorem evalFv_oAppNVal {Ψ : EvalCtx} {b₀ b₁ : Basis} {n₀ n₁ : Term}
    {env₀ env₁ : ValExpr} {τ_out : ValTy}
    (_h₀ : ValExpr.OpStep Ψ n₀ (.frame b₀ b₁) env₀)
    (_h₁ : ValExpr.OpStep Ψ n₁ b₀ env₁)
    (_hout : ValTy.EvalT Ψ (Basis.instantiate n₁ b₁).tof τ_out)
    (ih_h₀ : fvMotive4 Ψ n₀ (.frame b₀ b₁) env₀ True)
    (ih_h₁ : fvMotive4 Ψ n₁ b₀ env₁ True)
    (ih_hout : fvMotive2 Ψ (Basis.instantiate n₁ b₁).tof τ_out True) :
    fvMotive4 Ψ (.appN n₀ n₁) (Basis.instantiate n₁ b₁) (.applyAt env₀ env₁ τ_out) True := by
  intro hΨ
  exact (ValExpr.fv_applyAt_subset _ _ _).trans
    (Finset.union_subset (Finset.union_subset (ih_h₀ hΨ) (ih_h₁ hΨ)) (ih_hout hΨ))
private theorem evalFv_oFrameReanchor {Ψ : EvalCtx} {b₀ b₀' b₁ : Basis} {n₀ : Term}
    {leev env₁ : ValExpr} {τv₀ τv₀' τv₁' : ValTy}
    (_h₀ : ValTy.EvalT Ψ (Basis.tof b₀) τv₀)
    (_htof : Basis.tof b₀' = Basis.tof b₀)
    (_hfn : ValExpr.OpStep Ψ n₀ (.frame b₀' b₁) leev)
    (_hdom : ValTy.EvalT Ψ (Basis.tof b₀') τv₀')
    (L : Finset VName)
    (_hx : ∀ y, y ∉ L → ValExpr.OpStep (Ψ.extend y b₀ (.var y τv₀))
              (.var y) b₀' (ValExpr.openVar y τv₀ env₁))
    (_hcod : ∀ y, y ∉ L → ValTy.EvalT (Ψ.extend y b₀ (.var y τv₀))
              (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁'))
    (ih_h₀ : fvMotive2 Ψ (Basis.tof b₀) τv₀ True)
    (ih_hfn : fvMotive4 Ψ n₀ (.frame b₀' b₁) leev True)
    (ih_hdom : fvMotive2 Ψ (Basis.tof b₀') τv₀' True)
    (ih_hx : ∀ y, y ∉ L → fvMotive4 (Ψ.extend y b₀ (.var y τv₀))
              (.var y) b₀' (ValExpr.openVar y τv₀ env₁) True)
    (ih_hcod : ∀ y, y ∉ L → fvMotive2 (Ψ.extend y b₀ (.var y τv₀))
              (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁') True) :
    fvMotive4 Ψ n₀ (.frame b₀ b₁)
      (.vlam τv₀ τv₁'
        (.reshap (.applyValue leev (.reshap env₁ τv₀' τv₀')) τv₁' τv₁')) True := by
  intro hΨ
  have hfv₀ := ih_h₀ hΨ
  have hfvτ₁' := nllam_codomain_fv_drop ih_hcod hfv₀ _h₀ hΨ
  have hfvenv₁ := nllam_body_fv_drop ih_hx hfv₀ _h₀ hΨ
  have hfvleev := ih_hfn hΨ
  have hfvτv₀' := ih_hdom hΨ
  have hcall := (ValExpr.fv_applyValue_subset leev (.reshap env₁ τv₀' τv₀')).trans
    (Finset.union_subset hfvleev
      (Finset.union_subset (Finset.union_subset hfvenv₁ hfvτv₀') hfvτv₀'))
  simp only [ValExpr.fv, ValTy.fv]
  exact Finset.union_subset (Finset.union_subset hfv₀ hfvτ₁')
    (Finset.union_subset (Finset.union_subset hcall hfvτ₁') hfvτ₁')
private theorem evalFv_oFrameEta {Ψ : EvalCtx} {b₀ b₁ : Basis} {n₀ : Term}
    {τv₀ τv₁ : ValTy} {env : ValExpr}
    (_h₀ : ValTy.EvalT Ψ (Basis.tof b₀) τv₀)
    (L : Finset VName)
    (_he : ∀ y, y ∉ L → ValExpr.OpStep (Ψ.extend y b₀ (.var y τv₀))
              (.appN n₀ (.var y)) (Basis.openVar y b₁) (ValExpr.openVar y τv₀ env))
    (_h₁ : ∀ y, y ∉ L → ValTy.EvalT (Ψ.extend y b₀ (.var y τv₀))
              (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁))
    (ih_h₀ : fvMotive2 Ψ (Basis.tof b₀) τv₀ True)
    (ih_he : ∀ y, y ∉ L → fvMotive4 (Ψ.extend y b₀ (.var y τv₀))
              (.appN n₀ (.var y)) (Basis.openVar y b₁) (ValExpr.openVar y τv₀ env) True)
    (ih_h₁ : ∀ y, y ∉ L → fvMotive2 (Ψ.extend y b₀ (.var y τv₀))
              (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁) True) :
    fvMotive4 Ψ n₀ (.frame b₀ b₁)
      (.vlam τv₀ τv₁ (.reshap env τv₁ τv₁)) True := by
  intro hΨ
  have hfv₀ := ih_h₀ hΨ
  have hfvτ₁ := nllam_codomain_fv_drop ih_h₁ hfv₀ _h₀ hΨ
  have hfvenv := nllam_body_fv_drop ih_he hfv₀ _h₀ hΨ
  simp only [ValExpr.fv, ValTy.fv]
  exact Finset.union_subset (Finset.union_subset hfv₀ hfvτ₁)
    (Finset.union_subset (Finset.union_subset hfvenv hfvτ₁) hfvτ₁)
private theorem evalFv_oReshape {Ψ : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
    {τv_src τv_tgt : ValTy}
    (_he : ValExpr.OpStep Ψ e b v)
    (_hsrc : ValTy.EvalT Ψ (Basis.tof b) τv_src)
    (_htgt : ValTy.EvalT Ψ (Basis.tof b) τv_tgt)
    (ih_he : fvMotive4 Ψ e b v True)
    (ih_hsrc : fvMotive2 Ψ (Basis.tof b) τv_src True)
    (ih_htgt : fvMotive2 Ψ (Basis.tof b) τv_tgt True) :
    fvMotive4 Ψ e b (.reshap v τv_tgt τv_src) True := by
  intro hΨ
  simp only [ValExpr.fv]
  exact Finset.union_subset (Finset.union_subset (ih_he hΨ) (ih_htgt hΨ)) (ih_hsrc hΨ)

/-- Shared fv-drop for the `llam_assemble` family: each `env i`'s fvs (which
    are `y`-independent) drop the fresh `y` through the `.delta`-binding
    extension. -/
private theorem llam_family_fv_drop {Ψ : EvalCtx} {b' bb : Basis} {e : Term}
    {sv' : ValSpace} {env : Fin (ValSpace.dofUB sv') → ValExpr} {L : Finset VName}
    (htof' : Basis.tof b' = .space (Basis.sof b'))
    (hsv' : ValSpace.EvalS Ψ (Basis.sof b') sv')
    (ih_hfam : ∀ y, y ∉ L → ∀ i : Fin (ValSpace.dofUB sv'),
      fvMotive4 (Ψ.extend y b' (.delta i.val sv')) (Term.openVar y e) bb (env i) True)
    (hΨ : EvalCtxValidPlus Ψ) (hfvsv' : ValSpace.fv sv' ⊆ Ψ.keyNames) :
    ∀ i : Fin (ValSpace.dofUB sv'), ValExpr.fv (env i) ⊆ Ψ.keyNames := by
  intro i
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset (L ∪ Ψ.keyNames ∪ ValExpr.fv (env i))
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at hy
  obtain ⟨⟨hyL, hykn⟩, hyfv⟩ := hy
  have hfresh : (y, b') ∉ Ψ :=
    fun hc => hykn (Finset.mem_image_of_mem Prod.fst (Finmap.mem_keys.mpr hc))
  have hΨ'' := evalCtxValidPlus_extend_delta (i := i.val) hΨ hfresh hfvsv'
    (realize_lc_joint.1 hsv' hΨ.toEvalCtxLc)
    (by rw [htof']; exact ValTy.EvalT.space hsv')
  have hres := ih_hfam y hyL i hΨ''
  rw [keyNames_extend] at hres
  exact fun w hw => (Finset.mem_insert.mp (hres hw)).resolve_left
    (fun h => hyfv (h ▸ hw))

private theorem evalFv_oLlamAssemble {Ψ : EvalCtx} {b' b : Basis} {e : Term}
    {sv' sv : ValSpace} {env : Fin (ValSpace.dofUB sv') → ValExpr}
    (htof' : Basis.tof b' = .space (Basis.sof b'))
    (hsv' : ValSpace.EvalS Ψ (Basis.sof b') sv')
    (_hsv : ValSpace.EvalS Ψ (Basis.sof b) sv)
    (L : Finset VName)
    (_hfam : ∀ y, y ∉ L → ∀ i : Fin (ValSpace.dofUB sv'),
      ValExpr.OpStep (Ψ.extend y b' (.delta i.val sv')) (Term.openVar y e) b (env i))
    (ih_hsv' : fvMotive1 Ψ (Basis.sof b') sv' True)
    (ih_hsv : fvMotive1 Ψ (Basis.sof b) sv True)
    (ih_hfam : ∀ y, y ∉ L → ∀ i : Fin (ValSpace.dofUB sv'),
      fvMotive4 (Ψ.extend y b' (.delta i.val sv')) (Term.openVar y e) b (env i) True) :
    fvMotive4 Ψ (.llam (Basis.sof b') (Basis.sof b) e) (.tprod (.dual b') b)
      (.sumAt sv' (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
        .tprodE (.delta i.val sv') (.reshap (env i) (.space sv) (.space sv)))
        (.tprod sv' sv)) True := by
  intro hΨ
  have hfvsv' := ih_hsv' hΨ
  have hfvsv := ih_hsv hΨ
  have hfvenv := llam_family_fv_drop htof' hsv' ih_hfam hΨ hfvsv'
  have hfvtgt : ValTy.fv (.space (.tprod sv' sv)) ⊆ Ψ.keyNames := by
    simp only [ValTy.fv, ValSpace.fv]
    exact Finset.union_subset hfvsv' hfvsv
  simp only [ValExpr.fv_sumAt, ValExpr.reshapBase, ValExpr.fv]
  refine Finset.union_subset (Finset.union_subset (Finset.union_subset hfvsv' ?_) hfvtgt) hfvtgt
  intro w hw
  obtain ⟨el, hel, hwel⟩ := ValExpr.mem_fvList.mp hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hel
  simp only [ValExpr.fv, ValTy.fv, Finset.mem_union] at hwel
  rcases hwel with h | ((h | h) | h)
  · exact hfvsv' h
  · exact hfvenv i h
  · exact hfvsv h
  · exact hfvsv h

private theorem evalFv_oLlamAssembleReal {Ψ : EvalCtx} {b' : Basis} {e : Term}
    {sv' : ValSpace} {env : Fin (ValSpace.dofUB sv') → ValExpr}
    (htof' : Basis.tof b' = .space (Basis.sof b'))
    (hsv' : ValSpace.EvalS Ψ (Basis.sof b') sv')
    (L : Finset VName)
    (_hfam : ∀ y, y ∉ L → ∀ i : Fin (ValSpace.dofUB sv'),
      ValExpr.OpStep (Ψ.extend y b' (.delta i.val sv')) (Term.openVar y e) .one (env i))
    (ih_hsv' : fvMotive1 Ψ (Basis.sof b') sv' True)
    (ih_hfam : ∀ y, y ∉ L → ∀ i : Fin (ValSpace.dofUB sv'),
      fvMotive4 (Ψ.extend y b' (.delta i.val sv')) (Term.openVar y e) .one (env i) True) :
    fvMotive4 Ψ (.llam (Basis.sof b') .real e) (.dual b')
      (.sumAt sv' (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
        .scale (.reshap (env i) (.space .real) (.space .real)) (.delta i.val sv')) sv') True := by
  intro hΨ
  have hfvsv' := ih_hsv' hΨ
  have hfvenv := llam_family_fv_drop htof' hsv' ih_hfam hΨ hfvsv'
  have hfvtgt : ValTy.fv (.space sv') ⊆ Ψ.keyNames := by
    simp only [ValTy.fv]
    exact hfvsv'
  simp only [ValExpr.fv_sumAt, ValExpr.reshapBase, ValExpr.fv]
  refine Finset.union_subset (Finset.union_subset (Finset.union_subset hfvsv' ?_) hfvtgt) hfvtgt
  intro w hw
  obtain ⟨el, hel, hwel⟩ := ValExpr.mem_fvList.mp hw
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hel
  simp only [ValExpr.fv, ValTy.fv, ValSpace.fv, Finset.mem_union,
    Finset.notMem_empty, or_false, false_or] at hwel
  rcases hwel with h | h
  · exact hfvenv i h
  · exact hfvsv' h

private theorem evalFv_oZero {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    (_htof : Basis.tof b = .space (Basis.sof b))
    (_hsv : ValSpace.EvalS Ψ (Basis.sof b) sv)
    (ih_hsv : fvMotive1 Ψ (Basis.sof b) sv True) :
    fvMotive4 Ψ (.zero (Basis.sof b)) b (.zero sv) True := by
  intro hΨ; simp only [ValExpr.fv]; exact ih_hsv hΨ

private theorem evalFv_oRlit {Ψ : EvalCtx} (r : ℝ) :
    fvMotive4 Ψ (.real r) .one (.rlit r) True := by
  intro _; exact Finset.empty_subset _

/-- All four operational fv-scoping facts, jointly, via ONE shared-recursor call.
    The named entry-points (`evalS_fv` / `evalT_fv` / `evalBB_fv` / `opStep_fv`)
    project out of this. -/
private theorem eval_fv_joint :
    (∀ {Ψ s sv}, ValSpace.EvalS Ψ s sv → fvMotive1 Ψ s sv True)
  ∧ (∀ {Ψ τ τv}, ValTy.EvalT Ψ τ τv → fvMotive2 Ψ τ τv True)
  ∧ (∀ {Ψ b env b'}, Basis.EvalBB Ψ b env b' → fvMotive3 Ψ b env b' True)
  ∧ (∀ {Ψ e b v}, ValExpr.OpStep Ψ e b v → fvMotive4 Ψ e b v True) := by
  refine ⟨@fun Ψ s sv h => ?_, @fun Ψ τ τv h => ?_, @fun Ψ b env b' h => ?_,
          @fun Ψ e b v h => ?_⟩
  all_goals
    first
    | exact h.rec
        (motive_1 := fun Ψ s sv _ => fvMotive1 Ψ s sv True)
        (motive_2 := fun Ψ τ τv _ => fvMotive2 Ψ τ τv True)
        (motive_3 := fun Ψ b env b' _ => fvMotive3 Ψ b env b' True)
        (motive_4 := fun Ψ e b v _ => fvMotive4 Ψ e b v True)
        evalFv_eReal evalFv_eEmpty evalFv_eDual evalFv_eKer evalFv_eCoker
        evalFv_eImg evalFv_eCoimg evalFv_eTprod evalFv_eDsum
        evalFv_eTspace evalFv_eTpiTy
        evalFv_bInv evalFv_bTrans evalFv_bTprod evalFv_bDsum evalFv_bDualStd
        evalFv_bImage evalFv_bImageSvds evalFv_bProjKC evalFv_bProjIC
        evalFv_bTermsRref evalFv_bRefl evalFv_bProjKCCod evalFv_bProjICDom
        evalFv_oVar evalFv_oCob evalFv_oScale evalFv_oAdd evalFv_oDsumE
        evalFv_oTprodE evalFv_oPinvTStd evalFv_oPinvTGpinv evalFv_oPinvDStd
        evalFv_oPinvDGpinv evalFv_oInnerStd evalFv_oEmbedKer evalFv_oEmbedCoker
        evalFv_oEmbedImg evalFv_oEmbedCoimg evalFv_oAppL evalFv_oAppI
        evalFv_oNllam evalFv_oAppNVal evalFv_oFrameReanchor
        evalFv_oFrameEta evalFv_oReshape evalFv_oLlamAssemble
        evalFv_oLlamAssembleReal evalFv_oZero evalFv_oRlit

theorem evalS_fv {Ψ : EvalCtx} {s : Space} {sv : ValSpace}
    (h : ValSpace.EvalS Ψ s sv) (hΨ : EvalCtxValidPlus Ψ) : ValSpace.fv sv ⊆ Ψ.keyNames :=
  eval_fv_joint.1 h hΨ

theorem evalT_fv {Ψ : EvalCtx} {τ : Ty} {τv : ValTy}
    (h : ValTy.EvalT Ψ τ τv) (hΨ : EvalCtxValidPlus Ψ) : ValTy.fv τv ⊆ Ψ.keyNames :=
  eval_fv_joint.2.1 h hΨ

theorem evalBB_fv {Ψ : EvalCtx} {b : Basis} {env : ValExpr} {b' : Basis}
    (h : Basis.EvalBB Ψ b env b') (hΨ : EvalCtxValidPlus Ψ) : ValExpr.fv env ⊆ Ψ.keyNames :=
  eval_fv_joint.2.2.1 h hΨ

theorem opStep_fv {Ψ : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e b v) (hΨ : EvalCtxValidPlus Ψ) : ValExpr.fv v ⊆ Ψ.keyNames :=
  eval_fv_joint.2.2.2 h hΨ

/-- **The `ESubst` construction for dependent application.** Discharging the
    fresh placeholder `(y,b₀)↦.var y
    τv₀` from `extend Ψ₀ y b₀ (.var y τv₀)` back to `Ψ₀`, substituting `y↦n₁`
    (source) / `y↦env₁` (value). -/
theorem appN_esubst {Ψ₀ : EvalCtx} {y : VName} {b₀ : Basis} {τv₀ : ValTy}
    {n₁ : Term} {env₁ : ValExpr}
    (hyfresh : ∀ b, (y, b) ∉ Ψ₀) (hyb₀ : y ∉ Basis.fv b₀)
    (hyv : ∀ z b v, EvalCtx.lookup Ψ₀ (z, b) = some v → y ∉ ValExpr.fv v)
    (hyb : ∀ z b v, EvalCtx.lookup Ψ₀ (z, b) = some v → y ∉ Basis.fv b)
    (hlcn : Term.lc n₁) (hlcenv₁ : ValExpr.lc env₁)
    (hinferarg : ValExpr.inferSpace env₁ = ValSpace.subst y env₁ (ValTy.spaceOf τv₀))
    (htypearg : ValExpr.inferType env₁ = ValTy.subst y env₁ τv₀)
    (hcut : ValExpr.OpStep Ψ₀ n₁ b₀ env₁) :
    ESubst y b₀ τv₀ n₁ env₁ (EvalCtx.extend Ψ₀ y b₀ (.var y τv₀)) Ψ₀ := by
  refine ⟨?_, ?_, ?_, ?_, hlcn, hlcenv₁, ?_, ?_⟩
  · -- xbind
    rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert]
  · -- xonly: `y` is bound only at `b₀` (it is fresh in `Ψ₀`).
    intro b' v' hl
    by_cases hk : (y, b') = (y, b₀)
    · exact congrArg Prod.snd hk
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      exact absurd (Finmap.mem_of_lookup_eq_some hl) (hyfresh b')
  · -- hcut: `subst y n₁ b₀ = b₀` (y ∉ fv b₀), so it is exactly `hcut`.
    rw [Basis.subst_fresh y n₁ b₀ hyb₀]; exact hcut
  · -- fwd: every surviving binding is `y`-free, so both substitutions are identity.
    intro z b v hzy hl
    have hk : (z, b) ≠ (y, b₀) := fun h => hzy (congrArg Prod.fst h)
    rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
    rw [Basis.subst_fresh y n₁ b (hyb z b v hl),
        ValExpr.subst_fresh y env₁ v (hyv z b v hl)]
    exact hl
  · -- hinfer: the placeholder commutes by `hinferarg` (the argument's space IS the
    -- annotation's, `y`-freshly); surviving bindings are `y`-free on the nose AND
    -- in their `inferSpace` (via `fv_inferSpace_subset`), so both sides are identity.
    intro z b v hl
    by_cases hk : (z, b) = (y, b₀)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      simp only [ValExpr.subst, if_pos rfl, ValExpr.inferSpace]
      exact hinferarg
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      rw [ValExpr.subst_fresh y env₁ v (hyv z b v hl),
          ValSpace.subst_fresh y env₁ _
            (fun hm => hyv z b v hl (ValExpr.fv_inferSpace_subset v hm))]

  · intro z b v hl
    unfold InferTypeSubstAt
    by_cases hk : (z, b) = (y, b₀)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
      subst hl
      simpa only [ValExpr.subst, if_pos rfl, ValExpr.inferType] using htypearg
    · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
      rw [ValExpr.subst_fresh y env₁ v (hyv z b v hl),
        ValTy.subst_fresh y env₁ _ (fun hm => hyv z b v hl (ValExpr.fv_inferType_subset v hm))]

/-- **The EvalT-realization core of nonlinear application.** Given the
    `ESubst` (`appN_esubst`) and the cofinite codomain `EvalT` at a fresh
    `y`, the dependent-preservation substitution `evalT_substC` realizes the
    substituted codomain, which `subst_intro` + `tof_openRec` re-align to the redex
    result basis's type `(Basis.instantiate n₁ b₁).tof`. The witness type is
    `subst y env₁ (openVar y τv₀ τv₁)` = `instantiate env₁ τv₁`. -/
theorem appN_realize_core {Ψ₀ : EvalCtx} {y : VName} {b₀ b₁ : Basis} {τv₀ τv₁ : ValTy}
    {n₁ : Term} {env₁ : ValExpr}
    (hes : ESubst y b₀ τv₀ n₁ env₁ (EvalCtx.extend Ψ₀ y b₀ (.var y τv₀)) Ψ₀)
    (hyfvb₁ : y ∉ Ty.fv (Basis.tof b₁))
    (hcod : ValTy.EvalT (EvalCtx.extend Ψ₀ y b₀ (.var y τv₀))
              (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁)) :
    ValTy.EvalT Ψ₀ (Basis.instantiate n₁ b₁).tof
      (ValTy.subst y env₁ (ValTy.openVar y τv₀ τv₁)) := by
  have hsub := evalT_substC hcod hes
  have halign : (Basis.instantiate n₁ b₁).tof
      = Ty.subst y n₁ (Ty.openVar y (Basis.tof b₁)) := by
    show Basis.tof (Basis.openRec 0 n₁ b₁)
        = Ty.subst y n₁ (Ty.openRec 0 (.var y) (Basis.tof b₁))
    rw [Basis.tof_openRec, ← Ty.subst_intro y n₁ (Basis.tof b₁) hyfvb₁ 0]
  rw [← halign] at hsub
  exact hsub

/-! ## The preservation motives (abbrevs, so the four entry points share arms). -/

/-- Part-3 motive: a realized value space is valid + key-scoped. -/
abbrev pMotive1 (Ψ' : EvalCtx) (s' : Space) (sv' : ValSpace) : Prop :=
  ∀ (_Δ' : LCtx) (Γ' : NLCtx) (ρ' : ValScope),
    EvalCtxValidPlus Ψ' → RhoValid Ψ' ρ' → KeyScope Ψ' ρ' →
    SValid Γ' s' → Nonempty (ValSValidC sv') ∧ ValSpace.fv sv' ⊆ Ψ'.keyNames

/-- EvalT-regularity motive. -/
abbrev pMotive2 (Ψ' : EvalCtx) (τ' : Ty) (τv' : ValTy) : Prop :=
  ∀ (_Δ' : LCtx) (Γ' : NLCtx) (ρ' : ValScope) (_k : Kind),
    EvalCtxValidPlus Ψ' → RhoValid Ψ' ρ' → KeyScope Ψ' ρ' →
    TValid Γ' τ' _k → ValTyOk τv' ∧ ValTy.fv τv' ⊆ Ψ'.keyNames

/-- Part-2 motive: COB-witness shape (the target basis is dropped — unused). -/
abbrev pMotive3 (Ψ' : EvalCtx) (bsrc : Basis) (env' : ValExpr) : Prop :=
  ∀ (_Δ' : LCtx) (Γ' : NLCtx) (ρ' : ValScope),
    EvalCtxValidPlus Ψ' → RhoValid Ψ' ρ' → KeyScope Ψ' ρ' →
    SValid Γ' (Basis.sof bsrc) → CobShapeT Ψ' env' Ψ'.keyNames

/-- Part-1 motive: term preservation. -/
abbrev pMotive4 (Ψ' : EvalCtx) (e' : Term) (b' : Basis) (v' : ValExpr) : Prop :=
  ∀ (Δ' : LCtx) (Γ' : NLCtx) (ρ' : ValScope),
    EvalCtxValidPlus Ψ' → RhoValid Ψ' ρ' → KeyScope Ψ' ρ' →
      HasType Δ' Γ' e' (Basis.tof b') → SValid Γ' (Basis.sof b') →
        (∃ τv, ValTy.EvalT Ψ' (Basis.tof b') τv
              ∧ ReshapEq (ValExpr.inferType v') τv)
        ∧ ValTyOk (ValExpr.inferType v')
        ∧ (ValTy.fv (ValExpr.inferType v') ∪ ValExpr.fv v' ⊆ Ψ'.keyNames)

/-- **`proj_*_cod/dom` arm helper** (P6a one-side-pinned proj conversions).
    The 2-factor sandwich
    `mtm 0 0 svA svA (reshap env₁ (svA⊗sv')) (reshap env₃ (sv⊗svA))` has
    inferType `.space (sv ⊗ sv')` — both factors realizations of the SAME
    subspace `s` — exactly `term_bb_proj_ker_coker_v2` minus the COB middle
    factor (`svA` = the unchanged-ambient realization: `sv₀` for
    `proj_ker_coker_cod`, `sv₁` for `proj_img_coimg_dom`). -/
private theorem term_bb_proj_sandwich_v2 {Ψ : EvalCtx} {ρ' : Finset VName}
    {env₁ env₃ : ValExpr} {svA sv sv' : ValSpace} {s : Space}
    (hsv  : ValSpace.EvalS Ψ s sv)
    (hsv' : ValSpace.EvalS Ψ s sv')
    (hsvval  : Nonempty (ValSValidC sv))
    (hsv'val : Nonempty (ValSValidC sv'))
    (hfvsvA : ValSpace.fv svA ⊆ ρ')
    (hfvsv  : ValSpace.fv sv ⊆ ρ') (hfvsv' : ValSpace.fv sv' ⊆ ρ')
    (hfvenv₁ : ValExpr.fv env₁ ⊆ ρ') (hfvenv₃ : ValExpr.fv env₃ ⊆ ρ') :
    CobShapeT Ψ
      (.mtm 0 0 svA svA
        (.reshap env₁ (.space (.tprod svA sv')) (.space (.tprod svA sv')))
        (.reshap env₃ (.space (.tprod sv svA)) (.space (.tprod sv svA)))) ρ' := by
  obtain ⟨vsv⟩ := hsvval
  obtain ⟨vsv'⟩ := hsv'val
  have hinfer : ValExpr.inferType
      (.mtm 0 0 svA svA
        (.reshap env₁ (.space (.tprod svA sv')) (.space (.tprod svA sv')))
        (.reshap env₃ (.space (.tprod sv svA)) (.space (.tprod sv svA))))
        = .space (.tprod sv sv') := by
    simp only [ValExpr.inferType]
  refine ⟨⟨s, s, sv, sv', hinfer, hsv, hsv'⟩, ?_, ?_⟩
  · rw [hinfer]; exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod vsv vsv')⟩⟩
  · simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
    repeat' apply Finset.union_subset
    all_goals first
      | exact hfvsvA | exact hfvsv | exact hfvsv'
      | exact hfvenv₁ | exact hfvenv₃

set_option maxHeartbeats 4000000 in

theorem preservation_master :
    (∀ {Ψ : EvalCtx} {s : Space} {sv : ValSpace},
        ValSpace.EvalS Ψ s sv → pMotive1 Ψ s sv)
  ∧ (∀ {Ψ : EvalCtx} {τ : Ty} {τv : ValTy},
        ValTy.EvalT Ψ τ τv → pMotive2 Ψ τ τv)
  ∧ (∀ {Ψ : EvalCtx} {b : Basis} {env : ValExpr} {b' : Basis},
        Basis.EvalBB Ψ b env b' → pMotive3 Ψ b env)
  ∧ (∀ {Ψ : EvalCtx} {e : Term} {b : Basis} {v : ValExpr},
        ValExpr.OpStep Ψ e b v → pMotive4 Ψ e b v) := by
  refine ⟨@fun Ψ s sv h => ?_, @fun Ψ τ τv h => ?_,
          @fun Ψ b env b' h => ?_, @fun Ψ e b v h => ?_⟩
  all_goals
    exact h.rec
      (motive_1 := fun Ψ' s' sv' _ => pMotive1 Ψ' s' sv')
      (motive_2 := fun Ψ' τ' τv' _ => pMotive2 Ψ' τ' τv')
      (motive_3 := fun Ψ' bsrc env' _ _ => pMotive3 Ψ' bsrc env')
      (motive_4 := fun Ψ' e' b' v' _ => pMotive4 Ψ' e' b' v')
      -- EvalS structural arms (part 3): cases on `SValid`, recurse, build ValSValidC + fv.
      -- arm: eReal
      (by
        intro _ _ _ _ _ _ _ _; exact ⟨⟨.real⟩, Finset.empty_subset _⟩)
      -- arm: eEmpty
      (by
        intro _ _ _ _ _ _ _ _; exact ⟨⟨.empty⟩, Finset.empty_subset _⟩)
      -- arm: eDual
      (by
        intro _ _ _ _ ih Δ' Γ' ρ' hΨ' hρ' hkey hsv'
        cases hsv' with
        | dual hs => exact ih Δ' Γ' ρ' hΨ' hρ' hkey hs)
      -- EvalS ker (part 3, FFS cross-part): the witness is reshaped to svb, so its
      -- inferType IS svb (no witness typing needed for ValSValidC); the part-1 IH on
      -- the witness OpStep supplies only fv leev ⊆ ρ'.
      -- arm: eKer
      (by
        intro _ s₀ s₁ e b leev svb he hb hcompat hsvb ih_he ih_svb _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        cases hsval with
        | ker hs0 hs1 hwit =>
          have hSsofb : SValid Γ' (Basis.sof b) := by rw [hb]; exact .tprod (.dual hs0) hs1
          obtain ⟨svbval, hfvsvb⟩ := ih_svb ∅ Γ' ρ' hΨ' hρ' hkey hSsofb
          obtain ⟨sva, svb1, rfl⟩ := evalS_tprod_inv (hb ▸ hsvb)
          obtain ⟨svbv⟩ := svbval
          obtain ⟨hsva, hsvb1⟩ := valSValidC_tprod_inv svbv
          have hwit' : HasType ∅ Γ' e (Basis.tof b) := by
            rw [hcompat.tof_eq_space, hb]
            exact hwit
          obtain ⟨_, _, hfvleev_u⟩ := ih_he ∅ Γ' ρ' hΨ' hρ' hkey hwit' hSsofb
          have hfvleev := Finset.Subset.trans Finset.subset_union_right hfvleev_u
          exact ⟨⟨ValSValidC.ffs hsva hsvb1 rfl⟩,
            Finset.union_subset hfvsvb
              (Finset.union_subset (Finset.union_subset hfvleev hfvsvb) hfvsvb)⟩)
      -- EvalS coker/img/coimg: identical to ker modulo prop tag; via term_ffs_v2.
      -- arm: eCoker
      (by
        intro _ s₀ s₁ e b leev svb he hb hcompat hsvb ih_he ih_svb _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        cases hsval with
        | coker hs0 hs1 hwit =>
          have hSsofb : SValid Γ' (Basis.sof b) := by rw [hb]; exact .tprod (.dual hs0) hs1
          obtain ⟨svbval, hfvsvb⟩ := ih_svb ∅ Γ' ρ' hΨ' hρ' hkey hSsofb
          have hwit' : HasType ∅ Γ' e (Basis.tof b) := by
            rw [hcompat.tof_eq_space, hb]
            exact hwit
          obtain ⟨_, _, hfvleev_u⟩ := ih_he ∅ Γ' ρ' hΨ' hρ' hkey hwit' hSsofb
          exact term_ffs_v2 .cokernel hb hsvb svbval hfvsvb
            (Finset.Subset.trans Finset.subset_union_right hfvleev_u))
      -- arm: eImg
      (by
        intro _ s₀ s₁ e b leev svb he hb hcompat hsvb ih_he ih_svb _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        cases hsval with
        | img hs0 hs1 hwit =>
          have hSsofb : SValid Γ' (Basis.sof b) := by rw [hb]; exact .tprod (.dual hs0) hs1
          obtain ⟨svbval, hfvsvb⟩ := ih_svb ∅ Γ' ρ' hΨ' hρ' hkey hSsofb
          have hwit' : HasType ∅ Γ' e (Basis.tof b) := by
            rw [hcompat.tof_eq_space, hb]
            exact hwit
          obtain ⟨_, _, hfvleev_u⟩ := ih_he ∅ Γ' ρ' hΨ' hρ' hkey hwit' hSsofb
          exact term_ffs_v2 .image hb hsvb svbval hfvsvb
            (Finset.Subset.trans Finset.subset_union_right hfvleev_u))
      -- arm: eCoimg
      (by
        intro _ s₀ s₁ e b leev svb he hb hcompat hsvb ih_he ih_svb _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        cases hsval with
        | coimg hs0 hs1 hwit =>
          have hSsofb : SValid Γ' (Basis.sof b) := by rw [hb]; exact .tprod (.dual hs0) hs1
          obtain ⟨svbval, hfvsvb⟩ := ih_svb ∅ Γ' ρ' hΨ' hρ' hkey hSsofb
          have hwit' : HasType ∅ Γ' e (Basis.tof b) := by
            rw [hcompat.tof_eq_space, hb]
            exact hwit
          obtain ⟨_, _, hfvleev_u⟩ := ih_he ∅ Γ' ρ' hΨ' hρ' hkey hwit' hSsofb
          exact term_ffs_v2 .coimage hb hsvb svbval hfvsvb
            (Finset.Subset.trans Finset.subset_union_right hfvleev_u))
      -- arm: eTprod
      (by
        intro _ _ _ _ _ _ _ ih₀ ih₁ Δ' Γ' ρ' hΨ' hρ' hkey hsv'
        cases hsv' with
        | tprod hs0 hs1 =>
          obtain ⟨n0, f0⟩ := ih₀ Δ' Γ' ρ' hΨ' hρ' hkey hs0
          obtain ⟨n1, f1⟩ := ih₁ Δ' Γ' ρ' hΨ' hρ' hkey hs1
          obtain ⟨v0⟩ := n0; obtain ⟨v1⟩ := n1
          exact ⟨⟨.tprod v0 v1⟩, Finset.union_subset f0 f1⟩)
      -- arm: eDsum
      (by
        intro _ _ _ _ _ _ _ ih₀ ih₁ Δ' Γ' ρ' hΨ' hρ' hkey hsv'
        cases hsv' with
        | dsum hs0 hs1 =>
          obtain ⟨n0, f0⟩ := ih₀ Δ' Γ' ρ' hΨ' hρ' hkey hs0
          obtain ⟨n1, f1⟩ := ih₁ Δ' Γ' ρ' hΨ' hρ' hkey hs1
          obtain ⟨v0⟩ := n0; obtain ⟨v1⟩ := n1
          exact ⟨⟨.dsum v0 v1⟩, Finset.union_subset f0 f1⟩)
      -- EvalT space (motive_2, EvalT-regularity): a realized space is valid via part-3.
      -- arm: eTspace
      (by
        intro _ s sv h ih_s _Δ' Γ' ρ' _k hΨ' hρ' hkey htv
        cases htv with
        | space hs =>
          obtain ⟨svval, hfvsv⟩ := ih_s ∅ Γ' ρ' hΨ' hρ' hkey hs
          obtain ⟨svv⟩ := svval
          exact ⟨⟨.base, ⟨ValTValidC.space svv⟩⟩, hfvsv⟩)
      -- EvalT piTy (motive_2, EvalT-regularity for a dependent function type). Domain
      -- validity from `ih₀`; the codomain SOURCE typing at a fresh `z` is the COFINITE
      -- `TValid.piTy` premise `hcod z` DIRECTLY (LN: no `TValid.rename_binder`, no
      -- `x∉bound τ₁`), fed to `ih₁` under the extend helpers, then assembled into
      -- `ValTValidC.piTy`. The `fv` of the codomain is recovered from the opened IH `fv`
      -- via `fv_subset_openRec` + a fresh-`z` drop.
      -- arm: eTpiTy
      (by
        -- LN re-proof: assemble `ValTValidC.piTy` by feeding the opened-codomain
        -- validity (`ih₁` at fresh `z`, under the extend helpers + the cofinite source
        -- codomain typing `hcod z`) DIRECTLY to the cofinite constructor. The codomain
        -- kind is uniform (`τv₁.structuralKind`, openRec-invariant). `fv τv₁` is
        -- recovered from the opened IH `fv` via `fv_subset_openRec` + a fresh-`z` drop.
        intro _Ψ b₀ τ₀ τ₁ τv₀ τv₁ h₀ hb L h₁ ih₀ ih₁ _Δ' Γ' ρ' _k hΨ' hρ' hkey htv
        cases htv with
        | @piTy _ _ _ k₀ k₁ Lτ hdom hcod =>
          obtain ⟨⟨k₀v, ⟨vτv₀⟩⟩, hfv₀⟩ := ih₀ _Δ' Γ' ρ' k₀ hΨ' hρ' hkey hdom
          have hev0 : ValTy.EvalT _Ψ (Basis.tof b₀) τv₀ := by rw [hb]; exact h₀
          -- the opened-codomain IH, valid for any `z` outside the exclusion set.
          have codIH : ∀ z, z ∉ L ∪ _Ψ.keyNames ∪ Γ'.keys ∪ Lτ →
              ValTyOk (ValTy.openVar z τv₀ τv₁) ∧
              ValTy.fv (ValTy.openVar z τv₀ τv₁) ⊆ insert z _Ψ.keyNames := by
            intro z hz
            simp only [Finset.mem_union, not_or] at hz
            obtain ⟨⟨⟨hzL, hzkn⟩, _hzΓ⟩, hzLτ⟩ := hz
            have hfresh : (z, b₀) ∉ _Ψ :=
              fun hc => hzkn (Finset.mem_image_of_mem Prod.fst (Finmap.mem_keys.mpr hc))
            have hΨ'' := evalCtxValidPlus_extend hΨ' hfresh hfv₀ hev0
            have hρ'' : RhoValid (EvalCtx.extend _Ψ z b₀ (.var z τv₀)) (insert z ρ') :=
              rhoValid_extend hρ' hzkn hkey ⟨k₀v, ⟨vτv₀⟩⟩ hfv₀
            have hkey'' : KeyScope (EvalCtx.extend _Ψ z b₀ (.var z τv₀)) (insert z ρ') :=
              keyScope_extend hkey
            have hTV := hcod z hzLτ
            have hres := ih₁ z hzL _Δ' _ (insert z ρ') k₁ hΨ'' hρ'' hkey'' hTV
            rwa [keyNames_extend] at hres
          -- codomain validity at the uniform kind `τv₁.structuralKind` (per-`z` via
          -- `Classical.choice`, since the IH only gives `Nonempty`).
          have hpiv : Nonempty (ValTValidC (.piTy τv₀ τv₁) (.arrow k₀v τv₁.structuralKind)) :=
            ⟨ValTValidC.piTy (L ∪ _Ψ.keyNames ∪ Γ'.keys ∪ Lτ) vτv₀
              (fun z hz => Classical.choice (by
                obtain ⟨kz, ⟨vcz⟩⟩ := (codIH z hz).1
                have hkz : kz = τv₁.structuralKind := by
                  rw [ValTValidC.kind_eq_structural vcz, ValTy.openVar, ValTy.structuralKind_openRec]
                exact ⟨hkz ▸ vcz⟩))⟩
          refine ⟨⟨_, hpiv⟩, ?_⟩
          · -- `fv (.piTy τv₀ τv₁) = fv τv₀ ∪ fv τv₁ ⊆ keyNames`.
            obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
              (L ∪ _Ψ.keyNames ∪ Γ'.keys ∪ Lτ ∪ ValTy.fv τv₁)
            rw [Finset.mem_union, not_or] at hz
            obtain ⟨hzbig, hzfv⟩ := hz
            obtain ⟨_, hcodfv⟩ := codIH z hzbig
            have hfvτv₁ : ValTy.fv τv₁ ⊆ _Ψ.keyNames := by
              intro w hw
              have hw' : w ∈ ValTy.fv (ValTy.openVar z τv₀ τv₁) := ValTy.fv_subset_openRec hw
              rcases Finset.mem_insert.mp (hcodfv hw') with rfl | hwk
              · exact absurd hw hzfv
              · exact hwk
            simp only [ValTy.fv]
            exact Finset.union_subset hfv₀ hfvτv₁)
      -- EvalBB inverse (part 2 producer): swap the sub-CobShape's factors.
      -- arm: bInv
      (by
        intro _ b₀ b₁ leev h ih _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        have hsofeq : Basis.sof b₁ = Basis.sof b₀ := Basis.EvalBB.sof_eq h
        obtain ⟨⟨s₀, s₁, sv₀, sv₁, hinfer, hes0, hes1⟩, hok, hfv⟩ :=
          ih ∅ Γ' ρ' hΨ' hρ' hkey (by rw [hsofeq]; exact hsval)
        obtain ⟨_, ⟨hokv⟩⟩ := hok
        rw [hinfer] at hokv
        obtain ⟨hsv0, hsv1⟩ := valSValidC_tprod_inv (valTValidC_space_inv hokv)
        have hinv : ValExpr.inferType (.inv leev) = .space (.tprod sv₁ sv₀) := by
          simp only [ValExpr.inferType, hinfer]
        refine ⟨⟨s₁, s₀, sv₁, sv₀, hinv, hes1, hes0⟩, ?_, hfv⟩
        rw [hinv]; exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod hsv1 hsv0)⟩⟩)

      (by
        intro _ b₀ b₁ b₂ env₀ env₁ sv h₀ h₁ hsv ih_h₀ ih_h₁ ih_hsv _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        have hsofeq : Basis.sof b₀ = Basis.sof b₁ := Basis.EvalBB.sof_eq h₀
        obtain ⟨hsvval, hfvsv⟩ := ih_hsv ∅ Γ' ρ' hΨ' hρ' hkey hsval
        exact term_bb_trans_v2 hsv hsvval hfvsv
          (ih_h₀ ∅ Γ' ρ' hΨ' hρ' hkey hsval)
          (ih_h₁ ∅ Γ' ρ' hΨ' hρ' hkey (by rw [← hsofeq]; exact hsval)))
      -- arm: bTprod (premises aligned with `dsum`, erratum G3-E1: `b₀' →_{env₀} b₀`)
      (by
        intro _ b₀ b₁ b₀' b₁' env₀ env₁ h₀ h₁ ih_h₀ ih_h₁ _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        cases hsval with
        | tprod hs0 hs1 =>
          exact term_bb_tprod_v2 (ih_h₀ ∅ Γ' ρ' hΨ' hρ' hkey hs0)
            (ih_h₁ ∅ Γ' ρ' hΨ' hρ' hkey hs1))
      -- arm: bDsum
      (by
        intro _ b₀ b₁ b₀' b₁' env₀ env₁ h₀ h₁ ih_h₀ ih_h₁ _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        cases hsval with
        | dsum hs0 hs1 =>
          exact term_bb_dsum_v2 (ih_h₀ ∅ Γ' ρ' hΨ' hρ' hkey hs0)
            (ih_h₁ ∅ Γ' ρ' hΨ' hρ' hkey hs1))
      -- EvalBB dual_std (part-2 producer): witness `vtrans (inv leev)` has the SAME
      -- inferType as `leev` (inv flips the tprod, vtrans flips it back), so CobShapeT
      -- is inherited from the sub-derivation on `leev`.
      -- arm: bDualStd
      (by
        intro _ b₀ leev htof hb₁ ih_hb₁ _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        -- `hsval : SValid Γ' (.dual (sof b₀))`; peel the dual to feed the IH.
        have hsofb₀ : SValid Γ' (Basis.sof b₀) := by
          cases hsval with | dual h => exact h
        exact term_bb_dual_std_v2 (ih_hb₁ ∅ Γ' ρ' hΨ' hρ' hkey hsofb₀))
      -- EvalBB image (part-2 producer): witness is the SAME `leev`; CobShapeT inherited.
      -- arm: bImage
      (by
        intro _ b₀ b₀' leev hcoker h ih_h _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        -- `hsval : SValid Γ' (sof (.image b₀))`; with `sof b₀ = coker s₀ s₁ e`,
        -- `sof (.image b₀) = .img s₀ s₁ e`, whose validity rebuilds `SValid (sof b₀)`.
        obtain ⟨s₀, s₁, e, hcok⟩ := hcoker
        have hsofb₀ : SValid Γ' (Basis.sof b₀) := by
          rw [hcok]
          have himg : Basis.sof (.image b₀) = .img s₀ s₁ e := by
            simp only [Basis.sof, hcok]
          rw [himg] at hsval
          cases hsval with | img h0 h1 he => exact .coker h0 h1 he
        exact term_bb_image_v2 (ih_h ∅ Γ' ρ' hΨ' hρ' hkey hsofb₀))
      -- EvalBB image_svds (part-2 producer): the §9.17-corrected witness is the
      -- SVDS reshaped to the canonical `coker-realization ⊗ img-realization`
      -- matrix, so its inferType IS that tprod literally; the factor realizations
      -- come from `EvalS.coker`/`EvalS.img` on the rule's own premises; validity
      -- free via `evalT_valid`; fv from the witness/realization fv lemmas (no
      -- typing/SValid use at all).
      -- arm: bImageSvds
      (by
        intro _Ψ b₀ b₁ e leev s₀ s₁ svb hs₀ hs₁ _hb₀ _hb₁ he hsvb _ih_he _ih_hsvb
              _Δ' Γ' ρ' hΨ' _hρ' _hkey _hsval
        have hb : Basis.sof (.tprod (.dual b₀) b₁) = .tprod (.dual s₀) s₁ := by
          simp only [Basis.sof, hs₀, hs₁]
        have hcok : ValSpace.EvalS _Ψ (.coker s₀ s₁ e)
            (.ffs .cokernel svb (.reshap leev (.space svb) (.space svb))) :=
          .coker he hb ⟨b₀, b₁, rfl⟩ hsvb
        have himg : ValSpace.EvalS _Ψ (.img s₀ s₁ e)
            (.ffs .image svb (.reshap leev (.space svb) (.space svb))) :=
          .img he hb ⟨b₀, b₁, rfl⟩ hsvb
        have hevT : ValTy.EvalT _Ψ (.space (.tprod (.coker s₀ s₁ e) (.img s₀ s₁ e)))
            (.space (.tprod
              (.ffs .cokernel svb (.reshap leev (.space svb) (.space svb)))
              (.ffs .image svb (.reshap leev (.space svb) (.space svb))))) :=
          .space (.tprod hcok himg)
        refine ⟨⟨.coker s₀ s₁ e, .img s₀ s₁ e, _, _, ?_, hcok, himg⟩, ?_, ?_⟩
        · simp only [ValExpr.inferType_reshap]
        · rw [ValExpr.inferType_reshap]
          exact ⟨_, evalT_valid hevT⟩
        · simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
          have hcoordsFv : (ValExpr.imageCoords svb leev).fv ⊆ _Ψ.keyNames :=
            (ValExpr.imageCoords_fv svb leev).trans
              (Finset.union_subset (evalS_fv hsvb hΨ') (opStep_fv he hΨ'))
          have hinferFv : ValSpace.fv (ValExpr.inferSpaceCtx [] (ValExpr.imageCoords svb leev)) ⊆ _Ψ.keyNames := by
            rw [ValExpr.inferSpaceCtx_nil]
            exact (ValExpr.fv_inferSpace_subset _).trans hcoordsFv
          repeat' apply Finset.union_subset
          all_goals first
            | exact opStep_fv he hΨ'
            | exact evalS_fv hsvb hΨ'
            | exact hinferFv
            | exact hcoordsFv)
      -- EvalBB proj_ker_coker (part-2 producer): the witness is a nested `mtm`
      -- whose corrected edges (§9.18) give inferType `.space (.tprod sv sv')`,
      -- realizations of the SAME ambient `s` (`hsv`/`hsv'`). The sub-IHs supply
      -- validity of `sv`/`sv'` and fv of the spaces/operands.
      -- arm: bProjKC
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₀' env₁ env₂ env₃ sv₀ sv₁ sv sv' sv₀'
              hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₀' hcob hembd hproj
              ih_sv₀ ih_sv₁ ih_sv ih_sv' ih_sv₀' ih_cob ih_embd ih_proj
              _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        -- `hsval : SValid Γ' s`, `s = ker/coker s₀ s₁ e`; decompose to space-validity.
        -- `SValid` is `Type`-valued and `hs` is a `Prop` disjunction, so we cannot
        -- eliminate `hs` into a `Type` goal; route through `Nonempty` (`Prop`) and
        -- recover the data via `Classical.choice` (only `fv ⊆ ρ` — a `Prop` — is
        -- ultimately needed, so this is sound for the obligation at hand).
        have hSsofb₀ : SValid Γ' (Basis.sof b₀) := by
          rw [hsofb₀]
          refine Classical.choice ?_
          rcases hs with rfl | rfl
          · cases hsval with | ker h0 _ _ => exact ⟨h0⟩
          · cases hsval with | coker h0 _ _ => exact ⟨h0⟩
        have hsofeq : Basis.sof b₀ = Basis.sof b₀' := Basis.EvalBB.sof_eq hcob
        have hSsofb₀' : SValid Γ' (Basis.sof b₀') := by rw [← hsofeq]; exact hSsofb₀
        -- Space validity of the ambient `s` and of `s₀ = sof b₀ = sof b₀'`.
        have hSs₀ : SValid Γ' s₀ := hsofb₀ ▸ hSsofb₀
        have hsofb₀'eq : Basis.sof b₀' = s₀ := by rw [← hsofeq, hsofb₀]
        -- The embedded term `e` is typed at `s₀* ⊗ s₁` (from `hsval`), and `s ≤ s₀`.
        -- Extract both as `Nonempty` (data lives in `Type`, only `Prop` is needed).
        have hsub : Nonempty (SubType Γ' s s₀) := by
          rcases hs with rfl | rfl
          · cases hsval with | ker h0 h1 he => exact ⟨.sub_ker h0 h1 he⟩
          · cases hsval with | coker h0 h1 he => exact ⟨.sub_coker h0 h1 he⟩
        -- EvalS IHs → validity + fv of the spaces.
        obtain ⟨_, hfvsv⟩ := ih_sv ∅ Γ' ρ' hΨ' hρ' hkey hsval
        obtain ⟨_, hfvsv'⟩ := ih_sv' ∅ Γ' ρ' hΨ' hρ' hkey hsval
        obtain ⟨_, hfvsv₀⟩ := ih_sv₀ ∅ Γ' ρ' hΨ' hρ' hkey hSsofb₀
        obtain ⟨_, hfvsv₀'⟩ := ih_sv₀' ∅ Γ' ρ' hΨ' hρ' hkey hSsofb₀'
        -- env₂ fv from the COB sub-derivation (motive_3 IH).
        obtain ⟨_, _, hfvenv₂⟩ := ih_cob ∅ Γ' ρ' hΨ' hρ' hkey hSsofb₀
        -- env₃ fv from the OpStep (motive_4) IH on `lembd s` (typed `s* ⊗ s₀`).
        have hembd_ty : HasType ∅ Γ' (Term.lembd s)
            (Basis.tof (.tprod (.dual (.proj s b₀ b₁)) b₀)) := by
          simp only [Basis.tof, Basis.sof, hsofb₀]
          exact HasType.lembd (Classical.choice hsub)
        have hembd_sval : SValid Γ' (Basis.sof (.tprod (.dual (.proj s b₀ b₁)) b₀)) := by
          simp only [Basis.sof, hsofb₀]; exact .tprod (.dual hsval) hSs₀
        obtain ⟨_, _, hfvenv₃_u⟩ := ih_embd ∅ Γ' ρ' hΨ' hρ' hkey hembd_ty hembd_sval
        -- env₁ fv from the OpStep (motive_4) IH on `lproj s (sof b₀')` (typed `s₀* ⊗ s`).
        have hproj_ty : HasType ∅ Γ' (Term.lproj s (Basis.sof b₀'))
            (Basis.tof (.tprod (.dual b₀') (.proj s b₀' b₁))) := by
          simp only [Basis.tof, Basis.sof, hsofb₀'eq]
          exact HasType.lproj hsval hSs₀ (Classical.choice hsub)
        have hproj_sval : SValid Γ' (Basis.sof (.tprod (.dual b₀') (.proj s b₀' b₁))) := by
          simp only [Basis.sof, hsofb₀'eq]; exact .tprod (.dual hSs₀) hsval
        obtain ⟨_, _, hfvenv₁_u⟩ := ih_proj ∅ Γ' ρ' hΨ' hρ' hkey hproj_ty hproj_sval
        exact term_bb_proj_ker_coker_v2 hsv hsv'
          (ih_sv ∅ Γ' ρ' hΨ' hρ' hkey hsval).1
          (ih_sv' ∅ Γ' ρ' hΨ' hρ' hkey hsval).1
          hfvsv₀ hfvsv₀' hfvsv hfvsv'
          (Finset.Subset.trans Finset.subset_union_right hfvenv₁_u) hfvenv₂
          (Finset.Subset.trans Finset.subset_union_right hfvenv₃_u))
      -- EvalBB proj_img_coimg (part-2 producer): codomain mirror of `bProjKC`.
      -- The witness's corrected edges (§9.18) give inferType `.space (.tprod sv sv')`
      -- (both realizations of the ambient `s ∈ {Img, CoImg}`); the change-of-basis
      -- and embedding act on the codomain bases `b₁`/`b₁'`, and `s ≤ s₁`.
      -- arm: bProjIC
      (by
        intro _ s₀ s₁ e s b₀ b₁ b₁' env₁ env₂ env₃ sv₀ sv₁ sv sv' sv₁'
              hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₁' hcob hembd hproj
              ih_sv₀ ih_sv₁ ih_sv ih_sv' ih_sv₁' ih_cob ih_embd ih_proj
              _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        -- Codomain-side space validity: `s₁ = sof b₁ = sof b₁'`.
        have hSsofb₁ : SValid Γ' (Basis.sof b₁) := by
          rw [hsofb₁]
          refine Classical.choice ?_
          rcases hs with rfl | rfl
          · cases hsval with | img _ h1 _ => exact ⟨h1⟩
          · cases hsval with | coimg _ h1 _ => exact ⟨h1⟩
        have hsofeq : Basis.sof b₁ = Basis.sof b₁' := Basis.EvalBB.sof_eq hcob
        have hSsofb₁' : SValid Γ' (Basis.sof b₁') := by rw [← hsofeq]; exact hSsofb₁
        have hSs₁ : SValid Γ' s₁ := hsofb₁ ▸ hSsofb₁
        have hsofb₁'eq : Basis.sof b₁' = s₁ := by rw [← hsofeq, hsofb₁]
        -- The embedded term `e` is typed at `s₀* ⊗ s₁` (from `hsval`), and `s ≤ s₁`.
        have hsub : Nonempty (SubType Γ' s s₁) := by
          rcases hs with rfl | rfl
          · cases hsval with | img h0 h1 he => exact ⟨.sub_img h0 h1 he⟩
          · cases hsval with | coimg h0 h1 he => exact ⟨.sub_coimg h0 h1 he⟩
        -- EvalS IHs → validity + fv of the spaces.
        obtain ⟨_, hfvsv⟩ := ih_sv ∅ Γ' ρ' hΨ' hρ' hkey hsval
        obtain ⟨_, hfvsv'⟩ := ih_sv' ∅ Γ' ρ' hΨ' hρ' hkey hsval
        obtain ⟨_, hfvsv₁⟩ := ih_sv₁ ∅ Γ' ρ' hΨ' hρ' hkey hSsofb₁
        obtain ⟨_, hfvsv₁'⟩ := ih_sv₁' ∅ Γ' ρ' hΨ' hρ' hkey hSsofb₁'
        -- env₂ fv from the COB sub-derivation (motive_3 IH on `b₁`).
        obtain ⟨_, _, hfvenv₂⟩ := ih_cob ∅ Γ' ρ' hΨ' hρ' hkey hSsofb₁
        -- env₃ fv from the OpStep IH on `lembd s` (typed `s* ⊗ s₁`).
        have hembd_ty : HasType ∅ Γ' (Term.lembd s)
            (Basis.tof (.tprod (.dual (.proj s b₀ b₁)) b₁)) := by
          simp only [Basis.tof, Basis.sof, hsofb₁]
          exact HasType.lembd (Classical.choice hsub)
        have hembd_sval : SValid Γ' (Basis.sof (.tprod (.dual (.proj s b₀ b₁)) b₁)) := by
          simp only [Basis.sof, hsofb₁]; exact .tprod (.dual hsval) hSs₁
        obtain ⟨_, _, hfvenv₃_u⟩ := ih_embd ∅ Γ' ρ' hΨ' hρ' hkey hembd_ty hembd_sval
        -- env₁ fv from the OpStep IH on `lproj s (sof b₁')` (typed `s₁* ⊗ s`).
        have hproj_ty : HasType ∅ Γ' (Term.lproj s (Basis.sof b₁'))
            (Basis.tof (.tprod (.dual b₁') (.proj s b₀ b₁'))) := by
          simp only [Basis.tof, Basis.sof, hsofb₁'eq]
          exact HasType.lproj hsval hSs₁ (Classical.choice hsub)
        have hproj_sval : SValid Γ' (Basis.sof (.tprod (.dual b₁') (.proj s b₀ b₁'))) := by
          simp only [Basis.sof, hsofb₁'eq]; exact .tprod (.dual hSs₁) hsval
        obtain ⟨_, _, hfvenv₁_u⟩ := ih_proj ∅ Γ' ρ' hΨ' hρ' hkey hproj_ty hproj_sval
        exact term_bb_proj_img_coimg_v2 hsv hsv'
          (ih_sv ∅ Γ' ρ' hΨ' hρ' hkey hsval).1
          (ih_sv' ∅ Γ' ρ' hΨ' hρ' hkey hsval).1
          hfvsv₁ hfvsv₁' hfvsv hfvsv'
          (Finset.Subset.trans Finset.subset_union_right hfvenv₁_u) hfvenv₂
          (Finset.Subset.trans Finset.subset_union_right hfvenv₃_u))
      -- EvalBB terms_rref (part 2): TRIVIAL BY DESIGN — the witness is reshaped
      -- to the canonical `sv ⊗ sv` (`sv` the rule's own realization of `sof b`),
      -- so `CobShapeT` reads off directly: shape via `inferType_reshap`, validity
      -- via the operational regularity `evalS_valid`, fv via the operational fv
      -- lemmas (no IHs / no source typing needed).
      -- arm: bTermsRref
      (by
        intro _Ψ b b' e es env₀ env₁ sv hbb hch hsv _ih_bb _ih_ch _ih_sv
              _Δ' _Γ' ρ' hΨ' _hρ' _hkey _hsval
        obtain ⟨vsv⟩ := evalS_valid hsv
        have hinfer : ValExpr.inferType
            (.reshap (.rrefRep env₀ (.reshapBase env₁ (.tprod sv sv)))
              (.space (.tprod sv sv)) (.space (.tprod sv sv))) = .space (.tprod sv sv) :=
          ValExpr.inferType_reshap _ _ _
        refine ⟨⟨Basis.sof b, Basis.sof b, sv, sv, hinfer, hsv, hsv⟩, ?_, ?_⟩
        · rw [hinfer]; exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod vsv vsv)⟩⟩
        · have hfvsv := evalS_fv hsv hΨ'
          simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
          repeat' apply Finset.union_subset
          all_goals first
            | exact hfvsv | exact opStep_fv hch hΨ' | exact evalBB_fv hbb hΨ')
      -- EvalBB refl (part 2, erratum-fix reflexivity — trivial by design): the
      -- reshaped idelta witness's inferType is STRUCTURALLY `.space (sv ⊗ sv)`
      -- with both factors the rule's own realization premise (§9.17 device).
      -- arm: bRefl
      (by
        intro _Ψ b sv htof hsv _ih_hsv _Δ' _Γ' ρ' hΨ' _hρ' _hkey _hsval
        obtain ⟨vsv⟩ := evalS_valid hsv
        have hinfer : ValExpr.inferType
            (.reshap (.idelta sv) (.space (.tprod sv sv)) (.space (.tprod sv sv)))
              = .space (.tprod sv sv) :=
          ValExpr.inferType_reshap _ _ _
        refine ⟨⟨Basis.sof b, Basis.sof b, sv, sv, hinfer, hsv, hsv⟩, ?_, ?_⟩
        · rw [hinfer]; exact ⟨.base, ⟨ValTValidC.space (ValSValidC.tprod vsv vsv)⟩⟩
        · have hfvsv := evalS_fv hsv hΨ'
          simp only [ValExpr.fv, ValTy.fv, ValSpace.fv]
          repeat' apply Finset.union_subset
          all_goals exact hfvsv)

      (by
        intro _ s₀ s₁ e s b₀ b₁ b₁' env₁ env₃ sv₀ sv sv'
              hs hsofb₀ hsofb₁ hsofb₁' hsv₀ hsv hsv' hembd hproj
              ih_sv₀ ih_sv ih_sv' ih_embd ih_proj
              _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        -- `hsval : SValid Γ' s`, `s = ker/coker s₀ s₁ e`; decompose to
        -- space-validity (same `Nonempty`/`Classical.choice` route as `bProjKC`).
        have hSsofb₀ : SValid Γ' (Basis.sof b₀) := by
          rw [hsofb₀]
          refine Classical.choice ?_
          rcases hs with rfl | rfl
          · cases hsval with | ker h0 _ _ => exact ⟨h0⟩
          · cases hsval with | coker h0 _ _ => exact ⟨h0⟩
        have hSs₀ : SValid Γ' s₀ := hsofb₀ ▸ hSsofb₀
        -- The embedded term `e` is typed at `s₀* ⊗ s₁` (from `hsval`), `s ≤ s₀`.
        have hsub : Nonempty (SubType Γ' s s₀) := by
          rcases hs with rfl | rfl
          · cases hsval with | ker h0 h1 he => exact ⟨.sub_ker h0 h1 he⟩
          · cases hsval with | coker h0 h1 he => exact ⟨.sub_coker h0 h1 he⟩
        -- EvalS IHs → validity + fv of the spaces.
        obtain ⟨_, hfvsv⟩ := ih_sv ∅ Γ' ρ' hΨ' hρ' hkey hsval
        obtain ⟨_, hfvsv'⟩ := ih_sv' ∅ Γ' ρ' hΨ' hρ' hkey hsval
        obtain ⟨_, hfvsv₀⟩ := ih_sv₀ ∅ Γ' ρ' hΨ' hρ' hkey hSsofb₀
        -- env₃ fv from the OpStep (motive_4) IH on `lembd s` (typed `s* ⊗ s₀`).
        have hembd_ty : HasType ∅ Γ' (Term.lembd s)
            (Basis.tof (.tprod (.dual (.proj s b₀ b₁)) b₀)) := by
          simp only [Basis.tof, Basis.sof, hsofb₀]
          exact HasType.lembd (Classical.choice hsub)
        have hembd_sval : SValid Γ' (Basis.sof (.tprod (.dual (.proj s b₀ b₁)) b₀)) := by
          simp only [Basis.sof, hsofb₀]; exact .tprod (.dual hsval) hSs₀
        obtain ⟨_, _, hfvenv₃_u⟩ := ih_embd ∅ Γ' ρ' hΨ' hρ' hkey hembd_ty hembd_sval
        -- env₁ fv from the OpStep IH on `lproj s (sof b₀)` (typed `s₀* ⊗ s`).
        have hproj_ty : HasType ∅ Γ' (Term.lproj s (Basis.sof b₀))
            (Basis.tof (.tprod (.dual b₀) (.proj s b₀ b₁'))) := by
          simp only [Basis.tof, Basis.sof, hsofb₀]
          exact HasType.lproj hsval hSs₀ (Classical.choice hsub)
        have hproj_sval : SValid Γ' (Basis.sof (.tprod (.dual b₀) (.proj s b₀ b₁'))) := by
          simp only [Basis.sof, hsofb₀]; exact .tprod (.dual hSs₀) hsval
        obtain ⟨_, _, hfvenv₁_u⟩ := ih_proj ∅ Γ' ρ' hΨ' hρ' hkey hproj_ty hproj_sval
        exact term_bb_proj_sandwich_v2 hsv hsv'
          (ih_sv ∅ Γ' ρ' hΨ' hρ' hkey hsval).1
          (ih_sv' ∅ Γ' ρ' hΨ' hρ' hkey hsval).1
          hfvsv₀ hfvsv hfvsv'
          (Finset.Subset.trans Finset.subset_union_right hfvenv₁_u)
          (Finset.Subset.trans Finset.subset_union_right hfvenv₃_u))

      (by
        intro _ s₀ s₁ e s b₀ b₁ b₀' env₁ env₃ sv₁ sv sv'
              hs hsofb₀ hsofb₁ hsofb₀' hsv₁ hsv hsv' hembd hproj
              ih_sv₁ ih_sv ih_sv' ih_embd ih_proj
              _Δ' Γ' ρ' hΨ' hρ' hkey hsval
        -- `hsval : SValid Γ' s`, `s = img/coimg s₀ s₁ e`; codomain-side validity.
        have hSsofb₁ : SValid Γ' (Basis.sof b₁) := by
          rw [hsofb₁]
          refine Classical.choice ?_
          rcases hs with rfl | rfl
          · cases hsval with | img _ h1 _ => exact ⟨h1⟩
          · cases hsval with | coimg _ h1 _ => exact ⟨h1⟩
        have hSs₁ : SValid Γ' s₁ := hsofb₁ ▸ hSsofb₁
        -- The embedded term `e` is typed at `s₀* ⊗ s₁` (from `hsval`), `s ≤ s₁`.
        have hsub : Nonempty (SubType Γ' s s₁) := by
          rcases hs with rfl | rfl
          · cases hsval with | img h0 h1 he => exact ⟨.sub_img h0 h1 he⟩
          · cases hsval with | coimg h0 h1 he => exact ⟨.sub_coimg h0 h1 he⟩
        -- EvalS IHs → validity + fv of the spaces.
        obtain ⟨_, hfvsv⟩ := ih_sv ∅ Γ' ρ' hΨ' hρ' hkey hsval
        obtain ⟨_, hfvsv'⟩ := ih_sv' ∅ Γ' ρ' hΨ' hρ' hkey hsval
        obtain ⟨_, hfvsv₁⟩ := ih_sv₁ ∅ Γ' ρ' hΨ' hρ' hkey hSsofb₁
        -- env₃ fv from the OpStep (motive_4) IH on `lembd s` (typed `s* ⊗ s₁`).
        have hembd_ty : HasType ∅ Γ' (Term.lembd s)
            (Basis.tof (.tprod (.dual (.proj s b₀ b₁)) b₁)) := by
          simp only [Basis.tof, Basis.sof, hsofb₁]
          exact HasType.lembd (Classical.choice hsub)
        have hembd_sval : SValid Γ' (Basis.sof (.tprod (.dual (.proj s b₀ b₁)) b₁)) := by
          simp only [Basis.sof, hsofb₁]; exact .tprod (.dual hsval) hSs₁
        obtain ⟨_, _, hfvenv₃_u⟩ := ih_embd ∅ Γ' ρ' hΨ' hρ' hkey hembd_ty hembd_sval
        -- env₁ fv from the OpStep IH on `lproj s (sof b₁)` (typed `s₁* ⊗ s`).
        have hproj_ty : HasType ∅ Γ' (Term.lproj s (Basis.sof b₁))
            (Basis.tof (.tprod (.dual b₁) (.proj s b₀' b₁))) := by
          simp only [Basis.tof, Basis.sof, hsofb₁]
          exact HasType.lproj hsval hSs₁ (Classical.choice hsub)
        have hproj_sval : SValid Γ' (Basis.sof (.tprod (.dual b₁) (.proj s b₀' b₁))) := by
          simp only [Basis.sof, hsofb₁]; exact .tprod (.dual hSs₁) hsval
        obtain ⟨_, _, hfvenv₁_u⟩ := ih_proj ∅ Γ' ρ' hΨ' hρ' hkey hproj_ty hproj_sval
        exact term_bb_proj_sandwich_v2 hsv hsv'
          (ih_sv ∅ Γ' ρ' hΨ' hρ' hkey hsval).1
          (ih_sv' ∅ Γ' ρ' hΨ' hρ' hkey hsval).1
          hfvsv₁ hfvsv hfvsv'
          (Finset.Subset.trans Finset.subset_union_right hfvenv₁_u)
          (Finset.Subset.trans Finset.subset_union_right hfvenv₃_u))
      -- OpStep var (part 1, leaf): value from Ψ; EvalT from EvalCtxValid; validity+fv
      -- from RhoValid (x∈ρ from the Ψ-lookup via KeyScope); ReshapEq refl.
      -- arm: oVar
      (by
        intro _ x b v hlk Δ' Γ' ρ' hΨ' hρ' hkey _htype _hsof
        have hxρ : x ∈ ρ' := mem_scope_of_lookup hkey hlk
        obtain ⟨hokτ, _, _⟩ := hρ' x b v hxρ hlk
        obtain ⟨hfvv, hevT, hfvτ, _⟩ := hΨ' x b v hlk
        obtain ⟨k, ⟨hkv⟩⟩ := hokτ
        exact ⟨⟨_, hevT, ReshapEq.refl hkv⟩, ⟨k, ⟨hkv⟩⟩, Finset.union_subset hfvτ hfvv⟩)
      -- OpStep cob (change-of-basis): the genuine THREE-part cross arm — fires the
      -- part-1 IH (inner OpStep, retargeted across sof b₁ = sof b₀), the part-2 IH
      -- (the EvalBB premise), and the part-3 IH (the EvalS premise), then the helper.
      -- arm: oCob
      (by
        intro _ e b₀ b₁ v env₀ sv htof₀ htof₁ _he hbb hes ih_he ih_bb ih_es
              Δ' Γ' ρ' hΨ' hρ' hkey htype hsof
        have hsofeq : Basis.sof b₁ = Basis.sof b₀ := Basis.EvalBB.sof_eq hbb
        obtain ⟨hsvval, hfvsv⟩ := ih_es Δ' Γ' ρ' hΨ' hρ' hkey hsof
        obtain ⟨_, _, hfvenv⟩ := ih_bb Δ' Γ' ρ' hΨ' hρ' hkey (by rw [hsofeq]; exact hsof)
        obtain ⟨_, _, hfvv_union⟩ := ih_he Δ' Γ' ρ' hΨ' hρ' hkey
          (show HasType Δ' Γ' e (Basis.tof b₁) by rw [htof₁, hsofeq, ← htof₀]; exact htype)
          (by rw [hsofeq]; exact hsof)
        have hfvv := Finset.Subset.trans Finset.subset_union_right hfvv_union
        exact term_cob_v2 htof₀ hes hsvval hfvsv hfvenv hfvv)
      -- OpStep scale (`e₀ * e₁`): inferType (.scale v₀ v₁) = inferType v₁ ⟹ (a)/(b)
      -- forward from ih₁; (c) adds fv v₀ ⊆ ρ' from ih₀.
      -- arm: oScale
      (by
        intro _ e₀ e₁ b v₀ v₁ he₀ he₁ ih₀ ih₁ Δ' Γ' ρ' hΨ' hρ' hkey htype _hsof
        obtain ⟨Δa, Δb, Γa, s, hτ, hsv, h₀, h₁⟩ := hasType_smul_inv htype
        have hsofb : Basis.sof b = s := sof_of_tof_eq_space hτ
        obtain ⟨ih1a, ih1b, ih1c⟩ := ih₁ Δb Γa ρ' hΨ' hρ' hkey
          (show HasType Δb Γa e₁ (Basis.tof b) by rw [hτ]; exact h₁)
          (show SValid Γa (Basis.sof b) by rw [hsofb]; exact hsv)
        obtain ⟨_, _, ih0c⟩ := ih₀ Δa Γa ρ' hΨ' hρ' hkey h₀ SValid.real
        have hv0 : ValExpr.fv v₀ ⊆ _ := fun a ha => ih0c (Finset.mem_union_right _ ha)
        refine ⟨ih1a, ih1b, ?_⟩
        have : ValTy.fv (ValExpr.inferType v₁) ∪ (ValExpr.fv v₀ ∪ ValExpr.fv v₁) ⊆ _ :=
          Finset.union_subset (fun a hA => ih1c (Finset.mem_union_left _ hA))
            (Finset.union_subset hv0 (fun a hC => ih1c (Finset.mem_union_right _ hC)))
        exact this)
      -- OpStep add (`e₀ + e₁`): the rule's explicit `sv` annotation fixes the
      -- result type.  Its own `EvalS` premise supplies realization, validity,
      -- and scoping; operand realizations may be different.
      -- arm: oAdd
      (by
        intro _Ψ e₀ e₁ b sv v₀ v₁ htof hsv he₀ he₁
          _ih_hsv _ih₀ _ih₁ _Δ' _Γ' _ρ' hΨ' _hρ' _hkey _htype _hsof
        obtain ⟨vsv⟩ := evalS_valid hsv
        have hevT : ValTy.EvalT _Ψ (Basis.tof b) (.space sv) := by
          rw [htof]
          exact .space hsv
        have hfvval := opStep_fv (ValExpr.OpStep.add htof hsv he₀ he₁) hΨ'
        have hfvsv := evalS_fv hsv hΨ'
        have hinf : ValExpr.inferType (.vadd sv v₀ v₁) = .space sv := rfl
        refine ⟨⟨_, hevT, ?_⟩, ?_, ?_⟩
        · rw [hinf]
          exact ReshapEq.refl (ValTValidC.space vsv)
        · rw [hinf]
          exact ⟨.base, ⟨ValTValidC.space vsv⟩⟩
        · rw [hinf]
          exact Finset.union_subset hfvsv hfvval)
      -- OpStep dsumE / tprodE (compound): invert the source typing, fire both IHs at
      -- the operand bases, apply the agent-built standalone helpers.
      -- arm: oDsumE
      (by
        intro _ e₀ e₁ b₀ b₁ v₀ v₁ _he₀ _he₁ htof₀ htof₁ ih₀ ih₁ Δ' Γ' ρ' hΨ' hρ' hkey htype _hsof
        obtain ⟨Δa, Γa, s₀, s₁, hτ, hsv0, hsv1, h₀, h₁⟩ := hasType_dsumE_inv htype
        obtain ⟨hsb0, hsb1⟩ : Basis.sof b₀ = s₀ ∧ Basis.sof b₁ = s₁ := by
          injection hτ with hτ'; injection hτ' with a b; exact ⟨a, b⟩
        exact term_dsumE_v2 htof₀ htof₁
          (ih₀ Δa Γa ρ' hΨ' hρ' hkey
            (show HasType Δa Γa e₀ (Basis.tof b₀) by rw [htof₀, hsb0]; exact h₀)
            (show SValid Γa (Basis.sof b₀) by rw [hsb0]; exact hsv0))
          (ih₁ Δa Γa ρ' hΨ' hρ' hkey
            (show HasType Δa Γa e₁ (Basis.tof b₁) by rw [htof₁, hsb1]; exact h₁)
            (show SValid Γa (Basis.sof b₁) by rw [hsb1]; exact hsv1)))
      -- arm: oTprodE
      (by
        intro _ e₀ e₁ b₀ b₁ v₀ v₁ _he₀ _he₁ htof₀ htof₁ ih₀ ih₁ Δ' Γ' ρ' hΨ' hρ' hkey htype _hsof
        obtain ⟨Δ₀, Δ₁, Γa, s₀, s₁, hτ, hsv0, hsv1, h₀, h₁⟩ := hasType_tprodE_inv htype
        obtain ⟨hsb0, hsb1⟩ : Basis.sof b₀ = s₀ ∧ Basis.sof b₁ = s₁ := by
          injection hτ with hτ'; injection hτ' with a b; exact ⟨a, b⟩
        exact term_tprodE_v2 htof₀ htof₁
          (ih₀ Δ₀ Γa ρ' hΨ' hρ' hkey
            (show HasType Δ₀ Γa e₀ (Basis.tof b₀) by rw [htof₀, hsb0]; exact h₀)
            (show SValid Γa (Basis.sof b₀) by rw [hsb0]; exact hsv0))
          (ih₁ Δ₁ Γa ρ' hΨ' hρ' hkey
            (show HasType Δ₁ Γa e₁ (Basis.tof b₁) by rw [htof₁, hsb1]; exact h₁)
            (show SValid Γa (Basis.sof b₁) by rw [hsb1]; exact hsv1)))
      -- OpStep pinvT_std (part 1): invert the `pinvT` source typing (premise typing +
      -- SValids), fire the operand IH, invert its realization (a `.space` tprod) into
      -- per-factor `EvalS`s, and rebuild the SWAPPED realization for the conclusion
      -- basis. The value's inferType is base-valid with operand-bounded fvs via
      -- `pinv_inferType_valid` (off the IH's `ReshapEq`, `fst_base_space`).
      -- arm: oPinvTStd
      (by
        intro _Ψ b₀ b₁ e v he _hb₀ _hb₁ ih_he _Δ' _Γ' ρ' hΨ' hρ' hkey htype _hsof
        obtain ⟨Γ'', _hτ, hsv₀, hsv₁, h⟩ := hasType_pinvT_inv htype
        obtain ⟨⟨τw, hevw, hrew⟩, _, hfvw⟩ := ih_he ∅ Γ'' ρ' hΨ' hρ' hkey
          (show HasType ∅ Γ'' e (Basis.tof (.tprod (.dual b₁) b₀)) by
            simpa only [Basis.tof, Basis.sof] using h)
          (show SValid Γ'' (Basis.sof (.tprod (.dual b₁) b₀)) by
            simp only [Basis.sof]; exact .tprod (.dual hsv₀) hsv₁)
        have hevw' : ValTy.EvalT _Ψ
            (.space (.tprod (.dual (Basis.sof b₁)) (Basis.sof b₀))) τw := by
          simpa only [Basis.tof, Basis.sof] using hevw
        obtain ⟨svw, hesw, rfl⟩ := evalT_space_inv hevw'
        cases hesw with
        | @tprod _ _ _ w₁ w₀ hw₁ hw₀ =>
        cases hw₁ with
        | dual hw₁ =>
        have hevT : ValTy.EvalT _Ψ (Basis.tof (.tprod (.dual b₀) b₁)) (.space (.tprod w₀ w₁)) := by
          have htofc : Basis.tof (.tprod (.dual b₀) b₁)
              = .space (.tprod (.dual (Basis.sof b₀)) (Basis.sof b₁)) := by
            simp only [Basis.tof, Basis.sof]
          rw [htofc]
          exact .space (.tprod (.dual hw₀) hw₁)
        obtain ⟨sv', hshape, ⟨hsval⟩⟩ := hrew.fst_base_space
        obtain ⟨⟨hpv⟩, hpfv⟩ := pinv_inferType_valid hshape hsval
        obtain ⟨hfvτ, hfvv⟩ := Finset.union_subset_iff.mp hfvw
        refine ⟨⟨_, hevT, ⟨.base, ⟨hpv⟩, ⟨(evalT_valid hevT).some⟩⟩⟩, ⟨.base, ⟨hpv⟩⟩, ?_⟩
        simp only [ValExpr.fv]
        exact Finset.union_subset (hpfv.trans hfvτ) hfvv)
      -- OpStep pinvT_gpinv (part 1): same realization/typing skeleton as pinvT_std;
      -- the value is `.gpinv v env₀ env₁` (gpinv_inferType_valid), with the
      -- inner-product witnesses' fvs read off `opStep_fv` (no `.inner` typing needed).
      -- arm: oPinvTGpinv
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ he hi₀ hi₁ ih_he _ih_hi₀ _ih_hi₁
              _Δ' _Γ' ρ' hΨ' hρ' hkey htype _hsof
        obtain ⟨Γ'', _hτ, hsv₀, hsv₁, h⟩ := hasType_pinvT_inv htype
        obtain ⟨⟨τw, hevw, hrew⟩, _, hfvw⟩ := ih_he ∅ Γ'' ρ' hΨ' hρ' hkey
          (show HasType ∅ Γ'' e (Basis.tof (.tprod (.dual b₁) b₀)) by
            simpa only [Basis.tof, Basis.sof] using h)
          (show SValid Γ'' (Basis.sof (.tprod (.dual b₁) b₀)) by
            simp only [Basis.sof]; exact .tprod (.dual hsv₀) hsv₁)
        have hevw' : ValTy.EvalT _Ψ
            (.space (.tprod (.dual (Basis.sof b₁)) (Basis.sof b₀))) τw := by
          simpa only [Basis.tof, Basis.sof] using hevw
        obtain ⟨svw, hesw, rfl⟩ := evalT_space_inv hevw'
        cases hesw with
        | @tprod _ _ _ w₁ w₀ hw₁ hw₀ =>
        cases hw₁ with
        | dual hw₁ =>
        have hevT : ValTy.EvalT _Ψ (Basis.tof (.tprod (.dual b₀) b₁)) (.space (.tprod w₀ w₁)) := by
          have htofc : Basis.tof (.tprod (.dual b₀) b₁)
              = .space (.tprod (.dual (Basis.sof b₀)) (Basis.sof b₁)) := by
            simp only [Basis.tof, Basis.sof]
          rw [htofc]
          exact .space (.tprod (.dual hw₀) hw₁)
        obtain ⟨sv', hshape, ⟨hsval⟩⟩ := hrew.fst_base_space
        -- E3: Gram slots domain-first — the value is `.gpinv v env₁ env₀`.
        obtain ⟨⟨hpv⟩, hpfv⟩ := gpinv_inferType_valid (env₀ := env₁) (env₁ := env₀) hshape hsval
        obtain ⟨hfvτ, hfvv⟩ := Finset.union_subset_iff.mp hfvw
        refine ⟨⟨_, hevT, ⟨.base, ⟨hpv⟩, ⟨(evalT_valid hevT).some⟩⟩⟩, ⟨.base, ⟨hpv⟩⟩, ?_⟩
        simp only [ValExpr.fv]
        exact Finset.union_subset (hpfv.trans hfvτ)
          (Finset.union_subset (Finset.union_subset hfvv (opStep_fv hi₁ hΨ'))
            (opStep_fv hi₀ hΨ')))
      -- OpStep pinvD_std (part 1): degenerate pseudo-inverse — operand at `.dual b₁`,
      -- domain factor pinned to ℝ by `hsofb₀`. E4/E7: the operand is reshaped to the
      -- canonical `sv₁ ⊗ ℝ` (rule premise `hsv₁`), so `inferType` of the value is
      -- STRUCTURALLY `.space (ℝ ⊗ sv₁)` — exactly the conclusion realization built from
      -- `hsv₁`; the operand IH is needed only for the value's fv bound.
      -- arm: oPinvDStd
      (by
        intro _Ψ b₀ b₁ e v sv₁ he hsofb₀ _hb₀ _hb₁ hsv₁ ih_he _ih_hsv₁
              _Δ' _Γ' ρ' hΨ' hρ' hkey htype _hsof
        obtain ⟨Γ'', _hτ, hsval₁, h⟩ := hasType_pinvD_inv htype
        obtain ⟨_, _, hfvw⟩ := ih_he ∅ Γ'' ρ' hΨ' hρ' hkey
          (show HasType ∅ Γ'' e (Basis.tof (.dual b₁)) by
            simpa only [Basis.tof, Basis.sof] using h)
          (show SValid Γ'' (Basis.sof (.dual b₁)) by
            simp only [Basis.sof]; exact .dual hsval₁)
        have hevT : ValTy.EvalT _Ψ (Basis.tof (.tprod (.dual b₀) b₁)) (.space (.tprod .real sv₁)) := by
          have htofc : Basis.tof (.tprod (.dual b₀) b₁)
              = .space (.tprod (.dual .real) (Basis.sof b₁)) := by
            simp only [Basis.tof, Basis.sof, hsofb₀]
          rw [htofc]
          exact .space (.tprod (.dual .real) hsv₁)
        obtain ⟨_, hfvv⟩ := Finset.union_subset_iff.mp hfvw
        refine ⟨⟨_, hevT, ReshapEq.refl (evalT_valid hevT).some⟩,
                ⟨_, evalT_valid hevT⟩, ?_⟩
        simp only [ValExpr.inferType, ValExpr.fv, ValTy.fv, ValSpace.fv]
        repeat' apply Finset.union_subset
        all_goals first | exact hfvv | exact evalS_fv hsv₁ hΨ' | exact Finset.empty_subset _)
      -- OpStep pinvD_gpinv (part 1): pinvD_std's realization + pinvT_gpinv's value
      -- (E3 slot order, E4 reshaped operand).
      -- arm: oPinvDGpinv
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ sv₁ he hsofb₀ _hb₀ hi₀ hi₁ hsv₁ ih_he _ih_hi₀ _ih_hi₁ _ih_hsv₁
              _Δ' _Γ' ρ' hΨ' hρ' hkey htype _hsof
        obtain ⟨Γ'', _hτ, hsval₁, h⟩ := hasType_pinvD_inv htype
        obtain ⟨_, _, hfvw⟩ := ih_he ∅ Γ'' ρ' hΨ' hρ' hkey
          (show HasType ∅ Γ'' e (Basis.tof (.dual b₁)) by
            simpa only [Basis.tof, Basis.sof] using h)
          (show SValid Γ'' (Basis.sof (.dual b₁)) by
            simp only [Basis.sof]; exact .dual hsval₁)
        have hevT : ValTy.EvalT _Ψ (Basis.tof (.tprod (.dual b₀) b₁)) (.space (.tprod .real sv₁)) := by
          have htofc : Basis.tof (.tprod (.dual b₀) b₁)
              = .space (.tprod (.dual .real) (Basis.sof b₁)) := by
            simp only [Basis.tof, Basis.sof, hsofb₀]
          rw [htofc]
          exact .space (.tprod (.dual .real) hsv₁)
        obtain ⟨_, hfvv⟩ := Finset.union_subset_iff.mp hfvw
        refine ⟨⟨_, hevT, ReshapEq.refl (evalT_valid hevT).some⟩,
                ⟨_, evalT_valid hevT⟩, ?_⟩
        simp only [ValExpr.inferType, ValExpr.fv, ValTy.fv, ValSpace.fv]
        repeat' apply Finset.union_subset
        all_goals first | exact hfvv | exact evalS_fv hsv₁ hΨ' | exact opStep_fv hi₀ hΨ' | exact opStep_fv hi₁ hΨ' | exact Finset.empty_subset _)
      -- OpStep inner_std (part 1): the value `.idelta sv` has inferType
      -- `.space (.tprod sv sv)`, which IS a realization of the conclusion basis's
      -- type `.space ((sof b₀)* ⊗ (sof b₀)*)` (EvalS.dual forgets the star; both
      -- factors realize via the rule's own `hsv`). ReshapEq/validity free via
      -- `evalT_valid`; fv via `evalS_fv`. No typing inversion needed.
      -- arm: oInnerStd
      (by
        intro _Ψ b₀ s sv _hb₀ hsv hsofb₀ _ih_hsv _Δ' Γ' ρ' hΨ' _hρ' _hkey _htype _hsof
        have hevT : ValTy.EvalT _Ψ (Basis.tof (.tprod (.dual b₀) (.dual b₀)))
            (.space (.tprod sv sv)) := by
          have htof : Basis.tof (.tprod (.dual b₀) (.dual b₀))
              = .space (.tprod (.dual s) (.dual s)) := by
            simp only [Basis.tof, Basis.sof, hsofb₀]
          rw [htof]
          exact .space (.tprod (.dual hsv) (.dual hsv))
        have hfvsv : ValSpace.fv sv ⊆ _Ψ.keyNames := evalS_fv hsv hΨ'
        refine ⟨⟨_, hevT, ReshapEq.refl (evalT_valid hevT).some⟩,
                ⟨_, evalT_valid hevT⟩, ?_⟩
        simp only [ValExpr.inferType, ValExpr.fv, ValTy.fv, ValSpace.fv]
        exact Finset.union_subset (Finset.union_subset hfvsv hfvsv) hfvsv)
      -- OpStep embed_ker (part 1): NO typing inversion — the motive's
      -- `SValid (sof b')` hypothesis contains the FFS witness typing (the ambient
      -- factor is `.ker s₀ s₁ e`, whose `SValid.ker` carries `⊢ e : s₀*⊗s₁`).
      -- Fire the matrix IH, invert its `.space`-tprod realization, rebuild the
      -- conclusion realization `(ffs .kernel ⊗ s₀-factor)` via `EvalS.ker` on the
      -- rule's own premises. Value validity/fv via `gsvdU_inferType_valid`.
      -- arm: oEmbedKer
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he _ih_hi₀ _ih_hi₁ ih_he
              _Δ' Γ' ρ' hΨ' hρ' hkey _htype hsof
        have hsof' : SValid Γ' (.tprod (.dual (.ker s₀ s₁ e)) (Basis.sof b₀)) := by
          simpa only [Basis.sof] using hsof
        cases hsof' with
        | tprod hkerv hsb₀ =>
        cases hkerv with
        | dual hkerv =>
        cases hkerv with
        | ker hv0 hv1 hwit =>
        obtain ⟨⟨τw, hevw, hrew⟩, _, hfvw⟩ := ih_he ∅ Γ' ρ' hΨ' hρ' hkey
          (show HasType ∅ Γ' e (Basis.tof (.tprod (.dual b₀) b₁)) by
            simp only [Basis.tof, Basis.sof, hs₀, hs₁]; exact hwit)
          (show SValid Γ' (Basis.sof (.tprod (.dual b₀) b₁)) by
            simp only [Basis.sof, hs₀, hs₁]; exact .tprod (.dual hv0) hv1)
        have hevw' : ValTy.EvalT _Ψ (.space (.tprod (.dual s₀) s₁)) τw := by
          simpa only [Basis.tof, Basis.sof, hs₀, hs₁] using hevw
        obtain ⟨svw, hesw, rfl⟩ := evalT_space_inv hevw'
        cases hesw with
        | @tprod _ _ _ wa wb hwa hwb =>
        cases hwa with
        | dual hwa =>
        have hkerS : ValSpace.EvalS _Ψ (.ker s₀ s₁ e)
            (.ffs .kernel (.tprod wa wb)
              (.reshap v (.space (.tprod wa wb)) (.space (.tprod wa wb)))) := by
          refine ValSpace.EvalS.ker he ?_ ⟨b₀, b₁, rfl⟩ ?_
          · simp only [Basis.sof, hs₀, hs₁]
          · simp only [Basis.sof, hs₀, hs₁]; exact .tprod (.dual hwa) hwb
        have hevT : ValTy.EvalT _Ψ
            (Basis.tof (.tprod (.dual (.proj (.ker s₀ s₁ e) b₀ b₁)) b₀))
            (.space (.tprod
              (.ffs .kernel (.tprod wa wb)
                (.reshap v (.space (.tprod wa wb)) (.space (.tprod wa wb)))) wa)) := by
          have htofc : Basis.tof (.tprod (.dual (.proj (.ker s₀ s₁ e) b₀ b₁)) b₀)
              = .space (.tprod (.dual (.ker s₀ s₁ e)) s₀) := by
            simp only [Basis.tof, Basis.sof, hs₀]
          rw [htofc]
          exact .space (.tprod (.dual hkerS) hwa)
        obtain ⟨sv', hshape, ⟨hsval⟩⟩ := hrew.fst_base_space
        -- E1/E2: value `.vtrans (.gsvdUI v env₀ env₁)`.
        obtain ⟨⟨hgv⟩, hgfv⟩ := gsvdUI_inferType_valid (env₀ := env₀) (env₁ := env₁) hshape hsval
        obtain ⟨⟨htv⟩, htfv⟩ := vtrans_inferType_valid ⟨hgv⟩
        refine ⟨⟨_, hevT, ⟨.base, ⟨htv⟩, ⟨(evalT_valid hevT).some⟩⟩⟩, ⟨.base, ⟨htv⟩⟩, ?_⟩
        simp only [ValExpr.fv]
        refine Finset.union_subset ((htfv.trans hgfv).trans hfvw) ?_
        exact Finset.union_subset
          (Finset.union_subset (Finset.union_subset_iff.mp hfvw).2 (opStep_fv hi₀ hΨ'))
          (opStep_fv hi₁ hΨ'))
      -- OpStep embed_coker: mirror of embed_ker (CoKer ambient, `.gsvdUI`).
      -- arm: oEmbedCoker
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he _ih_hi₀ _ih_hi₁ ih_he
              _Δ' Γ' ρ' hΨ' hρ' hkey _htype hsof
        have hsof' : SValid Γ' (.tprod (.dual (.coker s₀ s₁ e)) (Basis.sof b₀)) := by
          simpa only [Basis.sof] using hsof
        cases hsof' with
        | tprod hkerv hsb₀ =>
        cases hkerv with
        | dual hkerv =>
        cases hkerv with
        | coker hv0 hv1 hwit =>
        obtain ⟨⟨τw, hevw, hrew⟩, _, hfvw⟩ := ih_he ∅ Γ' ρ' hΨ' hρ' hkey
          (show HasType ∅ Γ' e (Basis.tof (.tprod (.dual b₀) b₁)) by
            simp only [Basis.tof, Basis.sof, hs₀, hs₁]; exact hwit)
          (show SValid Γ' (Basis.sof (.tprod (.dual b₀) b₁)) by
            simp only [Basis.sof, hs₀, hs₁]; exact .tprod (.dual hv0) hv1)
        have hevw' : ValTy.EvalT _Ψ (.space (.tprod (.dual s₀) s₁)) τw := by
          simpa only [Basis.tof, Basis.sof, hs₀, hs₁] using hevw
        obtain ⟨svw, hesw, rfl⟩ := evalT_space_inv hevw'
        cases hesw with
        | @tprod _ _ _ wa wb hwa hwb =>
        cases hwa with
        | dual hwa =>
        have hkerS : ValSpace.EvalS _Ψ (.coker s₀ s₁ e)
            (.ffs .cokernel (.tprod wa wb)
              (.reshap v (.space (.tprod wa wb)) (.space (.tprod wa wb)))) := by
          refine ValSpace.EvalS.coker he ?_ ⟨b₀, b₁, rfl⟩ ?_
          · simp only [Basis.sof, hs₀, hs₁]
          · simp only [Basis.sof, hs₀, hs₁]; exact .tprod (.dual hwa) hwb
        have hevT : ValTy.EvalT _Ψ
            (Basis.tof (.tprod (.dual (.proj (.coker s₀ s₁ e) b₀ b₁)) b₀))
            (.space (.tprod
              (.ffs .cokernel (.tprod wa wb)
                (.reshap v (.space (.tprod wa wb)) (.space (.tprod wa wb)))) wa)) := by
          have htofc : Basis.tof (.tprod (.dual (.proj (.coker s₀ s₁ e) b₀ b₁)) b₀)
              = .space (.tprod (.dual (.coker s₀ s₁ e)) s₀) := by
            simp only [Basis.tof, Basis.sof, hs₀]
          rw [htofc]
          exact .space (.tprod (.dual hkerS) hwa)
        obtain ⟨sv', hshape, ⟨hsval⟩⟩ := hrew.fst_base_space
        -- E1/E2: value `.vtrans (.gsvdU v env₀ env₁)`.
        obtain ⟨⟨hgv⟩, hgfv⟩ := gsvdU_inferType_valid (env₀ := env₀) (env₁ := env₁) hshape hsval
        obtain ⟨⟨htv⟩, htfv⟩ := vtrans_inferType_valid ⟨hgv⟩
        refine ⟨⟨_, hevT, ⟨.base, ⟨htv⟩, ⟨(evalT_valid hevT).some⟩⟩⟩, ⟨.base, ⟨htv⟩⟩, ?_⟩
        simp only [ValExpr.fv]
        refine Finset.union_subset ((htfv.trans hgfv).trans hfvw) ?_
        exact Finset.union_subset
          (Finset.union_subset (Finset.union_subset_iff.mp hfvw).2 (opStep_fv hi₀ hΨ'))
          (opStep_fv hi₁ hΨ'))
      -- OpStep embed_img: codomain-side mirror (Img ambient, tail factor `b₁`,
      -- `.gsvdV`).
      -- arm: oEmbedImg
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he _ih_hi₀ _ih_hi₁ ih_he
              _Δ' Γ' ρ' hΨ' hρ' hkey _htype hsof
        have hsof' : SValid Γ' (.tprod (.dual (.img s₀ s₁ e)) (Basis.sof b₁)) := by
          simpa only [Basis.sof] using hsof
        cases hsof' with
        | tprod hkerv hsb₁ =>
        cases hkerv with
        | dual hkerv =>
        cases hkerv with
        | img hv0 hv1 hwit =>
        obtain ⟨⟨τw, hevw, hrew⟩, _, hfvw⟩ := ih_he ∅ Γ' ρ' hΨ' hρ' hkey
          (show HasType ∅ Γ' e (Basis.tof (.tprod (.dual b₀) b₁)) by
            simp only [Basis.tof, Basis.sof, hs₀, hs₁]; exact hwit)
          (show SValid Γ' (Basis.sof (.tprod (.dual b₀) b₁)) by
            simp only [Basis.sof, hs₀, hs₁]; exact .tprod (.dual hv0) hv1)
        have hevw' : ValTy.EvalT _Ψ (.space (.tprod (.dual s₀) s₁)) τw := by
          simpa only [Basis.tof, Basis.sof, hs₀, hs₁] using hevw
        obtain ⟨svw, hesw, rfl⟩ := evalT_space_inv hevw'
        cases hesw with
        | @tprod _ _ _ wa wb hwa hwb =>
        cases hwa with
        | dual hwa =>
        have hkerS : ValSpace.EvalS _Ψ (.img s₀ s₁ e)
            (.ffs .image (.tprod wa wb)
              (.reshap v (.space (.tprod wa wb)) (.space (.tprod wa wb)))) := by
          refine ValSpace.EvalS.img he ?_ ⟨b₀, b₁, rfl⟩ ?_
          · simp only [Basis.sof, hs₀, hs₁]
          · simp only [Basis.sof, hs₀, hs₁]; exact .tprod (.dual hwa) hwb
        have hevT : ValTy.EvalT _Ψ
            (Basis.tof (.tprod (.dual (.proj (.img s₀ s₁ e) b₀ b₁)) b₁))
            (.space (.tprod
              (.ffs .image (.tprod wa wb)
                (.reshap v (.space (.tprod wa wb)) (.space (.tprod wa wb)))) wb)) := by
          have htofc : Basis.tof (.tprod (.dual (.proj (.img s₀ s₁ e) b₀ b₁)) b₁)
              = .space (.tprod (.dual (.img s₀ s₁ e)) s₁) := by
            simp only [Basis.tof, Basis.sof, hs₁]
          rw [htofc]
          exact .space (.tprod (.dual hkerS) hwb)
        obtain ⟨sv', hshape, ⟨hsval⟩⟩ := hrew.fst_base_space
        -- E2: value `.vtrans (.gsvdV v env₀ env₁)`.
        obtain ⟨⟨hgv⟩, hgfv⟩ := gsvdV_inferType_valid (env₀ := env₀) (env₁ := env₁) hshape hsval
        obtain ⟨⟨htv⟩, htfv⟩ := vtrans_inferType_valid ⟨hgv⟩
        refine ⟨⟨_, hevT, ⟨.base, ⟨htv⟩, ⟨(evalT_valid hevT).some⟩⟩⟩, ⟨.base, ⟨htv⟩⟩, ?_⟩
        simp only [ValExpr.fv]
        refine Finset.union_subset ((htfv.trans hgfv).trans hfvw) ?_
        exact Finset.union_subset
          (Finset.union_subset (Finset.union_subset_iff.mp hfvw).2 (opStep_fv hi₀ hΨ'))
          (opStep_fv hi₁ hΨ'))
      -- OpStep embed_coimg: codomain-side mirror (CoImg ambient, `.gsvdVI`).
      -- arm: oEmbedCoimg
      (by
        intro _Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ hs₀ hs₁ hi₀ hi₁ he _ih_hi₀ _ih_hi₁ ih_he
              _Δ' Γ' ρ' hΨ' hρ' hkey _htype hsof
        have hsof' : SValid Γ' (.tprod (.dual (.coimg s₀ s₁ e)) (Basis.sof b₁)) := by
          simpa only [Basis.sof] using hsof
        cases hsof' with
        | tprod hkerv hsb₁ =>
        cases hkerv with
        | dual hkerv =>
        cases hkerv with
        | coimg hv0 hv1 hwit =>
        obtain ⟨⟨τw, hevw, hrew⟩, _, hfvw⟩ := ih_he ∅ Γ' ρ' hΨ' hρ' hkey
          (show HasType ∅ Γ' e (Basis.tof (.tprod (.dual b₀) b₁)) by
            simp only [Basis.tof, Basis.sof, hs₀, hs₁]; exact hwit)
          (show SValid Γ' (Basis.sof (.tprod (.dual b₀) b₁)) by
            simp only [Basis.sof, hs₀, hs₁]; exact .tprod (.dual hv0) hv1)
        have hevw' : ValTy.EvalT _Ψ (.space (.tprod (.dual s₀) s₁)) τw := by
          simpa only [Basis.tof, Basis.sof, hs₀, hs₁] using hevw
        obtain ⟨svw, hesw, rfl⟩ := evalT_space_inv hevw'
        cases hesw with
        | @tprod _ _ _ wa wb hwa hwb =>
        cases hwa with
        | dual hwa =>
        have hkerS : ValSpace.EvalS _Ψ (.coimg s₀ s₁ e)
            (.ffs .coimage (.tprod wa wb)
              (.reshap v (.space (.tprod wa wb)) (.space (.tprod wa wb)))) := by
          refine ValSpace.EvalS.coimg he ?_ ⟨b₀, b₁, rfl⟩ ?_
          · simp only [Basis.sof, hs₀, hs₁]
          · simp only [Basis.sof, hs₀, hs₁]; exact .tprod (.dual hwa) hwb
        have hevT : ValTy.EvalT _Ψ
            (Basis.tof (.tprod (.dual (.proj (.coimg s₀ s₁ e) b₀ b₁)) b₁))
            (.space (.tprod
              (.ffs .coimage (.tprod wa wb)
                (.reshap v (.space (.tprod wa wb)) (.space (.tprod wa wb)))) wb)) := by
          have htofc : Basis.tof (.tprod (.dual (.proj (.coimg s₀ s₁ e) b₀ b₁)) b₁)
              = .space (.tprod (.dual (.coimg s₀ s₁ e)) s₁) := by
            simp only [Basis.tof, Basis.sof, hs₁]
          rw [htofc]
          exact .space (.tprod (.dual hkerS) hwb)
        obtain ⟨sv', hshape, ⟨hsval⟩⟩ := hrew.fst_base_space
        -- E2: value `.vtrans (.gsvdVI v env₀ env₁)`.
        obtain ⟨⟨hgv⟩, hgfv⟩ := gsvdVI_inferType_valid (env₀ := env₀) (env₁ := env₁) hshape hsval
        obtain ⟨⟨htv⟩, htfv⟩ := vtrans_inferType_valid ⟨hgv⟩
        refine ⟨⟨_, hevT, ⟨.base, ⟨htv⟩, ⟨(evalT_valid hevT).some⟩⟩⟩, ⟨.base, ⟨htv⟩⟩, ?_⟩
        simp only [ValExpr.fv]
        refine Finset.union_subset ((htfv.trans hgfv).trans hfvw) ?_
        exact Finset.union_subset
          (Finset.union_subset (Finset.union_subset_iff.mp hfvw).2 (opStep_fv hi₀ hΨ'))
          (opStep_fv hi₁ hΨ'))
      -- OpStep appL_lin (part 1): source typing pins the conclusion basis to a
      -- space basis. The ordinary rule carries the codomain realization and
      -- returns the same checked reshape as `S.Term.appL_lin`.
      -- arm: oAppL
      (by
        intro _Ψ b₀ b₁ n₀ n₁ env₀ env₁ sv₀ sv₁
              h₀ hsv₀ h₁ hsv₁ _htof₁ _ih_h₀ _ih_hsv₀ _ih_h₁ _ih_hsv₁
              _Δ' _Γ' ρ' hΨ' hρ' hkey htype _hsof
        obtain ⟨_, _, _, hτ, _, _, _, _⟩ := hasType_appL_inv htype
        have hevT : ValTy.EvalT _Ψ (Basis.tof b₁) (.space sv₁) := by
          rw [hτ]
          exact .space hsv₁
        refine ⟨⟨_, hevT, ReshapEq.refl (evalT_valid hevT).some⟩,
                ⟨_, evalT_valid hevT⟩, ?_⟩
        simp only [ValExpr.reshapBase, ValExpr.inferType, ValExpr.fv,
          ValTy.fv, ValSpace.fv]
        repeat' apply Finset.union_subset
        all_goals first
          | exact evalS_fv hsv₀ hΨ'
          | exact evalS_fv hsv₁ hΨ'
          | exact opStep_fv h₀ hΨ'
          | exact opStep_fv h₁ hΨ'
          | exact Finset.empty_subset _)
      -- OpStep appI_lin (part 1): degenerate (ℝ codomain at basis `.one`). E7: the
      -- functional is reshaped to `sv ⊗ ℝ`, so `inferType` of the value is
      -- STRUCTURALLY `.space .real` (the `.ttv` tprod branch) — no typing inversion
      -- or operand IH needed; fvs from `opStep_fv`/`evalS_fv`.
      -- arm: oAppI
      (by
        intro _Ψ b₀ n₀ n₁ env₀ env₁ sv h₀ hsv h₁ _ih_h₀ _ih_hsv _ih_h₁
              _Δ' _Γ' ρ' hΨ' _hρ' _hkey _htype _hsof
        have hevT : ValTy.EvalT _Ψ (Basis.tof .one) (.space .real) := by
          have : Basis.tof .one = Ty.space .real := by simp only [Basis.tof, Basis.sof]
          rw [this]; exact .space .real
        refine ⟨⟨_, hevT, ReshapEq.refl (evalT_valid hevT).some⟩,
                ⟨_, evalT_valid hevT⟩, ?_⟩
        simp only [ValExpr.inferType, ValExpr.fv, ValTy.fv, ValSpace.fv]
        repeat' apply Finset.union_subset
        all_goals first | exact evalS_fv hsv hΨ' | exact opStep_fv h₀ hΨ' | exact opStep_fv h₁ hΨ' | exact Finset.empty_subset _)
      -- arm: oNllam
      (by
        -- LN re-proof. The de-named `OpStep.nllam` drops the binder name `x`; the body
        -- `he`/codomain `h₁` premises are COFINITE (`∀y∉L`, opened via `openVar`). The
        -- produced value is `.vlam τv₀ τv₁ (.reshap env τv₁ τv₁)`; `tof (frame b₀ b₁)
        -- = .piTy (tof b₀) (tof b₁)` and `inferType (vlam …) = .piTy τv₀ τv₁`. Invert
        -- the source `nllam` typing (promote-aware, de-named `NllamInvData` with cofinite
        -- `hbody`/`hcod`) to recover the inner `Γ'` + premises.
        intro _Ψ b₀ b₁ τ₀ τ₁ e τv₀ τv₁ env hb₀ hb₁ h₀ L he h₁ ih_h₀ ih_he ih_h₁
              _Δ' _Γ0 ρ' hΨ' hρ' hkey htype _hsof
        rw [Basis.tof, hb₀, hb₁] at htype
        obtain ⟨Γ', τ₁i, k₀i, k₁i, _Lh, hτeq, htval, _hbody⟩ := hasType_nllam_inv htype
        injection hτeq with _ heτ₁
        subst heτ₁
        cases htval with
        | @piTy _ _ _ _ _ Lc hdom hcod =>
            obtain ⟨⟨k₀v, ⟨vτv₀⟩⟩, hfv₀⟩ := ih_h₀ ∅ Γ' ρ' _ hΨ' hρ' hkey hdom
            have hev0 : ValTy.EvalT _Ψ (Basis.tof b₀) τv₀ := by rw [hb₀]; exact h₀
            -- codomain validity IH (mirror of `eTpiTy`): the cofinite source codomain
            -- typing `hcod z` feeds `ih_h₁` under the extend helpers.
            have codIH : ∀ z, z ∉ L ∪ _Ψ.keyNames ∪ Γ'.keys ∪ Lc →
                ValTyOk (ValTy.openVar z τv₀ τv₁) ∧
                ValTy.fv (ValTy.openVar z τv₀ τv₁) ⊆ insert z _Ψ.keyNames := by
              intro z hz
              simp only [Finset.mem_union, not_or] at hz
              obtain ⟨⟨⟨hzL, hzkn⟩, _hzΓ⟩, hzLc⟩ := hz
              have hfresh : (z, b₀) ∉ _Ψ :=
                fun hc => hzkn (Finset.mem_image_of_mem Prod.fst (Finmap.mem_keys.mpr hc))
              have hΨ'' := evalCtxValidPlus_extend hΨ' hfresh hfv₀ hev0
              have hρ'' : RhoValid (EvalCtx.extend _Ψ z b₀ (.var z τv₀)) (insert z ρ') :=
                rhoValid_extend hρ' hzkn hkey ⟨k₀v, ⟨vτv₀⟩⟩ hfv₀
              have hkey'' : KeyScope (EvalCtx.extend _Ψ z b₀ (.var z τv₀)) (insert z ρ') :=
                keyScope_extend hkey
              have hTV := hcod z hzLc
              have hres := ih_h₁ z hzL ∅ _ (insert z ρ') _ hΨ'' hρ'' hkey'' hTV
              rwa [keyNames_extend] at hres
            -- `fv τv₁ ⊆ keyNames` (fresh-`z` drop, via `codIH`).
            have hfvτv₁ : ValTy.fv τv₁ ⊆ _Ψ.keyNames := by
              obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
                (L ∪ _Ψ.keyNames ∪ Γ'.keys ∪ Lc ∪ ValTy.fv τv₁)
              rw [Finset.mem_union, not_or] at hz
              obtain ⟨hzbig, hzfv⟩ := hz
              intro w hw
              have hw' : w ∈ ValTy.fv (ValTy.openVar z τv₀ τv₁) := ValTy.fv_subset_openRec hw
              rcases Finset.mem_insert.mp ((codIH z hzbig).2 hw') with rfl | hwk
              · exact absurd hw hzfv
              · exact hwk
            -- `fv env ⊆ keyNames` (the body-value scoping). Reconstruct the produced
            -- `OpStep.nllam` from the arm's own premises and read the value's fv off the
            -- independent fv-scoping induction (`opStep_fv`, via `eval_fv_joint`); the
            -- value is `.vlam τv₀ τv₁ (.reshap env τv₁ τv₁)`, whose fv contains `fv env`.
            have hfvenv : ValExpr.fv env ⊆ _Ψ.keyNames := by
              have hfvval := opStep_fv (ValExpr.OpStep.nllam hb₀ hb₁ h₀ L he h₁) hΨ'
              simp only [ValExpr.fv, ValTy.fv] at hfvval
              exact ((Finset.subset_union_left.trans Finset.subset_union_left).trans
                Finset.subset_union_right).trans hfvval
            -- the `.piTy τv₀ τv₁` validity (uniform codomain kind), reused 3×.
            have hpiv : Nonempty (ValTValidC (.piTy τv₀ τv₁) (.arrow k₀v τv₁.structuralKind)) :=
              ⟨ValTValidC.piTy (L ∪ _Ψ.keyNames ∪ Γ'.keys ∪ Lc) vτv₀
                (fun z hz => Classical.choice (by
                  obtain ⟨kz, ⟨vcz⟩⟩ := (codIH z hz).1
                  have hkz : kz = τv₁.structuralKind := by
                    rw [ValTValidC.kind_eq_structural vcz, ValTy.openVar, ValTy.structuralKind_openRec]
                  exact ⟨hkz ▸ vcz⟩))⟩
          -- assemble the three conjuncts.
            refine ⟨⟨.piTy τv₀ τv₁, ?_, ?_⟩, ?_, ?_⟩
            · -- EvalT realization.
              rw [Basis.tof, hb₀, hb₁]; exact ValTy.EvalT.piTy h₀ hb₀ L h₁
            · -- ReshapEq (self).
              rw [ValExpr.inferType_vlam]; exact ReshapEq.refl (Classical.choice hpiv)
            · -- ValTyOk (inferType value).
              rw [ValExpr.inferType_vlam]; exact ⟨_, hpiv⟩
            · -- fv scoping.
              rw [ValExpr.inferType_vlam]
              simp only [ValTy.fv, ValExpr.fv]
              refine Finset.union_subset (Finset.union_subset hfv₀ hfvτv₁) ?_
              exact Finset.union_subset (Finset.union_subset hfv₀ hfvτv₁)
                (Finset.union_subset (Finset.union_subset hfvenv hfvτv₁) hfvτv₁))
      -- OpStep appN_val (part 1, plain function eval): TRIVIAL BY DESIGN — the
      -- result type IS the rule's own `hout` realization of the instantiated
      -- codomain (`inferType (.appV _ _ τ_out) = τ_out`); validity via the
      -- operational regularity `evalT_valid`; fv via `evalT_fv` + `opStep_fv`.
      -- arm: oAppNVal
      (by
        intro _Ψ b₀ b₁ n₀ n₁ env₀ env₁ τ_out h₀ h₁ hout _ih_h₀ _ih_h₁ _ih_hout
              _Δ' _Γ' _ρ' hΨ' _hρ' _hkey _htype _hsof
        have hfvout : ValTy.fv τ_out ⊆ _Ψ.keyNames := evalT_fv hout hΨ'
        refine ⟨⟨τ_out, hout, ?_⟩, ?_, ?_⟩
        · rw [ValExpr.inferType_applyAt]; exact ReshapEq.refl (evalT_valid hout).some
        · rw [ValExpr.inferType_applyAt]; exact ⟨_, evalT_valid hout⟩
        · rw [ValExpr.inferType_applyAt]
          exact Finset.union_subset hfvout
            ((ValExpr.fv_applyAt_subset _ _ _).trans
              (Finset.union_subset
                (Finset.union_subset (opStep_fv h₀ hΨ') (opStep_fv h₁ hΨ')) hfvout)))
      -- OpStep frame_reanchor (part 1): the modern recipe — the rule carries
      -- EXACTLY the `EvalT.piTy` components (anchored cofinite codomain), so the
      -- realization is rebuilt from its own premises; validity via `evalT_valid`;
      -- fv via `opStep_fv` on the reconstructed step (the value contains its type).
      -- arm: oFrameReanchor
      (by
        intro _Ψ b₀ b₀' b₁ n₀ leev env₁ τv₀ τv₀' τv₁' h₀ htof hfn hdom L hx hcod
              _ih_h₀ _ih_hfn _ih_hdom _ih_hx _ih_hcod
              _Δ' _Γ' _ρ' hΨ' _hρ' _hkey _htype _hsof
        have hevPi : ValTy.EvalT _Ψ (Basis.tof (.frame b₀ b₁)) (.piTy τv₀ τv₁') := by
          show ValTy.EvalT _Ψ (.piTy (Basis.tof b₀) (Basis.tof b₁)) (.piTy τv₀ τv₁')
          exact ValTy.EvalT.piTy h₀ rfl L hcod
        have hfvval := opStep_fv
          (ValExpr.OpStep.frame_reanchor h₀ htof hfn hdom L hx hcod) hΨ'
        have hsub : ValTy.fv (ValTy.piTy τv₀ τv₁')
            ⊆ ValExpr.fv (.vlam τv₀ τv₁'
                (.reshap (.applyValue leev (.reshap env₁ τv₀' τv₀'))
                  τv₁' τv₁')) := by
          simp only [ValExpr.fv, ValTy.fv]
          exact Finset.subset_union_left
        refine ⟨⟨.piTy τv₀ τv₁', hevPi, ?_⟩, ?_, ?_⟩
        · rw [ValExpr.inferType_vlam]; exact ReshapEq.refl (evalT_valid hevPi).some
        · rw [ValExpr.inferType_vlam]; exact ⟨_, evalT_valid hevPi⟩
        · rw [ValExpr.inferType_vlam]
          exact Finset.union_subset (hsub.trans hfvval) hfvval)
      -- OpStep frame_eta (part 1): same recipe as frame_reanchor.
      -- arm: oFrameEta
      (by
        intro _Ψ b₀ b₁ n₀ τv₀ τv₁ env h₀ L he h₁ _ih_h₀ _ih_he _ih_h₁
              _Δ' _Γ' _ρ' hΨ' _hρ' _hkey _htype _hsof
        have hevPi : ValTy.EvalT _Ψ (Basis.tof (.frame b₀ b₁)) (.piTy τv₀ τv₁) := by
          show ValTy.EvalT _Ψ (.piTy (Basis.tof b₀) (Basis.tof b₁)) (.piTy τv₀ τv₁)
          exact ValTy.EvalT.piTy h₀ rfl L h₁
        have hfvval := opStep_fv (ValExpr.OpStep.frame_eta h₀ L he h₁) hΨ'
        have hsub : ValTy.fv (ValTy.piTy τv₀ τv₁)
            ⊆ ValExpr.fv (.vlam τv₀ τv₁ (.reshap env τv₁ τv₁)) := by
          simp only [ValExpr.fv, ValTy.fv]
          exact Finset.subset_union_left
        refine ⟨⟨.piTy τv₀ τv₁, hevPi, ?_⟩, ?_, ?_⟩
        · rw [ValExpr.inferType_vlam]; exact ReshapEq.refl (evalT_valid hevPi).some
        · rw [ValExpr.inferType_vlam]; exact ⟨_, evalT_valid hevPi⟩
        · rw [ValExpr.inferType_vlam]
          exact Finset.union_subset (hsub.trans hfvval) hfvval)
      -- OpStep reshape_cob: cross-part (uses BOTH the part-1 IH on the inner OpStep
      -- and the part-3 IH on the rule's EvalS premise hsv'), then the helper.
      -- arm: oReshape
      (by

        intro Ψ0 e b v τv_src τv_tgt he hsrc htgt ih_he _ih_hsrc _ih_htgt
              Δ' Γ' ρ' hΨ' hρ' hkey htype hsof
        obtain ⟨_, _, hfv_he⟩ := ih_he Δ' Γ' ρ' hΨ' hρ' hkey htype hsof
        have hfvv : ValExpr.fv v ⊆ Ψ0.keyNames :=
          Finset.Subset.trans Finset.subset_union_right hfv_he
        have hfvsrc : ValTy.fv τv_src ⊆ Ψ0.keyNames := evalT_fv hsrc hΨ'
        have hfvtgt : ValTy.fv τv_tgt ⊆ Ψ0.keyNames := evalT_fv htgt hΨ'
        simp only [ValExpr.inferType_reshap]
        refine ⟨⟨τv_tgt, htgt, ReshapEq.refl (evalT_valid htgt).some⟩,
          ⟨_, evalT_valid htgt⟩, ?_⟩
        change ValTy.fv τv_tgt ∪
          ((ValExpr.fv v ∪ ValTy.fv τv_tgt) ∪ ValTy.fv τv_src) ⊆ Ψ0.keyNames
        exact Finset.union_subset hfvtgt
          (Finset.union_subset (Finset.union_subset hfvv hfvtgt) hfvsrc))

      (by
        intro _Ψ b' b e sv' sv env htof' hsv' hsv L hfam _ih_hsv' _ih_hsv _ih_hfam
              _Δ' _Γ' _ρ' hΨ' _hρ' _hkey _htype _hsof
        obtain ⟨vsv'⟩ := evalS_valid hsv'
        obtain ⟨vsv⟩ := evalS_valid hsv
        have hevT : ValTy.EvalT _Ψ (Basis.tof (.tprod (.dual b') b))
            (.space (.tprod sv' sv)) := by
          show ValTy.EvalT _Ψ (.space (.tprod (.dual (Basis.sof b')) (Basis.sof b)))
            (.space (.tprod sv' sv))
          exact .space (.tprod (.dual hsv') hsv)
        have hfvval := opStep_fv
          (ValExpr.OpStep.llam_assemble htof' hsv' hsv L hfam) hΨ'
        simp only [ValExpr.sumAt, ValExpr.reshapBase, ValExpr.inferType_reshap]
        refine ⟨⟨_, hevT, ?_⟩, ?_, ?_⟩
        · exact ReshapEq.refl (ValTValidC.space (.tprod vsv' vsv))
        · exact ⟨.base, ⟨.space (.tprod vsv' vsv)⟩⟩
        · refine Finset.union_subset ?_ hfvval
          simp only [ValTy.fv, ValSpace.fv]
          exact Finset.union_subset (evalS_fv hsv' hΨ') (evalS_fv hsv hΨ'))
      -- OpStep llam_assemble_real (part 1): the ℝ/dual degeneracy — realized
      -- type `.space sv'`; same S1 annotation structure.
      -- arm: oLlamAssembleReal
      (by
        intro _Ψ b' e sv' env htof' hsv' L hfam _ih_hsv' _ih_hfam
              _Δ' _Γ' _ρ' hΨ' _hρ' _hkey _htype _hsof
        obtain ⟨vsv'⟩ := evalS_valid hsv'
        have hevT : ValTy.EvalT _Ψ (Basis.tof (.dual b')) (.space sv') := by
          show ValTy.EvalT _Ψ (.space (.dual (Basis.sof b'))) (.space sv')
          exact .space (.dual hsv')
        have hfvval := opStep_fv
          (ValExpr.OpStep.llam_assemble_real htof' hsv' L hfam) hΨ'
        simp only [ValExpr.sumAt, ValExpr.reshapBase, ValExpr.inferType_reshap]
        refine ⟨⟨_, hevT, ?_⟩, ?_, ?_⟩
        · exact ReshapEq.refl (ValTValidC.space vsv')
        · exact ⟨.base, ⟨.space vsv'⟩⟩
        · exact Finset.union_subset (evalS_fv hsv' hΨ') hfvval)
      -- OpStep zero (part 1, erratum-fix literal — trivial by design): the
      -- realized type `.space sv` and the value's structural
      -- `inferType (.zero sv) = .space sv` both read off the rule's own
      -- premises (`htof`/`hsv`); validity + fv via operational regularity.
      -- arm: oZero
      (by
        intro _Ψ b sv htof hsv _ih_hsv _Δ' _Γ' _ρ' hΨ' _hρ' _hkey _htype _hsof
        obtain ⟨vsv⟩ := evalS_valid hsv
        have hevT : ValTy.EvalT _Ψ (Basis.tof b) (.space sv) := by
          rw [htof]; exact .space hsv
        have hinf : ValExpr.inferType (.zero sv) = .space sv := rfl
        refine ⟨⟨_, hevT, ?_⟩, ?_, ?_⟩
        · rw [hinf]; exact ReshapEq.refl (ValTValidC.space vsv)
        · rw [hinf]; exact ⟨.base, ⟨ValTValidC.space vsv⟩⟩
        · rw [hinf]
          have hfvsv := evalS_fv hsv hΨ'
          simp only [ValTy.fv, ValExpr.fv]
          exact Finset.union_subset hfvsv hfvsv)
      -- OpStep rlit (part 1, erratum-fix literal — trivial by design):
      -- `tof .one = .space .real` and `inferType (.rlit r) = .space .real`
      -- both hold structurally; everything is closed-form.
      -- arm: oRlit
      (by
        intro _Ψ r _Δ' _Γ' _ρ' _hΨ' _hρ' _hkey _htype _hsof
        have hevT : ValTy.EvalT _Ψ (Basis.tof .one) (.space .real) := .space .real
        have hinf : ValExpr.inferType (.rlit r) = .space .real := rfl
        refine ⟨⟨_, hevT, ?_⟩, ?_, ?_⟩
        · rw [hinf]; exact ReshapEq.refl (ValTValidC.space .real)
        · rw [hinf]; exact ⟨.base, ⟨ValTValidC.space .real⟩⟩
        · rw [hinf]
          exact Finset.union_subset (Finset.empty_subset _) (Finset.empty_subset _))

/-- **Joint** (part 3 entry) — corollary of `preservation_master`. -/
theorem preservation_joint
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {ρ : ValScope} {s : Space} {sv : ValSpace}
    (hev : ValSpace.EvalS Ψ s sv)
    (hwfΔΓ : CtxWF' Δ Γ) (hwfΨ : EvalCtxValid Ψ) (hwflc : EvalCtxLc Ψ)
    (hanch : EvalCtxLamAnchored Ψ) (hwfρ : RhoValid Ψ ρ)
    (hΓΨ : TypingImplyEval Δ Γ Ψ) (hΓΨρ : ScopeImplyVal Δ Γ ρ)
    (hsv : SValid Γ s) :
      Nonempty (ValSValidC sv) ∧ (ValSpace.fv sv ⊆ ρ) := by
  have key : Ψ.keyNames ⊆ ρ := keyScope_of hΓΨ hΓΨρ
  have h := preservation_master.1 hev Δ Γ ρ
    (evalCtxValidPlus_of hwfΨ hwflc hanch hwfρ hΓΨ hΓΨρ) hwfρ key hsv
  exact ⟨h.1, h.2.trans key⟩

/-- **Part 3 (space)** — the corollary advertised above: a realized value space is
    valid + scoped, immediately from `preservation_joint`. -/
theorem preservation_space
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {ρ : ValScope}
    {s : Space} {sv : ValSpace}
    (hwfΔΓ : CtxWF' Δ Γ) (hwfΨ : EvalCtxValid Ψ) (hwflc : EvalCtxLc Ψ)
    (hanch : EvalCtxLamAnchored Ψ) (hwfρ : RhoValid Ψ ρ)
    (hΓΨ : TypingImplyEval Δ Γ Ψ) (hΓΨρ : ScopeImplyVal Δ Γ ρ)
    (hsv : SValid Γ s)
    (hev : ValSpace.EvalS Ψ s sv) :
      Nonempty (ValSValidC sv)
    ∧ (ValSpace.fv sv ⊆ ρ) :=
  preservation_joint hev hwfΔΓ hwfΨ hwflc hanch hwfρ hΓΨ hΓΨρ hsv

/-- **Part 1 (term).** `term → value`: there is a space-eval path to a realization
    the value's type is reshape-compatible with; the value's type is valid; and
    `fv` is scoped. The OpStep entry of `preservation_master`; `SValid (sof b)`
    is recovered from the basis-validity premise via `BasisValid.sof_valid`. -/
theorem preservation_term
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {ρ : ValScope}
    {e : Term} {b : Basis} {v : ValExpr}
    (hwfΔΓ : CtxWF' Δ Γ) (hwfΨ : EvalCtxValid Ψ) (hwflc : EvalCtxLc Ψ)
    (hanch : EvalCtxLamAnchored Ψ) (hwfρ : RhoValid Ψ ρ)
    (hΓΨ : TypingImplyEval Δ Γ Ψ) (hΓΨρ : ScopeImplyVal Δ Γ ρ)
    (htype : HasType Δ Γ e (Basis.tof b))
    (hbval : Basis.BasisValid Γ b)
    (hstep : ValExpr.OpStep Ψ e b v) :
      (∃ τv, ValTy.EvalT Ψ (Basis.tof b) τv ∧ ReshapEq (ValExpr.inferType v) τv)
    ∧ ValTyOk (ValExpr.inferType v)
    ∧ (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ ρ) := by
  have key : Ψ.keyNames ⊆ ρ := keyScope_of hΓΨ hΓΨρ
  obtain ⟨hsof⟩ := hbval.sof_valid
  obtain ⟨h₁, h₂, h₃⟩ := preservation_master.2.2.2 hstep Δ Γ ρ
    (evalCtxValidPlus_of hwfΨ hwflc hanch hwfρ hΓΨ hΓΨρ) hwfρ key htype hsof
  exact ⟨h₁, h₂, h₃.trans key⟩

/-- **Part 2 (COB).** The change-of-basis witness `env` is a matrix `sv₀ ⊗ sv₁` of
    genuine realizations (∃ pinned by `inferType env`). -/
theorem preservation_cob
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {ρ : ValScope}
    {b₀ b₁ : Basis} {env : ValExpr} {s : Space}
    (hwfΔΓ : CtxWF' Δ Γ) (hwfΨ : EvalCtxValid Ψ) (hwflc : EvalCtxLc Ψ)
    (hanch : EvalCtxLamAnchored Ψ) (hwfρ : RhoValid Ψ ρ)
    (hΓΨ : TypingImplyEval Δ Γ Ψ) (hΓΨρ : ScopeImplyVal Δ Γ ρ)
    (hb₀ : Basis.BasisValid Γ b₀) (hb₁ : Basis.BasisValid Γ b₁)
    (htof₀ : Basis.tof b₀ = .space s) (htof₁ : Basis.tof b₁ = .space s)
    (hbb : Basis.EvalBB Ψ b₀ env b₁) :
      (∃ s₀ s₁ sv₀ sv₁, ValExpr.inferType env = .space (.tprod sv₀ sv₁)
                ∧ ValSpace.EvalS Ψ s₀ sv₀ ∧ ValSpace.EvalS Ψ s₁ sv₁)
    ∧ ValTyOk (ValExpr.inferType env)
    ∧ (ValExpr.fv env ⊆ ρ) := by
  have key : Ψ.keyNames ⊆ ρ := keyScope_of hΓΨ hΓΨρ
  obtain ⟨hsof⟩ := hb₀.sof_valid
  obtain ⟨hshape, hok, hfv⟩ := preservation_master.2.2.1 hbb Δ Γ ρ
    (evalCtxValidPlus_of hwfΨ hwflc hanch hwfρ hΓΨ hΓΨρ) hwfρ key hsof
  exact ⟨hshape, hok, hfv.trans key⟩

end GLang.V2
