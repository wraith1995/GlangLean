

import GLang.Proofs.Progress.Supporting.ProgressTransportSpec
import GLang.Proofs.Progress.Supporting.ProgressCob

set_option maxHeartbeats 1600000

namespace GLang

/-! ## Structural inversions of `Basis.tof`. -/

/-- Only `.frame`s have a `.piTy` type: `tof b = .piTy τ₀ τ₁` forces
    `b = .frame b₀ b₁` with `tof b₀ = τ₀`, `tof b₁ = τ₁` (every other
    constructor's `tof` is `.space (sof b)`). -/
theorem Basis.tof_piTy_inv {b : Basis} {τ₀ τ₁ : Ty}
    (h : Basis.tof b = .piTy τ₀ τ₁) :
    ∃ b₀ b₁, b = .frame b₀ b₁ ∧ Basis.tof b₀ = τ₀ ∧ Basis.tof b₁ = τ₁ := by
  cases b with
  | frame b₀ b₁ =>
      simp only [Basis.tof, Ty.piTy.injEq] at h
      exact ⟨b₀, b₁, rfl, h.1, h.2⟩
  | empty => simp [Basis.tof] at h
  | one => simp [Basis.tof] at h
  | dual b => simp [Basis.tof] at h
  | dsum b₀ b₁ => simp [Basis.tof] at h
  | tprod b₀ b₁ => simp [Basis.tof] at h
  | proj s b₀ b₁ => simp [Basis.tof] at h
  | image b => simp [Basis.tof] at h
  | terms s es b => simp [Basis.tof] at h

/-- A basis of space type is not a frame (`tof (.frame …)` is a `.piTy`). -/
theorem Basis.ne_frame_of_tof_space {b : Basis} {s : Space}
    (h : Basis.tof b = .space s) : ∀ b₀ b₁, b ≠ .frame b₀ b₁ := by
  intro b₀ b₁ heq
  subst heq
  simp [Basis.tof] at h

/-- Type-validity of a valid basis's type, derived recursively from basis validity. -/
theorem Basis.BasisValid.tof_tvalid {ε : NLCtx} {b : Basis}
    (h : Basis.BasisValid ε b) : ∃ k, Nonempty (TValid ε (Basis.tof b) k) := by
  exact ⟨_, h.tof_valid_structural⟩

/-! ## Hereditary well-formedness is `openRec`-invariant.

`IsSpaceBasis`/`IsTyBasis` only constrain constructor heads (no frames in
space positions) and `.terms`-list nonemptiness; `Basis.openRec` preserves
both (it maps the list, keeping its length). -/

/-- `IsSpaceBasis` survives opening a bound index (any replacement term). -/
theorem Basis.IsSpaceBasis.openRec (k : Nat) (u : Term) :
    ∀ {b : Basis}, Basis.IsSpaceBasis b →
      Basis.IsSpaceBasis (Basis.openRec k u b)
  | .empty, _ => trivial
  | .one, _ => trivial
  | .dual b, h => Basis.IsSpaceBasis.openRec k u (b := b) h
  | .dsum b₀ b₁, h =>
      ⟨Basis.IsSpaceBasis.openRec k u h.1, Basis.IsSpaceBasis.openRec k u h.2⟩
  | .tprod b₀ b₁, h =>
      ⟨Basis.IsSpaceBasis.openRec k u h.1, Basis.IsSpaceBasis.openRec k u h.2⟩
  | .proj s b₀ b₁, h =>
      ⟨Basis.IsSpaceBasis.openRec k u h.1, Basis.IsSpaceBasis.openRec k u h.2⟩
  | .image b, h => Basis.IsSpaceBasis.openRec k u (b := b) h
  | .terms s es b, h => by
      refine ⟨?_, Basis.IsSpaceBasis.openRec k u h.2⟩
      obtain ⟨e, es', rfl⟩ := List.exists_cons_of_ne_nil h.1
      simp [Term.openRecList]
  | .frame _ _, h => False.elim h

/-- `IsTyBasis` survives opening a bound index: the frame arm recurses
    componentwise (codomain at `k+1`); every non-frame head keeps its
    constructor under `openRec`, so the `IsSpaceBasis` delegate transports. -/
theorem Basis.IsTyBasis.openRec (u : Term) :
    ∀ {b : Basis} (k : Nat), Basis.IsTyBasis b →
      Basis.IsTyBasis (Basis.openRec k u b)
  | .frame _ _, k, h =>
      ⟨Basis.IsTyBasis.openRec u k h.1, Basis.IsTyBasis.openRec u (k+1) h.2⟩
  | .empty, k, h => Basis.IsSpaceBasis.openRec k u h
  | .one, k, h => Basis.IsSpaceBasis.openRec k u h
  | .dual _, k, h => Basis.IsSpaceBasis.openRec k u h
  | .dsum _ _, k, h => Basis.IsSpaceBasis.openRec k u h
  | .tprod _ _, k, h => Basis.IsSpaceBasis.openRec k u h
  | .proj _ _ _, k, h => Basis.IsSpaceBasis.openRec k u h
  | .image _, k, h => Basis.IsSpaceBasis.openRec k u h
  | .terms _ _ _, k, h => Basis.IsSpaceBasis.openRec k u h

end GLang

namespace GLang.V2

/-! ## `ExtBy` — iterated fresh-key, `lc`-value context extension.

The weakening order along which carrier-context facts transport into the
judgment context (see the header). Storing only `lc` values keeps `EvalCtxLc`
transportable (the P3 kit's `lc` side conditions). -/

/-- `ExtBy Ψ Ψp`: `Ψp` extends `Ψ` by finitely many fresh keys, each storing a
    locally-closed value. -/
inductive ExtBy : EvalCtx → EvalCtx → Prop
  | refl (Ψ : EvalCtx) : ExtBy Ψ Ψ
  | step {Ψ Ψ' : EvalCtx} {x : VName} {b : Basis} {v : ValExpr} :
      ExtBy Ψ Ψ' → (x, b) ∉ Ψ' → ValExpr.lc v →
      ExtBy Ψ (EvalCtx.extend Ψ' x b v)

/-- `OpStep` weakens along an `ExtBy` extension (iterated `opStep_wk`). -/
theorem opStep_wk_ext {Ψ Ψp : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
    (hext : ExtBy Ψ Ψp) (h : ValExpr.OpStep Ψ e b v) :
    ValExpr.OpStep Ψp e b v := by
  induction hext with
  | refl => exact h
  | step _ hfresh _ ih => exact opStep_wk ih hfresh

/-- `EvalT` weakens along an `ExtBy` extension. -/
theorem evalT_wk_ext {Ψ Ψp : EvalCtx} {τ : Ty} {τv : ValTy}
    (hext : ExtBy Ψ Ψp) (h : ValTy.EvalT Ψ τ τv) : ValTy.EvalT Ψp τ τv := by
  induction hext with
  | refl => exact h
  | step _ hfresh _ ih => exact evalT_wk ih hfresh

/-- `EvalS` weakens along an `ExtBy` extension. -/
theorem evalS_wk_ext {Ψ Ψp : EvalCtx} {s : Space} {sv : ValSpace}
    (hext : ExtBy Ψ Ψp) (h : ValSpace.EvalS Ψ s sv) :
    ValSpace.EvalS Ψp s sv := by
  induction hext with
  | refl => exact h
  | step _ hfresh _ ih => exact evalS_wk ih hfresh

/-- `EvalBB` weakens along an `ExtBy` extension. -/
theorem evalBB_wk_ext {Ψ Ψp : EvalCtx} {b : Basis} {env : ValExpr} {b' : Basis}
    (hext : ExtBy Ψ Ψp) (h : Basis.EvalBB Ψ b env b') :
    Basis.EvalBB Ψp b env b' := by
  induction hext with
  | refl => exact h
  | step _ hfresh _ ih => exact evalBB_wk ih hfresh

/-- `EvalCtxLc` transports along an `ExtBy` extension (every added value is
    `lc` by construction). -/
theorem ExtBy.evalCtxLc {Ψ Ψp : EvalCtx} (hext : ExtBy Ψ Ψp)
    (h : EvalCtxLc Ψ) : EvalCtxLc Ψp := by
  induction hext with
  | refl => exact h
  | step _ _ hlc ih => exact EvalCtxLc.extend ih hlc

/-- An `ExtBy` extension survives extending BOTH ends by the same fresh
    binding (insert-commute through every step). -/
theorem ExtBy.extend {Ψ Ψp : EvalCtx} (hext : ExtBy Ψ Ψp) :
    ∀ (y : VName) (c : Basis) (w : ValExpr), (y, c) ∉ Ψp → ValExpr.lc w →
      ExtBy (EvalCtx.extend Ψ y c w) (EvalCtx.extend Ψp y c w) := by
  induction hext with
  | refl => exact fun _ _ _ _ _ => .refl _
  | @step Ψ' x b v _ hx hlcv ih =>
      intro y c w hfresh hlcw
      have hne : (y, c) ≠ (x, b) := by
        intro hh
        exact hfresh (by
          rw [EvalCtx.extend]
          exact Finmap.mem_insert.mpr (Or.inl hh))
      have hyΨ' : (y, c) ∉ Ψ' := fun hm =>
        hfresh (by
          rw [EvalCtx.extend]
          exact Finmap.mem_insert.mpr (Or.inr hm))
      have hxe : (x, b) ∉ EvalCtx.extend Ψ' y c w := by
        rw [EvalCtx.extend]
        exact fun hm =>
          (Finmap.mem_insert.mp hm).elim (fun hh => hne hh.symm) hx
      have hcomm :
          Finmap.insert (y, c) w (EvalCtx.extend Ψ' x b v)
            = EvalCtx.extend (Finmap.insert (y, c) w Ψ') x b v :=
        evalctx_extend_comm hne
      show ExtBy (EvalCtx.extend Ψ y c w)
        (Finmap.insert (y, c) w (EvalCtx.extend Ψ' x b v))
      rw [hcomm]
      exact .step (ih y c w hyΨ' hlcw) hxe hlcv

/-! ## Small extension lemmas (arbitrary-basis forms). -/

/-- `keyNames ⊆ avoidB` (the key-name component of the ambient name set). -/
theorem keyNames_subset_avoidB (Ψ : EvalCtx) :
    Ψ.keyNames ⊆ EvalCtx.avoidB Ψ := by
  intro z hz
  rw [EvalCtx.keyNames] at hz
  rw [EvalCtx.avoidB, EvalCtx.avoid]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)

/-- Covering extends across a binder stored at an ARBITRARY basis `b` (the
    `Γ`-side binding records its type `tof b`) — the arbitrary-basis mirror of
    `VarsCovered.extend_var` (which is specific to `Basis.std`). -/
theorem VarsCovered.extend_var_basis {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {y : VName} {b : Basis} {v : ValExpr}
    (h : VarsCovered Δ Γ Ψ) :
    VarsCovered Δ (Finmap.insert y (Basis.tof b) Γ)
      (EvalCtx.extend Ψ y b v) := by
  constructor
  · intro x s hx
    obtain ⟨b', hb', htof⟩ := h.1 x s hx
    exact ⟨b', by
      rw [EvalCtx.extend]
      exact Finmap.mem_insert.mpr (Or.inr hb'), htof⟩
  · intro x τ hx
    by_cases hxy : x = y
    · subst hxy
      simp only [Finmap.lookup_insert, Option.some.injEq] at hx
      subst hx
      exact ⟨b, by
        rw [EvalCtx.extend]
        exact Finmap.mem_insert.mpr (Or.inl rfl), rfl⟩
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      obtain ⟨b', hb', htof⟩ := h.2 x τ hx
      exact ⟨b', by
        rw [EvalCtx.extend]
        exact Finmap.mem_insert.mpr (Or.inr hb'), htof⟩

/-- `StoredWF` survives extending by an `IsTyBasis`-keyed binding. -/
theorem StoredWF.extend {Ψ : EvalCtx} {y : VName} {b : Basis} {v : ValExpr}
    (h : StoredWF Ψ) (hb : Basis.IsTyBasis b) :
    StoredWF (EvalCtx.extend Ψ y b v) := by
  intro x c hmem
  rw [EvalCtx.extend] at hmem
  rcases Finmap.mem_insert.mp hmem with heq | hmem'
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact hb
  · exact h x c hmem'

/-! ## The fuel-bounded transport statement. -/

/-- **`TransportN n`** — the `BasisTransport` body at types of size `≤ n`,
    with the judgment context generalized to an `ExtBy` extension `Ψp` of the
    carrier context `Ψ` (see the file header for why the gap is load-bearing).
    `basis_transport` is the `Ψp := Ψ` (gap-0) instance at
    `n := Ty.size (tof b₁)`. -/
def TransportN (n : Nat) : Prop :=
  ∀ (Γ : NLCtx) (Ψ Ψp : EvalCtx) (e : Term) (b₁ b₂ : Basis) (v₁ : ValExpr),
    PCarrier Ψ → VarsCovered ∅ Γ Ψ → StoredWF Ψ → ExtBy Ψ Ψp →
    Basis.BasisValid Γ b₁ → Basis.IsTyBasis b₁ →
    Basis.BasisValid Γ b₂ → Basis.IsTyBasis b₂ →
    Basis.tof b₂ = Basis.tof b₁ →
    Ty.size (Basis.tof b₁) ≤ n →
    ValExpr.OpStep Ψp e b₁ v₁ →
    ∃ v₂, ValExpr.OpStep Ψp e b₂ v₂

/-! ## Component (b): carrier extension at an ARBITRARY valid `IsTyBasis`
    basis, parameterized by same-level transport. -/

/-- Carrier extension at an arbitrary valid type basis. `PCarrier`, `VarsCovered`, and `StoredWF` are preserved by fresh variable insertion. -/
theorem pcarrier_extend_transport {n : Nat} (hT : TransportN n)
    {Γ : NLCtx} {Ψ : EvalCtx} {y₀ : VName} {b₀ : Basis} {τv₀ : ValTy}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ) (hsw : StoredWF Ψ)
    (hb : Basis.BasisValid Γ b₀) (ht : Basis.IsTyBasis b₀)
    (hev : ValTy.EvalT Ψ (Basis.tof b₀) τv₀)
    (hfresh : (y₀, b₀) ∉ Ψ)
    (hsize : Ty.size (Basis.tof b₀) ≤ n) :
    PCarrier (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀))
    ∧ VarsCovered ∅ (Finmap.insert y₀ (Basis.tof b₀) Γ)
        (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀))
    ∧ StoredWF (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀)) := by
  obtain ⟨hplus, hstd⟩ := hP
  have hτfv : ValTy.fv τv₀ ⊆ Ψ.keyNames := evalT_fv hev hplus
  have hlcτv₀ : ValTy.lc τv₀ := evalT_lc hev hplus.toEvalCtxLc
  obtain ⟨k, ⟨hTV⟩⟩ := hb.tof_tvalid
  -- the new entry's std-basis evaluation: `OpStep.var` at the stored `b₀`,
  -- transported to `Basis.std (tof b₀)` at the same fuel level (gap 1).
  have hvar : ValExpr.OpStep (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀))
      (.var y₀) b₀ (.var y₀ τv₀) :=
    .var (by rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert])
  have hnew : ∃ v, ValExpr.OpStep (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀))
      (.var y₀) (Basis.std (Basis.tof b₀)) v :=
    hT Γ Ψ _ (.var y₀) b₀ (Basis.std (Basis.tof b₀)) (.var y₀ τv₀)
      ⟨hplus, hstd⟩ hcov hsw (.step (.refl _) hfresh (.var hlcτv₀))
      hb ht (Basis.std_valid _ hTV) (Basis.isTyBasis_std _)
      (Basis.tof_std _) hsize hvar
  refine ⟨⟨evalCtxValidPlus_extend hplus hfresh hτfv hev, ?_, ?_⟩,
    VarsCovered.extend_var_basis hcov, StoredWF.extend hsw ht⟩
  · -- StdComplete clause 1
    intro x b hmem
    rw [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact hnew
    · obtain ⟨v, hv⟩ := hstd.1 x b hmem'
      exact ⟨v, opStep_wk hv hfresh⟩
  · -- StdComplete clause 2 (the Π-anchored tail)
    intro x b hmem τa τb htofb
    rw [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ((progress_master_std.2.1 hTV Ψ ⟨hplus, hstd⟩ hcov).2
        τa τb htofb).wk hfresh
    · exact (hstd.2 x b hmem' τa τb htofb).wk hfresh

/-! ## The strong induction (component (a)). -/

/-- **The transport induction** — `TransportN n` for every fuel `n`, by strong
    induction on `n`. Space types via `progress_cob_master` + `OpStep.cob`;
    Π types via `OpStep.frame_eta` + `appN_val` with both recursive transports
    and the binder-carrier extension at STRICTLY SMALLER sizes (see the file
    header for the full route). -/
theorem transportN : ∀ n, TransportN n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Γ Ψ Ψp e b₁ b₂ v₁ hP hcov hsw hext hv₁ ht₁ hv₂ ht₂ htofeq hsize hstep
  cases hτ : Basis.tof b₁ with
  | space s =>
      -- ===== space case: cob across the composed conversions =====
      have hsb₁ : Basis.IsSpaceBasis b₁ :=
        ht₁.toIsSpaceBasis (Basis.ne_frame_of_tof_space hτ)
      have hsb₂ : Basis.IsSpaceBasis b₂ :=
        ht₂.toIsSpaceBasis (Basis.ne_frame_of_tof_space (htofeq.trans hτ))
      obtain ⟨env₁, hc₁⟩ := progress_cob_master hP hcov hv₁ hsb₁
      obtain ⟨env₂, hc₂⟩ := progress_cob_master hP hcov hv₂ hsb₂
      rw [htofeq] at hc₂
      obtain ⟨vS⟩ := hv₁.sof_valid
      obtain ⟨sv, hes⟩ := evalS_of_svalid hP hcov ⟨vS⟩
      have hbb : Basis.EvalBB Ψ b₁ _ b₂ := .trans hc₁ (.inverse hc₂) hes
      have hsofeq : Basis.sof b₂ = Basis.sof b₁ := by
        rw [sof_of_tof_eq_space (htofeq.trans hτ), sof_of_tof_eq_space hτ]
      have hes₂ : ValSpace.EvalS Ψ (Basis.sof b₂) sv := by
        rw [hsofeq]; exact hes
      exact ⟨_, .cob hsb₂.tof_eq hsb₁.tof_eq hstep
        (evalBB_wk_ext hext hbb) (evalS_wk_ext hext hes₂)⟩
  | piTy τ₀ τ₁ =>
      -- ===== Π case: frame_eta at (b₂₀, b₂₁) =====
      obtain ⟨b₁₀, b₁₁, rfl, htof₁₀, htof₁₁⟩ := Basis.tof_piTy_inv hτ
      obtain ⟨b₂₀, b₂₁, rfl, htof₂₀, htof₂₁⟩ :=
        Basis.tof_piTy_inv (htofeq.trans hτ)
      rw [hτ] at hsize
      simp only [Ty.size] at hsize
      have hs₀ : Ty.size τ₀ < n := by omega
      have hs₁ : Ty.size τ₁ < n := by omega
      -- validity inversions (both frames)
      obtain ⟨hv₁₀, ⟨L₁, hL₁⟩, -⟩ := hv₁.frame_inv
      obtain ⟨hv₂₀, ⟨L₂, hL₂⟩, k₀, k₁, ⟨hTpi⟩⟩ := hv₂.frame_inv
      rw [htof₂₀, htof₂₁] at hTpi
      cases hTpi with
      | piTy L_T hτ₀v hbody =>
      obtain ⟨ht₁₀, ht₁₁⟩ := ht₁
      obtain ⟨ht₂₀, ht₂₁⟩ := ht₂
      -- domain realization at the carrier context
      obtain ⟨⟨τv₀, hevτ₀⟩, -⟩ := progress_master_std.2.1 hτ₀v Ψ hP hcov
      have hlcτv₀ : ValTy.lc τv₀ := evalT_lc hevτ₀ hP.1.toEvalCtxLc
      have hfvτv₀ : ValTy.fv τv₀ ⊆ Ψ.keyNames := evalT_fv hevτ₀ hP.1
      -- one fresh name against everything in sight
      obtain ⟨y₀, hy₀⟩ := Infinite.exists_notMem_finset
        (EvalCtx.avoidB Ψ ∪ EvalCtx.avoidB Ψp ∪ L₁ ∪ L₂ ∪ L_T
          ∪ Basis.fv b₂₀ ∪ Basis.fv b₂₁ ∪ Term.fv e
          ∪ Ty.fv (Basis.tof b₂₁))
      simp only [Finset.mem_union, not_or] at hy₀
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hy₀Ψ, hy₀Ψp⟩, hy₀L₁⟩, hy₀L₂⟩, hy₀LT⟩, hy₀b₂₀⟩,
        hy₀b₂₁⟩, hy₀e⟩, hy₀τ⟩ := hy₀
      have hy₀τv₀ : y₀ ∉ ValTy.fv τv₀ := fun hm =>
        hy₀Ψ (keyNames_subset_avoidB Ψ (hfvτv₀ hm))
      have hfreshc : (y₀, b₂₀) ∉ Ψ := (EvalCtx.avoidB_spec hy₀Ψ).1 b₂₀
      have hfreshp : (y₀, b₂₀) ∉ Ψp := (EvalCtx.avoidB_spec hy₀Ψp).1 b₂₀
      have hlcvar : ValExpr.lc (ValExpr.var y₀ τv₀) := .var hlcτv₀
      -- carrier extension at the strictly smaller domain (component (b))
      have hevb₂₀ : ValTy.EvalT Ψ (Basis.tof b₂₀) τv₀ := by
        rw [htof₂₀]; exact hevτ₀
      obtain ⟨hP', hcov', hsw'⟩ :=
        pcarrier_extend_transport (ih (Ty.size τ₀) hs₀) hP hcov hsw
          hv₂₀ ht₂₀ hevb₂₀ hfreshc (le_of_eq (by rw [htof₂₀]))
      rw [htof₂₀] at hcov'
      have hcovΓ : VarsCovered ∅ Γ (EvalCtx.extend Ψ y₀ b₂₀ (.var y₀ τv₀)) :=
        hcov.wk_psi
      have hext' : ExtBy (EvalCtx.extend Ψ y₀ b₂₀ (.var y₀ τv₀))
          (EvalCtx.extend Ψp y₀ b₂₀ (.var y₀ τv₀)) :=
        hext.extend y₀ b₂₀ (.var y₀ τv₀) hfreshp hlcvar
      -- (i) the function: the GIVEN evaluation, weakened past the fresh key
      have hstep' : ValExpr.OpStep (EvalCtx.extend Ψp y₀ b₂₀ (.var y₀ τv₀))
          e (.frame b₁₀ b₁₁) v₁ := opStep_wk hstep hfreshp
      -- (ii) the argument: `.var y₀` from its stored `b₂₀` to `b₁₀`
      --      (component (a) at the strictly smaller domain)
      have hvary : ValExpr.OpStep (EvalCtx.extend Ψp y₀ b₂₀ (.var y₀ τv₀))
          (.var y₀) b₂₀ (.var y₀ τv₀) :=
        .var (by rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert])
      obtain ⟨env₁, henv₁⟩ := ih (Ty.size τ₀) hs₀ Γ
        (EvalCtx.extend Ψ y₀ b₂₀ (.var y₀ τv₀))
        (EvalCtx.extend Ψp y₀ b₂₀ (.var y₀ τv₀))
        (.var y₀) b₂₀ b₁₀ (.var y₀ τv₀)
        hP' hcovΓ hsw' hext' hv₂₀ ht₂₀ hv₁₀ ht₁₀
        (htof₁₀.trans htof₂₀.symm) (le_of_eq (by rw [htof₂₀])) hvary
      -- (iii) the output realization (TValid.piTy's codomain premise at y₀)
      obtain ⟨⟨τvout, hevout⟩, -⟩ := progress_master_std.2.1
        (hbody y₀ hy₀LT) (EvalCtx.extend Ψ y₀ b₂₀ (.var y₀ τv₀)) hP' hcov'
      have hlcτvout : ValTy.lc τvout := evalT_lc hevout hP'.1.toEvalCtxLc
      have hevoutp : ValTy.EvalT (EvalCtx.extend Ψp y₀ b₂₀ (.var y₀ τv₀))
          (Ty.openVar y₀ τ₁) τvout := evalT_wk_ext hext' hevout
      -- (iv) appN_val at the instantiated b₁₁-codomain basis
      have houttof : Basis.tof (Basis.instantiate (.var y₀) b₁₁)
          = Ty.openVar y₀ τ₁ := by
        show Basis.tof (Basis.openRec 0 (.var y₀) b₁₁) = Ty.openVar y₀ τ₁
        rw [Basis.tof_openRec, htof₁₁]
      have happ : ValExpr.OpStep (EvalCtx.extend Ψp y₀ b₂₀ (.var y₀ τv₀))
          (.appN e (.var y₀)) (Basis.instantiate (.var y₀) b₁₁)
          (.applyAt v₁ env₁ τvout) :=
        .appN_val hstep' henv₁ (by rw [houttof]; exact hevoutp)
      -- (v) transport the result basis to `openVar y₀ b₂₁` (size τ₁ < n)
      have hv₁₁' : Basis.BasisValid (Finmap.insert y₀ τ₀ Γ)
          (Basis.openVar y₀ b₁₁) := by
        have := hL₁ y₀ hy₀L₁; rwa [htof₁₀] at this
      have hv₂₁' : Basis.BasisValid (Finmap.insert y₀ τ₀ Γ)
          (Basis.openVar y₀ b₂₁) := by
        have := hL₂ y₀ hy₀L₂; rwa [htof₂₀] at this
      have htofeq' : Basis.tof (Basis.openVar y₀ b₂₁)
          = Basis.tof (Basis.openVar y₀ b₁₁) := by
        show Basis.tof (Basis.openRec 0 (.var y₀) b₂₁)
          = Basis.tof (Basis.openRec 0 (.var y₀) b₁₁)
        rw [Basis.tof_openRec, Basis.tof_openRec, htof₁₁, htof₂₁]
      have hsizeout : Ty.size (Basis.tof (Basis.openVar y₀ b₁₁))
          ≤ Ty.size τ₁ := by
        show Ty.size (Basis.tof (Basis.openRec 0 (.var y₀) b₁₁)) ≤ Ty.size τ₁
        rw [Basis.tof_openRec, htof₁₁]
        exact le_of_eq (Ty.size_openVar 0 y₀ τ₁)
      obtain ⟨w, hw⟩ := ih (Ty.size τ₁) hs₁ (Finmap.insert y₀ τ₀ Γ)
        (EvalCtx.extend Ψ y₀ b₂₀ (.var y₀ τv₀))
        (EvalCtx.extend Ψp y₀ b₂₀ (.var y₀ τv₀))
        (.appN e (.var y₀)) (Basis.openVar y₀ b₁₁) (Basis.openVar y₀ b₂₁)
        (.applyAt v₁ env₁ τvout)
        hP' hcov' hsw' hext' hv₁₁' (Basis.IsTyBasis.openRec _ 0 ht₁₁)
        hv₂₁' (Basis.IsTyBasis.openRec _ 0 ht₂₁) htofeq' hsizeout happ
      have hlcw : ValExpr.lc w :=
        opStep_lc hw (hext'.evalCtxLc hP'.1.toEvalCtxLc)
      -- (vi) cofinite packaging (P3 kit) at kit-Ψ := Ψp
      obtain ⟨Lhe, hhe⟩ := opStep_frame_eta_cofinite_of_fresh hw
        hy₀Ψp hy₀b₂₀ hy₀τv₀ hy₀e hy₀b₂₁ hlcτv₀ hlcw
      have hevout' : ValTy.EvalT (EvalCtx.extend Ψp y₀ b₂₀ (.var y₀ τv₀))
          (Ty.openVar y₀ (Basis.tof b₂₁)) τvout := by
        rw [htof₂₁]; exact hevoutp
      obtain ⟨Lh₁, hh₁⟩ := evalT_cofinite_of_fresh hevout'
        hy₀Ψp hy₀b₂₀ hy₀τv₀ hy₀τ hlcτv₀ hlcτvout
      -- (vii) fire frame_eta
      have h₀' : ValTy.EvalT Ψp (Basis.tof b₂₀) τv₀ := by
        rw [htof₂₀]; exact evalT_wk_ext hext hevτ₀
      have he' : ∀ y, y ∉ Lhe ∪ Lh₁ →
          ValExpr.OpStep (EvalCtx.extend Ψp y b₂₀ (.var y τv₀))
            (.appN e (.var y)) (Basis.openVar y b₂₁)
            (ValExpr.openVar y τv₀ (ValExpr.closeRec 0 y₀ w)) :=
        fun y hy => hhe y (fun hm => hy (Finset.mem_union_left _ hm))
      have h₁' : ∀ y, y ∉ Lhe ∪ Lh₁ →
          ValTy.EvalT (EvalCtx.extend Ψp y b₂₀ (.var y τv₀))
            (Ty.openVar y (Basis.tof b₂₁))
            (ValTy.openVar y τv₀ (ValTy.closeRec 0 y₀ τvout)) :=
        fun y hy => hh₁ y (fun hm => hy (Finset.mem_union_right _ hm))
      exact ⟨_, .frame_eta h₀' (Lhe ∪ Lh₁) he' h₁'⟩

/-! ## The interface theorems. -/

theorem basis_transport : BasisTransport := by
  intro Γ Ψ e b₁ b₂ v₁ hP hcov hsw hv₁ ht₁ hv₂ ht₂ htof hstep
  exact transportN (Ty.size (Basis.tof b₁)) Γ Ψ Ψ e b₁ b₂ v₁
    hP hcov hsw (.refl Ψ) hv₁ ht₁ hv₂ ht₂ htof le_rfl hstep

/-- **Transport to the literal standard basis** (the P7a/P8 sugar):
    `b₂ := Basis.std (tof b₁)`, validity via `Basis.std_valid` on the
    `tof`-regularity `TValid`, hereditary well-formedness via
    `Basis.isTyBasis_std`. -/
theorem basis_transport_to_std {Γ : NLCtx} {Ψ : EvalCtx} {e : Term}
    {b : Basis} {v : ValExpr}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ) (hsw : StoredWF Ψ)
    (hb : Basis.BasisValid Γ b) (ht : Basis.IsTyBasis b)
    (hstep : ValExpr.OpStep Ψ e b v) :
    ∃ v', ValExpr.OpStep Ψ e (Basis.std (Basis.tof b)) v' := by
  obtain ⟨k, ⟨hTV⟩⟩ := hb.tof_tvalid
  exact basis_transport Γ Ψ e b (Basis.std (Basis.tof b)) v hP hcov hsw
    hb ht (Basis.std_valid _ hTV) (Basis.isTyBasis_std _)
    (Basis.tof_std _) hstep

end GLang.V2
