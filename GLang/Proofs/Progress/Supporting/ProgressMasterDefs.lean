

import GLang.Proofs.Preservation.ValuePreservationV2
import GLang.Proofs.Progress.Supporting.ProgressStdBasis
import GLang.Proofs.Progress.Supporting.ProgressRename
import GLang.Proofs.Value.Soundness.ValueProgress

namespace GLang

-- `ValExpr.fv_inferType_subset` is proved in `ValueInferenceFv`.

/-- `Basis.stdSpace` commutes with `Space.subst` (Space-level companion). -/
theorem Basis.stdSpace_subst (x : Name) (e : Term) :
    ∀ s : Space,
      Basis.stdSpace (Space.subst x e s) = Basis.subst x e (Basis.stdSpace s)
  | .empty => rfl
  | .real => rfl
  | .dual s => by
      simp [Space.subst, Basis.stdSpace, Basis.subst, Basis.stdSpace_subst x e s]
  | .dsum s₀ s₁ => by
      simp [Space.subst, Basis.stdSpace, Basis.subst,
        Basis.stdSpace_subst x e s₀, Basis.stdSpace_subst x e s₁]
  | .tprod s₀ s₁ => by
      simp [Space.subst, Basis.stdSpace, Basis.subst,
        Basis.stdSpace_subst x e s₀, Basis.stdSpace_subst x e s₁]
  | .ker s₀ s₁ t => by
      simp [Space.subst, Basis.stdSpace, Basis.subst,
        Basis.stdSpace_subst x e s₀, Basis.stdSpace_subst x e s₁]
  | .coker s₀ s₁ t => by
      simp [Space.subst, Basis.stdSpace, Basis.subst,
        Basis.stdSpace_subst x e s₀, Basis.stdSpace_subst x e s₁]
  | .img s₀ s₁ t => by
      simp [Space.subst, Basis.stdSpace, Basis.subst,
        Basis.stdSpace_subst x e s₀, Basis.stdSpace_subst x e s₁]
  | .coimg s₀ s₁ t => by
      simp [Space.subst, Basis.stdSpace, Basis.subst,
        Basis.stdSpace_subst x e s₀, Basis.stdSpace_subst x e s₁]

/-- `Basis.std` commutes with `Ty.subst`: `std (Ty.subst x e τ) =
    Basis.subst x e (std τ)`. The subst companion of `Basis.std_openRec`. -/
theorem Basis.std_subst (x : Name) (e : Term) :
    ∀ τ : Ty, Basis.std (Ty.subst x e τ) = Basis.subst x e (Basis.std τ)
  | .space s => by
      simp [Ty.subst, Basis.std, Basis.stdSpace_subst x e s]
  | .piTy τ₀ τ₁ => by
      simp [Ty.subst, Basis.std, Basis.subst,
        Basis.std_subst x e τ₀, Basis.std_subst x e τ₁]

end GLang

namespace GLang.V2

/-! ## (a) `VarsCovered` — forward-only context covering. -/

/-- **Forward-only covering** of the typing contexts by `Ψ`: every variable
    bound in `Δ` (resp. `Γ`) has SOME `Ψ`-binding whose basis is of the bound
    space (resp. type). Deliberately an IMPLICATION, not an iff (cf.
    `TypingImplyEval`'s clause 1): forward-only is monotone under
    linear-context splitting (`Δ₀ ∪ Δ₁ → Δᵢ` keeps the hypothesis side
    smaller), which is what the `smul`/`app_linear`/`tprodE` arms need —
    preservation's archived lesson. -/
def VarsCovered (Δ : LCtx) (Γ : NLCtx) (Ψ : EvalCtx) : Prop :=
    (∀ x s, Δ.lookup x = some s →
      ∃ b, (x, b) ∈ Ψ ∧ Basis.tof b = .space s)
  ∧ (∀ x τ, Γ.lookup x = some τ →
      ∃ b, (x, b) ∈ Ψ ∧ Basis.tof b = τ)

/-! ## (b) `PCarrier` — the threadable carrier. -/

/-- The progress-master motive carrier: preservation's five-conjunct
    `EvalCtxValidPlus` (extension lemmas `evalCtxValidPlus_extend` /
    `_extend_delta` already exist) plus the `lem:prog` std-completeness
    hypothesis. Everything Ψ-only — it threads through binder extensions and
    is untouched by linear splitting / promotion. -/
def PCarrier (Ψ : EvalCtx) : Prop := EvalCtxValidPlus Ψ ∧ StdComplete Ψ

/-! ## (c) The four motives (∀Ψ-quantified). -/

/-- `SValid Γ s` motive: under any carried `Ψ` covering `Γ`, the space
    evaluates. (`SValid` lives at `Δ = ∅`.) -/
def pMotiveS (Γ : NLCtx) (s : Space) : Prop :=
  ∀ Ψ : EvalCtx, PCarrier Ψ → VarsCovered ∅ Γ Ψ →
    ∃ sv, ValSpace.EvalS Ψ s sv

def pMotiveT (Γ : NLCtx) (τ : Ty) : Prop :=
  ∀ Ψ : EvalCtx, PCarrier Ψ → VarsCovered ∅ Γ Ψ →
    (∃ τv, ValTy.EvalT Ψ τ τv)
    ∧ (∀ τ₀ τ₁, τ = .piTy τ₀ τ₁ → StdPiAnchored Ψ τ₀ τ₁)

/-- `SubType Γ s₀ s₁` motive: the embedding term `.embed s₀` (the ONLY
    consumer of `SubType` — `HasType.embed`) evaluates at the literal standard
    basis of its type `.space (.tprod (.dual s₀) s₁)`. Shape verified against
    `HasType.embed` + the `OpStep.embed_*` conclusions (see header). -/
def pMotiveSub (Γ : NLCtx) (s₀ s₁ : Space) : Prop :=
  ∀ Ψ : EvalCtx, PCarrier Ψ → VarsCovered ∅ Γ Ψ →
    ∃ v, ValExpr.OpStep Ψ (.embed s₀)
      (Basis.std (.space (.tprod (.dual s₀) s₁))) v

def pMotiveH (Δ : LCtx) (Γ : NLCtx) (e : Term) (τ : Ty) : Prop :=
  ∀ Ψ : EvalCtx, PCarrier Ψ → VarsCovered Δ Γ Ψ →
    (∃ v, ValExpr.OpStep Ψ e (Basis.std τ) v)
    ∧ (∀ τ₀ τ₁, τ = .piTy τ₀ τ₁ → StdPiAnchored Ψ τ₀ τ₁)

/-! ## (d)/(e) Carrier extension across binder extensions.

P5c: `StdPiAnchored.wk` (the R4 fresh-key weakening) moved to
`GLang/Proofs/Value/Soundness/ValueProgress.lean` next to the recursive definition
(`StdAnchored.wk` + the wrapper). -/

/-! ## (d′) The `StdAnchored` substitution/rename kit (P5c).

The recursive anchoring's two transport lemmas — the `evalT_substC` /
`evalT_cofinite_of_fresh` companions, with every Π binder pinned at the
literal `Basis.std` (re-aligned through the substitution by
`Basis.std_subst` above). `stdAnchored_substC` is what closes R2 (the
`app_nonlinear` Π-output tail: substitute the carried anchored codomain
decomposition along the dependent-application `ESubst`); `stdAnchored_cofinite_of_fresh`
is what closes R3 (the `piTy` producer arm: package its single-fresh-`y₀`
anchored codomain IH into `StdAnchored.piTy`'s cofinite premise). -/

/-- **`StdAnchored` substitution (context form)** — the `evalT_substC`
    companion. Mirrors its `piTy` arm: domain by recursion; the cofinite
    codomain at a fresh `y` via the extended `ESubst` (`ESubst.extend` at
    `bz := Basis.std τ₀`), commuting `subst` past `openVar` by
    `Ty.subst_openRec` (source) / `ValTy.subst_openRec` (value); the ONE
    extra move vs `evalT_substC` is `Basis.std_subst`, re-anchoring the
    substituted binder basis `Basis.subst x n₁ (Basis.std τ₀)` at the
    literal `Basis.std (Ty.subst x n₁ τ₀)` the constructor demands. -/
theorem stdAnchored_substC {x : VName} {b₀ : Basis} {τv₀ : ValTy} {n₁ : Term}
    {arg : ValExpr} {Ψ : EvalCtx} {τ : Ty} {τv : ValTy}
    (h : StdAnchored Ψ τ τv) :
    ∀ {Ψ' : EvalCtx}, ESubst x b₀ τv₀ n₁ arg Ψ Ψ' →
      StdAnchored Ψ' (Ty.subst x n₁ τ) (ValTy.subst x arg τv) := by
  induction h with
  | space h =>
      intro Ψ' hes
      exact .space (evalT_substC h hes)
  | @piTy Ψ₀ τ₀ τ₁ τva τvb h₀ L h₁ ih₀ ih₁ =>
      intro Ψ' hes
      simp only [Ty.subst, ValTy.subst]
      refine StdAnchored.piTy (ih₀ hes)
        (L ∪ {x} ∪ EvalCtx.avoid Ψ₀ ∪ EvalCtx.avoid Ψ') (fun y hy => ?_)
      simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
      obtain ⟨⟨⟨hyL, hyx⟩, hyΨ⟩, hyΨ'⟩ := hy
      have hes' := ESubst.extend (bz := Basis.std τ₀) (tv0z := τva) hes hyx
        (EvalCtx.avoid_spec hyΨ).1 ((EvalCtx.avoid_spec hyΨ').1 _)
      have hrec := ih₁ y hyL hes'
      have hsrc : Ty.subst x n₁ (Ty.openVar y τ₁)
          = Ty.openVar y (Ty.subst x n₁ τ₁) := by
        simp only [Ty.openVar, Ty.subst_openRec x n₁ hes.lcn τ₁ 0 (.var y),
          Term.subst, if_neg (Ne.symm hyx)]
      have hval : ValTy.subst x arg (ValTy.openVar y τva τvb)
          = ValTy.openVar y (ValTy.subst x arg τva) (ValTy.subst x arg τvb) := by
        simp only [ValTy.openVar,
          ValTy.subst_openRec x arg hes.lcarg τvb 0 (.var y τva),
          ValExpr.subst, if_neg hyx]
      rw [hsrc, hval, ← Basis.std_subst] at hrec
      exact hrec

/-- **`StdAnchored` cofinite packaging** — the `evalT_cofinite_of_fresh`
    companion (P3 kit shape): from an anchored realization of the
    `y₀`-opened codomain at the single fresh `y₀`, the cofinite premise of
    `StdAnchored.piTy`, with body `ValTy.closeRec 0 y₀ τv₁`. Routes through
    `ESubst.rename` + `stdAnchored_substC`; the source side re-opens by
    `Ty.subst_intro`, the value side by kit (5b)
    (`ValTy.openVar_closeRec_of_lc`). -/
theorem stdAnchored_cofinite_of_fresh {Ψ : EvalCtx} {b₀ : Basis}
    {τv₀ τv₁ : ValTy} {τ₁ : Ty} {y₀ : VName}
    (h : StdAnchored (EvalCtx.extend Ψ y₀ b₀ (.var y₀ τv₀))
      (Ty.openVar y₀ τ₁) τv₁)
    (hy₀Ψ : y₀ ∉ EvalCtx.avoidB Ψ) (hy₀b₀ : y₀ ∉ Basis.fv b₀)
    (hy₀τv₀ : y₀ ∉ ValTy.fv τv₀) (hy₀τ₁ : y₀ ∉ Ty.fv τ₁)
    (hlcτv₀ : ValTy.lc τv₀) (hlcτv₁ : ValTy.lc τv₁) :
    ∃ L : Finset VName, ∀ y, y ∉ L →
      StdAnchored (EvalCtx.extend Ψ y b₀ (.var y τv₀)) (Ty.openVar y τ₁)
        (ValTy.openVar y τv₀ (ValTy.closeRec 0 y₀ τv₁)) := by
  refine ⟨EvalCtx.avoidB Ψ, fun y hy => ?_⟩
  have hrec := stdAnchored_substC h (ESubst.rename hy₀Ψ hy hy₀b₀ hy₀τv₀ hlcτv₀)
  rw [show Ty.subst y₀ (.var y) (Ty.openVar y₀ τ₁) = Ty.openVar y τ₁ from
    (Ty.subst_intro y₀ (.var y) τ₁ hy₀τ₁ 0).symm] at hrec
  rw [ValTy.openVar_closeRec_of_lc y₀ y τv₀ hlcτv₁]
  exact hrec

/-- `PCarrier` survives a fresh binder extension `(y, Basis.std τ₀) ↦ .var y
    τv₀` (the `nllam`/`piTy`-arm extension — progress always extends at the
    LITERAL standard basis of the source annotation). -/
theorem PCarrier.extend_var {Ψ : EvalCtx} {y : VName} {τ₀ : Ty} {τv₀ : ValTy}
    (h : PCarrier Ψ) (hfresh : (y, Basis.std τ₀) ∉ Ψ)
    (hτv₀ : ValTy.fv τv₀ ⊆ Ψ.keyNames)
    (hev : ValTy.EvalT Ψ τ₀ τv₀)
    (hpi : ∀ τ₀' τ₁', τ₀ = .piTy τ₀' τ₁' → StdPiAnchored Ψ τ₀' τ₁') :
    PCarrier (EvalCtx.extend Ψ y (Basis.std τ₀) (.var y τv₀)) := by
  obtain ⟨hplus, hstd⟩ := h
  have hev' : ValTy.EvalT Ψ (Basis.tof (Basis.std τ₀)) τv₀ := by
    rw [Basis.tof_std]; exact hev
  refine ⟨evalCtxValidPlus_extend hplus hfresh hτv₀ hev', ?_, ?_⟩
  · intro x b hmem
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hmem'
    ·
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [Basis.tof_std]
      exact ⟨_,
        .var (by rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert])⟩
    ·
      obtain ⟨v, hv⟩ := hstd.1 x b hmem'
      exact ⟨v, opStep_wk hv hfresh⟩
  · intro x b hmem τ₀' τ₁' htof
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hmem'
    ·
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [Basis.tof_std] at htof
      exact (hpi τ₀' τ₁' htof).wk hfresh
    ·
      exact (hstd.2 x b hmem' τ₀' τ₁' htof).wk hfresh

theorem PCarrier.extend_delta {Ψ : EvalCtx} {y : VName} {s : Space}
    {i : Nat} {sv' : ValSpace}
    (h : PCarrier Ψ) (hfresh : (y, Basis.stdSpace s) ∉ Ψ)
    (hsvfv : ValSpace.fv sv' ⊆ Ψ.keyNames) (hsvlc : ValSpace.lc sv')
    (hev : ValSpace.EvalS Ψ s sv') :
    PCarrier (EvalCtx.extend Ψ y (Basis.stdSpace s) (.delta i sv')) := by
  obtain ⟨hplus, hstd⟩ := h
  have hev' : ValTy.EvalT Ψ (Basis.tof (Basis.stdSpace s)) (.space sv') := by
    rw [Basis.tof_stdSpace]; exact .space hev
  refine ⟨evalCtxValidPlus_extend_delta hplus hfresh hsvfv hsvlc hev', ?_, ?_⟩
  · intro x b hmem
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [Basis.tof_stdSpace,
        show Basis.std (.space s) = Basis.stdSpace s from rfl]
      exact ⟨_,
        .var (by rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert])⟩
    · obtain ⟨v, hv⟩ := hstd.1 x b hmem'
      exact ⟨v, opStep_wk hv hfresh⟩
  · intro x b hmem τ₀ τ₁ htof
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hmem'
    ·
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rw [Basis.tof_stdSpace] at htof
      exact nomatch htof
    · exact (hstd.2 x b hmem' τ₀ τ₁ htof).wk hfresh

/-! ## (f) Covering extension across binder extensions. -/

/-- Covering extends across a non-linear binder: `Γ` grows by `(y, τ₀)`, `Ψ`
    by `(y, Basis.std τ₀) ↦ v` (any stored value — covering only reads keys). -/
theorem VarsCovered.extend_var {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {y : VName} {τ₀ : Ty} {v : ValExpr}
    (h : VarsCovered Δ Γ Ψ) :
    VarsCovered Δ (Finmap.insert y τ₀ Γ)
      (EvalCtx.extend Ψ y (Basis.std τ₀) v) := by
  constructor
  · intro x s hx
    obtain ⟨b, hb, htof⟩ := h.1 x s hx
    exact ⟨b, by
      simp only [EvalCtx.extend]
      exact Finmap.mem_insert.mpr (Or.inr hb), htof⟩
  · intro x τ hx
    by_cases hxy : x = y
    · subst hxy
      simp only [Finmap.lookup_insert, Option.some.injEq] at hx
      subst hx
      exact ⟨Basis.std τ₀, by
        simp only [EvalCtx.extend]
        exact Finmap.mem_insert.mpr (Or.inl rfl), Basis.tof_std τ₀⟩
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      obtain ⟨b, hb, htof⟩ := h.2 x τ hx
      exact ⟨b, by
        simp only [EvalCtx.extend]
        exact Finmap.mem_insert.mpr (Or.inr hb), htof⟩

/-- Covering extends across a LINEAR binder (the `llam_*` rules): `Δ` grows by
    `(y, s)`, `Ψ` by `(y, Basis.stdSpace s) ↦ v`. -/
theorem VarsCovered.extend_var_lin {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {y : VName} {s : Space} {v : ValExpr}
    (h : VarsCovered Δ Γ Ψ) :
    VarsCovered (Finmap.insert y s Δ) Γ
      (EvalCtx.extend Ψ y (Basis.stdSpace s) v) := by
  constructor
  · intro x s' hx
    by_cases hxy : x = y
    · subst hxy
      simp only [Finmap.lookup_insert, Option.some.injEq] at hx
      subst hx
      exact ⟨Basis.stdSpace s, by
        simp only [EvalCtx.extend]
        exact Finmap.mem_insert.mpr (Or.inl rfl), Basis.tof_stdSpace s⟩
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      obtain ⟨b, hb, htof⟩ := h.1 x s' hx
      exact ⟨b, by
        simp only [EvalCtx.extend]
        exact Finmap.mem_insert.mpr (Or.inr hb), htof⟩
  · intro x τ hx
    obtain ⟨b, hb, htof⟩ := h.2 x τ hx
    exact ⟨b, by
      simp only [EvalCtx.extend]
      exact Finmap.mem_insert.mpr (Or.inr hb), htof⟩

/-! ## (g) Splitting / promotion monotonicity. -/

/-- Linear-split monotonicity (the payoff of forward-only covering): a
    covering of `Δ₀ ∪ Δ₁` covers each fragment. The `Δ₀` half is union-lookup
    priority; the `Δ₁` half needs the split's `Disjoint` premise (carried by
    every splitting typing rule) to route the lookup past `Δ₀`. -/
theorem VarsCovered.mono_lin {Δ₀ Δ₁ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    (hdisj : Finmap.Disjoint Δ₀ Δ₁)
    (h : VarsCovered (Δ₀ ∪ Δ₁) Γ Ψ) :
    VarsCovered Δ₀ Γ Ψ ∧ VarsCovered Δ₁ Γ Ψ := by
  refine ⟨⟨fun x s hx => ?_, h.2⟩, ⟨fun x s hx => ?_, h.2⟩⟩
  · refine h.1 x s ?_
    rw [Finmap.lookup_union_left (Finmap.mem_iff.mpr ⟨s, hx⟩)]
    exact hx
  · refine h.1 x s ?_
    rw [Finmap.lookup_union_right
      (fun hmem => hdisj x hmem (Finmap.mem_iff.mpr ⟨s, hx⟩))]
    exact hx

/-- The `HasType.promote` re-bucketing: a covering of the rule's CONCLUSION
    contexts `(Δ, lin.toNL ∪ ε')` covers its PREMISE contexts `(lin ∪ Δ, ε')`.
    The `lin` entries move from clause B (at `.space s`, via `LCtx.toNL`) to
    clause A (at `s`); the `ε'` entries stay in clause B (routed past
    `lin.toNL` by the rule's own `Disjoint lin.toNL ε'` premise). -/
theorem VarsCovered.promote {lin Δ : LCtx} {ε' : NLCtx} {Ψ : EvalCtx}
    (hdisj : Finmap.Disjoint lin.toNL ε')
    (h : VarsCovered Δ (lin.toNL ∪ ε') Ψ) :
    VarsCovered (lin ∪ Δ) ε' Ψ := by
  constructor
  · intro x s hx
    rcases Finmap.mem_lookup_union.mp (Option.mem_def.mpr hx) with hx' | ⟨hnx, hx'⟩
    · -- `x ∈ lin`: clause B of `h` at `.space s` (via `toNL`).
      refine h.2 x (.space s) ?_
      rw [Finmap.lookup_union_left
        (by rw [LCtx.mem_toNL_iff]
            exact Finmap.mem_iff.mpr ⟨s, Option.mem_def.mp hx'⟩)]
      exact LCtx.toNL_lookup lin x s (Option.mem_def.mp hx')
    · exact h.1 x s (Option.mem_def.mp hx')
  · intro x τ hx
    refine h.2 x τ ?_
    rw [Finmap.lookup_union_right
      (fun hmem => hdisj x hmem (Finmap.mem_iff.mpr ⟨τ, hx⟩))]
    exact hx

/-! ## (h) Boundary derivations (to `ValueProgress`'s hypothesis set). -/

/-- Boundary derivation of the carrier, Ψ-ONLY (progress's statements carry no
    `ρ`-side judgments, unlike preservation's `evalCtxValidPlus_of`):
    clauses (1)(2) of `EvalCtxValidPlus` from `EvalCtxValid`, (3) from the
    value-fv clause via `ValExpr.fv_inferType_subset`, (4) `EvalCtxLc`,
    (5) `EvalCtxLamAnchored`. -/
theorem pCarrier_of {Ψ : EvalCtx}
    (hwf : EvalCtxValid Ψ) (hlc : EvalCtxLc Ψ) (hanch : EvalCtxLamAnchored Ψ)
    (hstd : StdComplete Ψ) : PCarrier Ψ := by
  refine ⟨?_, hstd⟩
  intro x b v hlk
  obtain ⟨_hbfv, hvfv, hevT⟩ := hwf x b v hlk
  exact ⟨hvfv, hevT, (ValExpr.fv_inferType_subset v).trans hvfv,
    hlc (x, b) v hlk,
    fun b₀ b₁ τv₀ τv₁ body hb hv => hanch x b₀ b₁ τv₀ τv₁ body (hb ▸ hv ▸ hlk)⟩

/-- `RhoValid` at the canonical scope `Ψ.keyNames`, from the carrier:
    `ValTyOk` via `evalT_valid` on the stored `EvalT` clause; both fv clauses
    are carrier clauses. -/
theorem EvalCtxValidPlus.rhoValid_keyNames {Ψ : EvalCtx}
    (h : EvalCtxValidPlus Ψ) : RhoValid Ψ Ψ.keyNames := by
  intro x b v _hx hlk
  obtain ⟨hvfv, hevT, hτfv, _, _⟩ := h x b v hlk
  exact ⟨⟨_, evalT_valid hevT⟩, hτfv, hvfv⟩

/-- `KeyScope` at the canonical scope (definitionally reflexive). -/
theorem keyScope_keyNames (Ψ : EvalCtx) : KeyScope Ψ Ψ.keyNames :=
  Finset.Subset.refl _

/-- Covering is monotone in `Ψ` (forward-only pays off again): inserting any
    binding preserves it. Used when an arm re-instantiates an IH at an
    extended `Ψ` WITHOUT a matching context extension (e.g. the `piTy` arm's
    type-side recursion under the binder). -/
theorem VarsCovered.wk_psi {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    {y : VName} {b : Basis} {v : ValExpr}
    (h : VarsCovered Δ Γ Ψ) :
    VarsCovered Δ Γ (EvalCtx.extend Ψ y b v) := by
  constructor
  · intro x s hx
    obtain ⟨b', hb', htof⟩ := h.1 x s hx
    exact ⟨b', by
      simp only [EvalCtx.extend]
      exact Finmap.mem_insert.mpr (Or.inr hb'), htof⟩
  · intro x τ hx
    obtain ⟨b', hb', htof⟩ := h.2 x τ hx
    exact ⟨b', by
      simp only [EvalCtx.extend]
      exact Finmap.mem_insert.mpr (Or.inr hb'), htof⟩

theorem varsCovered_of {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    (h : TypingImplyEval Δ Γ Ψ) : VarsCovered Δ Γ Ψ := by
  refine ⟨fun x s hx => ?_, fun x τ hx => ?_⟩
  · obtain ⟨b, hb⟩ := (h.1 x).mp (Or.inl (Finmap.mem_iff.mpr ⟨s, hx⟩))
    exact ⟨b, hb, h.2.1 x s b hx hb⟩
  · obtain ⟨b, hb⟩ := (h.1 x).mp (Or.inr (Finmap.mem_iff.mpr ⟨τ, hx⟩))
    exact ⟨b, hb, h.2.2.1 x τ b hx hb⟩

end GLang.V2
