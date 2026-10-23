

import GLang.Proofs.Preservation.ValuePreservationV2
import GLang.Proofs.Progress.Supporting.ProgressStdBasis
import GLang.Proofs.Progress.Supporting.ProgressRename

namespace GLang

end GLang

namespace GLang.V2

inductive StdAnchored : EvalCtx → Ty → ValTy → Prop
  /-- Space-typed leaf: any realization (no binder to anchor). -/
  | space {Ψ : EvalCtx} {s : Space} {τv : ValTy}
      (h : ValTy.EvalT Ψ (.space s) τv) :
      StdAnchored Ψ (.space s) τv
  /-- Π-type: the domain realizes std-anchored at `Ψ`, and the codomain
      realizes std-anchored cofinitely under a binder stored at the LITERAL
      `Basis.std τ₀`. -/
  | piTy {Ψ : EvalCtx} {τ₀ τ₁ : Ty} {τv₀ τv₁ : ValTy}
      (h₀ : StdAnchored Ψ τ₀ τv₀)
      (L : Finset VName)
      (h₁ : ∀ y ∉ L,
        StdAnchored (EvalCtx.extend Ψ y (Basis.std τ₀) (.var y τv₀))
          (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁)) :
      StdAnchored Ψ (.piTy τ₀ τ₁) (.piTy τv₀ τv₁)

def StdPiAnchored (Ψ : EvalCtx) (τ₀ τ₁ : Ty) : Prop :=
  ∃ τv, StdAnchored Ψ (.piTy τ₀ τ₁) τv

/-- Forget the anchoring: every hereditarily std-anchored realization IS an
    `EvalT` derivation, binding each Π binder at `b₀ := Basis.std τ₀`
    (`hb := Basis.tof_std`). -/
theorem StdAnchored.toEvalT {Ψ : EvalCtx} {τ : Ty} {τv : ValTy}
    (h : StdAnchored Ψ τ τv) : ValTy.EvalT Ψ τ τv := by
  induction h with
  | space h => exact h
  | piTy h₀ L h₁ ih₀ ih₁ => exact .piTy ih₀ (Basis.tof_std _) L ih₁

/-- Build an anchored realization from the strengthened-motive parts
    (the `pMotiveT` conjunction after `intro Ψ hP hcov`): space-typed `τ`
    wraps the plain witness; Π-typed `τ` takes the carried anchoring (R3's
    shape splitter — the bridge between the conjunction-shaped motive tail
    and the inductive). -/
theorem stdAnchored_of_parts {Ψ : EvalCtx} {τ : Ty}
    (h : (∃ τv, ValTy.EvalT Ψ τ τv)
      ∧ (∀ τ₀ τ₁, τ = .piTy τ₀ τ₁ → StdPiAnchored Ψ τ₀ τ₁)) :
    ∃ τv, StdAnchored Ψ τ τv := by
  cases τ with
  | space s => obtain ⟨τv, hev⟩ := h.1; exact ⟨τv, .space hev⟩
  | piTy τ₀ τ₁ => exact h.2 τ₀ τ₁ rfl

/-- **(R1) Domain decomposition**: a Π-typed binder DOMAIN of an anchored
    Π-realization is itself std-anchored — what `PCarrier.extend_var`'s
    `hpi` consumers (`nllam`, `piTy` at higher-order domains) need. -/
theorem StdPiAnchored.dom_pi {Ψ : EvalCtx} {τ₀ τ₁ a b : Ty}
    (h : StdPiAnchored Ψ τ₀ τ₁) (heq : τ₀ = .piTy a b) :
    StdPiAnchored Ψ a b := by
  obtain ⟨τv, hA⟩ := h
  cases hA with
  | piTy h₀ L h₁ => exact ⟨_, heq ▸ h₀⟩

/-- **(R2) Full inversion**: the components of an anchored Π-realization,
    each still `StdAnchored` (the codomain family AT THE EXTENDED `Ψ` — so a
    Π-headed opened codomain decomposes anchored there, and
    `stdAnchored_substC` transports it). -/
theorem StdPiAnchored.inv {Ψ : EvalCtx} {τ₀ τ₁ : Ty}
    (h : StdPiAnchored Ψ τ₀ τ₁) :
    ∃ τv₀ τv₁, StdAnchored Ψ τ₀ τv₀ ∧ ∃ L : Finset VName, ∀ y ∉ L,
      StdAnchored (EvalCtx.extend Ψ y (Basis.std τ₀) (.var y τv₀))
        (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁) := by
  obtain ⟨τv, hA⟩ := h
  cases hA with
  | piTy h₀ L h₁ => exact ⟨_, _, h₀, L, h₁⟩

/-- The P5b one-level (flat) form, recovered by forgetting the recursive
    anchoring — verbatim the pre-P5c `StdPiAnchored` definition body (what
    the `app_nonlinear` witness wiring consumes). -/
theorem StdPiAnchored.toFlat {Ψ : EvalCtx} {τ₀ τ₁ : Ty}
    (h : StdPiAnchored Ψ τ₀ τ₁) :
    ∃ τv₀ τv₁, ValTy.EvalT Ψ τ₀ τv₀ ∧ ∃ L : Finset VName, ∀ y ∉ L,
      ValTy.EvalT (EvalCtx.extend Ψ y (Basis.std τ₀) (.var y τv₀))
        (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁) := by
  obtain ⟨τv₀, τv₁, h₀, L, h₁⟩ := h.inv
  exact ⟨τv₀, τv₁, h₀.toEvalT, L, fun y hy => (h₁ y hy).toEvalT⟩

theorem StdAnchored.wk {Ψ : EvalCtx} {τ : Ty} {τv : ValTy}
    (h : StdAnchored Ψ τ τv) :
    ∀ {y : VName} {b : Basis} {v : ValExpr}, (y, b) ∉ Ψ →
      StdAnchored (EvalCtx.extend Ψ y b v) τ τv := by
  induction h with
  | space h =>
      intro y b v hfresh
      exact .space (evalT_wk h hfresh)
  | @piTy Ψ τ₀ τ₁ τv₀ τv₁ h₀ L h₁ ih₀ ih₁ =>
      intro y b v hfresh
      refine .piTy (ih₀ hfresh) (insert y L) (fun y' hy' => ?_)
      rw [Finset.mem_insert, not_or] at hy'
      obtain ⟨hy'y, hy'L⟩ := hy'
      have hne : (y, b) ≠ (y', Basis.std τ₀) :=
        fun h => hy'y (congrArg Prod.fst h).symm
      have hfresh' :
          (y, b) ∉ EvalCtx.extend Ψ y' (Basis.std τ₀) (.var y' τv₀) := by
        rw [EvalCtx.extend]
        exact fun h => (Finmap.mem_insert.mp h).elim hne hfresh
      exact evalctx_extend_comm hne ▸ ih₁ y' hy'L hfresh'

/-- `StdPiAnchored` weakens across a fresh-key extension (any stored value)
    — R4 at the wrapper level (what `PCarrier.extend_var`/`.extend_delta`
    consume). -/
theorem StdPiAnchored.wk {Ψ : EvalCtx} {τ₀ τ₁ : Ty} {y : VName} {b : Basis}
    {v : ValExpr}
    (h : StdPiAnchored Ψ τ₀ τ₁) (hfresh : (y, b) ∉ Ψ) :
    StdPiAnchored (EvalCtx.extend Ψ y b v) τ₀ τ₁ := by
  obtain ⟨τv, hA⟩ := h
  exact ⟨τv, hA.wk hfresh⟩

def StdComplete (Ψ : EvalCtx) : Prop :=
  (∀ x b, (x, b) ∈ Ψ →
    ∃ v, ValExpr.OpStep Ψ (.var x) (Basis.std (Basis.tof b)) v)
  ∧ (∀ x b, (x, b) ∈ Ψ → ∀ τ₀ τ₁, Basis.tof b = .piTy τ₀ τ₁ →
      StdPiAnchored Ψ τ₀ τ₁)

structure SourceEntryValid (Δ : LCtx) (Γ : NLCtx) (x : VName) : Prop where
  freshLinear : x ∉ Δ
  freshNonlinear : x ∉ Γ

/-- A representation-only evaluator entry belongs to an existing source
binding and its key basis has exactly that binding's type.  This is the
one-entry form of the source-to-evaluator link; it deliberately says nothing
about other `(x, b')` representations. -/
def SourceEntryLinked (Δ : LCtx) (Γ : NLCtx) (x : VName) (b : Basis) : Prop :=
  (∃ s, Δ.lookup x = some s ∧ Basis.tof b = .space s) ∨
    Γ.lookup x = some (Basis.tof b)

theorem SourceEntryLinked.mem_source
    (h : SourceEntryLinked Δ Γ x b) : x ∈ Δ ∨ x ∈ Γ := by
  rcases h with ⟨s, hx, _htof⟩ | hx
  · exact Or.inl (Finmap.mem_of_lookup_eq_some hx)
  · exact Or.inr (Finmap.mem_of_lookup_eq_some hx)

/-- A function value stored under a frame is realized using that frame's
literal domain basis.  Plain `EvalT` is intentionally weaker: its Pi rule may
choose any basis having the right source type.  This small correlation is the
only extra entry-local fact needed by the higher-order operational rules. -/
def EvalFrameAnchored (Ψ : EvalCtx) (b : Basis) (v : ValExpr) : Prop :=
  ∀ b₀ b₁ τv₀ τv₁ body, b = .frame b₀ b₁ → v = .vlam τv₀ τv₁ body →
    ∃ L : Finset VName, ∀ y, y ∉ L →
      ValTy.EvalT (EvalCtx.extend Ψ y b₀ (.var y τv₀))
        (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁)

/-- Local validity of one evaluator entry at its creation prefix.  The value
may mention the newly installed name (the explicit self-placeholder case),
but it cannot mention a genuinely future entry. -/
structure EvalEntryValid (Ψ : EvalCtx) (x : VName) (b : Basis)
    (v : ValExpr) : Prop where
  typeRealized : ValTy.EvalT Ψ (Basis.tof b) (ValExpr.inferType v)
  valueScoped : ValExpr.fv v ⊆ (EvalCtx.extend Ψ x b v).keyNames
  locallyClosed : ValExpr.lc v

/-- The operational certificate for installing one evaluator entry. -/
structure EvalEntryCreation (Ψ : EvalCtx) (x : VName) (b : Basis)
    (v : ValExpr) : Prop where
  valid : EvalEntryValid Ψ x b v
  frameAnchored : EvalFrameAnchored Ψ b v

/-- A space-typed key cannot be a frame, so its frame-correlation clause is
vacuous. -/
def EvalEntryCreation.ofSpace
    (entry : EvalEntryValid Ψ x b v) (htof : Basis.tof b = .space s) :
    EvalEntryCreation Ψ x b v := by
  refine ⟨entry, ?_⟩
  intro b₀ b₁ τv₀ τv₁ body hbFrame _hv
  subst b
  exact nomatch htof

inductive CtxTele : LCtx → NLCtx → EvalCtx → Prop
  | empty : CtxTele ∅ ∅ ∅
  | extend_nlin {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {x : VName} {b : Basis}
      {v : ValExpr} :
      CtxTele Δ Γ Ψ →
      SourceEntryValid Δ Γ x →
      EvalEntryCreation Ψ x b v →
      Basis.BasisValid Γ b →
      CtxTele Δ (Finmap.insert x (Basis.tof b) Γ) (EvalCtx.extend Ψ x b v)
  | extend_lin {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {x : VName} {b : Basis}
      {v : ValExpr} {s : Space} :
      CtxTele Δ Γ Ψ →
      SourceEntryValid Δ Γ x →
      EvalEntryCreation Ψ x b v →
      Basis.BasisValid Γ b →
      Basis.tof b = .space s →
      CtxTele (Finmap.insert x s Δ) Γ (EvalCtx.extend Ψ x b v)
  | extend_rep {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx} {x : VName} {b : Basis}
      {v : ValExpr} :
      CtxTele Δ Γ Ψ →
      SourceEntryLinked Δ Γ x b →
      (x, b) ∉ Ψ →
      EvalEntryCreation Ψ x b v →
      Basis.BasisValid Γ b →
      CtxTele Δ Γ (EvalCtx.extend Ψ x b v)

end GLang.V2
