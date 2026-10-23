import GLang.Proofs.Value.Soundness.ValueProgress

/-! Ordered operational histories, separated from their operational consistency.
The existing `V2.CtxTele` API is preserved and characterized exactly below.
Scope permits the newly installed name, as in `EvalEntryValid` (self placeholders).
No successful semantic evaluation or denotational agreement is assumed here. -/

namespace GLang.V2

/-- Ordered declarations; representation extensions introduce no source binding. -/
inductive History where
  | empty
  | lin (prior : History) (x : VName) (b : Basis) (v : ValExpr)
  | nlin (prior : History) (x : VName) (b : Basis) (v : ValExpr)
  | rep (prior : History) (x : VName) (b : Basis) (v : ValExpr)

namespace History

def linContext : History → LCtx
  | .empty => ∅
  | .lin h x b _ => Finmap.insert x (Basis.sof b) h.linContext
  | .nlin h .. | .rep h .. => h.linContext

def nlinContext : History → NLCtx
  | .empty => ∅
  | .nlin h x b _ => Finmap.insert x (Basis.tof b) h.nlinContext
  | .lin h .. | .rep h .. => h.nlinContext

noncomputable def evalContext : History → EvalCtx
  | .empty => ∅
  | .lin h x b v | .nlin h x b v | .rep h x b v =>
      EvalCtx.extend h.evalContext x b v

/-- Pure prefix scope and closure of a stored value. -/
structure EntryScoped (h : History) (x : VName) (b : Basis) (v : ValExpr) : Prop where
  valueScoped : ValExpr.fv v ⊆ (EvalCtx.extend h.evalContext x b v).keyNames
  locallyClosed : ValExpr.lc v

inductive WellFormed : History → Prop
  | empty : WellFormed .empty
  | lin : WellFormed h → SourceEntryValid h.linContext h.nlinContext x →
      EntryScoped h x b v → WellFormed (.lin h x b v)
  | nlin : WellFormed h → SourceEntryValid h.linContext h.nlinContext x →
      EntryScoped h x b v → WellFormed (.nlin h x b v)
  | rep : WellFormed h → (x ∈ h.linContext ∨ x ∈ h.nlinContext) →
      (x, b) ∉ h.evalContext → EntryScoped h x b v → WellFormed (.rep h x b v)

/-- Entry conditions beyond pure history: a valid basis, realized value type,
and the dependent-function correlation with this literal frame. -/
structure EntryConsistent (h : History) (b : Basis) (v : ValExpr) : Prop where
  basisValid : Basis.BasisValid h.nlinContext b
  typeRealized : ValTy.EvalT h.evalContext (Basis.tof b) (ValExpr.inferType v)
  frameAnchored : EvalFrameAnchored h.evalContext b v

/-- Operational consistency of the ordered declarations, checked at every
prefix. This is distinct from semantic consistency used for adequacy. -/
inductive OperationallyConsistent : History → Prop
  | empty : OperationallyConsistent .empty
  | lin : OperationallyConsistent h → SourceEntryValid h.linContext h.nlinContext x →
      EntryScoped h x b v → EntryConsistent h b v →
      Basis.tof b = .space (Basis.sof b) → OperationallyConsistent (.lin h x b v)
  | nlin : OperationallyConsistent h → SourceEntryValid h.linContext h.nlinContext x →
      EntryScoped h x b v → EntryConsistent h b v → OperationallyConsistent (.nlin h x b v)
  | rep : OperationallyConsistent h → SourceEntryLinked h.linContext h.nlinContext x b →
      (x, b) ∉ h.evalContext → EntryScoped h x b v → EntryConsistent h b v →
      OperationallyConsistent (.rep h x b v)

def ConsistentWith (Δ : LCtx) (Γ : NLCtx) (h : History) : Prop :=
  h.linContext = Δ ∧ h.nlinContext = Γ ∧ h.OperationallyConsistent

theorem OperationallyConsistent.wellFormed (hc : OperationallyConsistent h) :
    WellFormed h := by
  induction hc with
  | empty => exact .empty
  | lin _ fresh hs _ _ ih => exact .lin ih fresh hs
  | nlin _ fresh hs _ ih => exact .nlin ih fresh hs
  | rep _ linked fresh hs _ ih => exact .rep ih linked.mem_source fresh hs

private def entryCreation (hs : EntryScoped h x b v) (hc : EntryConsistent h b v) :
    EvalEntryCreation h.evalContext x b v :=
  ⟨⟨hc.typeRealized, hs.valueScoped, hs.locallyClosed⟩, hc.frameAnchored⟩

theorem OperationallyConsistent.ctxTele (hc : OperationallyConsistent h) :
    CtxTele h.linContext h.nlinContext h.evalContext := by
  induction hc with
  | empty => exact .empty
  | lin _ fresh hs entry htof ih =>
      exact .extend_lin ih fresh (entryCreation hs entry) entry.basisValid htof
  | nlin _ fresh hs entry ih =>
      exact .extend_nlin ih fresh (entryCreation hs entry) entry.basisValid
  | rep _ linked fresh hs entry ih =>
      exact .extend_rep ih linked fresh (entryCreation hs entry) entry.basisValid

end History

theorem CtxTele.exists_history (hc : CtxTele Δ Γ Ψ) :
    ∃ h : History, h.linContext = Δ ∧ h.nlinContext = Γ ∧
      h.evalContext = Ψ ∧ h.OperationallyConsistent := by
  induction hc with
  | empty => exact ⟨.empty, rfl, rfl, rfl, .empty⟩
  | @extend_nlin Δ Γ Ψ x b v _ fresh entry valid ih =>
      obtain ⟨h, rfl, rfl, rfl, hh⟩ := ih
      exact ⟨.nlin h x b v, rfl, rfl, rfl,
        .nlin hh fresh ⟨entry.valid.valueScoped, entry.valid.locallyClosed⟩
          ⟨valid, entry.valid.typeRealized, entry.frameAnchored⟩⟩
  | @extend_lin Δ Γ Ψ x b v s _ fresh entry valid htof ih =>
      obtain ⟨h, rfl, rfl, rfl, hh⟩ := ih
      have hs := Basis.sof_eq_of_tof_eq_space htof
      refine ⟨.lin h x b v, ?_, rfl, rfl, ?_⟩
      · simp only [History.linContext, hs]
      · exact .lin hh fresh ⟨entry.valid.valueScoped, entry.valid.locallyClosed⟩
          ⟨valid, entry.valid.typeRealized, entry.frameAnchored⟩ (by simpa only [hs] using htof)
  | @extend_rep Δ Γ Ψ x b v _ linked fresh entry valid ih =>
      obtain ⟨h, rfl, rfl, rfl, hh⟩ := ih
      exact ⟨.rep h x b v, rfl, rfl, rfl,
        .rep hh linked fresh ⟨entry.valid.valueScoped, entry.valid.locallyClosed⟩
          ⟨valid, entry.valid.typeRealized, entry.frameAnchored⟩⟩

theorem ctxTele_iff_exists_consistent_history :
    CtxTele Δ Γ Ψ ↔ ∃ h : History, History.ConsistentWith Δ Γ h ∧ h.evalContext = Ψ := by
  constructor
  · intro hc
    obtain ⟨h, hd, hg, hp, hh⟩ := hc.exists_history
    exact ⟨h, ⟨hd, hg, hh⟩, hp⟩
  · rintro ⟨h, ⟨rfl, rfl, hh⟩, rfl⟩
    exact hh.ctxTele

end GLang.V2
