

import GLang.Proofs.Progress.Supporting.ProgressTransportSpec
import GLang.Proofs.Progress.Supporting.ProgressCob
import GLang.Proofs.Basis.BasisFvClosure

set_option maxHeartbeats 1000000

namespace GLang

/-- Constructor split for a hereditary type basis: it is a `.frame` or a
    hereditary SPACE basis (`IsTyBasis` delegates to `IsSpaceBasis` on every
    non-frame head). -/
theorem Basis.frame_or_isSpace {b : Basis} (hty : Basis.IsTyBasis b) :
    (∃ b₀ b₁, b = .frame b₀ b₁) ∨ Basis.IsSpaceBasis b := by
  cases b with
  | frame b₀ b₁ => exact Or.inl ⟨b₀, b₁, rfl⟩
  | empty => exact Or.inr hty
  | one => exact Or.inr hty
  | dual b => exact Or.inr hty
  | dsum b₀ b₁ => exact Or.inr hty
  | tprod b₀ b₁ => exact Or.inr hty
  | proj s b₀ b₁ => exact Or.inr hty
  | image b => exact Or.inr hty
  | terms s es b => exact Or.inr hty

end GLang

namespace GLang.V2

private theorem anchClause_wk {Ψ : EvalCtx} {b₀ : Basis} {τv₀ τv₁ : ValTy}
    {τc : Ty} {x' : VName} {bᵢ : Basis} {v' : ValExpr}
    (h : ∃ L : Finset VName, ∀ y, y ∉ L →
      ValTy.EvalT (EvalCtx.extend Ψ y b₀ (.var y τv₀))
        (Ty.openVar y τc) (ValTy.openVar y τv₀ τv₁))
    (hfresh : (x', bᵢ) ∉ Ψ) :
    ∃ L : Finset VName, ∀ y, y ∉ L →
      ValTy.EvalT (EvalCtx.extend (EvalCtx.extend Ψ x' bᵢ v') y b₀ (.var y τv₀))
        (Ty.openVar y τc) (ValTy.openVar y τv₀ τv₁) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨insert x' L, fun y hy => ?_⟩
  rw [Finset.mem_insert, not_or] at hy
  obtain ⟨hyx, hyL⟩ := hy
  have hne : (x', bᵢ) ≠ (y, b₀) := fun h => hyx (congrArg Prod.fst h).symm
  have hfresh' : (x', bᵢ) ∉ EvalCtx.extend Ψ y b₀ (.var y τv₀) := by
    rw [EvalCtx.extend]
    exact fun h => (Finmap.mem_insert.mp h).elim hne hfresh
  exact evalctx_extend_comm hne ▸ evalT_wk (hL y hyL) hfresh'

theorem evalCtxValidPlus_extend_gen {Ψ : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr}
    (hΨ : EvalCtxValidPlus Ψ) (hfresh : (x, b) ∉ Ψ)
    (hvfv : ValExpr.fv v ⊆ (EvalCtx.extend Ψ x b v).keyNames)
    (hev : ValTy.EvalT Ψ (Basis.tof b) (ValExpr.inferType v))
    (hlc : ValExpr.lc v)
    (hanch : ∀ b₀ b₁ τv₀ τv₁ body, b = .frame b₀ b₁ → v = .vlam τv₀ τv₁ body →
      ∃ L : Finset VName, ∀ y, y ∉ L →
        ValTy.EvalT (EvalCtx.extend Ψ y b₀ (.var y τv₀))
          (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁)) :
    EvalCtxValidPlus (EvalCtx.extend Ψ x b v) := by
  have hkn := keyNames_extend Ψ x b v
  intro x' b' v' hlk
  simp only [EvalCtx.extend, EvalCtx.lookup] at hlk
  by_cases hk : (x', b') = (x, b)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
    rw [Finmap.lookup_insert, Option.some.injEq] at hlk
    subst hlk
    have hvfv' : ValExpr.fv v ⊆ insert x' Ψ.keyNames := by
      simpa only [hkn] using hvfv
    rw [hkn]
    exact ⟨hvfv', evalT_wk hev hfresh,
      (ValExpr.fv_inferType_subset _).trans hvfv',
      hlc,
      fun b₀ b₁ τv₀ τv₁ body hb hv =>
        anchClause_wk (hanch b₀ b₁ τv₀ τv₁ body hb hv) hfresh⟩
  · rw [Finmap.lookup_insert_of_ne _ hk] at hlk
    obtain ⟨h1, h2, h3, h4, h5⟩ := hΨ x' b' v' hlk
    rw [hkn]
    exact ⟨h1.trans (Finset.subset_insert _ _), evalT_wk h2 hfresh,
      h3.trans (Finset.subset_insert _ _), h4,
      fun b₀ b₁ τv₀ τv₁ body hb hv =>
        anchClause_wk (h5 b₀ b₁ τv₀ τv₁ body hb hv) hfresh⟩

/-- Every evaluator name belongs to one of the two source contexts.  First
representations establish this in lockstep; `extend_rep` preserves it through
its explicit source link.  Consequently source freshness still implies
evaluator freshness for a genuinely new source binder. -/
theorem CtxTele.evalName_mem_source :
    forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {z : VName},
      CtxTele Delta Gamma Psi ->
      (exists b, (z, b) ∈ Psi) -> z ∈ Delta \/ z ∈ Gamma := by
  intro Delta Gamma Psi z h
  induction h with
  | empty =>
      rintro ⟨b, hmem⟩
      exact absurd hmem Finmap.notMem_empty
  | @extend_nlin Delta Gamma Psi x b v htele hsource hcreation hb ih =>
      rintro ⟨b', hmem⟩
      simp only [EvalCtx.extend, Finmap.mem_insert] at hmem
      rcases hmem with hnew | hold
      · have hzx : z = x := (Prod.mk.inj hnew).1
        subst z
        exact Or.inr (Finmap.mem_insert.mpr (Or.inl rfl))
      · rcases ih ⟨b', hold⟩ with hDelta | hGamma
        · exact Or.inl hDelta
        · exact Or.inr (Finmap.mem_insert.mpr (Or.inr hGamma))
  | @extend_lin Delta Gamma Psi x b v s htele hsource hcreation hb htof ih =>
      rintro ⟨b', hmem⟩
      simp only [EvalCtx.extend, Finmap.mem_insert] at hmem
      rcases hmem with hnew | hold
      · have hzx : z = x := (Prod.mk.inj hnew).1
        subst z
        exact Or.inl (Finmap.mem_insert.mpr (Or.inl rfl))
      · rcases ih ⟨b', hold⟩ with hDelta | hGamma
        · exact Or.inl (Finmap.mem_insert.mpr (Or.inr hDelta))
        · exact Or.inr hGamma
  | @extend_rep Delta Gamma Psi x b v htele hlink hpair hcreation hb ih =>
      rintro ⟨b', hmem⟩
      simp only [EvalCtx.extend, Finmap.mem_insert] at hmem
      rcases hmem with hnew | hold
      · have hzx : z = x := (Prod.mk.inj hnew).1
        subst z
        exact hlink.mem_source
      · exact ih ⟨b', hold⟩

/-- A name fresh in both source contexts is automatically absent at every
    evaluator basis because every evaluator entry is linked to a source
    binding. -/
theorem CtxTele.freshEvalName
    (h : CtxTele Delta Gamma Psi) (hx : SourceEntryValid Delta Gamma x) :
    forall b, (x, b) ∉ Psi := by
  intro b hmem
  rcases h.evalName_mem_source ⟨b, hmem⟩ with hDelta | hGamma
  · exact hx.freshLinear hDelta
  · exact hx.freshNonlinear hGamma

/-- Lockstep creation ensures that every nonlinear source-context name has
already appeared in the evaluator.  This is the structural half of basis
non-recursion; it uses no evaluation or progress theorem. -/
theorem CtxTele.nlKeys_subset_keyNames :
    ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx},
      CtxTele Δ Γ Ψ → Γ.keys ⊆ Ψ.keyNames := by
  intro Δ Γ Ψ h
  induction h with
  | empty => simp
  | @extend_nlin Δ Γ Ψ x b v htele hsource hcreation hb ih =>
      intro z hz
      rw [Finmap.mem_keys, Finmap.mem_insert] at hz
      rw [keyNames_extend, Finset.mem_insert]
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · exact Or.inr (ih (Finmap.mem_keys.mpr hz))
  | @extend_lin Δ Γ Ψ x b v s htele hsource hcreation hb htof ih =>
      intro z hz
      rw [keyNames_extend, Finset.mem_insert]
      exact Or.inr (ih hz)
  | @extend_rep Δ Γ Ψ x b v htele hlink hpair hcreation hb ih =>
      intro z hz
      rw [keyNames_extend, Finset.mem_insert]
      exact Or.inr (ih hz)

theorem CtxTele.basisFvPrefix
    (h : CtxTele Δ Γ Ψ) (hb : Basis.BasisValid Γ b) :
    Basis.fv b ⊆ Ψ.keyNames :=
  hb.fv_subset_keys_for_progress.trans h.nlKeys_subset_keyNames

theorem CtxTele.evalCtxValid : ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx},
    CtxTele Δ Γ Ψ → EvalCtxValid Ψ := by
  intro Δ Γ Ψ h
  induction h with
  | empty =>
      intro x b v hlk
      rw [EvalCtx.lookup, Finmap.lookup_empty] at hlk
      cases hlk
  | @extend_nlin Δ Γ Ψ x b v htele hsource hcreation hb ih =>
      have hbfv := htele.basisFvPrefix hb
      have hfresh := htele.freshEvalName hsource
      intro x' b' v' hlk
      have hkn := keyNames_extend Ψ x b v
      simp only [EvalCtx.extend, EvalCtx.lookup] at hlk
      by_cases hk : (x', b') = (x, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
        rw [Finmap.lookup_insert, Option.some.injEq] at hlk
        subst hlk
        rw [hkn]
        exact ⟨hbfv.trans (Finset.subset_insert _ _),
          by simpa only [hkn] using hcreation.valid.valueScoped,
          evalT_wk hcreation.valid.typeRealized (hfresh b')⟩
      · rw [Finmap.lookup_insert_of_ne _ hk] at hlk
        obtain ⟨h1, h2, h3⟩ := ih x' b' v' hlk
        rw [hkn]
        exact ⟨h1.trans (Finset.subset_insert _ _),
          h2.trans (Finset.subset_insert _ _),
          evalT_wk h3 (hfresh b)⟩
  | @extend_lin Δ Γ Ψ x b v s htele hsource hcreation hb htof ih =>
      have hbfv := htele.basisFvPrefix hb
      have hfresh := htele.freshEvalName hsource
      intro x' b' v' hlk
      have hkn := keyNames_extend Ψ x b v
      simp only [EvalCtx.extend, EvalCtx.lookup] at hlk
      by_cases hk : (x', b') = (x, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
        rw [Finmap.lookup_insert, Option.some.injEq] at hlk
        subst hlk
        rw [hkn]
        exact ⟨hbfv.trans (Finset.subset_insert _ _),
          by simpa only [hkn] using hcreation.valid.valueScoped,
          evalT_wk hcreation.valid.typeRealized (hfresh b')⟩
      · rw [Finmap.lookup_insert_of_ne _ hk] at hlk
        obtain ⟨h1, h2, h3⟩ := ih x' b' v' hlk
        rw [hkn]
        exact ⟨h1.trans (Finset.subset_insert _ _),
          h2.trans (Finset.subset_insert _ _),
          evalT_wk h3 (hfresh b)⟩
  | @extend_rep Δ Γ Ψ x b v htele hlink hpair hcreation hb ih =>
      have hbfv := htele.basisFvPrefix hb
      intro x' b' v' hlk
      have hkn := keyNames_extend Ψ x b v
      simp only [EvalCtx.extend, EvalCtx.lookup] at hlk
      by_cases hk : (x', b') = (x, b)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
        rw [Finmap.lookup_insert, Option.some.injEq] at hlk
        subst hlk
        rw [hkn]
        exact ⟨hbfv.trans (Finset.subset_insert _ _),
          by simpa only [hkn] using hcreation.valid.valueScoped,
          evalT_wk hcreation.valid.typeRealized hpair⟩
      · rw [Finmap.lookup_insert_of_ne _ hk] at hlk
        obtain ⟨h1, h2, h3⟩ := ih x' b' v' hlk
        rw [hkn]
        exact ⟨h1.trans (Finset.subset_insert _ _),
          h2.trans (Finset.subset_insert _ _),
          evalT_wk h3 hpair⟩

/-- `⊢ (Δ,Γ), Ψ ⟹` the five-conjunct motive carrier (the prefix version of
    preservation's `EvalCtxValidPlus`): per-entry by
    `evalCtxValidPlus_extend_gen` on the telescope clauses (the `extend_lin`
    anchoring obligation is vacuous — a space-typed key is never a
    `.frame`). -/
theorem CtxTele.evalCtxValidPlus : ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx},
    CtxTele Δ Γ Ψ → EvalCtxValidPlus Ψ := by
  intro Δ Γ Ψ h
  induction h with
  | empty =>
      intro x b v hlk
      rw [EvalCtx.lookup, Finmap.lookup_empty] at hlk
      cases hlk
  | @extend_nlin Δ Γ Ψ x b v htele hsource hcreation hb ih =>
      exact evalCtxValidPlus_extend_gen ih (htele.freshEvalName hsource b)
        hcreation.valid.valueScoped hcreation.valid.typeRealized
        hcreation.valid.locallyClosed hcreation.frameAnchored
  | @extend_lin Δ Γ Ψ x b v s htele hsource hcreation hb htof ih =>
      exact evalCtxValidPlus_extend_gen ih (htele.freshEvalName hsource b)
        hcreation.valid.valueScoped hcreation.valid.typeRealized
        hcreation.valid.locallyClosed hcreation.frameAnchored
  | @extend_rep Δ Γ Ψ x b v htele hlink hpair hcreation hb ih =>
      exact evalCtxValidPlus_extend_gen ih hpair hcreation.valid.valueScoped
        hcreation.valid.typeRealized hcreation.valid.locallyClosed
        hcreation.frameAnchored

/-- `⊢ (Δ,Γ), Ψ ⟹ StoredWF Ψ`: hereditary basis shape is derived from
each entry's `BasisValid` proof and collected over the evaluator. -/
theorem CtxTele.storedWF : ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx},
    CtxTele Δ Γ Ψ → StoredWF Ψ := by
  intro Δ Γ Ψ h
  induction h with
  | empty => exact fun x b hmem => absurd hmem Finmap.notMem_empty
  | @extend_nlin Δ Γ Ψ x b v htele hsource hcreation hb ih =>
      intro x' b' hmem
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with heq | hmem'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact hb.isTyBasis
      · exact ih x' b' hmem'
  | @extend_lin Δ Γ Ψ x b v s htele hsource hcreation hb htof ih =>
      intro x' b' hmem
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with heq | hmem'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact hb.isTyBasis
      · exact ih x' b' hmem'
  | @extend_rep Δ Γ Ψ x b v htele hlink hpair hcreation hb ih =>
      intro x' b' hmem
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with heq | hmem'
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact hb.isTyBasis
      · exact ih x' b' hmem'

/-- `⊢ (Δ,Γ), Ψ ⟹ VarsCovered Δ Γ Ψ`: the lockstep growth means every
    context binding has its `Ψ` entry at the matching `tof` (`extend_nlin`
    stores `tof b` itself; `extend_lin` carries `tof b = .space s`). -/
theorem CtxTele.varsCovered : ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx},
    CtxTele Δ Γ Ψ → VarsCovered Δ Γ Ψ := by
  intro Δ Γ Ψ h
  induction h with
  | empty =>
      refine ⟨fun x s hx => ?_, fun x τ hx => ?_⟩ <;>
        (rw [Finmap.lookup_empty] at hx; cases hx)
  | @extend_nlin Δ Γ Ψ x b v htele hsource hcreation hb ih =>
      refine ⟨fun x' s' hx' => ?_, fun x' τ' hx' => ?_⟩
      · obtain ⟨b', hb', htof'⟩ := ih.1 x' s' hx'
        exact ⟨b', by
          simp only [EvalCtx.extend]
          exact Finmap.mem_insert.mpr (Or.inr hb'), htof'⟩
      · by_cases hxx : x' = x
        · subst hxx
          rw [Finmap.lookup_insert, Option.some.injEq] at hx'
          subst hx'
          exact ⟨b, by
            simp only [EvalCtx.extend]
            exact Finmap.mem_insert.mpr (Or.inl rfl), rfl⟩
        · rw [Finmap.lookup_insert_of_ne _ hxx] at hx'
          obtain ⟨b', hb', htof'⟩ := ih.2 x' τ' hx'
          exact ⟨b', by
            simp only [EvalCtx.extend]
            exact Finmap.mem_insert.mpr (Or.inr hb'), htof'⟩
  | @extend_lin Δ Γ Ψ x b v s htele hsource hcreation hb htof ih =>
      refine ⟨fun x' s' hx' => ?_, fun x' τ' hx' => ?_⟩
      · by_cases hxx : x' = x
        · subst hxx
          rw [Finmap.lookup_insert, Option.some.injEq] at hx'
          subst hx'
          exact ⟨b, by
            simp only [EvalCtx.extend]
            exact Finmap.mem_insert.mpr (Or.inl rfl), htof⟩
        · rw [Finmap.lookup_insert_of_ne _ hxx] at hx'
          obtain ⟨b', hb', htof'⟩ := ih.1 x' s' hx'
          exact ⟨b', by
            simp only [EvalCtx.extend]
            exact Finmap.mem_insert.mpr (Or.inr hb'), htof'⟩
      · obtain ⟨b', hb', htof'⟩ := ih.2 x' τ' hx'
        exact ⟨b', by
          simp only [EvalCtx.extend]
          exact Finmap.mem_insert.mpr (Or.inr hb'), htof'⟩
  | @extend_rep Δ Γ Ψ x b v htele hlink hpair hcreation hb ih =>
      refine ⟨fun x' s' hx' => ?_, fun x' τ' hx' => ?_⟩
      · obtain ⟨b', hb', htof'⟩ := ih.1 x' s' hx'
        exact ⟨b', by
          simp only [EvalCtx.extend]
          exact Finmap.mem_insert.mpr (Or.inr hb'), htof'⟩
      · obtain ⟨b', hb', htof'⟩ := ih.2 x' τ' hx'
        exact ⟨b', by
          simp only [EvalCtx.extend]
          exact Finmap.mem_insert.mpr (Or.inr hb'), htof'⟩

/-- `⊢ (Δ,Γ), Ψ ⟹ EvalCtxLc Ψ` (the carrier's lc projection). -/
theorem CtxTele.evalCtxLc {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    (h : CtxTele Δ Γ Ψ) : EvalCtxLc Ψ :=
  h.evalCtxValidPlus.toEvalCtxLc

/-- `EvalCtxValidPlus ⟹ EvalCtxLamAnchored` (clause-5 projection — the ⑥
    judgment is the per-binding anchoring read at `.frame`-keyed `.vlam`s). -/
theorem EvalCtxValidPlus.toLamAnchored {Ψ : EvalCtx}
    (h : EvalCtxValidPlus Ψ) : EvalCtxLamAnchored Ψ :=
  fun x b₀ b₁ τv₀ τv₁ body hlk =>
    (h x (.frame b₀ b₁) (.vlam τv₀ τv₁ body) hlk).2.2.2.2 b₀ b₁ τv₀ τv₁ body
      rfl rfl

/-- `⊢ (Δ,Γ), Ψ ⟹ EvalCtxLamAnchored Ψ`. -/
theorem CtxTele.lamAnchored {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}
    (h : CtxTele Δ Γ Ψ) : EvalCtxLamAnchored Ψ :=
  h.evalCtxValidPlus.toLamAnchored

/-! ## (b) The `StdComplete` lift. -/

def PiEntryTransport : Prop :=
  ∀ (Γ : NLCtx) (Ψ : EvalCtx) (x : VName) (b₀ b₁ : Basis) (v : ValExpr),
    PCarrier Ψ → VarsCovered ∅ Γ Ψ → StoredWF Ψ →
    Basis.BasisValid Γ (.frame b₀ b₁) → Basis.IsTyBasis (.frame b₀ b₁) →
    (x, .frame b₀ b₁) ∉ Ψ →
    Basis.fv (.frame b₀ b₁) ⊆ Ψ.keyNames →
    ValTy.EvalT Ψ (Basis.tof (.frame b₀ b₁)) (ValExpr.inferType v) →
    ValExpr.fv v ⊆ (EvalCtx.extend Ψ x (.frame b₀ b₁) v).keyNames →
    ValExpr.lc v →
    (∀ τv₀ τv₁ body, v = .vlam τv₀ τv₁ body →
      ∃ L : Finset VName, ∀ y, y ∉ L →
        ValTy.EvalT (EvalCtx.extend Ψ y b₀ (.var y τv₀))
          (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁)) →
    ∃ w, ValExpr.OpStep (EvalCtx.extend Ψ x (.frame b₀ b₁) v) (.var x)
      (Basis.std (Basis.tof (.frame b₀ b₁))) w

theorem stdComplete_extend {Γ : NLCtx} {Ψ : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ)
    (hbv : Basis.BasisValid Γ b) (hty : Basis.IsTyBasis b)
    (hfresh : (x, b) ∉ Ψ)
    (hev : ValTy.EvalT Ψ (Basis.tof b) (ValExpr.inferType v))
    (hpi : ∀ b₀ b₁, b = .frame b₀ b₁ →
      ∃ w, ValExpr.OpStep (EvalCtx.extend Ψ x b v) (.var x)
        (Basis.std (Basis.tof b)) w) :
    StdComplete (EvalCtx.extend Ψ x b v) := by
  constructor
  · -- clause 1: every entry evaluates at the std basis of its type.
    intro x' b' hmem
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rcases Basis.frame_or_isSpace hty with ⟨b₀, b₁, rfl⟩ | hsb
      · exact hpi b₀ b₁ rfl
      ·
        obtain ⟨env, hbb⟩ := progress_cob_master hP hcov hbv hsb
        have hbbS : Basis.EvalBB Ψ b' env (Basis.stdSpace (Basis.sof b')) :=
          evalBB_stdSpace_of_std_tof hsb.tof_eq hbb
        have hev' : ValTy.EvalT Ψ (.space (Basis.sof b'))
            (ValExpr.inferType v) := hsb.tof_eq ▸ hev
        obtain ⟨sv, hes, _⟩ := evalT_space_inv hev'
        have hvar : ValExpr.OpStep (EvalCtx.extend Ψ x' b' v) (.var x') b' v :=
          .var (by rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert])
        have hesS : ValSpace.EvalS (EvalCtx.extend Ψ x' b' v)
            (Basis.sof (Basis.stdSpace (Basis.sof b'))) sv := by
          rw [Basis.sof_stdSpace]
          exact evalS_wk hes hfresh
        rw [Basis.std_tof_eq_stdSpace hsb.tof_eq]
        exact ⟨_, .cob (Basis.htof_stdSpace _) hsb.tof_eq hvar
          (evalBB_wk hbbS hfresh) hesS⟩
    · obtain ⟨w, hw⟩ := hP.2.1 x' b' hmem'
      exact ⟨w, opStep_wk hw hfresh⟩
  · -- clause 2: Π-typed entries carry the std-anchored realization.
    intro x' b' hmem τ₀ τ₁ htof'
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hmem'
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      rcases Basis.frame_or_isSpace hty with ⟨b₀, b₁, rfl⟩ | hsb
      · simp only [Basis.tof] at htof'
        injection htof' with hτ₀ hτ₁
        subst hτ₀; subst hτ₁
        obtain ⟨_, _, k₀, k₁, ⟨htv⟩⟩ := hbv.frame_inv
        exact ((progress_master_std.2.1 htv Ψ hP hcov).2 _ _ rfl).wk hfresh
      · rw [hsb.tof_eq] at htof'
        exact nomatch htof'
    · exact (hP.2.2 x' b' hmem' τ₀ τ₁ htof').wk hfresh

theorem stdComplete_of_tele (hpiE : PiEntryTransport) :
    ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}, CtxTele Δ Γ Ψ → StdComplete Ψ := by
  intro Δ Γ Ψ h
  induction h with
  | empty =>
      exact ⟨fun x b hmem => absurd hmem Finmap.notMem_empty,
             fun x b hmem _ _ _ => absurd hmem Finmap.notMem_empty⟩
  | @extend_nlin Δ Γ Ψ x b v htele hsource hcreation hb ih =>
      have hty := hb.isTyBasis
      have hbfv := htele.basisFvPrefix hb
      have hfresh := htele.freshEvalName hsource b
      refine stdComplete_extend ⟨htele.evalCtxValidPlus, ih⟩
        htele.varsCovered.drop_lin hb hty hfresh
          hcreation.valid.typeRealized (fun b₀ b₁ hb => ?_)
      subst hb
      exact hpiE Γ Ψ x b₀ b₁ v ⟨htele.evalCtxValidPlus, ih⟩
        htele.varsCovered.drop_lin htele.storedWF hb hty
        hfresh hbfv hcreation.valid.typeRealized
        hcreation.valid.valueScoped hcreation.valid.locallyClosed
        (fun τv₀ τv₁ body hv =>
          hcreation.frameAnchored b₀ b₁ τv₀ τv₁ body rfl hv)
  | @extend_lin Δ Γ Ψ x b v s htele hsource hcreation hb htof ih =>
      have hty := hb.isTyBasis
      exact stdComplete_extend ⟨htele.evalCtxValidPlus, ih⟩
        htele.varsCovered.drop_lin hb hty (htele.freshEvalName hsource b)
          hcreation.valid.typeRealized
        (fun b₀ b₁ hbFrame => by subst b; exact nomatch htof)
  | @extend_rep Δ Γ Ψ x b v htele hlink hpair hcreation hb ih =>
      have hty := hb.isTyBasis
      have hbfv := htele.basisFvPrefix hb
      refine stdComplete_extend ⟨htele.evalCtxValidPlus, ih⟩
        htele.varsCovered.drop_lin hb hty hpair hcreation.valid.typeRealized
          (fun b₀ b₁ hb => ?_)
      subst hb
      exact hpiE Γ Ψ x b₀ b₁ v ⟨htele.evalCtxValidPlus, ih⟩
        htele.varsCovered.drop_lin htele.storedWF hb hty hpair hbfv
        hcreation.valid.typeRealized hcreation.valid.valueScoped
        hcreation.valid.locallyClosed
        (fun τv₀ τv₁ body hv =>
          hcreation.frameAnchored b₀ b₁ τv₀ τv₁ body rfl hv)

/-- The lift, UNCONDITIONAL on frame-free environments: a telescope none of
    whose stored bases is a `.frame` needs no Π-entry completion (the
    expected boundary shape for `thm:prog`'s first consumers — space-typed
    initial environments). -/
theorem stdComplete_of_tele_frameFree :
    ∀ {Δ : LCtx} {Γ : NLCtx} {Ψ : EvalCtx}, CtxTele Δ Γ Ψ →
      (∀ x b₀ b₁, (x, Basis.frame b₀ b₁) ∉ Ψ) → StdComplete Ψ := by
  intro Δ Γ Ψ h
  induction h with
  | empty =>
      exact fun _ =>
        ⟨fun x b hmem => absurd hmem Finmap.notMem_empty,
         fun x b hmem _ _ _ => absurd hmem Finmap.notMem_empty⟩
  | @extend_nlin Δ Γ Ψ x b v htele hsource hcreation hb ih =>
      have hty := hb.isTyBasis
      intro hnf
      have ihp : StdComplete Ψ := ih (fun x' c₀ c₁ hmem =>
        hnf x' c₀ c₁ (by
          simp only [EvalCtx.extend]
          exact Finmap.mem_insert.mpr (Or.inr hmem)))
      refine stdComplete_extend ⟨htele.evalCtxValidPlus, ihp⟩
        htele.varsCovered.drop_lin hb hty (htele.freshEvalName hsource b)
          hcreation.valid.typeRealized (fun b₀ b₁ hb => ?_)
      subst hb
      exact absurd (by
        simp only [EvalCtx.extend]
        exact Finmap.mem_insert.mpr (Or.inl rfl)) (hnf x b₀ b₁)
  | @extend_lin Δ Γ Ψ x b v s htele hsource hcreation hb htof ih =>
      have hty := hb.isTyBasis
      intro hnf
      have ihp : StdComplete Ψ := ih (fun x' c₀ c₁ hmem =>
        hnf x' c₀ c₁ (by
          simp only [EvalCtx.extend]
          exact Finmap.mem_insert.mpr (Or.inr hmem)))
      exact stdComplete_extend ⟨htele.evalCtxValidPlus, ihp⟩
        htele.varsCovered.drop_lin hb hty (htele.freshEvalName hsource b)
          hcreation.valid.typeRealized
        (fun b₀ b₁ hbFrame => by subst b; exact nomatch htof)
  | @extend_rep Δ Γ Ψ x b v htele hlink hpair hcreation hb ih =>
      have hty := hb.isTyBasis
      intro hnf
      have ihp : StdComplete Ψ := ih (fun x' c₀ c₁ hmem =>
        hnf x' c₀ c₁ (by
          simp only [EvalCtx.extend]
          exact Finmap.mem_insert.mpr (Or.inr hmem)))
      refine stdComplete_extend ⟨htele.evalCtxValidPlus, ihp⟩
        htele.varsCovered.drop_lin hb hty hpair hcreation.valid.typeRealized
          (fun b₀ b₁ hb => ?_)
      subst hb
      exact absurd (by
        simp only [EvalCtx.extend]
        exact Finmap.mem_insert.mpr (Or.inl rfl)) (hnf x b₀ b₁)

/-- `⊢ (Δ,Γ), Ψ ⟹ PCarrier Ψ` — the full progress-master carrier from the
    telescope (modulo the Π-entry interface): what `thm:prog`'s P8 assembly
    consumes to enter `progress_master_std` / `BasisTransport` at the
    boundary. -/
theorem CtxTele.pCarrier (hpiE : PiEntryTransport) {Δ : LCtx} {Γ : NLCtx}
    {Ψ : EvalCtx} (h : CtxTele Δ Γ Ψ) : PCarrier Ψ :=
  ⟨h.evalCtxValidPlus, stdComplete_of_tele hpiE h⟩

/-- Change-of-basis progress parameterized by basis conversion and dependent-entry conversion. -/
theorem progress_cob_of_transport (_htr : BasisTransport)
    (hpiE : PiEntryTransport)
    {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx} {b : Basis} {s : Space}
    (htele : CtxTele Δ Γ Ψ)
    (hwfΔΓ : CtxWF' Δ Γ) (hwfΨ : EvalCtxValid Ψ) (hwflc : EvalCtxLc Ψ)
    (hanch : EvalCtxLamAnchored Ψ) (hΓΨ : TypingImplyEval Δ Γ Ψ)
    (hb : Basis.BasisValid Γ b) (hsb : Basis.IsSpaceBasis b)
    (htof : Basis.tof b = .space s) :
    ∃ env, Basis.EvalBB Ψ b env (Basis.std (Basis.tof b)) :=
  progress_cob_std hwfΔΓ hwfΨ hwflc hanch hΓΨ
    (stdComplete_of_tele hpiE htele) hb hsb htof

end GLang.V2
