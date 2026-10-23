

import GLang.Proofs.Progress.Supporting.ProgressMasterDefs

namespace GLang.V2

/-! ## refine_1 `SValid.empty` -/

theorem progress_arm_empty : ∀ {ε : NLCtx}, pMotiveS ε Space.empty := by
  intro ε Ψ _hP _hcov
  exact ⟨.empty, .empty⟩

/-! ## refine_2 `SValid.real` -/

theorem progress_arm_real : ∀ {ε : NLCtx}, pMotiveS ε Space.real := by
  intro ε Ψ _hP _hcov
  exact ⟨.real, .real⟩

/-! ## refine_3 `SValid.dual` -/

theorem progress_arm_dual :
    ∀ {ε : NLCtx} {s : Space} (_ : SValid ε s), pMotiveS ε s → pMotiveS ε s.dual := by
  intro ε s _ ih Ψ hP hcov
  obtain ⟨sv, hsv⟩ := ih Ψ hP hcov
  exact ⟨sv, .dual hsv⟩

/-! ## refine_4 `SValid.dsum` -/

theorem progress_arm_dsum :
    ∀ {ε : NLCtx} {s₀ s₁ : Space} (_ : SValid ε s₀) (_ : SValid ε s₁),
      pMotiveS ε s₀ → pMotiveS ε s₁ → pMotiveS ε (s₀.dsum s₁) := by
  intro ε s₀ s₁ _ _ ih₀ ih₁ Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  exact ⟨.dsum sv₀ sv₁, .dsum hsv₀ hsv₁⟩

/-! ## refine_5 `SValid.tprod` -/

theorem progress_arm_tprod :
    ∀ {ε : NLCtx} {s₀ s₁ : Space} (_ : SValid ε s₀) (_ : SValid ε s₁),
      pMotiveS ε s₀ → pMotiveS ε s₁ → pMotiveS ε (s₀.tprod s₁) := by
  intro ε s₀ s₁ _ _ ih₀ ih₁ Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  exact ⟨.tprod sv₀ sv₁, .tprod hsv₀ hsv₁⟩

/-! ## refine_6–9 `SValid.ker / coker / img / coimg` (the ffs arms)

One pattern (catalog F1 route): `EvalS.ker` (resp. coker/img/coimg) at
`b := Basis.std (.space (.tprod (.dual s₀) s₁))` — definitionally
`Basis.stdSpace (.tprod (.dual s₀) s₁)` (C2), so the term IH's witness
evaluation IS the rule's `he`; `hb := sof_stdSpace`, matrix compatibility is
definitionally witnessed by the two endpoint standard bases, and `hsvb` comes
from the space IHs after rewriting by `sof_stdSpace`. -/

theorem progress_arm_ker :
    ∀ {ε : NLCtx} {e : Term} {s₀ s₁ : Space} (_ : SValid ε s₀) (_ : SValid ε s₁)
      (_ : HasType ∅ ε e (Ty.space (s₀.dual.tprod s₁))),
      pMotiveS ε s₀ → pMotiveS ε s₁ → pMotiveH ∅ ε e (Ty.space (s₀.dual.tprod s₁)) →
        pMotiveS ε (s₀.ker s₁ e) := by
  intro ε e s₀ s₁ _ _ _ ih₀ ih₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, hv⟩ := (ihe Ψ hP hcov).1
  have hsvb : ValSpace.EvalS Ψ
      (Basis.sof (Basis.stdSpace (.tprod (.dual s₀) s₁))) (.tprod sv₀ sv₁) := by
    rw [Basis.sof_stdSpace]
    exact .tprod (.dual hsv₀) hsv₁
  exact ⟨_, ValSpace.EvalS.ker hv (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩ hsvb⟩

theorem progress_arm_coker :
    ∀ {ε : NLCtx} {e : Term} {s₀ s₁ : Space} (_ : SValid ε s₀) (_ : SValid ε s₁)
      (_ : HasType ∅ ε e (Ty.space (s₀.dual.tprod s₁))),
      pMotiveS ε s₀ → pMotiveS ε s₁ → pMotiveH ∅ ε e (Ty.space (s₀.dual.tprod s₁)) →
        pMotiveS ε (s₀.coker s₁ e) := by
  intro ε e s₀ s₁ _ _ _ ih₀ ih₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, hv⟩ := (ihe Ψ hP hcov).1
  have hsvb : ValSpace.EvalS Ψ
      (Basis.sof (Basis.stdSpace (.tprod (.dual s₀) s₁))) (.tprod sv₀ sv₁) := by
    rw [Basis.sof_stdSpace]
    exact .tprod (.dual hsv₀) hsv₁
  exact ⟨_, ValSpace.EvalS.coker hv (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩ hsvb⟩

theorem progress_arm_img :
    ∀ {ε : NLCtx} {e : Term} {s₀ s₁ : Space} (_ : SValid ε s₀) (_ : SValid ε s₁)
      (_ : HasType ∅ ε e (Ty.space (s₀.dual.tprod s₁))),
      pMotiveS ε s₀ → pMotiveS ε s₁ → pMotiveH ∅ ε e (Ty.space (s₀.dual.tprod s₁)) →
        pMotiveS ε (s₀.img s₁ e) := by
  intro ε e s₀ s₁ _ _ _ ih₀ ih₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, hv⟩ := (ihe Ψ hP hcov).1
  have hsvb : ValSpace.EvalS Ψ
      (Basis.sof (Basis.stdSpace (.tprod (.dual s₀) s₁))) (.tprod sv₀ sv₁) := by
    rw [Basis.sof_stdSpace]
    exact .tprod (.dual hsv₀) hsv₁
  exact ⟨_, ValSpace.EvalS.img hv (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩ hsvb⟩

theorem progress_arm_coimg :
    ∀ {ε : NLCtx} {e : Term} {s₀ s₁ : Space} (_ : SValid ε s₀) (_ : SValid ε s₁)
      (_ : HasType ∅ ε e (Ty.space (s₀.dual.tprod s₁))),
      pMotiveS ε s₀ → pMotiveS ε s₁ → pMotiveH ∅ ε e (Ty.space (s₀.dual.tprod s₁)) →
        pMotiveS ε (s₀.coimg s₁ e) := by
  intro ε e s₀ s₁ _ _ _ ih₀ ih₁ ihe Ψ hP hcov
  obtain ⟨sv₀, hsv₀⟩ := ih₀ Ψ hP hcov
  obtain ⟨sv₁, hsv₁⟩ := ih₁ Ψ hP hcov
  obtain ⟨v, hv⟩ := (ihe Ψ hP hcov).1
  have hsvb : ValSpace.EvalS Ψ
      (Basis.sof (Basis.stdSpace (.tprod (.dual s₀) s₁))) (.tprod sv₀ sv₁) := by
    rw [Basis.sof_stdSpace]
    exact .tprod (.dual hsv₀) hsv₁
  exact ⟨_, ValSpace.EvalS.coimg hv (Basis.sof_stdSpace _)
    ⟨Basis.stdSpace s₀, Basis.stdSpace s₁, rfl⟩ hsvb⟩

/-! ## refine_10 `TValid.space` -/

theorem progress_arm_space :
    ∀ {ε : NLCtx} {s : Space} (_ : SValid ε s), pMotiveS ε s → pMotiveT ε (Ty.space s) := by
  intro ε s _ ih Ψ hP hcov
  obtain ⟨sv, hsv⟩ := ih Ψ hP hcov
  exact ⟨⟨.space sv, .space hsv⟩, fun _ _ h => nomatch h⟩

/-! ## refine_11 `TValid.piTy` — the P3-kit arm (P5c: VERBATIM; the producer
of the recursive anchoring).

Route: the strengthened `pMotiveT` IHs deliver hereditarily std-anchored
realizations through the shape splitter `stdAnchored_of_parts` (space-typed:
wrap the plain witness; Π-typed: the carried `StdPiAnchored`). The domain's
anchoring also feeds `PCarrier.extend_var`'s `hpi` directly (the closed
hpi-DISCHARGE). The cofinite codomain IH at one fresh `y₀` is packaged by
`stdAnchored_cofinite_of_fresh` (P3-kit shape), and `StdAnchored.piTy`
assembles the OUTER recursive anchoring — the arm's produced tail; the plain
`EvalT` witness is its `toEvalT` shadow. -/

theorem progress_arm_piTy :
    ∀ {ε : NLCtx} {τ₀ τ₁ : Ty} {k₀ k₁ : Kind} (L : Finset Name)
      (_ : TValid ε τ₀ k₀)
      (_ : (y : Name) → y ∉ L → TValid (Finmap.insert y τ₀ ε) (Ty.openVar y τ₁) k₁),
      pMotiveT ε τ₀ → (∀ y ∉ L, pMotiveT (Finmap.insert y τ₀ ε) (Ty.openVar y τ₁)) →
        pMotiveT ε (τ₀.piTy τ₁) := by
  intro ε τ₀ τ₁ k₀ k₁ L _ht₀ _ht₁ ih₀ ih₁ Ψ hP hcov
  -- 1. std-anchored domain realization at Ψ (the strengthened IH, both
  --    conjuncts, through the shape splitter).
  obtain ⟨τv₀, h₀A⟩ := stdAnchored_of_parts (ih₀ Ψ hP hcov)
  have h₀ : ValTy.EvalT Ψ τ₀ τv₀ := h₀A.toEvalT
  -- 2. pick a fresh binder name outside every participant.
  obtain ⟨y₀, hy₀⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Ψ ∪ L ∪ Ty.fv τ₀ ∪ Ty.fv τ₁ ∪ Basis.fv (Basis.std τ₀)
      ∪ ValTy.fv τv₀)
  simp only [Finset.mem_union, not_or] at hy₀
  obtain ⟨⟨⟨⟨⟨hy₀Ψ, hy₀L⟩, _hy₀τ₀⟩, hy₀τ₁⟩, hy₀b₀⟩, hy₀τv₀⟩ := hy₀
  -- 3. extend the carrier and the covering at `(y₀, Basis.std τ₀) ↦ .var y₀ τv₀`;
  --    `hpi` is the domain IH's own carried anchored clause (P5c).
  have hfresh : (y₀, Basis.std τ₀) ∉ Ψ := (EvalCtx.avoidB_spec hy₀Ψ).1 _
  have hP' : PCarrier (EvalCtx.extend Ψ y₀ (Basis.std τ₀) (.var y₀ τv₀)) :=
    hP.extend_var hfresh (evalT_fv h₀ hP.1) h₀
      (fun a b heq => (ih₀ Ψ hP hcov).2 a b heq)
  have hcov' : VarsCovered ∅ (Finmap.insert y₀ τ₀ ε)
      (EvalCtx.extend Ψ y₀ (Basis.std τ₀) (.var y₀ τv₀)) :=
    hcov.extend_var
  -- 4. the cofinite typing IH at `y₀`, at the extended Ψ — std-anchored
  --    opened codomain (both conjuncts, through the shape splitter).
  obtain ⟨τv₁, h₁A⟩ := stdAnchored_of_parts (ih₁ y₀ hy₀L _ hP' hcov')
  -- 5. exists-fresh → cofinite, at the ANCHORED judgment (P5c kit).
  obtain ⟨L', hcofA⟩ := stdAnchored_cofinite_of_fresh h₁A hy₀Ψ hy₀b₀ hy₀τv₀ hy₀τ₁
    (evalT_lc h₀ hP.1.toEvalCtxLc) (evalT_lc h₁A.toEvalT hP'.1.toEvalCtxLc)
  -- 6. assemble the recursive anchoring; the witness is its `toEvalT` shadow,
  --    and the produced tail (R3) is the anchoring itself.
  have hanch : StdAnchored Ψ (.piTy τ₀ τ₁)
      (.piTy τv₀ (ValTy.closeRec 0 y₀ τv₁)) := .piTy h₀A L' hcofA
  refine ⟨⟨_, hanch.toEvalT⟩, ?_⟩
  intro a b heq
  cases heq
  exact ⟨_, hanch⟩

end GLang.V2
