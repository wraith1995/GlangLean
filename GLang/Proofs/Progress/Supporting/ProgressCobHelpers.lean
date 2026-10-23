

import GLang.Proofs.Progress.Supporting.ProgressMaster

namespace GLang.V2

/-! ## Target-shape adapters (`Basis.std (tof b)` ⟷ `stdSpace (sof b)`).

`lem:cobProg`'s conclusion is at `Basis.std (Basis.tof b)`; the kit's
compositional currency is `Basis.stdSpace (Basis.sof b)` (the form the
`EvalBB` constructors produce/consume componentwise). For a SPACE basis
the two are propositionally equal (`Basis.std_tof_eq_stdSpace`). -/

/-- Re-target a conversion-to-std from the `stdSpace (sof b)` form to the
    `Basis.std (tof b)` form (`lem:cobProg`'s conclusion shape). -/
theorem evalBB_std_tof_of_stdSpace {Ψ : EvalCtx} {b : Basis} {env : ValExpr}
    (htof : Basis.tof b = .space (Basis.sof b))
    (h : Basis.EvalBB Ψ b env (Basis.stdSpace (Basis.sof b))) :
    Basis.EvalBB Ψ b env (Basis.std (Basis.tof b)) := by
  rw [Basis.std_tof_eq_stdSpace htof]; exact h

/-- Re-target a conversion-to-std from the `Basis.std (tof b)` form (the
    P6c induction hypotheses' shape) to the kit's `stdSpace (sof b)` form. -/
theorem evalBB_stdSpace_of_std_tof {Ψ : EvalCtx} {b : Basis} {env : ValExpr}
    (htof : Basis.tof b = .space (Basis.sof b))
    (h : Basis.EvalBB Ψ b env (Basis.std (Basis.tof b))) :
    Basis.EvalBB Ψ b env (Basis.stdSpace (Basis.sof b)) := by
  rw [← Basis.std_tof_eq_stdSpace htof]; exact h

/-- **Dual arm** of `lem:cobProgA`: a conversion-to-std for `b` lifts to one
    for `.dual b` via `EvalBB.dual_std` (whose conclusion basis
    `Basis.std (tof (.dual b))` reduces to `.dual (stdSpace (sof b))`). -/
theorem evalBB_dual_of_std {Ψ : EvalCtx} {b : Basis} {env : ValExpr}
    (htof : Basis.tof b = .space (Basis.sof b))
    (h : Basis.EvalBB Ψ b env (Basis.std (Basis.tof b))) :
    Basis.EvalBB Ψ (.dual b) (.vtrans (.inv env))
      (.dual (Basis.stdSpace (Basis.sof b))) :=
  Basis.EvalBB.dual_std htof h

theorem evalBB_tprod_to_std {Ψ : EvalCtx} {b₀ b₁ : Basis}
    {env₀ env₁ : ValExpr}
    (h₀ : Basis.EvalBB Ψ b₀ env₀ (Basis.stdSpace (Basis.sof b₀)))
    (h₁ : Basis.EvalBB Ψ b₁ env₁ (Basis.stdSpace (Basis.sof b₁))) :
    Basis.EvalBB Ψ (.tprod b₀ b₁) (.vkrn env₀ env₁)
      (Basis.stdSpace (Basis.sof (.tprod b₀ b₁))) :=
  Basis.EvalBB.tprod h₀ h₁

/-- **Direct-sum arm** of `lem:cobProgA`: component conversions-to-std
    compose to a `.dsum` conversion-to-std (`EvalBB.dsum` is direct —
    premises share the conclusion's orientation). -/
theorem evalBB_dsum_to_std {Ψ : EvalCtx} {b₀ b₁ : Basis}
    {env₀ env₁ : ValExpr}
    (h₀ : Basis.EvalBB Ψ b₀ env₀ (Basis.stdSpace (Basis.sof b₀)))
    (h₁ : Basis.EvalBB Ψ b₁ env₁ (Basis.stdSpace (Basis.sof b₁))) :
    Basis.EvalBB Ψ (.dsum b₀ b₁) (.vblk env₀ env₁)
      (Basis.stdSpace (Basis.sof (.dsum b₀ b₁))) :=
  Basis.EvalBB.dsum h₀ h₁

/-! ## (5) — the closing COB move. -/

theorem opStep_cob_of_std {Ψ : EvalCtx} {e : Term} {b : Basis}
    {v envc : ValExpr} {sv : ValSpace} {s : Space}
    (htof : Basis.tof b = .space (Basis.sof b))
    (hsof : Basis.sof b = s)
    (he : ValExpr.OpStep Ψ e (Basis.stdSpace s) v)
    (hconv : Basis.EvalBB Ψ b envc (Basis.stdSpace s))
    (hes : ValSpace.EvalS Ψ s sv) :
    ∃ v', ValExpr.OpStep Ψ e b v' := by
  subst hsof
  exact ⟨_, ValExpr.OpStep.cob htof (Basis.htof_stdSpace _) he
    (.inverse hconv) hes⟩

/-! ## (6) — the inner product at an arbitrary space basis. -/

theorem inner_at_basis {Ψ : EvalCtx} {b : Basis} {env : ValExpr}
    {s : Space} {sv : ValSpace}
    (htof : Basis.tof b = .space (Basis.sof b))
    (hsof : Basis.sof b = s)
    (hconv : Basis.EvalBB Ψ b env (Basis.stdSpace s))
    (hes : ValSpace.EvalS Ψ s sv) :
    ∃ env', ValExpr.OpStep Ψ (.inner s) (.tprod (.dual b) (.dual b)) env' := by
  subst hsof
  -- the composed conversion  .tprod (.dual b) (.dual b) ⟷ its stdSpace
  have hdual : Basis.EvalBB Ψ (.dual b) (.vtrans (.inv env))
      (.dual (Basis.stdSpace (Basis.sof b))) :=
    evalBB_dual_of_std htof (evalBB_std_tof_of_stdSpace htof hconv)
  have htp := evalBB_tprod_to_std hdual hdual
  -- ⟨·,·⟩ at the std dual pair
  have hinner : ValExpr.OpStep Ψ (.inner (Basis.sof b))
      (.tprod (.dual (Basis.stdSpace (Basis.sof b)))
              (.dual (Basis.stdSpace (Basis.sof b))))
      (.idelta sv) :=
    ValExpr.OpStep.inner_std (Basis.isStd_stdSpace _) hes (Basis.sof_stdSpace _)
  -- COB across the composed conversion
  exact opStep_cob_of_std
    (s := .tprod (.dual (Basis.sof b)) (.dual (Basis.sof b)))
    rfl rfl hinner htp (.tprod (.dual hes) (.dual hes))

/-! ## (9) — `lem:progA` re-entry (std-basis realizations). -/

/-- **`lem:progA` re-entry**: any (`Nonempty`-packaged, since `HasType` is
    `Type`-valued) typing evaluates at the literal standard basis of its
    type, under the master induction's internal currency
    (`PCarrier`/`VarsCovered` — derive at the boundary via `pCarrier_of` /
    `varsCovered_of`). -/
theorem opStep_of_hasType_std {Ψ : EvalCtx} {Δ : LCtx} {Γ : NLCtx}
    {e : Term} {τ : Ty}
    (hP : PCarrier Ψ) (hcov : VarsCovered Δ Γ Ψ)
    (ht : Nonempty (HasType Δ Γ e τ)) :
    ∃ v, ValExpr.OpStep Ψ e (Basis.std τ) v := by
  obtain ⟨ht⟩ := ht
  exact (progress_master_std.2.2.2 ht Ψ hP hcov).1

theorem opStep_lembd_std {Ψ : EvalCtx} {Γ : NLCtx} {s₀ s₁ : Space}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ)
    (hsub : Nonempty (SubType Γ s₀ s₁)) :
    ∃ v, ValExpr.OpStep Ψ (Term.lembd s₀)
      (Basis.std (.space (.tprod (.dual s₀) s₁))) v := by
  obtain ⟨hsub⟩ := hsub
  exact opStep_of_hasType_std hP hcov ⟨HasType.lembd hsub⟩

theorem opStep_lproj_std {Ψ : EvalCtx} {Γ : NLCtx} {s_sub s_amb : Space}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ)
    (h₀ : Nonempty (SValid Γ s_sub)) (h₁ : Nonempty (SValid Γ s_amb))
    (hsub : Nonempty (SubType Γ s_sub s_amb)) :
    ∃ v, ValExpr.OpStep Ψ (Term.lproj s_sub s_amb)
      (Basis.std (.space (.tprod (.dual s_amb) s_sub))) v := by
  obtain ⟨h₀⟩ := h₀; obtain ⟨h₁⟩ := h₁; obtain ⟨hsub⟩ := hsub
  exact opStep_of_hasType_std hP hcov ⟨HasType.lproj h₀ h₁ hsub⟩

/-- Accumulator core of `hasType_dsumChain`: fold `HasType.dsumE` along the
    tail, tracking the accumulated head space through `List.foldl`. -/
private theorem hasType_dsumChain_go {Δ : LCtx} {Γ : NLCtx} {s : Space}
    (hs : Nonempty (SValid Γ s)) (es : List Term) :
    ∀ (t : Space) (e₀ : Term),
      Nonempty (SValid Γ t) →
      Nonempty (HasType Δ Γ e₀ (.space t)) →
      (∀ e ∈ es, Nonempty (HasType Δ Γ e (.space s))) →
      Nonempty (HasType Δ Γ (Term.dsumChain e₀ es)
        (.space (es.foldl (fun t _ => Space.dsum t s) t))) := by
  induction es with
  | nil => intro t e₀ _ he _; exact he
  | cons a as ih =>
      intro t e₀ ht he hall
      obtain ⟨hsv⟩ := hs
      obtain ⟨htv⟩ := ht
      obtain ⟨hev⟩ := he
      obtain ⟨hav⟩ := hall a List.mem_cons_self
      exact ih (.dsum t s) (.dsumE e₀ a)
        ⟨SValid.dsum htv hsv⟩ ⟨HasType.dsumE htv hsv hev hav⟩
        (fun e he' => hall e (List.mem_cons_of_mem a he'))

/-- Bridge `List.foldl (⊕ s)` to the `Nat`-indexed `Space.dsumChain`. -/
private theorem foldl_dsum_dsumChain (s : Space) :
    ∀ (es : List Term) (n : Nat),
      es.foldl (fun t _ => Space.dsum t s) (Space.dsumChain s n)
        = Space.dsumChain s (n + es.length)
  | [], n => by simp
  | a :: as, n => by
      simp only [List.foldl_cons, List.length_cons]
      have hshift : Space.dsum (Space.dsumChain s n) s
          = Space.dsumChain s (n + 1) := rfl
      rw [hshift, foldl_dsum_dsumChain s as (n + 1)]
      congr 1
      omega

theorem hasType_dsumChain {Δ : LCtx} {Γ : NLCtx} {s : Space} {e₀ : Term}
    {es : List Term}
    (hs : Nonempty (SValid Γ s))
    (hall : ∀ e ∈ (e₀ :: es), Nonempty (HasType Δ Γ e (.space s))) :
    Nonempty (HasType Δ Γ (Term.dsumChain e₀ es)
      (.space (Space.dsumChain s es.length))) := by
  have h : Nonempty (HasType Δ Γ (Term.dsumChain e₀ es)
      (.space (es.foldl (fun t _ => Space.dsum t s) (Space.dsumChain s 0)))) :=
    hasType_dsumChain_go hs es s e₀ hs
      (hall e₀ List.mem_cons_self)
      (fun e he' => hall e (List.mem_cons_of_mem e₀ he'))
  rw [foldl_dsum_dsumChain s es 0, Nat.zero_add] at h
  exact h

theorem evalBB_dsumChain_to_std {Ψ : EvalCtx} {b : Basis} {env : ValExpr}
    (hconv : Basis.EvalBB Ψ b env (Basis.stdSpace (Basis.sof b))) :
    ∀ n : Nat, ∃ env',
      Basis.EvalBB Ψ (Basis.dsumChain b n) env'
        (Basis.stdSpace (Basis.sof (Basis.dsumChain b n)))
  | 0 => ⟨env, hconv⟩
  | n + 1 => by
      obtain ⟨env', ih⟩ := evalBB_dsumChain_to_std hconv n
      exact ⟨_, evalBB_dsum_to_std ih hconv⟩

/-- `evalBB_dsumChain_to_std` re-aligned to the `Space`-level chain via
    `Basis.sof_dsumChain` (the form whose target matches
    `hasType_dsumChain`'s chain space). -/
theorem evalBB_dsumChain_to_std' {Ψ : EvalCtx} {b : Basis} {env : ValExpr}
    {s : Space}
    (hsof : Basis.sof b = s)
    (hconv : Basis.EvalBB Ψ b env (Basis.stdSpace s)) (n : Nat) :
    ∃ env', Basis.EvalBB Ψ (Basis.dsumChain b n) env'
      (Basis.stdSpace (Space.dsumChain s n)) := by
  subst hsof
  obtain ⟨env', h⟩ := evalBB_dsumChain_to_std hconv n
  rw [Basis.sof_dsumChain] at h
  exact ⟨env', h⟩

/-- The chain space realizes whenever the base space does (n+1-fold
    `EvalS.dsum`). -/
theorem evalS_dsumChain {Ψ : EvalCtx} {s : Space} {sv : ValSpace}
    (h : ValSpace.EvalS Ψ s sv) :
    ∀ n : Nat, ∃ svn, ValSpace.EvalS Ψ (Space.dsumChain s n) svn
  | 0 => ⟨sv, h⟩
  | n + 1 => by
      obtain ⟨svn, hn⟩ := evalS_dsumChain h n
      exact ⟨.dsum svn sv, .dsum hn h⟩

theorem opStep_dsumChain_at_chain {Ψ : EvalCtx} {Γ : NLCtx} {b : Basis}
    {env : ValExpr} {s : Space} {sv : ValSpace} {e₀ : Term} {es : List Term}
    (hP : PCarrier Ψ) (hcov : VarsCovered ∅ Γ Ψ)
    (htof : Basis.tof b = .space (Basis.sof b))
    (hsof : Basis.sof b = s)
    (hconv : Basis.EvalBB Ψ b env (Basis.stdSpace s))
    (hes : ValSpace.EvalS Ψ s sv)
    (hs : Nonempty (SValid Γ s))
    (hall : ∀ e ∈ (e₀ :: es), Nonempty (HasType ∅ Γ e (.space s))) :
    ∃ v, ValExpr.OpStep Ψ (Term.dsumChain e₀ es)
      (Basis.dsumChain b es.length) v := by
  subst hsof
  -- type + evaluate the chain at the chain space's std basis
  obtain ⟨v, hv⟩ :=
    opStep_of_hasType_std hP hcov (hasType_dsumChain hs hall)
  -- chain conversion + chain realization
  obtain ⟨env', hbb⟩ := evalBB_dsumChain_to_std' rfl hconv es.length
  obtain ⟨svn, hsvn⟩ := evalS_dsumChain hes es.length
  exact opStep_cob_of_std
    (s := Space.dsumChain (Basis.sof b) es.length)
    (Basis.tof_dsumChain htof es.length)
    (Basis.sof_dsumChain b es.length)
    hv hbb hsvn

end GLang.V2
