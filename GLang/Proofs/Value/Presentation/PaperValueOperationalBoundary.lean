import GLang.Proofs.Value.Presentation.PaperValueFullCorrespondence

/-! Audit of the boundary between source agreement and extensional value
domains. Public operational definitions are deliberately unchanged. -/
namespace GLang.PaperValueOperationalBoundary
open PaperValueDomains
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev scalar : ValTy := .space .real
abbrev arrow : ValTy := .piTy scalar scalar
abbrev functional : ValTy := .piTy arrow scalar

def fails : FlatArray → Except DimError FlatArray := fun _ => .error .mismatch
def failsOnValid : FlatArray → Except DimError FlatArray := fun a =>
  if a.length = 1 then .error .mismatch else .ok (FlatArray.zeros 1)

theorem partial_arguments_related (orc : FFSOracleSem) (w w' : World) :
    Related orc arrow w w' fails failsOnValid := by
  intro a b hab
  have hb : b.length = 1 := by simpa [Related] using hab.2.2
  simp [fails, failsOnValid, hb, PartialRel]

def realBasis : BasisDenot := .vecs HSpace.real [1]
def arrowBasis : BasisDenot := .frame ℝ realBasis (fun _ => realBasis)

theorem zero_agrees (orc : FFSOracleSem) (σ : DEnv) (ρ : ValEnvSem)
    (Ds : List DVal) (Gv : List ValTy) (Dv : List ValValSem) :
    RawAgree orc σ ρ Ds Gv Dv (.space .real) scalar realBasis
      ((denotTyAux σ Ds (.space .real)).embed (0 : ℝ)) (.array (FlatArray.zeros 1)) := by
  simp [RawAgree, LegacyAgree, scalar, realBasis, denotTyAux, denotSpaceAux,
    HType.embed, DVal.atSpace, DVal.asHil, BasisDenot.atSpace,
    FlatArray.zeros, FlatArray.ofFn, FlatArray.get, ValSpace.dof_real, HSpace.real]
  symm
  apply Finset.sum_eq_zero
  intro i _
  exact zero_smul ℝ _

/-- Source-agreeing scalar functions must succeed on zero. The value domain,
in contrast, also contains functions that fail on every valid argument. -/
theorem agreeing_function_succeeds_zero (orc : FFSOracleSem) (σ : DEnv)
    (ρ : ValEnvSem) (x : DVal) (v : ValValSem)
    (f : FlatArray → Except DimError FlatArray)
    (h : RawAgree orc σ ρ [] [] [] (.piTy (.space .real) (.space .real))
      arrow arrowBasis x v)
    (hd : ValValSem.toEl (denotValTyS orc ρ [] [] arrow) v = .ok f) :
    ∃ a, f (FlatArray.zeros 1) = .ok a := by
  simp only [arrow, scalar] at h
  rw [RawAgree] at h
  obtain ⟨g, rfl, hg⟩ := h
  obtain ⟨out, hout, ha⟩ := hg (0 : ℝ) (.array (FlatArray.zeros 1)) (FlatArray.zeros 1)
    rfl (zero_agrees orc σ ρ [] [] [])
  obtain ⟨a, ha⟩ := RawAgree.toEl ha
  simp only [arrow, scalar, denotValTyS, ValValSem.toEl, dite_true] at hd
  cases hd
  refine ⟨a, ?_⟩
  simp only [hout]
  cases out <;> simpa only [denotValTyS, ValValSem.toEl] using ha

def callback (f : FlatArray → Except DimError FlatArray) : Except DimError ValValSem :=
  if ∃ a, f (FlatArray.zeros 1) = .ok a then .ok (.array (FlatArray.zeros 1))
  else match f FlatArray.empty with
    | .error e => .error e
    | .ok _ => .ok (.array (FlatArray.zeros 1))

def malicious : ValValSem := .fn (FlatArray → Except DimError FlatArray) callback
def functionalBasis : BasisDenot := .frame (ℝ → ℝ) arrowBasis (fun _ => realBasis)
def sourceZero : DVal := .pi (ℝ → ℝ) (fun _ => .hil ⟨HSpace.real, (0 : ℝ)⟩)
abbrev sourceFunctional : Ty :=
  .piTy (.piTy (.space .real) (.space .real)) (.space .real)

theorem malicious_agrees (orc : FFSOracleSem) (σ : DEnv) (ρ : ValEnvSem) :
    RawAgree orc σ ρ [] [] [] sourceFunctional functional functionalBasis sourceZero malicious := by
  unfold sourceFunctional functional
  rw [RawAgree]
  refine ⟨callback, rfl, ?_⟩
  intro x v f hd ha
  change ℝ → ℝ at x
  have hf := agreeing_function_succeeds_zero orc σ ρ _ v f ha hd
  refine ⟨.array (FlatArray.zeros 1), by simp [callback, hf], ?_⟩
  have hb : functionalBasis.applyEl x = realBasis := dif_pos rfl
  have hx : sourceZero.applyEl x = .hil ⟨HSpace.real, (0 : ℝ)⟩ := dif_pos rfl
  erw [hb, hx]
  exact zero_agrees orc σ ρ [_] [arrow] [v]

theorem malicious_not_related (orc : FFSOracleSem) (ρ : ValEnvSem) :
    ¬ RuntimeRelated orc functional ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩ malicious malicious := by
  intro h
  obtain ⟨_, _, hf⟩ := h
  have bad := hf fails failsOnValid (partial_arguments_related orc _ _)
  simp [callback, fails, failsOnValid, FlatArray.zeros, FlatArray.empty,
    FlatArray.ofFn, PartialRel] at bad

def arrowSyntax : Basis := .frame .one .one
def functionalSyntax : Basis := .frame arrowSyntax .one

theorem arrow_valid (Γ : NLCtx) : Basis.BasisValid Γ arrowSyntax :=
  .frame ∅ .one (fun _ _ => .one)

theorem functional_valid (Γ : NLCtx) : Basis.BasisValid Γ functionalSyntax :=
  .frame ∅ (arrow_valid Γ) (fun _ _ => .one)

theorem arrow_eval (Ψ : EvalCtx) :
    ValTy.EvalT Ψ (Basis.tof arrowSyntax) arrow :=
  .piTy (b₀ := .one) (.space .real) rfl ∅ (fun _ _ => .space .real)

theorem functional_eval (Ψ : EvalCtx) :
    ValTy.EvalT Ψ (Basis.tof functionalSyntax) functional :=
  .piTy (b₀ := arrowSyntax) (arrow_eval Ψ) rfl ∅ (fun _ _ => .space .real)

theorem functional_denot (σ : DEnv) : denotBasis σ functionalSyntax = functionalBasis := by
  simp [functionalSyntax, arrowSyntax, denotBasis, Basis.tof,
    denotTyAux, denotSpaceAux, Basis.openVar, Basis.openRec,
    functionalBasis, arrowBasis, realBasis, HType.El]

theorem valid_consistency_not_value_env :
    ¬ (∀ {Δ Γ Ψ Γv σ ρ}, RawConsistent directOracle Δ Γ Ψ Γv σ ρ →
      Nonempty (ValCtxValid Γv) → PaperValueResults.EnvWF Γv ρ) := by
  intro hall
  let σ : DEnv := ⟨∅⟩
  let ρ : ValEnvSem := fun _ => malicious
  let v : ValExpr := .var "bad" functional
  have hvscope : ValExpr.fv v ⊆ ((∅ : EvalCtx).extend "bad" functionalSyntax v).keyNames := by
    simp [v, ValExpr.fv, functional, arrow, scalar, ValTy.fv, ValSpace.fv,
      V2.keyNames_extend]
  have hvlc : ValExpr.lc v := by
    exact .var (.piTy ∅ (.piTy ∅ (.space .real) (fun _ _ => .space .real))
      (fun _ _ => .space .real))
  have hcreation : V2.EvalEntryCreation ∅ "bad" functionalSyntax v := by
    refine ⟨⟨functional_eval ∅, hvscope, hvlc⟩, ?_⟩
    intro b0 b1 t0 t1 body _ h
    change ValExpr.var "bad" functional = .vlam t0 t1 body at h
    cases h
  have hden : denotValB_semS directOracle ρ [] [] v = .ok malicious := by
    simp [v, denotValB_semS, ρ]
  have hshape : sourceZero.matchesShape (denotTy σ (Basis.tof functionalSyntax)) := by
    simp [DVal.matchesShape, DVal.shape, sourceZero, denotTy, denotTyAux,
      denotSpaceAux, functionalSyntax, arrowSyntax, Basis.tof, HType.El]
  have hagree : RawAgree directOracle σ ρ [] [] [] (Basis.tof functionalSyntax)
      functional (denotBasis σ functionalSyntax) sourceZero malicious := by
    rw [functional_denot]
    exact malicious_agrees directOracle σ ρ
  have hdims : RawAgreeDimsAt directOracle σ ρ [] [] [] (Basis.tof functionalSyntax)
      functional (denotBasis σ functionalSyntax) := by
    simp [functionalSyntax, arrowSyntax, Basis.tof, functional, arrow, scalar,
      RawAgreeDimsAt, srcShp]
  have hc := RawConsistent.extend_nl (RawConsistent.empty (orc := directOracle) (rho := ρ))
    (x := "bad") (b := functionalSyntax) (v := v) (xs := sourceZero)
    ⟨Finmap.notMem_empty, Finmap.notMem_empty⟩ (functional_valid ∅) (functional_eval ∅) rfl
    (by trivial) hvscope hvlc (Or.inr ⟨functional, rfl⟩)
    hshape hden hagree hdims hcreation
  have hvalid : ValCtxValid (Finmap.insert "bad" functional ∅) := by
    intro x τ hx
    by_cases h : x = "bad"
    · subst x
      simp only [Finmap.lookup_insert, Option.some.injEq] at hx
      subst τ
      exact ⟨_, .piTy ∅ (.piTy ∅ (.space .real) (fun _ _ => .space .real))
        (fun _ _ => .space .real)⟩
    · simp [h] at hx
  have hr := (hall hc ⟨hvalid⟩).member (x := "bad") (τ := functional) (by simp)
  have hv : (ρ.update "bad" malicious) "bad" = malicious := by simp [ValEnvSem.update]
  rw [hv] at hr
  exact malicious_not_related directOracle _ hr

theorem consistency_not_value_env :
    ¬ (∀ {Δ Γ Ψ Γv σ ρ}, RawConsistent directOracle Δ Γ Ψ Γv σ ρ →
      PaperValueResults.EnvWF Γv ρ) := by
  intro h
  exact valid_consistency_not_value_env (fun hc _ => h hc)

end
end GLang.PaperValueOperationalBoundary
