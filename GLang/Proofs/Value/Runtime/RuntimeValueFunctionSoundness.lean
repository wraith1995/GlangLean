import GLang.Proofs.Value.Runtime.RuntimeValueInfer
import GLang.Proofs.Value.Partial.PartialValueApplicationTransport

namespace GLang.RuntimeValue
open PartialValueDomains PaperValueDomains

/-- A checked reshape can use an independently realized input type. -/
theorem reshapeInferred_related (target source actual : ValTy) (orc : PartialFFSOracleSem)
    {I : Type 1} (w : I → World)
    (hs : ∀ i j, PartialRawTypeCoherent orc source (w i) (w j))
    (ht : ∀ i j, PartialRawTypeCoherent orc target (w i) (w j))
    (ha : ∀ i j, PartialRawTypeCoherent orc actual (w i) (w j))
    (i j : I) (v v' : ValValSem)
    (hv : WorldRuntimeRelated orc actual (w i) (w j) v v') :
    PartialRel (WorldRuntimeRelated orc target (w i) (w j))
      (PartialValueEval.reshapeInferred orc (w i).env (w i).types (w i).values v target source actual)
      (PartialValueEval.reshapeInferred orc (w j).env (w j).types (w j).values v' target source actual) := by
  cases source with
  | piTy d c =>
    cases actual with
    | space s => trivial
    | piTy a b =>
      exact partial_reshape_family target (.piTy a b) orc w w ha ht i j i j rfl rfl v v' hv
  | space ss =>
    cases target with
    | piTy d c =>
      cases v <;> cases v' <;> simp [PartialValueEval.reshapeInferred,PartialValueEval.reshapeBetween,PartialRel]
    | space st =>
      cases actual with
      | piTy d c =>
        cases hD : PartialWorldType orc (w i) (.piTy d c) <;>
          cases hE : PartialWorldType orc (w j) (.piTy d c) <;>
          cases v <;> cases v' <;>
          simp only [WorldRuntimeRelated,hD,hE,PartialRuntimeRelated] at hv
        all_goals try contradiction
        all_goals simp [PartialValueEval.reshapeInferred,PartialValueEval.reshapeBetween,PartialRel]
      | space sa =>
        cases v <;> cases v' <;> try exact False.elim hv
        rename_i a b
        cases hA : PartialWorldType orc (w i) (.space sa) <;>
          cases hB : PartialWorldType orc (w j) (.space sa) <;>
          simp only [WorldRuntimeRelated,PartialRuntimeRelated,hA,hB,PartialRelated] at hv
        all_goals try contradiction
        obtain ⟨rfl,_,_⟩ := hv
        have hs' := (PartialSpaceAgreement.observations _ _ ss (hs i j)).2
        have ht' := (PartialSpaceAgreement.observations _ _ st (ht i j)).2
        simp only [PartialValueEval.reshapeInferred,PartialValueEval.reshapeBetween,
          PartialValueEval.reshapeArray,hs',ht']
        cases hS : ss.dofPartial (orc (w j).env (w j).types (w j).values) with
        | error err => simp [PartialRel]
        | ok ns =>
          cases hT : st.dofPartial (orc (w j).env (w j).types (w j).values) with
          | error err => simp [PartialRel]
          | ok nt =>
            by_cases hn : a.length = ns ∧ ns = nt
            · simp only [hn,↓reduceIte,PartialRel,WorldRuntimeRelated,PartialWorldType,
                denotValTyPartial,ht',hT,PartialRuntimeRelated,PartialRelated]
              exact ⟨rfl,hn.1.trans hn.2,hn.1.trans hn.2⟩
            · simp [hn,PartialRel]

theorem eval_reshape_related {ε : ValCtx} {e : ValExpr} {actual source target : ValTy}
    (he : ValHasType ε e actual) {I : Type} (ρ : I → ValEnvSem)
    (hs : ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle source ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
    (ht : ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle target ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
    (ha : ∀ i j, PartialRawTypeCoherent PartialDirectOracle.oracle actual ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
    (i j : I)
    (hr : PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle actual ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] e)
      (denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] e)) :
    PartialRel (WorldRuntimeRelated PartialDirectOracle.oracle target ⟨ρ i,[],[]⟩ ⟨ρ j,[],[]⟩)
      (denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] (.reshap e target source))
      (denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] (.reshap e target source)) := by
  simp only [denotValB_partial,ValExpr.inferTypeCtx_eq_of_typed he]
  cases hl : denotValB_partial PartialDirectOracle.oracle (ρ i) [] [] e <;>
    cases hh : denotValB_partial PartialDirectOracle.oracle (ρ j) [] [] e <;>
    simp only [hl,hh,PartialRel] at hr ⊢
  simpa only [PartialRel] using (reshapeInferred_related target source actual PartialDirectOracle.oracle
    (fun p : ULift.{1} I => ⟨ρ p.down,[],[]⟩)
    (fun p q => hs p.down q.down) (fun p q => ht p.down q.down)
    (fun p q => ha p.down q.down) ⟨i⟩ ⟨j⟩ _ _ hr)

/-- A related function result is either an error or a runtime function. -/
theorem related_pi_noArray {orc : PartialFFSOracleSem} {d c : ValTy} {w w' : World}
    {r r' : Except DimError ValValSem}
    (h : PartialRel (WorldRuntimeRelated orc (.piTy d c) w w') r r') :
    (∀ a, r ≠ .ok (.array a)) ∧ (∀ a, r' ≠ .ok (.array a)) := by
  cases r with
  | error err =>
    cases r' <;> simp_all [PartialRel]
  | ok v =>
    cases r' with
    | error err => exact h.elim
    | ok v' =>
      cases hT : PartialWorldType orc w (.piTy d c) <;>
        cases hU : PartialWorldType orc w' (.piTy d c) <;>
        cases v <;> cases v' <;>
        simp_all [PartialRel,WorldRuntimeRelated,PartialRuntimeRelated]

theorem bindArrays_noArray_right {r : Except DimError ValValSem}
    (h : ∀ a, r ≠ .ok (.array a)) (l : Except DimError ValValSem)
    (f : FlatArray → FlatArray → Except DimError ValValSem) :
    ValValSem.bindArrays l r f = .error .mismatch := by
  cases l with
  | error err => cases err; rfl
  | ok v =>
    cases v with
    | fn _ _ => rfl
    | array a =>
      cases r with
      | error err => cases err; rfl
      | ok v => cases v with
        | fn _ _ => rfl
        | array a => exact (h a rfl).elim

theorem withDimensions_error (q : PartialFFSOracle) (ss : List ValSpace)
    (f : FFSOracle → Except DimError ValValSem) (h : ∀ q, f q = .error .mismatch) :
    PartialValueEval.withDimensions q ss f = .error .mismatch := by
  simp only [PartialValueEval.withDimensions]
  cases PartialValueEval.dimensions q ss with
  | error err => cases err; rfl
  | ok u => cases u; exact h _

theorem scale_noArray (orc : PartialFFSOracleSem) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e0 e1 : ValExpr)
    (h : ∀ a, denotValB_partial orc ρ Γ Δ e1 ≠ .ok (.array a)) :
    denotValB_partial orc ρ Γ Δ (.scale e0 e1) = .error .mismatch := by
  rw [denotValB_partial]
  apply withDimensions_error
  intro q
  exact bindArrays_noArray_right h _ _

theorem ttv_noArray (orc : PartialFFSOracleSem) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (s : ValSpace) (e0 e1 : ValExpr)
    (h : ∀ a, denotValB_partial orc ρ Γ Δ e1 ≠ .ok (.array a)) :
    denotValB_partial orc ρ Γ Δ (.ttv s e0 e1) = .error .mismatch := by
  rw [denotValB_partial]
  apply withDimensions_error
  intro q
  exact bindArrays_noArray_right h _ _

end GLang.RuntimeValue
