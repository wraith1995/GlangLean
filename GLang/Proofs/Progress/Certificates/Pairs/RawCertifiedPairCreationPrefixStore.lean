import GLang.Proofs.Progress.Certificates.Context.RawCertifiedConsistentPairStore

namespace GLang

open OperationalStrengthening
open RawCertifiedConsistentPairStore

/-- Adding another exact representation of an already-linked source name
preserves the source/evaluator linkage.  Unlike first insertion, this needs
only exact-key freshness: another basis for `x` may already be stored. -/
theorem V2.TypingImplyEval.extend_rep
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {x : VName} {b : Basis} {v : ValExpr}
    (hlink : V2.TypingImplyEval Delta Gamma Psi)
    (hwf : V2.CtxWF' Delta Gamma)
    (hsource : V2.SourceEntryLinked Delta Gamma x b)
    (hkey : (x, b) ∉ Psi)
    (hb : Basis.BasisValid Gamma b) :
    V2.TypingImplyEval Delta Gamma (Psi.extend x b v) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      obtain ⟨bZ, hmem⟩ := (hlink.1 z).mp hz
      exact ⟨bZ, by
        simp only [EvalCtx.extend]
        exact Finmap.mem_insert.mpr (Or.inr hmem)⟩
    · rintro ⟨bZ, hmem⟩
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with hnew | hold
      · have hzx : z = x := (Prod.mk.inj hnew).1
        subst z
        exact hsource.mem_source
      · exact (hlink.1 z).mpr ⟨bZ, hold⟩
  · intro z s bZ hlookup hmem
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with hnew | hold
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnew
      rcases hsource with ⟨s0, hlookup0, htof⟩ | hlookupGamma
      · have hs : s0 = s := Option.some.inj (hlookup0.symm.trans hlookup)
        simpa only [hs] using htof
      · exact False.elim (hwf.disjoint z
          (Finmap.mem_of_lookup_eq_some hlookup)
          (Finmap.mem_of_lookup_eq_some hlookupGamma))
    · exact hlink.2.1 z s bZ hlookup hold
  · intro z tau bZ hlookup hmem
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with hnew | hold
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnew
      rcases hsource with ⟨s, hlookupDelta, htof⟩ | hlookup0
      · exact False.elim (hwf.disjoint z
          (Finmap.mem_of_lookup_eq_some hlookupDelta)
          (Finmap.mem_of_lookup_eq_some hlookup))
      · exact Option.some.inj (hlookup0.symm.trans hlookup)
    · exact hlink.2.2.1 z tau bZ hlookup hold
  · intro z bZ hmem
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with hnew | hold
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnew
      exact hb
    · exact hlink.2.2.2 z bZ hold

/-- Raw consistency constructively provides the full source/evaluator
linkage.  In particular, every linear or nonlinear source binding has an
exact evaluator key of the same exposed type, and every evaluator key has a
basis valid in the current nonlinear context. -/
theorem RawConsistent.typingImplyEval
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    V2.TypingImplyEval Delta Gamma Psi := by
  induction h with
  | empty =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x
        constructor
        · rintro (hx | hx) <;>
            exact absurd hx Finmap.notMem_empty
        · rintro ⟨b, hmem⟩
          exact absurd hmem Finmap.notMem_empty
      · intro x s b hlookup
        exact absurd (Finmap.mem_of_lookup_eq_some hlookup)
          Finmap.notMem_empty
      · intro x tau b hlookup
        exact absurd (Finmap.mem_of_lookup_eq_some hlookup)
          Finmap.notMem_empty
      · intro x b hmem
        exact absurd hmem Finmap.notMem_empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauV xs s yV
      hprefix hx htof hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden
      hagree hdims ih =>
      have hlink := RawLocalCtxWFInsertionScratch.typingImplyEval_insert_lin
        (v := v) ih hx.1 hx.2 (hprefix.freshEvalName hx) hb
          (by simpa only [Basis.sof_eq_of_tof_eq_space htof] using htof)
      simpa only [Basis.sof_eq_of_tof_eq_space htof] using hlink
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hprefix hx hb hTy hinfer hinferSpace hfvv hlc hnr hxs hden hagree
      hdims _hanchor ih =>
      exact RawLocalCtxWFInsertionScratch.typingImplyEval_insert_nl
        (v := v) ih hx.1 hx.2 (hprefix.freshEvalName hx) hb
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauV xs yV
      hprefix hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc
      hxs hden hagree hdims hanchor ih =>
      exact ih.extend_rep hprefix.ctxWFPrime hsource hkey hb

/-- Every source-context name of a raw creation prefix is represented by an
evaluator key. -/
theorem RawConsistent.context_mem_to_eval
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    {x : VName} (hx : x ∈ Delta ∨ x ∈ Gamma) :
    exists b : Basis, (x, b) ∈ Psi :=
  (h.typingImplyEval.1 x).mp hx

/-- Finset form of `RawConsistent.context_mem_to_eval`. -/
theorem RawConsistent.context_keys_subset_keyNames
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    Delta.keys ∪ Gamma.keys ⊆ Psi.keyNames := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxDelta | hxGamma
  · obtain ⟨b, hmem⟩ := h.context_mem_to_eval
      (Or.inl (Finmap.mem_keys.mp hxDelta))
    exact EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hmem⟩
  · obtain ⟨b, hmem⟩ := h.context_mem_to_eval
      (Or.inr (Finmap.mem_keys.mp hxGamma))
    exact EvalCtx.mem_keyNames_iff_exists_basis.mpr ⟨b, hmem⟩

end GLang
