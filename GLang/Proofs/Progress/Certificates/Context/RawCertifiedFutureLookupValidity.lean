import GLang.Proofs.Progress.Certificates.Context.RawCertifiedHereditaryStore

/-!
# Basis validity for raw-consistent standard futures

A `CheckedStdFuture` contains two kinds of keys.  Keys inherited from its
root evaluator were installed by `RawConsistent`, while every genuinely new
key carries the literal standard basis of its own source type.  The theorem
below exposes that split at a lookup and proves basis validity in any
nonlinear context extending the raw-consistent root.
-/

namespace GLang
namespace RawCertifiedHereditaryStore

open Basis (BasisValid)

/-- Lookup-preserving evaluator inclusion also preserves the set of represented
source names. -/
theorem EvalCtx.Subctx.names_subset
    {Psi0 Psi : EvalCtx} (h : Psi0.Subctx Psi) : Psi0.names ⊆ Psi.names := by
  classical
  intro x hx
  obtain ⟨⟨x', b⟩, hkey, hname⟩ := Finset.mem_image.mp hx
  simp only at hname
  subst x'
  obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp (Finmap.mem_keys.mp hkey)
  exact EvalCtx.mem_names_of_lookup (h (x, b) v hlookup)

/-- Standard-only futures compose.  In particular, a frame callback world is
still a standard-only future of the original checked-progress root, so
root-relative certificate hypotheses can be reused below nested binders. -/
theorem CheckedStdFuture.trans
    {Psi0 Psi1 Psi2 : EvalCtx}
    (h01 : CheckedStdFuture Psi0 Psi1)
    (h12 : CheckedStdFuture Psi1 Psi2) :
    CheckedStdFuture Psi0 Psi2 where
  subctx := h01.subctx.trans h12.subctx
  extra_standard := by
    intro x b hmem hnot0
    by_cases hmem1 : (x, b) ∈ Psi1
    · exact h01.extra_standard x b hmem1 hnot0
    · exact h12.extra_standard x b hmem hmem1
  extra_name_fresh := by
    intro x b hmem hnot0
    by_cases hmem1 : (x, b) ∈ Psi1
    · exact h01.extra_name_fresh x b hmem1 hnot0
    · have hnotNames1 := h12.extra_name_fresh x b hmem hmem1
      exact fun hx0 => hnotNames1
        (EvalCtx.Subctx.names_subset h01.subctx hx0)
  extra_name_unique := by
    intro x b0 b1 hmem0 hnot0 hmem1
    by_cases hmem01 : (x, b0) ∈ Psi1
    · by_cases hmem11 : (x, b1) ∈ Psi1
      · exact h01.extra_name_unique x b0 b1 hmem01 hnot0 hmem11
      · have hx1 : x ∈ Psi1.names := by
          obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp hmem01
          exact EvalCtx.mem_names_of_lookup hlookup0
        exact False.elim (h12.extra_name_fresh x b1 hmem1 hmem11 hx1)
    · exact h12.extra_name_unique x b0 b1 hmem0 hmem01 hmem1

/-- A basis found in a standard-only future of a raw-consistent root is valid
in any nonlinear extension of the root, provided its source type is valid
there.

For a root key, `RawConsistent.lookup_basisValid_mono` transports the
creation-time basis-validity proof through the supplied context inclusion.
For a non-root key, `CheckedStdFuture.extra_standard` identifies the basis as
`Basis.std (Basis.tof b)`, so `Basis.std_valid` applies directly. -/
theorem CheckedStdFuture.lookup_basisValid_of_rawConsistent
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma0 Gamma : NLCtx}
    {Psi0 Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (hconsistent : RawConsistent orc Delta Gamma0 Psi0 GammaV sigma rho)
    (hfuture : CheckedStdFuture Psi0 Psi)
    {x : VName} {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (hGamma : NLCtxIncl Gamma0 Gamma)
    {k : Kind} (htof : TValid Gamma (Basis.tof b) k) :
    BasisValid Gamma b := by
  classical
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  by_cases hroot : (x, b) ∈ Psi0
  · obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp hroot
    exact hconsistent.lookup_basisValid_mono hlookup0 hGamma
  · rw [hfuture.extra_standard x b hmem hroot]
    exact Basis.std_valid (Basis.tof b) htof

end RawCertifiedHereditaryStore
end GLang
