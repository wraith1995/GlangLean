import GLang.Proofs.Adequacy.Raw.Context.RawConsistentRank
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedFutureLookupValidity

/-!
# Ranked lookup facts for automatic checked certificates

`RawConsistent` installs a basis only after every name free in that basis is
already represented by the evaluator prefix.  The pair-creation-rank theorem
turns that telescope invariant into a chosen exact predecessor lookup used by
a well-founded certificate construction.

This module also exposes the complementary root/future split at the level of
an exact lookup value.  Neither result adds a premise to consistency.
-/

namespace GLang
namespace RawConsistentRank

open RawCertifiedHereditaryStore

/-- One exact-pair rank simultaneously orders every root lookup.  Each name
free in a stored basis chooses one concrete predecessor representation; no
obligation is imposed on every other representation of that source name. -/
theorem RawConsistent.exists_ranked_lookup_predecessors
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    exists rank : (VName × Basis) -> Nat,
      forall {x : VName} {b : Basis} {v : ValExpr},
        EvalCtx.lookup Psi (x, b) = some v ->
        forall y, y ∈ Basis.fv b ->
          exists bY : Basis, exists vY : ValExpr,
            EvalCtx.lookup Psi (y, bY) = some vY /\
              rank (y, bY) < rank (x, b) := by
  exact EvalCtxCreationRank.exists_ranked_lookup_predecessors
    (ofRawConsistent h)

/-- An exact lookup in a standard-only future is either the unchanged root
lookup (including the same stored value), or a genuinely new standard key at
a name absent from the root evaluator. -/
theorem CheckedStdFuture.lookup_root_or_standard
    {Psi0 Psi : EvalCtx} (h : CheckedStdFuture Psi0 Psi)
    {x : VName} {b : Basis} {v : ValExpr}
    (hlookup : EvalCtx.lookup Psi (x, b) = some v) :
    EvalCtx.lookup Psi0 (x, b) = some v \/
      ((x, b) ∉ Psi0 /\ b = Basis.std (Basis.tof b) /\
        x ∉ Psi0.names) := by
  classical
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  by_cases hroot : (x, b) ∈ Psi0
  · obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp hroot
    have hlookup1 := h.subctx (x, b) v0 hlookup0
    have hv : v0 = v := Option.some.inj (hlookup1.symm.trans hlookup)
    subst v0
    exact Or.inl hlookup0
  · exact Or.inr
      ⟨hroot, h.extra_standard x b hmem hroot,
        h.extra_name_fresh x b hmem hroot⟩

end RawConsistentRank
end GLang
