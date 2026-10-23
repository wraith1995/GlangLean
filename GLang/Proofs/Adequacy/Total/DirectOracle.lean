import GLang.Proofs.Adequacy.Total.DirectOracleAssembly

/-!
# Constructive direct FFS oracle

This facade exposes the well-founded FFS oracle together with the complete
semantic specification needed by raw adequacy.  The construction has no fuel
approximation and assumes no evaluator-coherence axiom: locality and the
fresh-name/de-Bruijn transport are proved by the imported modules.
-/

namespace GLang

/-- The constructive, well-founded FFS oracle used by adequacy. -/
noncomputable abbrev directOracle : FFSOracleSem :=
  DirectOracleWF.derivedDirectOracle

/-- The direct oracle satisfies every oracle boundary required by raw adequacy. -/
theorem directOracle_spec : RawAdequacyOracleSpec directOracle :=
  DirectOracleAssembly.derivedDirectOracle_rawAdequacySpec

end GLang
