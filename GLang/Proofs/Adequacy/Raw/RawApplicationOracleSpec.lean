import GLang.Proofs.Adequacy.Raw.RawAgreement
import GLang.Proofs.Value.Runtime.RuntimeValueTotalSemanticSubstitution

namespace GLang

structure RawApplicationOracleSpec (orc : FFSOracleSem) : Prop
    extends RawAdequacyOracleSpec orc where
  codomainSubstitution : RuntimeValue.TotalSubstitution.CodomainLaw orc

instance {orc : FFSOracleSem} : Coe (RawApplicationOracleSpec orc)
    (RawAdequacyOracleSpec orc) := ⟨RawApplicationOracleSpec.toRawAdequacyOracleSpec⟩

theorem directApplicationOracle_spec : RawApplicationOracleSpec directOracle :=
  ⟨directOracle_spec, RuntimeValue.TotalSubstitution.codomainLaw⟩

end GLang
