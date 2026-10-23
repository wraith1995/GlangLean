import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFreeStandardStore

namespace GLang
namespace RawCertifiedPairFreeStandardCreationPrefixStore

open OperationalStrengthening
open RawCertifiedConsistentPairStore
open RawCertifiedPairFreeStandardStore

/-- The single structural operation used by fixed-root certificate assembly.

The uniform store contains precisely the bases already present when `b` is
created.  The source/evaluator linkage covers all variables available to the
validity derivation, including variables appearing only in hidden typing
premises. -/
def CheckedFreeStdCreationPrefixLayerBuilder : Prop :=
  forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis},
    V2.CtxWF' Delta Gamma ->
    V2.TypingImplyEval Delta Gamma Psi ->
    CheckedFreeStdFreshDepthQuadUniformStore Psi Gamma ->
    Basis.BasisValid Gamma b ->
      CheckedFreeStdFreshDepthQuadFinite Psi Gamma b

end RawCertifiedPairFreeStandardCreationPrefixStore
end GLang
