import GLang.Proofs.Adequacy.Raw.Conversion.RawCobInferMaster

/-!
# Provider interfaces for the direct raw adequacy assembly

The raw proof is mutually recursive, but its reusable components should not
need to import the eventual master theorem.  These small interfaces name the
three edges that remain after space/type adequacy and COB inference have been
factored into independent recursors:

* full term trace plus inferred-space facts;
* semantic change-of-basis agreement;
* their pairing with the already-complete COB inference provider.

The restricted `RawTermFactsProvider` used by FFS leaves is a projection of
the full term provider, not a second assumption.
-/

namespace GLang

/-- The complete conclusion sought for every strengthened term derivation. -/
def RawFullTermFactsProvider (orc : FFSOracleSem) : Prop :=
  forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy},
    S.Term Delta Gamma Psi e b v tauV ->
      RawTermDofFactsSubctx orc Delta Gamma Psi e b v tauV

/-- Forget the general linear-context and result-type cases, retaining exactly
the back-edge consumed by the four FFS space constructors and `image_svds`. -/
theorem RawFullTermFactsProvider.toFFSWitness
    {orc : FFSOracleSem} (hterm : RawFullTermFactsProvider orc) :
    RawTermFactsProvider orc := by
  intro Gamma Psi e b v sv h
  exact hterm h

/-- Semantic agreement for every strengthened change-of-basis derivation. -/
def RawCobAgreeProvider (orc : FFSOracleSem) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {bSrc bTgt : Basis}
    {env : ValExpr},
    S.Cob Gamma Psi bSrc env bTgt ->
      RawMCobSubctx orc Gamma Psi bSrc env bTgt

/-- The complete paired conclusion sought for every strengthened COB
derivation. -/
def RawCobFactsProvider (orc : FFSOracleSem) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {bSrc bTgt : Basis}
    {env : ValExpr},
    S.Cob Gamma Psi bSrc env bTgt ->
      RawCobFactsSubctx orc Gamma Psi bSrc env bTgt

/-- Exact-basis dimension agreement for every strengthened `S.TyAt`
derivation. -/
def RawTyAtProvider (orc : FFSOracleSem) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {tauV : ValTy},
    S.TyAt Gamma Psi b tauV ->
      RawMTyAtSubctx orc Gamma Psi b tauV

/-- A full term provider closes the only back-edge of space adequacy. -/
theorem RawFullTermFactsProvider.toSpace
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    (hterm : RawFullTermFactsProvider orc) :
    RawSpaceProvider orc :=
  S.Space.rawMasterOfTerm hspec hterm.toFFSWitness

/-- Exact type adequacy then follows from the resulting space provider. -/
theorem RawFullTermFactsProvider.toTyAt
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
    (hterm : RawFullTermFactsProvider orc) :
    RawTyAtProvider orc :=
  S.TyAt.rawMasterOfSpace hspec
    (hterm.toSpace hspec.toOracleSpec)

/-- COB inference also closes from the same full term provider: its term
dependency is restricted to closed, space-valued FFS witnesses. -/
theorem RawFullTermFactsProvider.toCobInfer
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    (hterm : RawFullTermFactsProvider orc) :
    RawCobInferProvider orc :=
  S.Cob.rawInferMaster hspec (hterm.toSpace hspec)
    hterm.toFFSWitness

/-- Pair an independently assembled semantic agreement provider with the
already-complete syntactic inference provider. -/
theorem rawCobFactsProvider_of
    {orc : FFSOracleSem}
    (hagree : RawCobAgreeProvider orc)
    (hinfer : RawCobInferProvider orc) :
    RawCobFactsProvider orc := by
  intro Gamma Psi bSrc bTgt env h
  exact ⟨hagree h, hinfer h⟩

/-- Once semantic COB agreement is supplied, a full term provider supplies
the other half of every paired COB conclusion constructively. -/
theorem RawFullTermFactsProvider.toCobFacts
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    (hterm : RawFullTermFactsProvider orc)
    (hagree : RawCobAgreeProvider orc) :
    RawCobFactsProvider orc :=
  rawCobFactsProvider_of hagree (hterm.toCobInfer hspec)

/-- Semantic agreement is the first projection of the paired provider. -/
theorem RawCobFactsProvider.toAgree
    {orc : FFSOracleSem} (h : RawCobFactsProvider orc) :
    RawCobAgreeProvider orc := by
  intro Gamma Psi bSrc bTgt env hcob
  exact (h hcob).agree

/-- COB inference is the second projection of the paired provider. -/
theorem RawCobFactsProvider.toInfer
    {orc : FFSOracleSem} (h : RawCobFactsProvider orc) :
    RawCobInferProvider orc := by
  intro Gamma Psi bSrc bTgt env hcob
  exact (h hcob).infer

end GLang
