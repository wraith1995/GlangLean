import GLang.Proofs.Adequacy.Raw.RawSpaceFFSAdequacy

/-!
# Provider-parameterized raw space and exact-type recursion

This module assembles the complete `S.Space` and `S.TyAt` raw adequacy
components without a residual record or global master.  The only back-edge
needed by an FFS space leaf is the already paired raw trace/dimension fact for
its witness term, exposed through `RawTermFactsProvider`.
-/

namespace GLang

/-- The precise term back-edge consumed by the four FFS `S.Space` leaves.
It is intentionally restricted to closed-linear-context, space-valued terms,
which is exactly the shape of every witness premise in `S.Space`. -/
def RawTermFactsProvider (orc : FFSOracleSem) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {b : Basis}
    {v : ValExpr} {sv : ValSpace},
    S.Term ∅ Gamma Psi e b v (.space sv) ->
      RawTermDofFactsSubctx orc ∅ Gamma Psi e b v (.space sv)

/-- The assembled raw conclusion for every strengthened space derivation. -/
def RawSpaceProvider (orc : FFSOracleSem) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {s : Space} {sv : ValSpace},
    S.Space Gamma Psi s sv -> RawMSpaceSubctx orc Gamma Psi s sv

/-! ## Complete space recursion -/

/-- Assemble every `S.Space` constructor from structural raw arms and the
paired witness facts supplied at the four FFS leaves. -/
theorem S.Space.rawMasterOfTerm
    {orc : FFSOracleSem} (hspec : OracleSpec orc)
    (hterm : RawTermFactsProvider orc) : RawSpaceProvider orc := by
  intro Gamma Psi s sv h
  refine h.rec
    (motive_1 := fun Gamma Psi s sv _ =>
      RawMSpaceSubctx orc Gamma Psi s sv)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    -- `S.Space` (9)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    -- `S.Ty` (2)
    ?_ ?_
    -- `S.TyAt` (2)
    ?_ ?_
    -- `S.Cob` (13)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    -- `S.Term` (28)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro Gamma Psi
    exact raw_arm_space_real
  · intro Gamma Psi
    exact raw_arm_space_empty
  · intro Gamma Psi s sv hs h ih
    exact raw_arm_space_dual hs h ih
  · intro Gamma Psi s0 s1 e b v svb hs hb hcompat hsvb he
      ihSpace _ihTerm
    exact raw_arm_space_ker hspec hs hb hcompat hsvb he ihSpace
      (hterm he)
  · intro Gamma Psi s0 s1 e b v svb hs hb hcompat hsvb he
      ihSpace _ihTerm
    exact raw_arm_space_coker hspec hs hb hcompat hsvb he ihSpace
      (hterm he)
  · intro Gamma Psi s0 s1 e b v svb hs hb hcompat hsvb he
      ihSpace _ihTerm
    exact raw_arm_space_img hspec hs hb hcompat hsvb he ihSpace
      (hterm he)
  · intro Gamma Psi s0 s1 e b v svb hs hb hcompat hsvb he
      ihSpace _ihTerm
    exact raw_arm_space_coimg hspec hs hb hcompat hsvb he ihSpace
      (hterm he)
  · intro Gamma Psi s0 s1 sv0 sv1 hs h0 h1 ih0 ih1
    exact raw_arm_space_tprod hs h0 h1 ih0 ih1
  · intro Gamma Psi s0 s1 sv0 sv1 hs h0 h1 ih0 ih1
    exact raw_arm_space_dsum hs h0 h1 ih0 ih1
  all_goals (intros; trivial)

/-! ## Complete exact-basis type recursion -/

/-- Assemble every `S.TyAt` constructor from a complete raw space provider.

For each evaluator-context extension we first transport the strengthened
derivation, then invoke the existing exact-basis structural recursion over
that transported derivation.  The space callback is obtained by taking the
current-world projection of `RawSpaceProvider`. -/
theorem S.TyAt.rawMasterOfSpace
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
    (hspace : RawSpaceProvider orc) :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {tauV : ValTy},
      S.TyAt Gamma Psi b tauV ->
        RawMTyAtSubctx orc Gamma Psi b tauV := by
  intro Gamma Psi b tauV hTy Psi' hsub
  have hspaceCurrent : RawSpaceClaim orc (RawTypedConsistent orc) := by
    intro Gamma0 Psi0 s0 sv0 hs0
    exact RawMSpaceSubctx.current (hspace hs0)
  exact rawMTyAt_holds_rawConsistent hspec hspaceCurrent
    (hTy.mono hsub)

/-- Close both the space and exact-type components from the single term-facts
back-edge used by the FFS leaves. -/
theorem S.TyAt.rawMasterOfTerm
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
    (hterm : RawTermFactsProvider orc) :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis} {tauV : ValTy},
      S.TyAt Gamma Psi b tauV ->
        RawMTyAtSubctx orc Gamma Psi b tauV :=
  S.TyAt.rawMasterOfSpace hspec
    (S.Space.rawMasterOfTerm
      hspec.toOracleSpec hterm)

/-- Read the exact-basis raw type fact attached to any strengthened term. -/
theorem S.Term.rawTyAtMasterOfTerm
    {orc : FFSOracleSem} (hspec : RawAdequacyOracleSpec orc)
    (hterm : RawTermFactsProvider orc)
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {e : GLang.Term}
    {b : Basis} {v : ValExpr} {tauV : ValTy}
    (h : S.Term Delta Gamma Psi e b v tauV) :
    RawMTyAtSubctx orc Gamma Psi b tauV :=
  S.TyAt.rawMasterOfTerm hspec hterm h.tyAt

end GLang
