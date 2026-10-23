import GLang.Proofs.Adequacy.Foundations.Agree

namespace GLang

/-- Application-facing agreement.  At Pi, the runtime function has exactly the
expected domain carrier and consumes the same raw value later recorded in the
dependent codomain stack. -/
noncomputable def RawAgree (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem) :
    List DVal -> List ValTy -> List ValValSem ->
    Ty -> ValTy -> BasisDenot -> DVal -> ValValSem -> Prop
  | Ds, Gv, Dv, .space s, .space sv, B, x, .array a =>
      LegacyAgree orc sigma rho Ds Gv Dv (.space s) (.space sv) B x (.array a)
  | _, _, _, .space _, .space _, _, _, .fn _ _ => False
  | Ds, Gv, Dv, .piTy tau0 tau1, .piTy tauv0 tauv1, B, x, y =>
      let T0 := denotTyAux sigma Ds tau0
      let Tv0 := denotValTyS orc rho Gv Dv tauv0
      exists f : Tv0.El -> Except DimError ValValSem,
        y = .fn Tv0.El f /\
        forall (x' : T0.El) (argVal : ValValSem) (arg : Tv0.El),
          ValValSem.toEl Tv0 argVal = .ok arg ->
          RawAgree orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis
            (T0.embed x') argVal ->
          exists out, f arg = .ok out /\
            RawAgree orc sigma rho (T0.embed x' :: Ds) (tauv0 :: Gv)
              (argVal :: Dv) tau1 tauv1 (B.applyEl x') (x.applyEl x') out
  | _, _, _, .space _, .piTy _ _, _, _, _ => False
  | _, _, _, .piTy _ _, .space _, _, _, _ => False
  termination_by _ _ _ tau tauv _ _ _ => Ty.size tau + ValTy.kindSize tauv
  decreasing_by all_goals simp only [Ty.size, ValTy.kindSize_piTy]; omega

/-- Exception-carrying boundary for `RawAgree`. -/
def RawResultAgree (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    (Ds : List DVal) (Gv : List ValTy) (Dv : List ValValSem)
    (tau : Ty) (tauv : ValTy) (B : BasisDenot) (x : DVal)
    (r : Except DimError ValValSem) : Prop :=
  exists y, r = .ok y /\ RawAgree orc sigma rho Ds Gv Dv tau tauv B x y

/-- Every raw-agreeing value decodes in its recorded value type.  At Pi this
uses the function's exact stored carrier; failures in its callback remain
delayed inside the successfully decoded function. -/
theorem RawAgree.toEl {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem} :
    forall {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
      {tau : Ty} {tauv : ValTy} {B : BasisDenot} {x : DVal}
      {y : ValValSem},
      RawAgree orc sigma rho Ds Gv Dv tau tauv B x y ->
      exists a : (denotValTyS orc rho Gv Dv tauv).El,
        ValValSem.toEl (denotValTyS orc rho Gv Dv tauv) y = .ok a := by
  intro Ds Gv Dv tau tauv B x y h
  cases tau with
  | space s =>
      cases tauv with
      | space sv =>
          cases y with
          | array a => exact ⟨a, rfl⟩
          | fn T f => simpa only [RawAgree] using h
      | piTy tauv0 tauv1 => simpa only [RawAgree] using h
  | piTy tau0 tau1 =>
      cases tauv with
      | space sv => simpa only [RawAgree] using h
      | piTy tauv0 tauv1 =>
          simp only [RawAgree] at h
          obtain ⟨f, rfl, _hf⟩ := h
          let Tv0 := denotValTyS orc rho Gv Dv tauv0
          let fam : Tv0.El -> ValTypeSem := fun arg =>
            denotValTyS orc rho (tauv0 :: Gv)
              (ValValSem.fromEl Tv0 arg :: Dv) tauv1
          let a : (arg : Tv0.El) -> Except DimError (fam arg).El := fun arg =>
            match f arg with
            | .error err => .error err
            | .ok out => ValValSem.toEl (fam arg) out
          refine ⟨a, ?_⟩
          simp [denotValTyS, ValValSem.toEl, Tv0, fam, a]
          funext arg
          cases f arg <;> rfl

/-- Basis-indexed dimensions using the same raw-argument convention as
`RawAgree`. -/
noncomputable def RawAgreeDimsAt (orc : FFSOracleSem) (sigma : DEnv)
    (rho : ValEnvSem) :
    List DVal -> List ValTy -> List ValValSem ->
    Ty -> ValTy -> BasisDenot -> Prop
  | Ds, Gv, Dv, .space s, .space sv, _B =>
      ValSpace.shpOf (orc rho Gv Dv) sv = srcShp sigma Ds s
  | Ds, Gv, Dv, .piTy tau0 tau1, .piTy tauv0 tauv1, B =>
      let T0 := denotTyAux sigma Ds tau0
      let Tv0 := denotValTyS orc rho Gv Dv tauv0
      RawAgreeDimsAt orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis /\
      forall (x' : T0.El) (argVal : ValValSem) (arg : Tv0.El),
        ValValSem.toEl Tv0 argVal = .ok arg ->
        RawAgree orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis
          (T0.embed x') argVal ->
        RawAgreeDimsAt orc sigma rho (T0.embed x' :: Ds)
          (tauv0 :: Gv) (argVal :: Dv) tau1 tauv1 (B.applyEl x')
  | _, _, _, .space _, .piTy _ _, _ => False
  | _, _, _, .piTy _ _, .space _, _ => False
  termination_by _ _ _ tau tauv _ => Ty.size tau + ValTy.kindSize tauv
  decreasing_by all_goals simp only [Ty.size, ValTy.kindSize_piTy]; omega

/-- Canonical value agreement. -/
noncomputable abbrev Agree := RawAgree

/-- Canonical exception-carrying result agreement. -/
abbrev ResultAgree := RawResultAgree

namespace Agree

/-- A canonically agreeing runtime value decodes at its recorded value type. -/
theorem toEl {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot} {x : DVal}
    {y : ValValSem}
    (h : Agree orc sigma rho Ds Gv Dv tau tauv B x y) :
    exists a : (denotValTyS orc rho Gv Dv tauv).El,
      ValValSem.toEl (denotValTyS orc rho Gv Dv tauv) y = .ok a :=
  RawAgree.toEl h

end Agree

namespace ResultAgree

/-- Canonical adequacy exposes a successful payload. -/
theorem isOk {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot} {x : DVal}
    {r : Except DimError ValValSem}
    (h : ResultAgree orc sigma rho Ds Gv Dv tau tauv B x r) :
    exists y, r = .ok y := by
  obtain ⟨y, hy, _⟩ := h
  exact ⟨y, hy⟩

/-- Consequently, canonical adequacy excludes every runtime dimension error. -/
theorem ne_error {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot} {x : DVal}
    {r : Except DimError ValValSem}
    (h : ResultAgree orc sigma rho Ds Gv Dv tau tauv B x r)
    (err : DimError) : r ≠ .error err := by
  intro hr
  obtain ⟨y, hy⟩ := h.isOk
  rw [hr] at hy
  cases hy

end ResultAgree

/-- Raw dimension agreement is invariant under replacing a fresh named value
binding by the corresponding value-type/value de Bruijn stack entries. -/
def RawAgreeDimsValueOpenPushAt (orc : FFSOracleSem) : Prop :=
  forall {sigma : DEnv} {rho : ValEnvSem} {y : VName}
      {tau : Ty} {tauv sigmav : ValTy} {d : DVal} {w : ValValSem}
      {B : BasisDenot},
    ValTy.lc sigmav -> y ∉ ValTy.fv sigmav -> y ∉ ValTy.fv tauv ->
    RawAgreeDimsAt orc sigma (rho.update y w) [d] [] [] tau
        (ValTy.openVar y sigmav tauv) B ->
      RawAgreeDimsAt orc sigma rho [d] [sigmav] [w] tau tauv B

/-- Raw adequate evaluator results obey the same fresh-name-to-de-Bruijn
presentation bridge.  The runtime value `w` is identical on both sides. -/
def RawResultAgreeValueOpenPushAt (orc : FFSOracleSem) : Prop :=
  forall {sigma : DEnv} {rho : ValEnvSem} {y : VName}
      {tau : Ty} {tauv sigmav : ValTy} {d : DVal} {w : ValValSem}
      {B : BasisDenot} {x : DVal} {e : ValExpr},
    ValTy.lc sigmav -> ValExpr.lc (ValExpr.openVar y sigmav e) ->
    y ∉ ValTy.fv sigmav ->
    y ∉ ValTy.fv tauv -> y ∉ ValExpr.fv e ->
    RawAgreeDimsAt orc sigma (rho.update y w) [d] [] [] tau
        (ValTy.openVar y sigmav tauv) B ->
    RawResultAgree orc sigma (rho.update y w) [d] [] [] tau
        (ValTy.openVar y sigmav tauv) B x
        (denotValB_semS orc (rho.update y w) [] []
          (ValExpr.openVar y sigmav e)) ->
      RawResultAgree orc sigma rho [d] [sigmav] [w] tau tauv B x
        (denotValB_semS orc rho [sigmav] [w] e)

/-! ## Fresh-name/de-Bruijn oracle boundaries -/

/-- Primitive oracle coherence for the two presentations of one fresh value
binder. `G/D` is the dependent prefix inside the distinguished slot, ordered
innermost first. Each queried term is opened at the *current* telescope depth
`G.length`; entries of `G` themselves are closed at their declaration
depth by `closePrefix`.

The statement equates only the natural number at one FFS leaf. It contains no
evaluator result or adequacy judgment.  The distinguished domain is required
to be locally closed: current obtains this from its well-formed evaluator
world, and the premise excludes the known self-referential malformed-domain
counterexample. -/
def RawValueOpenPushOracleCoherent (orc : FFSOracleSem) : Prop :=
  forall {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
      {G : List ValTy} {D : List ValValSem} {p : ValFFSProp}
      {s : ValSpace} {e : ValExpr},
    G.length = D.length ->
    ValTy.lc sigmaV ->
    y ∉ ValTy.fv sigmaV ->
    (forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) ->
    y ∉ ValSpace.fv s -> y ∉ ValExpr.fv e ->
    orc (rho.update y w) (ValTy.closePrefix (.var y sigmaV) G) D p
        (ValSpace.openRec G.length (.var y sigmaV) s)
        (ValExpr.openRec G.length (.var y sigmaV) e) =
      orc rho (G ++ [sigmaV]) (D ++ [w]) p s e

/-- Evaluator-level presentation coherence, restricted to the actual
closed-telescope shape consumed by nonlinear binder adequacy. -/
def RawValueOpenPushEvalCoherent (orc : FFSOracleSem) : Prop :=
  forall {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
      {e : ValExpr},
    ValTy.lc sigmaV ->
    ValExpr.lc (ValExpr.openVar y sigmaV e) ->
    y ∉ ValTy.fv sigmaV -> y ∉ ValExpr.fv e ->
    denotValB_semS orc (rho.update y w) [] []
        (ValExpr.openVar y sigmaV e) =
      denotValB_semS orc rho [sigmaV] [w] e

/-- The raw adequacy oracle contract. -/
structure RawAdequacyOracleSpec (orc : FFSOracleSem) : Prop
    extends OracleSpec orc where
  valueOpenPushOracleCoherent : RawValueOpenPushOracleCoherent orc

instance {orc : FFSOracleSem} : Coe (RawAdequacyOracleSpec orc) (OracleSpec orc) where
  coe h := h.toOracleSpec

end GLang
