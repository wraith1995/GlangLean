import GLang.Proofs.Adequacy.Foundations.Strengthened
import GLang.Annotated.Denotation
import GLang.Proofs.Basis.Binding
import GLang.Value.Supporting.StrictTyping
import GLang.Proofs.Value.Binding.ValueLN
import GLang.Proofs.Preservation.ValuePreservationV2

namespace GLang

open Basis (BasisValid)

noncomputable def DVal.applyEl {T : Type} (d : DVal) (t : T) : DVal :=
  match d with
  | .pi T' g =>
      haveI := Classical.dec (T = T')
      if h : T = T' then g (h ▸ t) else DVal.default
  | .hil _ => DVal.default

noncomputable def BasisDenot.applyEl {T : Type} (b : BasisDenot) (t : T) : BasisDenot :=
  match b with
  | .frame T' _ fb =>
      haveI := Classical.dec (T = T')
      if h : T = T' then fb (h ▸ t) else BasisDenot.default
  | .vecs _ _ => BasisDenot.default

noncomputable def ValValSem.applyEl {T : Type} (y : ValValSem) (t : T) :
    Except DimError ValValSem :=
  match y with
  | .fn T' f =>
      haveI := Classical.dec (T = T')
      if h : T = T' then f (h ▸ t) else .error .mismatch
  | .array _ => .error .mismatch

@[simp] theorem DVal.applyEl_pi {T : Type} (g : T → DVal) (x' : T) :
    (DVal.pi T g).applyEl x' = g x' := dif_pos rfl

@[simp] theorem BasisDenot.applyEl_frame {T : Type} (domB : BasisDenot) (fb : T → BasisDenot)
    (x' : T) : (BasisDenot.frame T domB fb).applyEl x' = fb x' := dif_pos rfl

@[simp] theorem ValValSem.applyEl_fn {T : Type} (f : T → Except DimError ValValSem) (y' : T) :
    (ValValSem.fn T f).applyEl y' = f y' := dif_pos rfl

noncomputable def srcShp (σ : DEnv) (Δs : List DVal) : Space → List Nat
  | .empty        => [0]
  | .real         => [1]
  | .dual s       => srcShp σ Δs s
  | .dsum s₀ s₁   =>
      [Module.finrank ℝ (denotSpaceAux σ Δs s₀).carrier
        + Module.finrank ℝ (denotSpaceAux σ Δs s₁).carrier]
  | .tprod s₀ s₁  =>
      [Module.finrank ℝ (denotSpaceAux σ Δs s₀).carrier,
       Module.finrank ℝ (denotSpaceAux σ Δs s₁).carrier]
  | s             => [Module.finrank ℝ (denotSpaceAux σ Δs s).carrier]

/-! ## `def:agree` — value agreement `x ≡_B y` -/

noncomputable def LegacyAgree (orc : FFSOracleSem) (σ : DEnv) (ρ : ValEnvSem) :
    List DVal → List ValTy → List ValValSem →
    Ty → ValTy → BasisDenot → DVal → ValValSem → Prop
  | Δs, Γv, Δv, .space s, .space sv, B, x, .array a =>
      let V := denotSpaceAux σ Δs s
      let vs := B.atSpace V
      let N := ValSpace.dof (orc ρ Γv Δv) sv
      vs.length = N ∧ a.length = N ∧
        x.atSpace V = ∑ i : Fin N, a.get i.val • vs.getD i.val 0
  | _, _, _, .space _, .space _, _, _, .fn _ _ => False
  | Δs, Γv, Δv, .piTy τ₀ τ₁, .piTy τv₀ τv₁, B, x, y =>
      let T₀ := denotTyAux σ Δs τ₀
      let Tv₀ := denotValTyS orc ρ Γv Δv τv₀
      ∀ (x' : T₀.El) (y' : Tv₀.El),
        LegacyAgree orc σ ρ Δs Γv Δv τ₀ τv₀ B.domainBasis (T₀.embed x') (ValValSem.fromEl Tv₀ y') →
        ∃ y'', y.applyEl y' = .ok y'' ∧
          LegacyAgree orc σ ρ (T₀.embed x' :: Δs) (τv₀ :: Γv) (ValValSem.fromEl Tv₀ y' :: Δv)
            τ₁ τv₁ (B.applyEl x') (x.applyEl x') y''
  | _, _, _, .space _,  .piTy _ _, _, _, _ => False
  | _, _, _, .piTy _ _, .space _,  _, _, _ => False

/-- Agreement lifted to the exception-carrying active denotation.  This is
    the adequacy boundary: an adequate denotation has a successful payload,
    so `DimError` is impossible. -/
def LegacyResultAgree (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    (Ds : List DVal) (Gv : List ValTy) (Dv : List ValValSem)
    (tau : Ty) (tauv : ValTy) (B : BasisDenot) (x : DVal)
    (r : Except DimError ValValSem) : Prop :=
  ∃ y, r = .ok y ∧ LegacyAgree orc sigma rho Ds Gv Dv tau tauv B x y

namespace LegacyResultAgree

/-- Adequacy exposes a successful payload; in particular, it does not reinterpret
    a runtime dimension failure as a value. -/
theorem isOk {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot} {x : DVal}
    {r : Except DimError ValValSem}
    (h : LegacyResultAgree orc sigma rho Ds Gv Dv tau tauv B x r) :
    ∃ y, r = .ok y := by
  obtain ⟨y, hy, _⟩ := h
  exact ⟨y, hy⟩

/-- An adequate result cannot be any `DimError`. -/
theorem ne_error {orc : FFSOracleSem} {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot} {x : DVal}
    {r : Except DimError ValValSem}
    (h : LegacyResultAgree orc sigma rho Ds Gv Dv tau tauv B x r) (err : DimError) :
    r ≠ .error err := by
  intro hr
  obtain ⟨y, hy⟩ := h.isOk
  rw [hr] at hy
  cases hy

end LegacyResultAgree

/-! ## `def:agreedims` — dimension agreement `⟦τ⟧σ ≡ ⟦τv⟧ρ` -/

noncomputable def LegacyAgreeDims (orc : FFSOracleSem) (σ : DEnv) (ρ : ValEnvSem) :
    List DVal → List ValTy → List ValValSem → Ty → ValTy → Prop
  | Δs, Γv, Δv, .space s, .space sv =>
      ValSpace.shpOf (orc ρ Γv Δv) sv = srcShp σ Δs s
  | Δs, Γv, Δv, .piTy τ₀ τ₁, .piTy τv₀ τv₁ =>
      let T₀ := denotTyAux σ Δs τ₀
      let Tv₀ := denotValTyS orc ρ Γv Δv τv₀
      LegacyAgreeDims orc σ ρ Δs Γv Δv τ₀ τv₀ ∧
      ∃ B : BasisDenot, ∀ (x' : T₀.El) (y' : Tv₀.El),
        LegacyAgree orc σ ρ Δs Γv Δv τ₀ τv₀ B (T₀.embed x') (ValValSem.fromEl Tv₀ y') →
        LegacyAgreeDims orc σ ρ (T₀.embed x' :: Δs) (τv₀ :: Γv) (ValValSem.fromEl Tv₀ y' :: Δv) τ₁ τv₁
  | _, _, _, .space _,  .piTy _ _ => False
  | _, _, _, .piTy _ _, .space _  => False

/-- Dimension agreement at one particular semantic basis. -/
noncomputable def LegacyAgreeDimsAt (orc : FFSOracleSem) (σ : DEnv) (ρ : ValEnvSem) :
    List DVal → List ValTy → List ValValSem →
    Ty → ValTy → BasisDenot → Prop
  | Δs, Γv, Δv, .space s, .space sv, _B =>
      ValSpace.shpOf (orc ρ Γv Δv) sv = srcShp σ Δs s
  | Δs, Γv, Δv, .piTy τ₀ τ₁, .piTy τv₀ τv₁, B =>
      let T₀ := denotTyAux σ Δs τ₀
      let Tv₀ := denotValTyS orc ρ Γv Δv τv₀
      LegacyAgreeDimsAt orc σ ρ Δs Γv Δv τ₀ τv₀ B.domainBasis ∧
      ∀ (x' : T₀.El) (y' : Tv₀.El),
        LegacyAgree orc σ ρ Δs Γv Δv τ₀ τv₀ B.domainBasis
          (T₀.embed x') (ValValSem.fromEl Tv₀ y') →
        LegacyAgreeDimsAt orc σ ρ (T₀.embed x' :: Δs)
          (τv₀ :: Γv) (ValValSem.fromEl Tv₀ y' :: Δv)
          τ₁ τv₁ (B.applyEl x')
  | _, _, _, .space _, .piTy _ _, _ => False
  | _, _, _, .piTy _ _, .space _, _ => False
  termination_by _ _ _ τ τv _ => Ty.size τ + ValTy.kindSize τv
  decreasing_by all_goals simp only [Ty.size, ValTy.kindSize_piTy]; omega

theorem LegacyAgreeDimsAt.toAgreeDims {orc : FFSOracleSem} {σ : DEnv} {ρ : ValEnvSem} :
    ∀ {Δs : List DVal} {Γv : List ValTy} {Δv : List ValValSem}
      {τ : Ty} {τv : ValTy} {B : BasisDenot},
      LegacyAgreeDimsAt orc σ ρ Δs Γv Δv τ τv B →
      LegacyAgreeDims orc σ ρ Δs Γv Δv τ τv := by
  intro Δs Γv Δv τ τv B h
  generalize hn : ValTy.kindSize τv = n
  induction n using Nat.strong_induction_on generalizing Δs Γv Δv τ τv B with
  | h n ih =>
      cases τ <;> cases τv <;>
        simp only [LegacyAgreeDimsAt, LegacyAgreeDims] at h ⊢
      · exact h
      · rename_i τ₀ τ₁ τv₀ τv₁
        refine ⟨?_, ⟨B.domainBasis, ?_⟩⟩
        · apply ih (ValTy.kindSize τv₀)
          · simp only [ValTy.kindSize_piTy] at hn
            omega
          · exact h.1
          · rfl
        · intro x' y' ha
          apply ih (ValTy.kindSize τv₁)
          · simp only [ValTy.kindSize_piTy] at hn
            omega
          · exact h.2 x' y' ha
          · rfl

/-! ## Claim 2 — change-of-basis agreement -/

def CobAgree (orc : FFSOracleSem) (σ : DEnv) (ρ : ValEnvSem)
    (bSrc bTgt : Basis) (env : ValExpr) : Prop :=
  let V := denotSpace σ (Basis.sof bSrc)
  let S := (denotBasis σ bSrc).atSpace V
  let T := (denotBasis σ bTgt).atSpace V
  let N := S.length
  T.length = N ∧
  ∃ a : FlatArray, denotValB_semS orc ρ [] [] env = .ok (.array a) ∧ a.length = N * N ∧
    ∀ j : Fin N, S.getD j.val 0 = ∑ i : Fin N, a.get (j.val * N + i.val) • T.getD i.val 0

/-! ## `def:allCtxAgree` — consistent environments -/

inductive LegacyConsistent (orc : FFSOracleSem) :
    LCtx → NLCtx → EvalCtx → ValCtx → DEnv → ValEnvSem → Prop
  | empty {ρ : ValEnvSem} : LegacyConsistent orc ∅ ∅ ∅ ∅ ⟨∅⟩ ρ
  | extend_lin {Δ Γ Ψ Γv σ ρ x b v τv xs s yv}
      (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ)
      (hx : x ∉ Δ ∧ x ∉ Γ ∧ ∀ b', (x, b') ∉ Ψ)
      (htof : Basis.tof b = .space s)
      (hb : BasisValid Γ b) (hfvb : Basis.fv b ⊆ Ψ.keyNames)
      (hτv : ValTy.EvalT Ψ (Basis.tof b) τv)
      (hinfer : ValExpr.inferType v = τv)
      (hinferSpace : ValExpr.inferSpaceCtx [] v = ValTy.spaceOf τv)
      (hfvv : ValExpr.fv v ⊆ (Ψ.extend x b v).keyNames) (hlc : ValExpr.lc v)
      (hnr : x ∉ ValExpr.fv v ∨ ∃ τ, v = .var x τ)
      (hanchor : ∀ b₀ b₁ τv₀ τv₁ body,
        b = .frame b₀ b₁ → v = .vlam τv₀ τv₁ body →
        ∃ L : Finset VName, ∀ y, y ∉ L →
          ValTy.EvalT (Ψ.extend x b v |>.extend y b₀ (.var y τv₀))
            (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁))
      (hxs : xs.matchesShape (denotTy σ (Basis.tof b)))
      (hden : denotValB_semS orc ρ [] [] v = .ok yv)
      (hagree : LegacyAgree orc σ ρ [] [] [] (Basis.tof b) τv (denotBasis σ b) xs yv)
      (hdims : LegacyAgreeDims orc σ ρ [] [] [] (Basis.tof b) τv)
      (hcert : ∃ Γcert, NLCtxIncl Γcert Γ ∧ S.Ty Γcert Ψ (Basis.tof b) τv) :
      LegacyConsistent orc (Finmap.insert x s Δ) Γ (Ψ.extend x b v) (Finmap.insert x τv Γv)
        (σ.bind x xs) (ρ.update x yv)
  | extend_nl {Δ Γ Ψ Γv σ ρ x b v τv xs yv}
      (h : LegacyConsistent orc Δ Γ Ψ Γv σ ρ)
      (hx : x ∉ Δ ∧ x ∉ Γ ∧ ∀ b', (x, b') ∉ Ψ)
      (hb : BasisValid Γ b) (hfvb : Basis.fv b ⊆ Ψ.keyNames)
      (hτv : ValTy.EvalT Ψ (Basis.tof b) τv)
      (hinfer : ValExpr.inferType v = τv)
      (hinferSpace : ValExpr.inferSpaceCtx [] v = ValTy.spaceOf τv)
      (hfvv : ValExpr.fv v ⊆ (Ψ.extend x b v).keyNames) (hlc : ValExpr.lc v)
      (hnr : x ∉ ValExpr.fv v ∨ ∃ τ, v = .var x τ)
      (hanchor : ∀ b₀ b₁ τv₀ τv₁ body,
        b = .frame b₀ b₁ → v = .vlam τv₀ τv₁ body →
        ∃ L : Finset VName, ∀ y, y ∉ L →
          ValTy.EvalT (Ψ.extend x b v |>.extend y b₀ (.var y τv₀))
            (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁))
      (hxs : xs.matchesShape (denotTy σ (Basis.tof b)))
      (hden : denotValB_semS orc ρ [] [] v = .ok yv)
      (hagree : LegacyAgree orc σ ρ [] [] [] (Basis.tof b) τv (denotBasis σ b) xs yv)
      (hdims : LegacyAgreeDims orc σ ρ [] [] [] (Basis.tof b) τv)
      (hcert : ∃ Γcert, NLCtxIncl Γcert Γ ∧ S.Ty Γcert Ψ (Basis.tof b) τv) :
      LegacyConsistent orc Δ (Finmap.insert x (Basis.tof b) Γ) (Ψ.extend x b v)
        (Finmap.insert x τv Γv) (σ.bind x xs) (ρ.update x yv)

/-! ## Adequacy-level oracle contract -/

/-- Remove a distinguished value slot lying immediately outside `G` from
the types of the entries in `G`.  Contexts are innermost-first, so the entry
at the head is opened at the number of entries outside it.  For example,
`closePrefix u [beta, alpha]` opens `beta` at one and `alpha` at zero. -/
def ValTy.closePrefix (u : ValExpr) : List ValTy → List ValTy
  | [] => []
  | tau :: G => ValTy.openRec G.length u tau :: ValTy.closePrefix u G

/-- Primitive value-substitution coherence at one FFS oracle leaf.

The left side evaluates a query while the distinguished argument still
occupies the outermost de Bruijn slot.  The right side removes that slot and
opens the dependent prefix and queried syntax with the closed argument.
Only the natural-number answer of this one FFS query is equated; evaluator
results and adequacy judgments are deliberately absent. -/
def RawValueSubstOracleCoherent (orc : FFSOracleSem) : Prop :=
  ∀ {rho : ValEnvSem} {u : ValExpr} {sigmaV : ValTy} {w : ValValSem}
      {G : List ValTy} {D : List ValValSem} {p : ValFFSProp}
      {s : ValSpace} {e : ValExpr},
    G.length = D.length →
    ValExpr.lc u →
    ValExpr.inferTypeCtx [] u = sigmaV →
    denotValB_semS orc rho [] [] u = .ok w →
    orc rho (G ++ [sigmaV]) (D ++ [w]) p s e =
      orc rho (ValTy.closePrefix u G) D p
        (ValSpace.openRec G.length u s)
        (ValExpr.openRec G.length u e)

/-- Value-side binder coherence for dimension agreement.

The two judgments below encode the same locally-nameless binding in the two
forms used by the strengthened operational semantics and by `LegacyAgreeDims`:

* on the left, the body is opened with a fresh name and its value is stored in
  the named environment;
* on the right, the body remains unopened and its type/value are pushed on the
  de Bruijn stacks.

This is an oracle law because an FFS leaf observes `(ρ, Γv, Δv)`.  Ordinary
source binding transport is proved separately and does not occur here. -/
def AgreeDimsValueOpenPush (orc : FFSOracleSem) : Prop :=
  ∀ {σ : DEnv} {ρ : ValEnvSem} {y : VName} {τ : Ty} {τv σv : ValTy}
      {d : DVal} {w : ValValSem},
    y ∉ ValTy.fv σv → y ∉ ValTy.fv τv →
    LegacyAgreeDims orc σ (ρ.update y w) [d] [] [] τ
        (ValTy.openVar y σv τv) →
      LegacyAgreeDims orc σ ρ [d] [σv] [w] τ τv

/-- Full-result value-side binder coherence.

This is the evaluator-level companion of `AgreeDimsValueOpenPush`.  Its
`namedDims` premise is deliberate: the opened codomain type IH supplies that
fact in `nllam`, and without it even base-kind `LegacyAgree` cannot be transported
between the two oracle worlds. The law remains an explicit theorem parameter
while `Adequacy/ValueOpenPushSpike.lean` audits a structural proof (all SVD/GSVD
array constructors are already covered there).

The source environment and source stack have already been normalized by the
proved source opening lemmas.  Only the value presentation changes:

* named: `ρ.update y w`, opened syntax, empty value stacks;
* nameless: `ρ`, unopened syntax, with `σv`/`w` pushed at slot zero. -/
def ResultAgreeValueOpenPush (orc : FFSOracleSem) : Prop :=
  ∀ {σ : DEnv} {ρ : ValEnvSem} {y : VName} {τ : Ty} {τv σv : ValTy}
      {d : DVal} {w : ValValSem} {B : BasisDenot} {x : DVal} {e : ValExpr},
    y ∉ ValTy.fv σv → y ∉ ValTy.fv τv → y ∉ ValExpr.fv e →
    LegacyAgreeDims orc σ (ρ.update y w) [d] [] [] τ
        (ValTy.openVar y σv τv) →
    LegacyResultAgree orc σ (ρ.update y w) [d] [] [] τ
        (ValTy.openVar y σv τv) B x
        (denotValB_semS orc (ρ.update y w) [] []
          (ValExpr.openVar y σv e)) →
      LegacyResultAgree orc σ ρ [d] [σv] [w] τ τv B x
        (denotValB_semS orc ρ [σv] [w] e)

/-- The oracle assumptions actually required by adequacy. -/
structure AdequacyOracleSpec (orc : FFSOracleSem) : Prop where
  toOracleSpec : OracleSpec orc
  binderCoherent : AgreeDimsValueOpenPush orc
  resultBinderCoherent : ResultAgreeValueOpenPush orc
  valueSubstCoherent : RawValueSubstOracleCoherent orc

instance {orc : FFSOracleSem} : Coe (AdequacyOracleSpec orc) (OracleSpec orc) where
  coe h := h.toOracleSpec

end GLang
