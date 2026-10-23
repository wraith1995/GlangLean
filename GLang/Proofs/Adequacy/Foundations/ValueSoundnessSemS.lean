import GLang.Proofs.Value.Typing.ValueInferenceClosure
import GLang.Proofs.Value.Typing.ValueContextSupport
import GLang.Proofs.Value.Soundness.ValueSoundnessSem
import GLang.Proofs.Adequacy.Foundations.FvIrrel
import GLang.Proofs.Adequacy.Total.DirectOracleEval
import GLang.Proofs.Adequacy.Raw.RawOracleTransport

namespace GLang

noncomputable section

def ValSoundOfDenotSemS (orc : FFSOracleSem) :
    ValEnvSem → List ValTy → List ValValSem → ValTy → ValValSem → Prop
  | ρ, Γ, Δ, .space s, .array a =>
      ∀ i : ValIdx,
        ¬ ValSpace.shapeInBounds (orc ρ Γ Δ) s i → a.get i = 0
  | _ρ, _Γ, _Δ, .space _, .fn _ _ => False
  | _ρ, _Γ, _Δ, .piTy _ _, .array _ => False
  | ρ, Γ, Δ, .piTy τ₀ τ₁, .fn T fam =>
      ∃ h : T = (denotValTyS orc ρ Γ Δ τ₀).El,
        ∀ (v : T) (out : ValValSem), fam v = .ok out →
          ValSoundOfDenotSemS orc ρ (τ₀ :: Γ)
            (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) (h ▸ v) :: Δ)
            τ₁ out

/-- Canonical semantic membership.  At base kind this is exact finite storage;
at function kind it is inherited by every successful callback result. -/
def ValCanonicalSoundOfDenotSemS (orc : FFSOracleSem) :
    ValEnvSem → List ValTy → List ValValSem → ValTy → ValValSem → Prop
  | ρ, Γ, Δ, .space s, .array a =>
      a.length = ValSpace.dof (orc ρ Γ Δ) s
  | _ρ, _Γ, _Δ, .space _, .fn _ _ => False
  | _ρ, _Γ, _Δ, .piTy _ _, .array _ => False
  | ρ, Γ, Δ, .piTy τ₀ τ₁, .fn T fam =>
      ∃ h : T = (denotValTyS orc ρ Γ Δ τ₀).El,
        ∀ (v : T) (out : ValValSem), fam v = .ok out →
          ValCanonicalSoundOfDenotSemS orc ρ (τ₀ :: Γ)
            (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) (h ▸ v) :: Δ)
            τ₁ out

/-- Partial correctness lifted over the evaluator's explicit error result. -/
def ValResultSoundOfDenotSemS (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy)
    (r : Except DimError ValValSem) : Prop :=
  ∀ out, r = .ok out → ValSoundOfDenotSemS orc ρ Γ Δ τ out

/-- Canonical partial correctness lifted over `Except`. -/
def ValCanonicalResultSoundOfDenotSemS (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (τ : ValTy)
    (r : Except DimError ValValSem) : Prop :=
  ∀ out, r = .ok out → ValCanonicalSoundOfDenotSemS orc ρ Γ Δ τ out

/-- A root named environment contains canonical values at all of its declared
types.  Nested value binders are handled by the Pi clause, not stored here. -/
def ValCanonicalEnvSoundSemS (orc : FFSOracleSem)
    (ε : ValCtx) (ρ : ValEnvSem) : Prop :=
  ∀ x τ, ε.lookup x = some τ →
    ValCanonicalSoundOfDenotSemS orc ρ [] [] τ (ρ x)

/-- Worlds reached while comparing a successfully checked higher-order
argument with its ordinary (resizing) reification.

`root` is the exact world pair created by higher-order reshape. `push` closes
the relation under an arbitrary dependent Pi prefix: the same carrier element
is reified against the two possibly dimension-different semantic domain
types. -/
inductive CheckedOrdinaryPrefixRel (orc : FFSOracleSem) (ρ : ValEnvSem) :
    List ValTy → List ValValSem → List ValValSem → Prop where
  | root {Γ : List ValTy} {Δ : List ValValSem} {dom₀ dom₁ : ValTy}
      {a : (denotValTyS orc ρ Γ Δ (.piTy dom₀ dom₁)).El}
      {raw : ValValSem}
      (hcheck : ValValSem.fromElChecked
        (denotValTyS orc ρ Γ Δ (.piTy dom₀ dom₁)) a = .ok raw) :
      CheckedOrdinaryPrefixRel orc ρ
        (.piTy dom₀ dom₁ :: Γ) (raw :: Δ)
        (ValValSem.fromEl
          (denotValTyS orc ρ Γ Δ (.piTy dom₀ dom₁)) a :: Δ)
  | push {Γ : List ValTy} {Δ₀ Δ₁ : List ValValSem} {τ : ValTy} {T : Type}
      (tail : CheckedOrdinaryPrefixRel orc ρ Γ Δ₀ Δ₁)
      (h₀ : T = (denotValTyS orc ρ Γ Δ₀ τ).El)
      (h₁ : T = (denotValTyS orc ρ Γ Δ₁ τ).El) (v : T) :
      CheckedOrdinaryPrefixRel orc ρ (τ :: Γ)
        (ValValSem.fromEl (denotValTyS orc ρ Γ Δ₀ τ) (h₀ ▸ v) :: Δ₀)
        (ValValSem.fromEl (denotValTyS orc ρ Γ Δ₁ τ) (h₁ ▸ v) :: Δ₁)

/-- Primitive checked/ordinary representation boundary. The oracle gives the
same answer at every FFS leaf in worlds related by
`CheckedOrdinaryPrefixRel`. This statement mentions neither evaluator results
nor a soundness judgment. -/
def CheckedOrdinaryPrefixOracleCoherent (orc : FFSOracleSem) : Prop :=
  ∀ {ρ : ValEnvSem} {Γ : List ValTy} {Δ₀ Δ₁ : List ValValSem},
    CheckedOrdinaryPrefixRel orc ρ Γ Δ₀ Δ₁ →
    ∀ (p : ValFFSProp) (s : ValSpace) (e : ValExpr),
      orc ρ Γ Δ₀ p s e = orc ρ Γ Δ₁ p s e

namespace CheckedOrdinaryPrefixRel

/-- The pointwise oracle law propagates through a complete value-space. -/
theorem dof_eq {orc : FFSOracleSem}
    (hcoh : CheckedOrdinaryPrefixOracleCoherent orc)
    {ρ : ValEnvSem} {Γ : List ValTy} {Δ₀ Δ₁ : List ValValSem}
    (hrel : CheckedOrdinaryPrefixRel orc ρ Γ Δ₀ Δ₁) :
    ∀ s : ValSpace,
      ValSpace.dof (orc ρ Γ Δ₀) s = ValSpace.dof (orc ρ Γ Δ₁) s
  | .empty => by simp
  | .real => by simp
  | .dsum s₀ s₁ => by
      simp only [ValSpace.dof_dsum]
      rw [dof_eq hcoh hrel s₀, dof_eq hcoh hrel s₁]
  | .tprod s₀ s₁ => by
      simp only [ValSpace.dof_tprod]
      rw [dof_eq hcoh hrel s₀, dof_eq hcoh hrel s₁]
  | .ffs p s e => by
      simp only [ValSpace.dof_ffs]
      exact hcoh hrel p s e

/-- Semantic carriers depend only on kind structure, not oracle dimensions. -/
private theorem carrier_eq (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ₀ Δ₁ : List ValValSem) (τ : ValTy) :
    (denotValTyS orc ρ Γ Δ₀ τ).El =
      (denotValTyS orc ρ Γ Δ₁ τ).El :=
  (denotValTyS_El_eq_carrierEl_raw orc ρ Γ Δ₀ τ).trans
    (denotValTyS_El_eq_carrierEl_raw orc ρ Γ Δ₁ τ).symm

/-- Structural transport of canonical membership along a checked/ordinary
prefix relation. -/
theorem canonicalSound_transport
    {orc : FFSOracleSem} (hcoh : CheckedOrdinaryPrefixOracleCoherent orc) :
    ∀ {ρ : ValEnvSem} {Γ : List ValTy} {Δ₀ Δ₁ : List ValValSem}
      {τ : ValTy} {out : ValValSem},
      CheckedOrdinaryPrefixRel orc ρ Γ Δ₀ Δ₁ →
      ValCanonicalSoundOfDenotSemS orc ρ Γ Δ₀ τ out →
      ValCanonicalSoundOfDenotSemS orc ρ Γ Δ₁ τ out
  | ρ, Γ, Δ₀, Δ₁, .space s, .array a, hrel, hsound => by
      simp only [ValCanonicalSoundOfDenotSemS] at hsound ⊢
      exact hsound.trans (dof_eq hcoh hrel s)
  | _, _, _, _, .space _, .fn _ _, _, hsound => by
      change False at hsound ⊢
      exact hsound
  | _, _, _, _, .piTy _ _, .array _, _, hsound => by
      change False at hsound ⊢
      exact hsound
  | ρ, Γ, Δ₀, Δ₁, .piTy τ₀ τ₁, .fn T fam, hrel, hsound => by
      simp only [ValCanonicalSoundOfDenotSemS] at hsound ⊢
      obtain ⟨hT₀, hbody⟩ := hsound
      have hcarrier :
          (denotValTyS orc ρ Γ Δ₀ τ₀).El =
            (denotValTyS orc ρ Γ Δ₁ τ₀).El :=
        carrier_eq orc ρ Γ Δ₀ Δ₁ τ₀
      let hT₁ : T = (denotValTyS orc ρ Γ Δ₁ τ₀).El :=
        hT₀.trans hcarrier
      refine ⟨hT₁, ?_⟩
      intro v result hresult
      exact canonicalSound_transport hcoh
        (.push hrel hT₀ hT₁ v) (hbody v result hresult)

/-- The reshape transport follows from the pointwise prefix oracle law. -/
theorem checkedArgTransport
    {orc : FFSOracleSem} (hcoh : CheckedOrdinaryPrefixOracleCoherent orc) :
    ∀ {ρ : ValEnvSem} {Γ : List ValTy} {Δ : List ValValSem}
      {dom₀ dom₁ cod : ValTy}
      {a : (denotValTyS orc ρ Γ Δ (.piTy dom₀ dom₁)).El}
      {raw out : ValValSem},
      ValValSem.fromElChecked
          (denotValTyS orc ρ Γ Δ (.piTy dom₀ dom₁)) a = .ok raw →
      ValCanonicalSoundOfDenotSemS orc ρ
          (.piTy dom₀ dom₁ :: Γ) (raw :: Δ) cod out →
      ValCanonicalSoundOfDenotSemS orc ρ
          (.piTy dom₀ dom₁ :: Γ)
          (ValValSem.fromEl
            (denotValTyS orc ρ Γ Δ (.piTy dom₀ dom₁)) a :: Δ) cod out := by
  intro ρ Γ Δ dom₀ dom₁ cod a raw out hcheck hsound
  exact canonicalSound_transport hcoh (.root hcheck) hsound

end CheckedOrdinaryPrefixRel

/-- The representation laws used by value soundness. Numerical rank/bound
laws play no role here. The first two come from `RawAdequacyOracleSpec`;
application additionally consumes the existing raw value-substitution leaf
law. Higher-order reshape has one further pointwise oracle boundary because
checked and ordinary reifications can differ as raw functions even when they
describe the same carrier element. -/
structure ValueSoundnessOracleSpec (orc : FFSOracleSem) : Prop where
  fvIrrel : OracleFvIrrel orc
  valueOpenPushOracleCoherent : RawValueOpenPushOracleCoherent orc
  valueSubstCoherent : RawValueSubstOracleCoherent orc
  checkedOrdinaryPrefixOracleCoherent : CheckedOrdinaryPrefixOracleCoherent orc

/-- Derived structural transport consumed by higher-order reshape. -/
theorem ValueSoundnessOracleSpec.checkedArgTransport
    {orc : FFSOracleSem} (h : ValueSoundnessOracleSpec orc) :
    ∀ {ρ : ValEnvSem} {Γ : List ValTy} {Δ : List ValValSem}
      {dom₀ dom₁ cod : ValTy}
      {a : (denotValTyS orc ρ Γ Δ (.piTy dom₀ dom₁)).El}
      {raw out : ValValSem},
      ValValSem.fromElChecked
          (denotValTyS orc ρ Γ Δ (.piTy dom₀ dom₁)) a = .ok raw →
      ValCanonicalSoundOfDenotSemS orc ρ
          (.piTy dom₀ dom₁ :: Γ) (raw :: Δ) cod out →
      ValCanonicalSoundOfDenotSemS orc ρ
          (.piTy dom₀ dom₁ :: Γ)
          (ValValSem.fromEl
            (denotValTyS orc ρ Γ Δ (.piTy dom₀ dom₁)) a :: Δ) cod out :=
  CheckedOrdinaryPrefixRel.checkedArgTransport
    h.checkedOrdinaryPrefixOracleCoherent

/-- Reification respects propositional equality of semantic types. -/
private theorem ValValSem.fromEl_cast_semS {T T' : ValTypeSem}
    (h : T = T') (a : T'.El) :
    ValValSem.fromEl T (cast (congrArg ValTypeSem.El h.symm) a) =
      ValValSem.fromEl T' a := by
  subst h
  rfl

private theorem cast_cancel_right {A B C : Type} (hAB : A = B)
    (hBC : B = C) (a : A) :
    cast hBC.symm (cast (hAB.trans hBC) a) = cast hAB a := by
  subst hAB
  subst hBC
  rfl

private theorem cast_compose {A B C : Type} (hAB : A = B)
    (hBC : B = C) (a : A) :
    cast (hAB.trans hBC) a = cast hBC (cast hAB a) := by
  subst hAB
  subst hBC
  rfl

/-- Assemble the smaller value-soundness contract from the adequacy oracle
package and its application/substitution law. -/
def ValueSoundnessOracleSpec.ofRawAdequacy
    {orc : FFSOracleSem} (h : RawAdequacyOracleSpec orc)
    (hsubst : RawValueSubstOracleCoherent orc)
    (hchecked : CheckedOrdinaryPrefixOracleCoherent orc) :
    ValueSoundnessOracleSpec orc where
  fvIrrel := h.fvIrrel
  valueOpenPushOracleCoherent := h.valueOpenPushOracleCoherent
  valueSubstCoherent := hsubst
  checkedOrdinaryPrefixOracleCoherent := hchecked

namespace ValCanonicalResultSoundOfDenotSemS

theorem ok {orc : FFSOracleSem} {ρ : ValEnvSem} {Γ : List ValTy}
    {Δ : List ValValSem} {τ : ValTy} {v : ValValSem}
    (h : ValCanonicalSoundOfDenotSemS orc ρ Γ Δ τ v) :
    ValCanonicalResultSoundOfDenotSemS orc ρ Γ Δ τ (.ok v) := by
  intro out hout
  cases hout
  exact h

theorem error {orc : FFSOracleSem} {ρ : ValEnvSem} {Γ : List ValTy}
    {Δ : List ValValSem} {τ : ValTy} (err : DimError) :
    ValCanonicalResultSoundOfDenotSemS orc ρ Γ Δ τ (.error err) := by
  intro out hout
  cases hout

theorem bindArray {orc : FFSOracleSem} {ρ : ValEnvSem} {Γ : List ValTy}
    {Δ : List ValValSem} {τ : ValTy}
    (r : Except DimError ValValSem)
    (k : FlatArray → Except DimError ValValSem)
    (hk : ∀ a, ValCanonicalResultSoundOfDenotSemS orc ρ Γ Δ τ (k a)) :
    ValCanonicalResultSoundOfDenotSemS orc ρ Γ Δ τ
      (ValValSem.bindArray r k) := by
  intro out hout
  cases hr : r with
  | error err => simp [ValValSem.bindArray, hr] at hout
  | ok v =>
      cases v with
      | fn T f => simp [ValValSem.bindArray, hr] at hout
      | array a => exact hk a out (by simpa [ValValSem.bindArray, hr] using hout)

theorem bindArrays {orc : FFSOracleSem} {ρ : ValEnvSem} {Γ : List ValTy}
    {Δ : List ValValSem} {τ : ValTy}
    (r₀ r₁ : Except DimError ValValSem)
    (k : FlatArray → FlatArray → Except DimError ValValSem)
    (hk : ∀ a₀ a₁,
      ValCanonicalResultSoundOfDenotSemS orc ρ Γ Δ τ (k a₀ a₁)) :
    ValCanonicalResultSoundOfDenotSemS orc ρ Γ Δ τ
      (ValValSem.bindArrays r₀ r₁ k) := by
  unfold ValValSem.bindArrays
  apply bindArray
  intro a₀
  apply bindArray
  exact hk a₀

theorem bindArrays3 {orc : FFSOracleSem} {ρ : ValEnvSem} {Γ : List ValTy}
    {Δ : List ValValSem} {τ : ValTy}
    (r₀ r₁ r₂ : Except DimError ValValSem)
    (k : FlatArray → FlatArray → FlatArray → Except DimError ValValSem)
    (hk : ∀ a₀ a₁ a₂,
      ValCanonicalResultSoundOfDenotSemS orc ρ Γ Δ τ (k a₀ a₁ a₂)) :
    ValCanonicalResultSoundOfDenotSemS orc ρ Γ Δ τ
      (ValValSem.bindArrays3 r₀ r₁ r₂ k) := by
  unfold ValValSem.bindArrays3
  apply bindArray
  intro a₀
  apply bindArray
  intro a₁
  apply bindArray
  exact hk a₀ a₁

end ValCanonicalResultSoundOfDenotSemS

namespace ValCanonicalSoundOfDenotSemS

theorem space_arrayOf {orc : FFSOracleSem} {ρ : ValEnvSem}
    {Γ : List ValTy} {Δ : List ValValSem} {s : ValSpace}
    {n : Nat} {f : Nat → ℝ}
    (hlen : n = ValSpace.dof (orc ρ Γ Δ) s) :
    ValCanonicalSoundOfDenotSemS orc ρ Γ Δ (.space s)
      (ValValSem.arrayOf n f) := by
  change (FlatArray.ofFn n f).length = ValSpace.dof (orc ρ Γ Δ) s
  simp [hlen]

/-- Reifying any element of the (unrefined) semantic carrier produces a
canonical runtime value.  At base kind `fromEl` performs the required resize;
at Pi kind it performs that normalization recursively on successful results. -/
theorem fromEl_sound (orc : FFSOracleSem) :
    ∀ (τ : ValTy) (ρ : ValEnvSem) (Γ : List ValTy)
      (Δ : List ValValSem) (a : (denotValTyS orc ρ Γ Δ τ).El),
      ValCanonicalSoundOfDenotSemS orc ρ Γ Δ τ
        (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ) a)
  | .space s, ρ, Γ, Δ, a => by
      simp only [denotValTyS, ValValSem.fromEl,
        ValCanonicalSoundOfDenotSemS]
      simp [FlatArray.resize]
  | .piTy τ₀ τ₁, ρ, Γ, Δ, a => by
      refine ⟨rfl, ?_⟩
      intro v out hout
      cases hav : a v with
      | error err =>
          simp only [hav, Except.map] at hout
          cases hout
      | ok z =>
          simp only [hav, Except.map] at hout
          injection hout with hout
          subst out
          exact fromEl_sound orc τ₁ ρ (τ₀ :: Γ)
            (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) v :: Δ) z
  termination_by τ _ _ _ _ => ValTy.kindSize τ
  decreasing_by
    all_goals simp_wf

private theorem resize_eq_self_of_length {a : FlatArray} {n : Nat}
    (h : a.length = n) : a.resize n = a := by
  apply FlatArray.ext h.symm
  intro i
  simp [FlatArray.resize, FlatArray.ofFn, FlatArray.get, h]

/-- Canonical soundness makes the evaluator's decode/reify bridge a true
retraction, recursively through higher-order values. -/
theorem toEl_fromEl_retract (orc : FFSOracleSem) :
    ∀ (τ : ValTy) (ρ : ValEnvSem) (Γ : List ValTy)
      (Δ : List ValValSem) (v : ValValSem),
      ValCanonicalSoundOfDenotSemS orc ρ Γ Δ τ v →
      ∃ a : (denotValTyS orc ρ Γ Δ τ).El,
        ValValSem.toEl (denotValTyS orc ρ Γ Δ τ) v = .ok a ∧
        ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ) a = v
  | .space s, ρ, Γ, Δ, .array a, hs => by
      refine ⟨a, rfl, ?_⟩
      simp only [denotValTyS, ValValSem.fromEl]
      rw [resize_eq_self_of_length hs]
  | .space _, _, _, _, .fn _ _, hs => hs.elim
  | .piTy _ _, _, _, _, .array _, hs => hs.elim
  | .piTy τ₀ τ₁, ρ, Γ, Δ, .fn T f, hs => by
      obtain ⟨hT, hbody⟩ := hs
      subst T
      let T₀ := denotValTyS orc ρ Γ Δ τ₀
      let F := fun y : T₀.El =>
        denotValTyS orc ρ (τ₀ :: Γ) (ValValSem.fromEl T₀ y :: Δ) τ₁
      have hex : ∀ y : T₀.El, ∃ z : Except DimError (F y).El,
          (match f y with
            | .error err => .error err
            | .ok out => ValValSem.toEl (F y) out) = z ∧
          z.map (ValValSem.fromEl (F y)) = f y := by
        intro y
        cases hfy : f y with
        | error err =>
            exact ⟨.error err, rfl, rfl⟩
        | ok out =>
            obtain ⟨a, hto, hfrom⟩ := toEl_fromEl_retract orc τ₁ ρ
              (τ₀ :: Γ) (ValValSem.fromEl T₀ y :: Δ) out
              (hbody y out hfy)
            refine ⟨.ok a, by simpa only [F, hfy] using hto, ?_⟩
            simp only [Except.map]
            change Except.ok
              (ValValSem.fromEl
                (denotValTyS orc ρ (τ₀ :: Γ)
                  (ValValSem.fromEl T₀ y :: Δ) τ₁) a) = .ok out
            rw [hfrom]
      let g : (y : T₀.El) → Except DimError (F y).El :=
        fun y => (hex y).choose
      refine ⟨g, ?_, ?_⟩
      · simp only [denotValTyS, ValValSem.toEl]
        apply congrArg Except.ok
        funext y
        exact (hex y).choose_spec.1
      · simp only [denotValTyS, ValValSem.fromEl]
        apply congrArg (ValValSem.fn T₀.El)
        funext y
        exact (hex y).choose_spec.2
  termination_by τ _ _ _ _ => ValTy.kindSize τ
  decreasing_by
    all_goals simp_wf

/-- Canonical values pass the immediate application-domain check, so its
successful decoding retains the existing decode/reify retraction. -/
theorem toElDomainChecked_fromEl_retract (orc : FFSOracleSem)
    (τ : ValTy) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (v : ValValSem)
    (hs : ValCanonicalSoundOfDenotSemS orc ρ Γ Δ τ v) :
    ∃ a : (denotValTyS orc ρ Γ Δ τ).El,
      ValValSem.toElDomainChecked (denotValTyS orc ρ Γ Δ τ) v = .ok a ∧
      ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ) a = v := by
  obtain ⟨a, hto, hfrom⟩ := toEl_fromEl_retract orc τ ρ Γ Δ v hs
  refine ⟨a, ?_, hfrom⟩
  cases τ with
  | space s =>
      cases v with
      | array arr =>
          exact (ValValSem.toElDomainChecked_eq_toEl_space s _ arr hs).trans hto
      | fn T f => exact hs.elim
  | piTy dom cod => exact hto

theorem implies_sound (orc : FFSOracleSem) :
    ∀ (τ : ValTy) (ρ : ValEnvSem) (Γ : List ValTy)
      (Δ : List ValValSem) (v : ValValSem),
      ValCanonicalSoundOfDenotSemS orc ρ Γ Δ τ v →
      ValSoundOfDenotSemS orc ρ Γ Δ τ v
  | .space s, ρ, Γ, Δ, .array a, hs => by
      intro i hi
      have hge : a.length ≤ i := by
        rw [hs]
        exact Nat.le_of_not_lt fun hlt =>
          hi (ValSpace.shapeInBounds_of_lt_dof (orc ρ Γ Δ) s i hlt)
      simp [FlatArray.get, Nat.not_lt.mpr hge]
  | .space _, _, _, _, .fn _ _, hs => hs.elim
  | .piTy _ _, _, _, _, .array _, hs => hs.elim
  | .piTy τ₀ τ₁, ρ, Γ, Δ, .fn T f, hs => by
      obtain ⟨hT, hbody⟩ := hs
      refine ⟨hT, ?_⟩
      intro v out hout
      exact implies_sound orc τ₁ ρ (τ₀ :: Γ)
        (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) (hT ▸ v) :: Δ)
        out (hbody v out hout)
  termination_by τ _ _ _ _ => ValTy.kindSize τ
  decreasing_by
    all_goals simp_wf

/-- Updating a named value outside the free variables of a type does not
change canonical soundness. -/
theorem update_iff (orc : FFSOracleSem) (hirr : OracleFvIrrel orc) :
    ∀ (τ : ValTy) (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
      (y : VName) (w v : ValValSem),
      ValTyCtxFresh y Γ → y ∉ ValTy.fv τ →
      (ValCanonicalSoundOfDenotSemS orc (ρ.update y w) Γ Δ τ v ↔
        ValCanonicalSoundOfDenotSemS orc ρ Γ Δ τ v)
  | .space s, ρ, Γ, Δ, y, w, .array a, hΓ, hy => by
      simp only [ValCanonicalSoundOfDenotSemS, ValTy.fv] at hy ⊢
      rw [ValSpace.dof_update_of_not_mem_fv hirr ρ y w Γ Δ hΓ s hy]
  | .space _, _, _, _, _, _, .fn _ _, _, _ => Iff.rfl
  | .piTy _ _, _, _, _, _, _, .array _, _, _ => Iff.rfl
  | .piTy τ₀ τ₁, ρ, Γ, Δ, y, w, .fn T f, hΓ, hy => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      unfold ValCanonicalSoundOfDenotSemS
      have hT := denotValTyS_update_of_not_mem_fv hirr ρ y w τ₀ Γ Δ hΓ hy.1
      constructor
      · rintro ⟨hdomU, hbody⟩
        let hdom : T = (denotValTyS orc ρ Γ Δ τ₀).El :=
          hdomU.trans (congrArg ValTypeSem.El hT)
        refine ⟨hdom, ?_⟩
        intro a out hout
        have harg :
            ValValSem.fromEl (denotValTyS orc (ρ.update y w) Γ Δ τ₀)
                (hdomU ▸ a) =
              ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀)
                (hdom ▸ a) := by
          have hcast := cast_cancel_right hdomU
            (congrArg ValTypeSem.El hT) a
          change ValValSem.fromEl _ (cast hdomU a) = _
          rw [← hcast]
          exact ValValSem.fromEl_cast_semS hT (hdom ▸ a)
        have hb := hbody a out hout
        rw [harg] at hb
        exact (update_iff orc hirr τ₁ ρ (τ₀ :: Γ)
          (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) (hdom ▸ a) :: Δ)
          y w out (ValTyCtxFresh.cons hy.1 hΓ) hy.2).mp hb
      · rintro ⟨hdom, hbody⟩
        let hdomU : T = (denotValTyS orc (ρ.update y w) Γ Δ τ₀).El :=
          hdom.trans (congrArg ValTypeSem.El hT.symm)
        refine ⟨hdomU, ?_⟩
        intro a out hout
        have harg :
            ValValSem.fromEl (denotValTyS orc (ρ.update y w) Γ Δ τ₀)
                (hdomU ▸ a) =
              ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀)
                (hdom ▸ a) := by
          have hcast : cast hdomU a =
              cast (congrArg ValTypeSem.El hT.symm) (cast hdom a) := by
            simpa only [hdomU] using
              (cast_compose hdom (congrArg ValTypeSem.El hT.symm) a)
          change ValValSem.fromEl _ (cast hdomU a) = _
          rw [hcast]
          exact ValValSem.fromEl_cast_semS hT (hdom ▸ a)
        rw [harg]
        exact (update_iff orc hirr τ₁ ρ (τ₀ :: Γ)
          (ValValSem.fromEl (denotValTyS orc ρ Γ Δ τ₀) (hdom ▸ a) :: Δ)
          y w out (ValTyCtxFresh.cons hy.1 hΓ) hy.2).mpr (hbody a out hout)
  termination_by τ _ _ _ _ _ _ _ _ => ValTy.kindSize τ
  decreasing_by
    all_goals simp_wf

end ValCanonicalSoundOfDenotSemS

namespace ValCanonicalEnvSoundSemS

/-- Extend a canonical named environment by a freshly reified semantic
carrier element. -/
theorem update (orc : FFSOracleSem) (hirr : OracleFvIrrel orc)
    (ε : ValCtx) (ρ : ValEnvSem) (y : VName) (τ₀ : ValTy)
    (henv : ValCanonicalEnvSoundSemS orc ε ρ)
    (hySupport : y ∉ ε.fvSupport)
    (hyTau : y ∉ ValTy.fv τ₀)
    (a : (denotValTyS orc ρ [] [] τ₀).El) :
    ValCanonicalEnvSoundSemS orc (Finmap.insert y τ₀ ε)
      (ρ.update y (ValValSem.fromEl (denotValTyS orc ρ [] [] τ₀) a)) := by
  intro x τ hx
  by_cases hxy : x = y
  · subst x
    rw [Finmap.lookup_insert] at hx
    obtain rfl : τ₀ = τ := Option.some.inj hx
    rw [ValEnvSem.update_same]
    exact (ValCanonicalSoundOfDenotSemS.update_iff orc hirr τ₀ ρ [] [] y
      (ValValSem.fromEl (denotValTyS orc ρ [] [] τ₀) a)
      (ValValSem.fromEl (denotValTyS orc ρ [] [] τ₀) a)
      (by simp [ValTyCtxFresh]) hyTau).mpr
        (ValCanonicalSoundOfDenotSemS.fromEl_sound orc τ₀ ρ [] [] a)
  · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
    rw [ValEnvSem.update_other _ _ _ _ hxy]
    have hyFv := ValCtx.not_mem_fv_of_not_mem_support hySupport hx
    exact (ValCanonicalSoundOfDenotSemS.update_iff orc hirr τ ρ [] [] y
      (ValValSem.fromEl (denotValTyS orc ρ [] [] τ₀) a) (ρ x)
      (by simp [ValTyCtxFresh]) hyFv).mpr
        (henv x τ hx)

end ValCanonicalEnvSoundSemS

namespace ValueSoundnessSemSTransport

/-- The raw substitution law propagates from individual FFS leaves to a
whole value-space shape. -/
theorem shpOf_valueSubst
    {orc : FFSOracleSem} (horacle : RawValueSubstOracleCoherent orc)
    {ρ : ValEnvSem} {u : ValExpr} {σv : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (huLc : ValExpr.lc u)
    (huInfer : ValExpr.inferTypeCtx [] u = σv)
    (huEval : denotValB_semS orc ρ [] [] u = .ok w) :
    ∀ s : ValSpace,
      ValSpace.shpOf (orc ρ (G ++ [σv]) (D ++ [w])) s =
        ValSpace.shpOf (orc ρ (ValTy.closePrefix u G) D)
          (ValSpace.openRec G.length u s) := by
  intro s
  generalize hn : ValSpace.size s = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      cases s with
      | empty => simp only [ValSpace.openRec, ValSpace.shpOf]
      | real => simp only [ValSpace.openRec, ValSpace.shpOf]
      | dsum s₀ s₁ =>
          have hlt₀ : ValSpace.size s₀ < n := by
            simp only [ValSpace.size] at hn
            omega
          have hlt₁ : ValSpace.size s₁ < n := by
            simp only [ValSpace.size] at hn
            omega
          have ih₀ := ih (ValSpace.size s₀) hlt₀ s₀ rfl
          have ih₁ := ih (ValSpace.size s₁) hlt₁ s₁ rfl
          have hd₀ := congrArg (fun xs => xs.foldr (· * ·) 1) ih₀
          have hd₁ := congrArg (fun xs => xs.foldr (· * ·) 1) ih₁
          simp only [ValSpace.openRec, ValSpace.shpOf_dsum,
            ValSpace.dof, hd₀, hd₁]
      | tprod s₀ s₁ =>
          have hlt₀ : ValSpace.size s₀ < n := by
            simp only [ValSpace.size] at hn
            omega
          have hlt₁ : ValSpace.size s₁ < n := by
            simp only [ValSpace.size] at hn
            omega
          have ih₀ := ih (ValSpace.size s₀) hlt₀ s₀ rfl
          have ih₁ := ih (ValSpace.size s₁) hlt₁ s₁ rfl
          have hd₀ := congrArg (fun xs => xs.foldr (· * ·) 1) ih₀
          have hd₁ := congrArg (fun xs => xs.foldr (· * ·) 1) ih₁
          simp only [ValSpace.openRec, ValSpace.shpOf_tprod,
            ValSpace.dof, hd₀, hd₁]
      | ffs p s e =>
          simp only [ValSpace.openRec, ValSpace.shpOf_ffs]
          rw [horacle hlen huLc huInfer huEval]

theorem dof_valueSubst
    {orc : FFSOracleSem} (horacle : RawValueSubstOracleCoherent orc)
    {ρ : ValEnvSem} {u : ValExpr} {σv : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (huLc : ValExpr.lc u)
    (huInfer : ValExpr.inferTypeCtx [] u = σv)
    (huEval : denotValB_semS orc ρ [] [] u = .ok w)
    (s : ValSpace) :
    ValSpace.dof (orc ρ (G ++ [σv]) (D ++ [w])) s =
      ValSpace.dof (orc ρ (ValTy.closePrefix u G) D)
        (ValSpace.openRec G.length u s) := by
  simpa only [ValSpace.dof] using congrArg
    (fun xs => xs.foldr (· * ·) 1)
    (shpOf_valueSubst horacle hlen huLc huInfer huEval s)

/-- Reification is stable when the distinguished local value slot is closed
by the syntax that evaluated to that value.  The proof is prefix-general so
the Pi case can recurse underneath further dependent binders. -/
theorem fromEl_valueSubst
    {orc : FFSOracleSem} (horacle : RawValueSubstOracleCoherent orc)
    {ρ : ValEnvSem} {u : ValExpr} {σv : ValTy} {w : ValValSem}
    (huLc : ValExpr.lc u)
    (huInfer : ValExpr.inferTypeCtx [] u = σv)
    (huEval : denotValB_semS orc ρ [] [] u = .ok w) :
    ∀ (τ : ValTy) (G : List ValTy) (D : List ValValSem),
      G.length = D.length →
      ∀ (a : (denotValTyS orc ρ (G ++ [σv]) (D ++ [w]) τ).El)
        (a' : (denotValTyS orc ρ (ValTy.closePrefix u G) D
          (ValTy.openRec G.length u τ)).El),
        HEq a a' →
        ValValSem.fromEl
            (denotValTyS orc ρ (G ++ [σv]) (D ++ [w]) τ) a =
          ValValSem.fromEl
            (denotValTyS orc ρ (ValTy.closePrefix u G) D
              (ValTy.openRec G.length u τ)) a'
  | .space s, G, D, hlen, a, a', haa => by
      obtain rfl : a = a' := eq_of_heq haa
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromEl]
      rw [dof_valueSubst horacle hlen huLc huInfer huEval]
  | .piTy τ₀ τ₁, G, D, hlen, a, a', haa => by
      have hdom :
          (denotValTyS orc ρ (G ++ [σv]) (D ++ [w]) τ₀).El =
            (denotValTyS orc ρ (ValTy.closePrefix u G) D
              (ValTy.openRec G.length u τ₀)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      have hcodFam : HEq
          (fun y : (denotValTyS orc ρ (G ++ [σv]) (D ++ [w]) τ₀).El =>
            Except DimError
              (denotValTyS orc ρ (τ₀ :: (G ++ [σv]))
                (ValValSem.fromEl
                  (denotValTyS orc ρ (G ++ [σv]) (D ++ [w]) τ₀) y ::
                    (D ++ [w])) τ₁).El)
          (fun y' : (denotValTyS orc ρ (ValTy.closePrefix u G) D
              (ValTy.openRec G.length u τ₀)).El =>
            Except DimError
              (denotValTyS orc ρ
                (ValTy.openRec G.length u τ₀ :: ValTy.closePrefix u G)
                (ValValSem.fromEl
                  (denotValTyS orc ρ (ValTy.closePrefix u G) D
                    (ValTy.openRec G.length u τ₀)) y' :: D)
                (ValTy.openRec (G.length + 1) u τ₁)).El) := by
        refine Function.hfunext hdom ?_
        intro y y' _
        apply heq_of_eq
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromEl]
      refine ValValSem.fn_congr _ _ hdom ?_
      intro y
      have hay : HEq (a y) (a' (hdom ▸ y)) :=
        heq_app_dep hdom hcodFam haa (cast_heq hdom y).symm
      have hraw :
          ValValSem.fromEl
              (denotValTyS orc ρ (G ++ [σv]) (D ++ [w]) τ₀) y =
            ValValSem.fromEl
              (denotValTyS orc ρ (ValTy.closePrefix u G) D
                (ValTy.openRec G.length u τ₀)) (hdom ▸ y) :=
        fromEl_valueSubst horacle huLc huInfer huEval τ₀ G D hlen
          y (hdom ▸ y) (cast_heq hdom y).symm
      have hcod :
          (denotValTyS orc ρ (τ₀ :: (G ++ [σv]))
            (ValValSem.fromEl
              (denotValTyS orc ρ (G ++ [σv]) (D ++ [w]) τ₀) y ::
                (D ++ [w])) τ₁).El =
          (denotValTyS orc ρ
            (ValTy.openRec G.length u τ₀ :: ValTy.closePrefix u G)
            (ValValSem.fromEl
              (denotValTyS orc ρ (ValTy.closePrefix u G) D
                (ValTy.openRec G.length u τ₀)) (hdom ▸ y) :: D)
            (ValTy.openRec (G.length + 1) u τ₁)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      apply except_map_heq_congr hcod (a y) (a' (hdom ▸ y)) hay
      intro z z' hzz
      let rawL := ValValSem.fromEl
        (denotValTyS orc ρ (G ++ [σv]) (D ++ [w]) τ₀) y
      let rawR := ValValSem.fromEl
        (denotValTyS orc ρ (ValTy.closePrefix u G) D
          (ValTy.openRec G.length u τ₀)) (hdom ▸ y)
      let TRnorm := denotValTyS orc ρ
        (ValTy.openRec G.length u τ₀ :: ValTy.closePrefix u G)
        (rawL :: D) (ValTy.openRec (G.length + 1) u τ₁)
      let TRactual := denotValTyS orc ρ
        (ValTy.openRec G.length u τ₀ :: ValTy.closePrefix u G)
        (rawR :: D) (ValTy.openRec (G.length + 1) u τ₁)
      have hsem : TRnorm = TRactual := by
        simp only [TRnorm, TRactual, rawL, rawR, hraw]
      let zNorm : TRnorm.El :=
        cast (congrArg ValTypeSem.El hsem.symm) z'
      have hzzNorm : HEq z zNorm := by
        exact HEq.trans hzz
          (cast_heq (congrArg ValTypeSem.El hsem.symm) z').symm
      have hlen' : (τ₀ :: G).length =
          (rawL :: D).length := by
        simp only [List.length_cons, hlen]
      have hrec := fromEl_valueSubst horacle huLc huInfer huEval τ₁
        (τ₀ :: G) (rawL :: D) hlen' z zNorm hzzNorm
      have hcast := ValValSem.fromEl_cast_semS hsem z'
      have hfinal := hrec.trans hcast
      simpa only [rawL, rawR, TRnorm, TRactual, List.cons_append,
        ValTy.closePrefix, List.length_cons, Nat.succ_eq_add_one] using hfinal
  termination_by τ _ _ _ _ _ _ => ValTy.kindSize τ
  decreasing_by
    all_goals simp_wf
    omega

/-- Canonical soundness is invariant under closing one pushed value slot by
the closed expression that evaluated to that slot's value.  The statement is
prefix-general so that the Pi case can recurse under further binders. -/
theorem canonicalSound_valueSubst_iff
    {orc : FFSOracleSem} (horacle : RawValueSubstOracleCoherent orc)
    {rho : ValEnvSem} {u : ValExpr} {sigmaV : ValTy} {w : ValValSem}
    (huLc : ValExpr.lc u)
    (huInfer : ValExpr.inferTypeCtx [] u = sigmaV)
    (huEval : denotValB_semS orc rho [] [] u = .ok w) :
    forall (tau : ValTy) (v : ValValSem) (G : List ValTy)
      (D : List ValValSem), G.length = D.length ->
      (ValCanonicalSoundOfDenotSemS orc rho
          (G ++ [sigmaV]) (D ++ [w]) tau v <->
        ValCanonicalSoundOfDenotSemS orc rho
          (ValTy.closePrefix u G) D (ValTy.openRec G.length u tau) v)
  | .space s, .array a, G, D, hlen => by
      simp only [ValTy.openRec, ValCanonicalSoundOfDenotSemS]
      rw [dof_valueSubst horacle hlen huLc huInfer huEval]
  | .space _, .fn _ _, _, _, _ => by
      simp only [ValTy.openRec, ValCanonicalSoundOfDenotSemS]
  | .piTy _ _, .array _, _, _, _ => by
      simp only [ValTy.openRec, ValCanonicalSoundOfDenotSemS]
  | .piTy tau0 tau1, .fn T f, G, D, hlen => by
      have hEl :
          (denotValTyS orc rho (G ++ [sigmaV]) (D ++ [w]) tau0).El =
            (denotValTyS orc rho (ValTy.closePrefix u G) D
              (ValTy.openRec G.length u tau0)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      simp only [ValTy.openRec, ValCanonicalSoundOfDenotSemS]
      constructor
      · rintro ⟨hTpush, hbody⟩
        have hTclosed : T =
            (denotValTyS orc rho (ValTy.closePrefix u G) D
              (ValTy.openRec G.length u tau0)).El :=
          hTpush.trans hEl
        refine ⟨hTclosed, ?_⟩
        intro a out hout
        have harg : HEq (hTpush ▸ a) (hTclosed ▸ a) :=
          HEq.trans (cast_heq hTpush a) (cast_heq hTclosed a).symm
        have hcanon := fromEl_valueSubst horacle huLc huInfer huEval
          tau0 G D hlen (hTpush ▸ a) (hTclosed ▸ a) harg
        have hleft := hbody a out hout
        rw [hcanon] at hleft
        have hlen' : (tau0 :: G).length =
            (ValValSem.fromEl
              (denotValTyS orc rho (ValTy.closePrefix u G) D
                (ValTy.openRec G.length u tau0)) (hTclosed ▸ a) :: D).length := by
          simp only [List.length_cons, hlen]
        have hiff := canonicalSound_valueSubst_iff horacle huLc huInfer
          huEval tau1 out (tau0 :: G)
            (ValValSem.fromEl
              (denotValTyS orc rho (ValTy.closePrefix u G) D
                (ValTy.openRec G.length u tau0)) (hTclosed ▸ a) :: D) hlen'
        simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
          Nat.succ_eq_add_one] using hiff.mp hleft
      · rintro ⟨hTclosed, hbody⟩
        have hTpush : T =
            (denotValTyS orc rho (G ++ [sigmaV]) (D ++ [w]) tau0).El :=
          hTclosed.trans hEl.symm
        refine ⟨hTpush, ?_⟩
        intro a out hout
        have harg : HEq (hTpush ▸ a) (hTclosed ▸ a) :=
          HEq.trans (cast_heq hTpush a) (cast_heq hTclosed a).symm
        have hcanon := fromEl_valueSubst horacle huLc huInfer huEval
          tau0 G D hlen (hTpush ▸ a) (hTclosed ▸ a) harg
        have hright := hbody a out hout
        have hlen' : (tau0 :: G).length =
            (ValValSem.fromEl
              (denotValTyS orc rho (ValTy.closePrefix u G) D
                (ValTy.openRec G.length u tau0)) (hTclosed ▸ a) :: D).length := by
          simp only [List.length_cons, hlen]
        have hiff := canonicalSound_valueSubst_iff horacle huLc huInfer
          huEval tau1 out (tau0 :: G)
            (ValValSem.fromEl
              (denotValTyS orc rho (ValTy.closePrefix u G) D
                (ValTy.openRec G.length u tau0)) (hTclosed ▸ a) :: D) hlen'
        have hpush := hiff.mpr (by
          simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
            Nat.succ_eq_add_one] using hright)
        rw [hcanon]
        exact hpush
  termination_by tau _ _ _ _ => ValTy.kindSize tau
  decreasing_by
    all_goals simp_wf

/-- Dimension transport between a pushed de-Bruijn value slot and its
fresh-name presentation. -/
theorem dof_valueOpenPush
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (hlcSigma : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    (s : ValSpace) (hy : y ∉ ValSpace.fv s) :
    ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s =
      ValSpace.dof
        (orc (rho.update y w) (ValTy.closePrefix (.var y sigmaV) G) D)
        (ValSpace.openRec G.length (.var y sigmaV) s) := by
  symm
  simpa only [ValSpace.dof] using congrArg
    (fun xs => xs.foldr (fun a b => a * b) 1)
    (rawShpOf_valueOpenPush horacle hlen hlcSigma hySigma hyG s hy)

/-- Reification agrees at every higher-order type between a pushed de-Bruijn
binder and its fresh-name presentation. -/
theorem fromEl_valueOpenPush
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {Dp Dc : List ValValSem}
    (hlen : G.length = Dp.length) (hD : Dp = Dc)
    (hlcSigma : ValTy.lc sigmaV) (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall (tau : ValTy), y ∉ ValTy.fv tau ->
      forall
        (v : (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau).El)
        (v' : (denotValTyS orc (rho.update y w)
          (ValTy.closePrefix (.var y sigmaV) G) Dc
          (ValTy.openRec G.length (.var y sigmaV) tau)).El),
        HEq v v' ->
        ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau) v =
          ValValSem.fromEl
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (.var y sigmaV) G) Dc
              (ValTy.openRec G.length (.var y sigmaV) tau)) v'
  | .space s, hy, v, v', hv => by
      simp only [ValTy.fv] at hy
      have hvv : v = v' := eq_of_heq hv
      subst hvv
      subst Dc
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromEl]
      rw [dof_valueOpenPush horacle hlen hlcSigma hySigma hyG s hy]
  | .piTy tau0 tau1, hy, v, v', hv => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      have hEl :
          (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0).El =
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (.var y sigmaV) G) Dc
              (ValTy.openRec G.length (.var y sigmaV) tau0)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      have hbeta : HEq
          (fun a : (denotValTyS orc rho
              (G ++ [sigmaV]) (Dp ++ [w]) tau0).El =>
            Except DimError
              (denotValTyS orc rho
                (tau0 :: (G ++ [sigmaV]))
                (ValValSem.fromEl
                  (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a ::
                    (Dp ++ [w])) tau1).El)
          (fun a' : (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (.var y sigmaV) G) Dc
              (ValTy.openRec G.length (.var y sigmaV) tau0)).El =>
            Except DimError
              (denotValTyS orc (rho.update y w)
                (ValTy.openRec G.length (.var y sigmaV) tau0 ::
                  ValTy.closePrefix (.var y sigmaV) G)
                (ValValSem.fromEl
                  (denotValTyS orc (rho.update y w)
                    (ValTy.closePrefix (.var y sigmaV) G) Dc
                    (ValTy.openRec G.length (.var y sigmaV) tau0)) a' :: Dc)
                (ValTy.openRec (G.length + 1) (.var y sigmaV) tau1)).El) := by
        refine Function.hfunext hEl ?_
        intro a a' _
        apply heq_of_eq
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromEl]
      refine ValValSem.fn_congr _ _ hEl ?_
      intro a
      have hva : HEq (v a) (v' (hEl ▸ a)) :=
        heq_app_dep hEl hbeta hv (cast_heq hEl a).symm
      have hcanon := fromEl_valueOpenPush horacle hlen hD hlcSigma
        hySigma hyG tau0 hy.1 a (hEl ▸ a) (cast_heq hEl a).symm
      have hCod :
          (denotValTyS orc rho
            (tau0 :: (G ++ [sigmaV]))
            (ValValSem.fromEl
              (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a ::
                (Dp ++ [w])) tau1).El =
          (denotValTyS orc (rho.update y w)
            (ValTy.openRec G.length (.var y sigmaV) tau0 ::
              ValTy.closePrefix (.var y sigmaV) G)
            (ValValSem.fromEl
              (denotValTyS orc (rho.update y w)
                (ValTy.closePrefix (.var y sigmaV) G) Dc
                (ValTy.openRec G.length (.var y sigmaV) tau0)) (hEl ▸ a) :: Dc)
            (ValTy.openRec (G.length + 1) (.var y sigmaV) tau1)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      apply except_map_heq_congr hCod (v a) (v' (hEl ▸ a)) hva
      intro z z' hzz
      have hlen' : (tau0 :: G).length =
          (ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a :: Dp).length := by
        simp only [List.length_cons, hlen]
      have hD' :
          (ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a :: Dp) =
          (ValValSem.fromEl
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (.var y sigmaV) G) Dc
              (ValTy.openRec G.length (.var y sigmaV) tau0)) (hEl ▸ a) :: Dc) :=
        congrArg₂ List.cons hcanon hD
      have hyG' : forall tauV, tauV ∈ tau0 :: G ->
          y ∉ ValTy.fv tauV := by
        intro tauV htau
        rcases List.mem_cons.mp htau with rfl | htau
        · exact hy.1
        · exact hyG tauV htau
      have ih := fromEl_valueOpenPush horacle hlen' hD' hlcSigma hySigma
        hyG' tau1 hy.2 z z' hzz
      simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
        Nat.succ_eq_add_one] using ih
  termination_by tau _ _ _ _ => ValTy.kindSize tau
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- Canonical soundness transports in both directions across the fresh-name /
pushed-binder presentation boundary. -/
theorem canonicalSound_valueOpenPush_iff
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {Dp Dc : List ValValSem}
    (hlen : G.length = Dp.length) (hD : Dp = Dc)
    (hlcSigma : ValTy.lc sigmaV) (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall (tau : ValTy) (v : ValValSem), y ∉ ValTy.fv tau ->
      (ValCanonicalSoundOfDenotSemS orc (rho.update y w)
          (ValTy.closePrefix (.var y sigmaV) G) Dc
          (ValTy.openRec G.length (.var y sigmaV) tau) v <->
        ValCanonicalSoundOfDenotSemS orc rho
          (G ++ [sigmaV]) (Dp ++ [w]) tau v)
  | .space s, .array a, hy => by
      simp only [ValTy.fv] at hy
      subst Dc
      simp only [ValTy.openRec, ValCanonicalSoundOfDenotSemS]
      rw [dof_valueOpenPush horacle hlen hlcSigma hySigma hyG s hy]
  | .space _, .fn _ _, _ => by
      simp only [ValTy.openRec, ValCanonicalSoundOfDenotSemS]
  | .piTy _ _, .array _, _ => by
      simp only [ValTy.openRec, ValCanonicalSoundOfDenotSemS]
  | .piTy tau0 tau1, .fn T f, hy => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      have hEl :
          (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0).El =
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (.var y sigmaV) G) Dc
              (ValTy.openRec G.length (.var y sigmaV) tau0)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      simp only [ValTy.openRec, ValCanonicalSoundOfDenotSemS]
      constructor
      · rintro ⟨hTleft, hbody⟩
        have hTright : T =
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0).El :=
          hTleft.trans hEl.symm
        refine ⟨hTright, ?_⟩
        intro a out hout
        have harg : HEq (hTright ▸ a) (hTleft ▸ a) :=
          HEq.trans (cast_heq hTright a) (cast_heq hTleft a).symm
        have hcanon := fromEl_valueOpenPush horacle hlen hD hlcSigma
          hySigma hyG tau0 hy.1 (hTright ▸ a) (hTleft ▸ a) harg
        have hlen' : (tau0 :: G).length =
            (ValValSem.fromEl
              (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0)
              (hTright ▸ a) :: Dp).length := by
          simp only [List.length_cons, hlen]
        have hD' :
            (ValValSem.fromEl
              (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0)
              (hTright ▸ a) :: Dp) =
            (ValValSem.fromEl
              (denotValTyS orc (rho.update y w)
                (ValTy.closePrefix (.var y sigmaV) G) Dc
                (ValTy.openRec G.length (.var y sigmaV) tau0))
              (hTleft ▸ a) :: Dc) :=
          congrArg₂ List.cons hcanon hD
        have hyG' : forall tauV, tauV ∈ tau0 :: G ->
            y ∉ ValTy.fv tauV := by
          intro tauV htau
          rcases List.mem_cons.mp htau with rfl | htau
          · exact hy.1
          · exact hyG tauV htau
        have hiff := canonicalSound_valueOpenPush_iff horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := tau0 :: G)
          (Dp := ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0)
            (hTright ▸ a) :: Dp)
          (Dc := ValValSem.fromEl
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (.var y sigmaV) G) Dc
              (ValTy.openRec G.length (.var y sigmaV) tau0))
            (hTleft ▸ a) :: Dc)
          hlen' hD' hlcSigma hySigma hyG' tau1 out hy.2
        simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
          Nat.succ_eq_add_one] using hiff.mp (hbody a out hout)
      · rintro ⟨hTright, hbody⟩
        have hTleft : T =
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (.var y sigmaV) G) Dc
              (ValTy.openRec G.length (.var y sigmaV) tau0)).El :=
          hTright.trans hEl
        refine ⟨hTleft, ?_⟩
        intro a out hout
        have harg : HEq (hTright ▸ a) (hTleft ▸ a) :=
          HEq.trans (cast_heq hTright a) (cast_heq hTleft a).symm
        have hcanon := fromEl_valueOpenPush horacle hlen hD hlcSigma
          hySigma hyG tau0 hy.1 (hTright ▸ a) (hTleft ▸ a) harg
        have hlen' : (tau0 :: G).length =
            (ValValSem.fromEl
              (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0)
              (hTright ▸ a) :: Dp).length := by
          simp only [List.length_cons, hlen]
        have hD' :
            (ValValSem.fromEl
              (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0)
              (hTright ▸ a) :: Dp) =
            (ValValSem.fromEl
              (denotValTyS orc (rho.update y w)
                (ValTy.closePrefix (.var y sigmaV) G) Dc
                (ValTy.openRec G.length (.var y sigmaV) tau0))
              (hTleft ▸ a) :: Dc) :=
          congrArg₂ List.cons hcanon hD
        have hyG' : forall tauV, tauV ∈ tau0 :: G ->
            y ∉ ValTy.fv tauV := by
          intro tauV htau
          rcases List.mem_cons.mp htau with rfl | htau
          · exact hy.1
          · exact hyG tauV htau
        have hiff := canonicalSound_valueOpenPush_iff horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := tau0 :: G)
          (Dp := ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0)
            (hTright ▸ a) :: Dp)
          (Dc := ValValSem.fromEl
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (.var y sigmaV) G) Dc
              (ValTy.openRec G.length (.var y sigmaV) tau0))
            (hTleft ▸ a) :: Dc)
          hlen' hD' hlcSigma hySigma hyG' tau1 out hy.2
        simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
          Nat.succ_eq_add_one] using hiff.mpr (hbody a out hout)
  termination_by tau _ _ => ValTy.kindSize tau
  decreasing_by
    all_goals simp_wf

end ValueSoundnessSemSTransport

namespace ValCanonicalSoundOfDenotSemS

/-- At a base domain, successful checked reification is exactly ordinary
reification. -/
theorem fromElChecked_space_eq_fromEl
    (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (s : ValSpace)
    (a : (denotValTyS orc ρ Γ Δ (.space s)).El)
    (raw : ValValSem)
    (h : ValValSem.fromElChecked
      (denotValTyS orc ρ Γ Δ (.space s)) a = .ok raw) :
    raw = ValValSem.fromEl (denotValTyS orc ρ Γ Δ (.space s)) a := by
  simp only [denotValTyS] at h ⊢
  by_cases hlen : a.length = ValSpace.dof (orc ρ Γ Δ) s
  · simp only [ValValSem.fromElChecked, hlen, ↓reduceIte] at h
    injection h with hraw
    subst raw
    simp only [ValValSem.fromEl]
    rw [resize_eq_self_of_length hlen]
  · simp only [ValValSem.fromElChecked, hlen, ↓reduceIte] at h
    cases h

/-- Every successful higher-kinded reshape is canonical at its target type.
Base reshape's runtime guards provide exact target length.  At Pi kind the
only non-structural step is the checked/ordinary argument transport derived
from `ValueSoundnessOracleSpec.checkedOrdinaryPrefixOracleCoherent`. -/
theorem reshapDenotSemBetweenS_canonical_sound
    (orc : FFSOracleSem) (hspec : ValueSoundnessOracleSpec orc) :
    ∀ (v : ValValSem) (τt τs : ValTy) (ρ : ValEnvSem)
      (Γt : List ValTy) (Δt : List ValValSem)
      (Γs : List ValTy) (Δs : List ValValSem),
      ValCanonicalResultSoundOfDenotSemS orc ρ Γt Δt τt
        (reshapDenotSemBetweenS orc ρ Γt Δt Γs Δs v τt τs)
  | .array a, .space st, .space ss, ρ, Γt, Δt, Γs, Δs => by
      rw [reshapDenotSemBetweenS, reshapArrayBetweenS]
      by_cases hlen : a.length = ValSpace.dof (orc ρ Γs Δs) ss
      · rw [if_pos hlen]
        by_cases hdim : ValSpace.dof (orc ρ Γs Δs) ss =
            ValSpace.dof (orc ρ Γt Δt) st
        · rw [if_pos hdim]
          exact ValCanonicalResultSoundOfDenotSemS.ok (hlen.trans hdim)
        · rw [if_neg hdim]
          exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
      · rw [if_neg hlen]
        exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | .array _, .space _, .piTy _ _, _, _, _, _, _ => by
      rw [reshapDenotSemBetweenS, reshapArrayBetweenS]
      exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | .fn _ _, .space _, _, _, _, _, _, _ => by
      rw [reshapDenotSemBetweenS]
      exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | .array _, .piTy _ _, .space _, _, _, _, _, _ => by
      rw [reshapDenotSemBetweenS]
      exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | .fn _ _, .piTy _ _, .space _, _, _, _, _, _ => by
      rw [reshapDenotSemBetweenS]
      exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | v, .piTy τt₀ τt₁, .piTy τs₀ τs₁, ρ, Γt, Δt, Γs, Δs => by
      rw [reshapDenotSemBetweenS]
      apply ValCanonicalResultSoundOfDenotSemS.ok
      refine ⟨rfl, ?_⟩
      intro argTEl out hout
      generalize hcheck : ValValSem.fromElChecked
        (denotValTyS orc ρ Γt Δt τt₀) argTEl = checkResult at hout
      cases checkResult with
      | error err => simp only [hcheck] at hout; cases hout
      | ok argT =>
          generalize harg : reshapDenotSemBetweenS orc ρ
            Γs Δs Γt Δt argT τs₀ τt₀ = argResult at hout
          cases argResult with
          | error err => simp only [hcheck, harg] at hout; cases hout
          | ok argS =>
              generalize hdecode : ValValSem.toEl
                (denotValTyS orc ρ Γs Δs τs₀) argS = decodeResult at hout
              cases decodeResult with
              | error err =>
                  simp only [hcheck, harg, hdecode] at hout
                  cases hout
              | ok argSEl =>
                  generalize happ : v.applyTyped argSEl = appResult at hout
                  cases appResult with
                  | error err =>
                      simp only [hcheck, harg, hdecode, happ] at hout
                      cases hout
                  | ok res =>
                      simp only [hcheck, harg, hdecode, happ] at hout
                      have hrec := reshapDenotSemBetweenS_canonical_sound
                        orc hspec res τt₁ τs₁ ρ
                        (τt₀ :: Γt) (argT :: Δt)
                        (τs₀ :: Γs) (argS :: Δs) out hout
                      cases τt₀ with
                      | space s =>
                          have heq := fromElChecked_space_eq_fromEl
                            orc ρ Γt Δt s argTEl argT hcheck
                          rw [heq] at hrec
                          exact hrec
                      | piTy dom₀ dom₁ => exact hspec.checkedArgTransport hcheck hrec
  termination_by _v τt τs _ _ _ _ _ =>
    ValTy.kindSize τt + ValTy.kindSize τs
  decreasing_by
    all_goals simp only [ValTy.kindSize_piTy]
    all_goals omega

theorem reshapDenotSemS_canonical_sound
    (orc : FFSOracleSem) (hspec : ValueSoundnessOracleSpec orc)
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (v : ValValSem) (τt τs : ValTy) :
    ValCanonicalResultSoundOfDenotSemS orc ρ Γ Δ τt
      (reshapDenotSemS orc ρ Γ Δ v τt τs) := by
  rw [reshapDenotSemS_eq_between]
  exact reshapDenotSemBetweenS_canonical_sound orc hspec
    v τt τs ρ Γ Δ Γ Δ

end ValCanonicalSoundOfDenotSemS

namespace ValCanonicalSoundOfDenotSemS

/-- Dynamic-oracle counterpart of the packaged application reduction lemma.
Keeping the recovered domain abstract until it is substituted avoids dependent
rewrite motives inside the evaluator's carrier check. -/
theorem denotValB_semS_appV_fn
    (orc : FFSOracleSem) (rho : ValEnvSem)
    (Gamma : List ValTy) (Delta : List ValValSem)
    (e0 e1 : ValExpr) (tauOut d : ValTy)
    (fam : (denotValTyS orc rho Gamma Delta d).El ->
      Except DimError ValValSem)
    (v1 : ValValSem) (arg : (denotValTyS orc rho Gamma Delta d).El)
    (hd : (ValExpr.inferTypeCtx Gamma e0).domain = d)
    (hv0 : denotValB_semS orc rho Gamma Delta e0 =
      .ok (.fn (denotValTyS orc rho Gamma Delta d).El fam))
    (hv1 : denotValB_semS orc rho Gamma Delta e1 = .ok v1)
    (hto : ValValSem.toElDomainChecked (denotValTyS orc rho Gamma Delta d) v1 = .ok arg) :
    denotValB_semS orc rho Gamma Delta (.appV e0 e1) = fam arg := by
  subst d
  rw [denotValB_semS.eq_28]
  simp only [hv0, hv1, ↓reduceDIte, hto]

/-- Canonical application soundness.  Exact soundness of the argument makes
`fromEl (toEl argument)` equal to the original runtime argument, so the raw
substitution law applies at precisely the callback world used by evaluation. -/
theorem appV_result_canonical_sound
    {orc : FFSOracleSem} (hspec : ValueSoundnessOracleSpec orc)
    {epsilon : ValCtx} {rho : ValEnvSem}
    {e0 e1 : ValExpr} {tau0 tau1 tauOut : ValTy}
    (h0 : ValHasType epsilon e0 (.piTy tau0 tau1))
    (h1 : ValHasType epsilon e1 tau0)
    (hsub : tauOut = ValTy.instantiate e1 tau1)
    (hlc1 : ValExpr.lc e1)
    (hfun : ValCanonicalResultSoundOfDenotSemS orc rho [] []
      (.piTy tau0 tau1) (denotValB_semS orc rho [] [] e0))
    (harg : ValCanonicalResultSoundOfDenotSemS orc rho [] [] tau0
      (denotValB_semS orc rho [] [] e1)) :
    ValCanonicalResultSoundOfDenotSemS orc rho [] [] tauOut
      (denotValB_semS orc rho [] [] (.appV e0 e1)) := by
  intro out hout
  cases hv0 : denotValB_semS orc rho [] [] e0 with
  | error err =>
      rw [denotValB_semS.eq_28, hv0] at hout
      cases hout
  | ok funVal =>
      cases funVal with
      | array a =>
          rw [denotValB_semS.eq_28, hv0] at hout
          cases hout
      | fn T fam =>
          obtain ⟨hT, hfam⟩ := hfun (.fn T fam) hv0
          subst T
          cases hv1 : denotValB_semS orc rho [] [] e1 with
          | error err =>
              rw [denotValB_semS.eq_28, hv0, hv1] at hout
              cases hout
          | ok argVal =>
              have hinfer0 : (ValExpr.inferTypeCtx [] e0).domain = tau0 := by
                rw [ValExpr.inferTypeCtx_eq_of_typed h0]
                rfl
              have hargSound := harg argVal hv1
              obtain ⟨arg, hto, hfrom⟩ :=
                toElDomainChecked_fromEl_retract orc tau0 rho [] [] argVal hargSound
              have happ := denotValB_semS_appV_fn orc rho [] [] e0 e1
                tauOut tau0 fam argVal arg hinfer0 hv0 hv1 hto
              have hout' : fam arg = .ok out := happ.symm.trans hout
              have hbody := hfam arg out hout'
              rw [hfrom] at hbody
              have hclosed :=
                (ValueSoundnessSemSTransport.canonicalSound_valueSubst_iff
                  hspec.valueSubstCoherent hlc1
                  (ValExpr.inferTypeCtx_eq_of_typed h1) hv1
                  tau1 out [] [] rfl).mp hbody
              rw [hsub]
              simpa only [ValTy.closePrefix, List.nil_append,
                ValTy.instantiate] using hclosed

theorem space_nonapp_canonical_sound
    {orc : FFSOracleSem} (hspec : ValueSoundnessOracleSpec orc)
    {epsilon : ValCtx} {rho : ValEnvSem}
    {e : ValExpr} {s : ValSpace}
    (henv : ValCanonicalEnvSoundSemS orc epsilon rho)
    (htype : ValHasType epsilon e (.space s))
    (hnotApp : forall e0 e1, e ≠ .appV e0 e1) :
    ValCanonicalResultSoundOfDenotSemS orc rho [] [] (.space s)
      (denotValB_semS orc rho [] [] e) := by
  have hlen_all :=
    ValHasType.inferSpaceCtx_dof_eq_of_space
      (orc := orc rho [] []) (Γ := []) htype
  cases htype with
  | @var _ x _ hlookup =>
      rw [denotValB_semS]
      exact ValCanonicalResultSoundOfDenotSemS.ok (henv x (.space s) hlookup)
  | zero _ =>
      rw [denotValB_semS]
      exact ValCanonicalResultSoundOfDenotSemS.ok
        (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
  | rlit _ =>
      rw [denotValB_semS]
      exact ValCanonicalResultSoundOfDenotSemS.ok
        (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
  | scale _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      split
      · exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @vadd _ e0 e1 _ _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      dsimp only
      split
      · split
        · exact ValCanonicalResultSoundOfDenotSemS.ok
            (ValCanonicalSoundOfDenotSemS.space_arrayOf rfl)
        · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | dsumE _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      split
      · exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | tprodE _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      split
      · exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | delta _ =>
      rw [denotValB_semS]
      exact ValCanonicalResultSoundOfDenotSemS.ok
        (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
  | idelta _ =>
      rw [denotValB_semS]
      exact ValCanonicalResultSoundOfDenotSemS.ok
        (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
  | ttv_space _ _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      split
      · exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | ttv_real _ _ _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      split
      · exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | mtm _ _ _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      split
      · exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @vsum _ s0 _ es _ _ _ _ =>
      rw [denotValB_semS]
      split
      · dsimp only
        split
        · exact ValCanonicalResultSoundOfDenotSemS.error _
        · split
          · exact ValCanonicalResultSoundOfDenotSemS.ok
              (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
          · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @reshap _ e0 tauSrc _ k he hsrc htgt =>
      rw [denotValB_semS]
      cases heval : denotValB_semS orc rho [] [] e0 with
      | error err =>
          simp only
          exact ValCanonicalResultSoundOfDenotSemS.error err
      | ok v =>
          simp only
          exact ValCanonicalSoundOfDenotSemS.reshapDenotSemS_canonical_sound
            orc hspec rho [] [] v (.space s) tauSrc
  | @appV _ e0 e1 tau0 tau1 _ _ h0 h1 hsub hvalid =>
      exact (hnotApp e0 e1 rfl).elim
  | vkrn _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      split
      · exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | vblk _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      split
      · exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | vtrans _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArray
      intro a
      split
      · exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @gsvdS _ e0 a b s0 s1 _ _ _ _ he _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays3
      intro ae aa ab
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only
      split
      · exact ValCanonicalResultSoundOfDenotSemS.error _
      · split
        · rename_i hdim
          apply ValCanonicalResultSoundOfDenotSemS.ok
          exact hdim.trans hlen_all
        · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @gsvdU _ e0 a b s0 s1 _ _ _ _ he _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays3
      intro ae aa ab
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only
      split
      · exact ValCanonicalResultSoundOfDenotSemS.error _
      · split
        · rename_i hdim
          apply ValCanonicalResultSoundOfDenotSemS.ok
          exact hdim.trans hlen_all
        · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @gsvdUI _ e0 a b s0 s1 _ _ _ _ he _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays3
      intro ae aa ab
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only
      split
      · exact ValCanonicalResultSoundOfDenotSemS.error _
      · split
        · rename_i hdim
          apply ValCanonicalResultSoundOfDenotSemS.ok
          exact hdim.trans hlen_all
        · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @gsvdV _ e0 a b s0 s1 _ _ _ _ he _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays3
      intro ae aa ab
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only
      split
      · exact ValCanonicalResultSoundOfDenotSemS.error _
      · split
        · rename_i hdim
          apply ValCanonicalResultSoundOfDenotSemS.ok
          exact hdim.trans hlen_all
        · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @gsvdVI _ e0 a b s0 s1 _ _ _ _ he _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays3
      intro ae aa ab
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only
      split
      · exact ValCanonicalResultSoundOfDenotSemS.error _
      · split
        · rename_i hdim
          apply ValCanonicalResultSoundOfDenotSemS.ok
          exact hdim.trans hlen_all
        · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @pinv_tensor _ e0 s0 s1 he =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArray
      intro a
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only
      by_cases hshape : a.length =
          ValSpace.dof (orc rho [] []) s0 * ValSpace.dof (orc rho [] []) s1
      · rw [if_pos hshape]
        exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @pinv_raw _ e0 s0 he hnontensor =>
      cases s0 with
      | tprod a b => exact (hnontensor a b rfl).elim
      | empty | real | dsum | ffs =>
          rw [denotValB_semS]
          apply ValCanonicalResultSoundOfDenotSemS.bindArray
          intro a
          rw [ValExpr.inferSpaceCtx_eq_of_typed he]
          dsimp only
          split
          · exact ValCanonicalResultSoundOfDenotSemS.ok
              (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
          · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @gpinv _ e0 a b s0 s1 _ _ _ _ he _ _ =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays3
      intro ae aa ab
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only
      by_cases hshape : GSVDInputsShape
          (ValSpace.dof (orc rho [] []) s0)
          (ValSpace.dof (orc rho [] []) s1) ae aa ab
      · rw [if_pos hshape]
        exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @rrefRep _ _ _ _ p0 p1 _ h1 =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArrays
      intro a0 a1
      rw [ValExpr.inferSpaceCtx_eq_of_typed h1]
      dsimp only
      by_cases hshape :
          ValSpace.dof (orc rho [] []) p0 = ValSpace.dof (orc rho [] []) p1 ∧
            a0.length = (a0.length / ValSpace.dof (orc rho [] []) p0) *
              ValSpace.dof (orc rho [] []) p0 ∧
            a1.length = ValSpace.dof (orc rho [] []) p0 *
              ValSpace.dof (orc rho [] []) p0
      · rw [if_pos hshape]
        exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @inv_tensor _ e0 s0 s1 he =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArray
      intro a
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only
      by_cases hshape : a.length =
          ValSpace.dof (orc rho [] []) s0 * ValSpace.dof (orc rho [] []) s1
      · rw [if_pos hshape]
        exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @inv_raw _ e0 s0 he hnontensor =>
      cases s0 with
      | tprod a b => exact (hnontensor a b rfl).elim
      | empty | real | dsum | ffs =>
          rw [denotValB_semS]
          apply ValCanonicalResultSoundOfDenotSemS.bindArray
          intro a
          rw [ValExpr.inferSpaceCtx_eq_of_typed he]
          dsimp only
          split
          · exact ValCanonicalResultSoundOfDenotSemS.ok
              (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
          · exact ValCanonicalResultSoundOfDenotSemS.error .mismatch
  | @svds _ e0 s0 s1 he =>
      rw [denotValB_semS]
      apply ValCanonicalResultSoundOfDenotSemS.bindArray
      intro a
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only
      by_cases hshape : a.length =
          ValSpace.dof (orc rho [] []) s0 * ValSpace.dof (orc rho [] []) s1
      · rw [if_pos hshape]
        exact ValCanonicalResultSoundOfDenotSemS.ok
          (ValCanonicalSoundOfDenotSemS.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValCanonicalResultSoundOfDenotSemS.error .mismatch

/-- Environment-aware value-denotation soundness at the root world. -/
theorem valHasType_denotValB_semS_canonical_sound_aux
    {orc : FFSOracleSem} (hspec : ValueSoundnessOracleSpec orc)
    {epsilon : ValCtx} {rho : ValEnvSem} {e : ValExpr} {tau : ValTy}
    (henv : ValCanonicalEnvSoundSemS orc epsilon rho)
    (hlc : ValExpr.lc e)
    (htype : ValHasType epsilon e tau) :
    ValCanonicalResultSoundOfDenotSemS orc rho [] [] tau
      (denotValB_semS orc rho [] [] e) := by
  cases htau : tau with
  | space s =>
      subst tau
      by_cases happ : exists e0 e1,
          e = .appV e0 e1
      · obtain ⟨e0, e1, rfl⟩ := happ
        cases htype with
        | @appV _ _ _ tau0 tau1 _ _ h0 h1 hsub _hvalid =>
            cases hlc with
            | appV hlc0 hlc1 =>
                exact appV_result_canonical_sound hspec h0 h1
                  (hsub.trans (ValTy.applyCodomain_eq_instantiate
                    (by simpa only [h0.inferType_eq_of_typed] using hlc0.inferType) hlc1)) hlc1
                  (valHasType_denotValB_semS_canonical_sound_aux hspec
                    henv hlc0 h0)
                  (valHasType_denotValB_semS_canonical_sound_aux hspec
                    henv hlc1 h1)
      · exact space_nonapp_canonical_sound hspec henv htype
          (by
            intro e0 e1 heq
            exact happ ⟨e0, e1, heq⟩)
  | piTy tau0 tau1 =>
      subst tau
      cases htype with
      | @var _ x _ hlookup =>
          rw [denotValB_semS]
          exact ValCanonicalResultSoundOfDenotSemS.ok
            (henv x (.piTy tau0 tau1) hlookup)
      | @vlam _ _ _ k0 k1 body L htvalid hbody =>
          cases hlc with
          | vlam Llc hlcTau0 _hlcTau1 hlcBody =>
              rw [denotValB_semS]
              apply ValCanonicalResultSoundOfDenotSemS.ok
              refine ⟨rfl, ?_⟩
              intro a out hout
              let avoid : Finset VName :=
                L ∪ Llc ∪ epsilon.fvSupport ∪
                  ValTy.fv tau0 ∪ ValTy.fv tau1 ∪ ValExpr.fv body
              let xf := freshFor avoid
              have hxf : xf ∉ avoid := freshFor_notMem avoid
              have hxL : xf ∉ L := by
                intro hx
                apply hxf
                simp only [avoid, Finset.mem_union]
                aesop
              have hxLlc : xf ∉ Llc := by
                intro hx
                apply hxf
                simp only [avoid, Finset.mem_union]
                aesop
              have hxSupport : xf ∉ epsilon.fvSupport := by
                intro hx
                apply hxf
                simp only [avoid, Finset.mem_union]
                aesop
              have hxTau0 : xf ∉ ValTy.fv tau0 := by
                intro hx
                apply hxf
                simp only [avoid, Finset.mem_union]
                aesop
              have hxTau1 : xf ∉ ValTy.fv tau1 := by
                intro hx
                apply hxf
                simp only [avoid, Finset.mem_union]
                aesop
              have hxBody : xf ∉ ValExpr.fv body := by
                intro hx
                apply hxf
                simp only [avoid, Finset.mem_union]
                aesop
              let raw :=
                ValValSem.fromEl (denotValTyS orc rho [] [] tau0) a
              have henv' := ValCanonicalEnvSoundSemS.update orc hspec.fvIrrel
                epsilon rho xf tau0 henv hxSupport hxTau0 a
              have hlcOpen := hlcBody xf hxLlc
              have htypedOpen := hbody xf hxL
              have ihbody :=
                valHasType_denotValB_semS_canonical_sound_aux hspec
                  henv' hlcOpen htypedOpen
              have heval :=
                DirectOracleEval.valueOpenPushEvalCoherent_from_leaf
                  hspec.valueOpenPushOracleCoherent
                (rho := rho) (y := xf) (sigmaV := tau0) (w := raw)
                (e := body) hlcTau0 hlcOpen hxTau0 hxBody
              have hnamed : denotValB_semS orc (rho.update xf raw) [] []
                  (ValExpr.openVar xf tau0 body) = .ok out :=
                heval.trans hout
              have hsNamed := ihbody out hnamed
              have hopen :=
                ValueSoundnessSemSTransport.canonicalSound_valueOpenPush_iff
                  hspec.valueOpenPushOracleCoherent
                  (rho := rho) (y := xf) (sigmaV := tau0) (w := raw)
                  (G := []) (Dp := []) (Dc := []) rfl rfl hlcTau0 hxTau0
                  (by simp) tau1 out hxTau1
              simpa only [ValTy.closePrefix, List.nil_append, ValTy.openVar] using
                hopen.mp hsNamed
      | @appV _ e0 e1 tau0' tau1' _ _ h0 h1 hsub _hvalid =>
          cases hlc with
          | appV hlc0 hlc1 =>
              exact appV_result_canonical_sound hspec h0 h1
                  (hsub.trans (ValTy.applyCodomain_eq_instantiate
                    (by simpa only [h0.inferType_eq_of_typed] using hlc0.inferType) hlc1)) hlc1
                (valHasType_denotValB_semS_canonical_sound_aux hspec
                  henv hlc0 h0)
                (valHasType_denotValB_semS_canonical_sound_aux hspec
                  henv hlc1 h1)
      | @reshap _ e0 tauSrc _ _k _he _hsrc _htgt =>
          rw [denotValB_semS]
          cases heval : denotValB_semS orc rho [] [] e0 with
          | error err =>
              simp only
              exact ValCanonicalResultSoundOfDenotSemS.error err
          | ok v =>
              simp only
              exact reshapDenotSemS_canonical_sound orc hspec rho [] [] v
                (.piTy tau0 tau1) tauSrc
  termination_by ValExpr.csize e
  decreasing_by
    all_goals first
      | assumption
      | (simp only [ValSoundOfDenotSem.ValExpr.csize_openRec]; omega)
      | (subst_vars; simp only [ValExpr.csize,
          ValSoundOfDenotSem.ValExpr.csize_openRec]; omega)

/-- The familiar zero-extension formulation follows immediately from the
canonical theorem.  Its environment premise remains canonical: admitting
short base arrays would make higher-order application unsound for an oracle
that observes the local runtime telescope. -/
theorem valHasType_denotValB_semS_sound_aux
    {orc : FFSOracleSem} (hspec : ValueSoundnessOracleSpec orc)
    {epsilon : ValCtx} {rho : ValEnvSem} {e : ValExpr} {tau : ValTy}
    (henv : ValCanonicalEnvSoundSemS orc epsilon rho)
    (hlc : ValExpr.lc e)
    (htype : ValHasType epsilon e tau) :
    ValResultSoundOfDenotSemS orc rho [] [] tau
      (denotValB_semS orc rho [] [] e) := by
  intro out hout
  exact implies_sound orc tau rho [] [] out
    (valHasType_denotValB_semS_canonical_sound_aux hspec henv hlc htype out hout)

end ValCanonicalSoundOfDenotSemS

/-- Public root theorem: exact value soundness for an environment-aware FFS
oracle and a non-constant, canonically sound named environment. -/
theorem valHasType_denotValB_semS_canonical_sound
    {orc : FFSOracleSem} (hspec : ValueSoundnessOracleSpec orc)
    {epsilon : ValCtx} {rho : ValEnvSem} {e : ValExpr} {tau : ValTy}
    (henv : ValCanonicalEnvSoundSemS orc epsilon rho)
    (hlc : ValExpr.lc e)
    (htype : ValHasType epsilon e tau) :
    ValCanonicalResultSoundOfDenotSemS orc rho [] [] tau
      (denotValB_semS orc rho [] [] e) :=
  ValCanonicalSoundOfDenotSemS.valHasType_denotValB_semS_canonical_sound_aux
    hspec henv hlc htype

/-- Public zero-extension corollary of environment-aware exact value
soundness. -/
theorem valHasType_denotValB_semS_sound
    {orc : FFSOracleSem} (hspec : ValueSoundnessOracleSpec orc)
    {epsilon : ValCtx} {rho : ValEnvSem} {e : ValExpr} {tau : ValTy}
    (henv : ValCanonicalEnvSoundSemS orc epsilon rho)
    (hlc : ValExpr.lc e)
    (htype : ValHasType epsilon e tau) :
    ValResultSoundOfDenotSemS orc rho [] [] tau
      (denotValB_semS orc rho [] [] e) :=
  ValCanonicalSoundOfDenotSemS.valHasType_denotValB_semS_sound_aux
    hspec henv hlc htype

end

end GLang
