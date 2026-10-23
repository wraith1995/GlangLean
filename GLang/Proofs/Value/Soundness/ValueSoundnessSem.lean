

import GLang.Value.Supporting.TotalDimensionSemantics
import GLang.Proofs.Value.Binding.ValueRaise
import GLang.Proofs.Value.Binding.ValueBetaOracle
import GLang.Proofs.Value.Soundness.ValueInferSpaceSound
import GLang.Proofs.Value.Typing.ValueInfer

namespace GLang

set_option maxErrors 5

namespace ValSoundOfDenot

/-- Same-shape relation on `ValTy`: `τ` and `τ'` agree at the head
    constructor and recursively on the function-type sub-types. This
    is the structural shadow of "same kind" used to make the
    typeless soundness recursion go through without a `ValKind`
    parameter.

    - Both `.space _`: same shape.
    - `.piTy _ τ₂ τ₃` and `.piTy _ τ₂' τ₃'`: same shape iff
      `τ₂` ~ `τ₂'` and `τ₃` ~ `τ₃'`.

    The argument-name `x` is irrelevant (only the structure matters,
    matching `ValKind`'s abstract `.arrow k₀ k₁`). -/
def ValTy.SameShape : ValTy → ValTy → Prop
  | .space _, .space _ => True
  | .piTy τ₂ τ₃, .piTy τ₂' τ₃' =>
      ValTy.SameShape τ₂ τ₂' ∧ ValTy.SameShape τ₃ τ₃'
  | _, _ => False

@[simp] theorem ValTy.SameShape.refl : ∀ τ : ValTy, ValTy.SameShape τ τ
  | .space _ => trivial
  | .piTy τ₂ τ₃ => ⟨ValTy.SameShape.refl τ₂, ValTy.SameShape.refl τ₃⟩

theorem ValTy.SameShape.symm : ∀ {τ₁ τ₂ : ValTy},
    ValTy.SameShape τ₁ τ₂ → ValTy.SameShape τ₂ τ₁
  | .space _, .space _, _ => trivial
  | .piTy a₁ a₂, .piTy b₁ b₂, h =>
      ⟨ValTy.SameShape.symm h.1, ValTy.SameShape.symm h.2⟩
  | .space _, .piTy _ _, h => h.elim
  | .piTy _ _, .space _, h => h.elim

theorem ValTy.SameShape.trans : ∀ {τ₁ τ₂ τ₃ : ValTy},
    ValTy.SameShape τ₁ τ₂ → ValTy.SameShape τ₂ τ₃ → ValTy.SameShape τ₁ τ₃
  | .space _, .space _, .space _, _, _ => trivial
  | .piTy a₁ a₂, .piTy b₁ b₂, .piTy c₁ c₂, h₁, h₂ =>
      ⟨ValTy.SameShape.trans h₁.1 h₂.1, ValTy.SameShape.trans h₁.2 h₂.2⟩
  | .space _, .piTy _ _, _, h, _ => h.elim
  | .piTy _ _, .space _, _, h, _ => h.elim
  | .space _, .space _, .piTy _ _, _, h => h.elim
  | .piTy _ _, .piTy _ _, .space _, _, h => h.elim

/-- Substitution preserves `SameShape` reflexivity-style: `subst x e τ`
    has the same shape as `τ`. Substitution recurses under the `.piTy`
    constructor and replaces `.space`-bound variables; the head
    constructor is unchanged. -/
theorem ValTy.SameShape_subst (x : VName) (e : ValExpr) :
    ∀ τ : ValTy, ValTy.SameShape (ValTy.subst x e τ) τ
  | .space _ => by unfold ValTy.subst; trivial
  | .piTy τ₂ τ₃ => by
      unfold ValTy.subst
      exact ⟨ValTy.SameShape_subst x e τ₂, ValTy.SameShape_subst x e τ₃⟩

/-- `openRec` (opening a bound index) preserves shape: `openRec k u τ` has the
    same shape as `τ`. Opening recurses through `.piTy` without changing the
    `.space`/`.piTy` head, so the shape is unchanged. -/
theorem ValTy.SameShape_openRec (k : Nat) (u : ValExpr) :
    ∀ τ : ValTy, ValTy.SameShape (ValTy.openRec k u τ) τ
  | .space _ => by unfold ValTy.openRec; trivial
  | .piTy τ₂ τ₃ => by
      unfold ValTy.openRec
      exact ⟨ValTy.SameShape_openRec k u τ₂, ValTy.SameShape_openRec (k+1) u τ₃⟩

/-- Raising de Bruijn indices preserves the type's `.space`/`.piTy` shape. -/
theorem ValTy.SameShape_raise (n cutoff : Nat) :
    ∀ τ : ValTy, ValTy.SameShape (ValTy.raise n cutoff τ) τ
  | .space _ => trivial
  | .piTy τ₀ τ₁ =>
      ⟨ValTy.SameShape_raise n cutoff τ₀,
        ValTy.SameShape_raise n (cutoff + 1) τ₁⟩

/-- Dependent result substitution preserves the function/array type structure. -/
theorem ValTy.SameShape_substBound (k : Nat) (u : ValExpr) :
    ∀ t : ValTy, ValTy.SameShape (ValTy.substBound k u t) t
  | .space _ => trivial
  | .piTy a b => ⟨ValTy.SameShape_substBound k u a,
      ValTy.SameShape_substBound (k + 1) u b⟩

/-- Two types with the same `ValKind` have the same `SameShape`. -/
theorem ValTy.SameShape_of_sameKind (k : ValKind) :
    ∀ {ε ε' : ValCtx} {τ τ' : ValTy}
      (_h : ValTValid ε τ k) (_h' : ValTValid ε' τ' k),
      ValTy.SameShape τ τ' := by
  induction k with
  | base =>
      intro _ _ _ _ h h'
      cases h with
      | space _ =>
          cases h' with
          | space _ => trivial
  | arrow k₀ k₁ ih₀ ih₁ =>
      intro ε ε' τ τ' h h'
      cases h with
      | @piTy _ τ₀ τ₁ _ _ L h_dom h_cod =>
          cases h' with
          | @piTy _ τ₀' τ₁' _ _ L' h_dom' h_cod' =>
              refine ⟨ih₀ h_dom h_dom', ?_⟩
              -- Codomains are cofinite bodies; instantiate at a fresh `x`, use the
              -- IH on the opened codomains, then strip the opening (shape-invariant).
              obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (L ∪ L')
              rw [Finset.mem_union, not_or] at hx
              have hopen : ValTy.SameShape (ValTy.openVar x τ₀ τ₁)
                  (ValTy.openVar x τ₀' τ₁') :=
                ih₁ (h_cod x hx.1) (h_cod' x hx.2)
              exact ((ValTy.SameShape_openRec 0 (.var x τ₀) τ₁).symm.trans hopen).trans
                (ValTy.SameShape_openRec 0 (.var x τ₀') τ₁')

end ValSoundOfDenot

def ValSoundOfDenotSem (orc : FFSOracle) :
    ValEnvSem → List ValValSem → ValTy → ValValSem → Prop
  | _ρ, _Δ, .space s, .array f =>
      ∀ i : ValIdx, ¬ ValSpace.shapeInBounds orc s i → f i = 0
  | _ρ, _Δ, .space _, .fn _ _ => False
  | _ρ, _Δ, .piTy _ _, .array _ => False
  | ρ, Δ, .piTy τ₀ τ₁, .fn T fam =>
      -- LN (D1): the carrier `T` equals the domain's denotation carrier; the body
      -- family is pointwise sound at the codomain under the LOCAL env `Δ` extended
      -- by the domain value (mirrors `denotValB_sem`'s `.vlam` arm: push onto `Δ`,
      -- recurse STRUCTURALLY on `τ₁`).
      ∃ h : T = (denotValTy orc ρ Δ τ₀).El,
        ∀ (v : T) (out : ValValSem), fam v = .ok out →
            ValSoundOfDenotSem orc ρ
              (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) (h ▸ v) :: Δ)
              τ₁ out

/-- Partial correctness for a partial denotation: whenever it succeeds, its
payload is sound. This predicate deliberately does **not** assert that an
evaluation succeeds. `DimError` is neither defaulted nor ruled out here;
adequacy/`LegacyResultAgree` is the separate layer that establishes an actual `.ok`. -/
def ValResultSoundOfDenotSem (orc : FFSOracle) (ρ : ValEnvSem)
    (Δ : List ValValSem) (τ : ValTy) (r : Except DimError ValValSem) : Prop :=
  ∀ out : ValValSem, r = .ok out → ValSoundOfDenotSem orc ρ Δ τ out

namespace ValResultSoundOfDenotSem

/-- A successful result is partially sound exactly when its payload is sound. -/
theorem ok {orc : FFSOracle} {ρ : ValEnvSem} {Δ : List ValValSem}
    {τ : ValTy} {v : ValValSem} (h : ValSoundOfDenotSem orc ρ Δ τ v) :
    ValResultSoundOfDenotSem orc ρ Δ τ (.ok v) := by
  intro out hout
  cases hout
  exact h

/-- An error result satisfies partial correctness vacuously. -/
theorem error {orc : FFSOracle} {ρ : ValEnvSem} {Δ : List ValValSem}
    {τ : ValTy} (err : DimError) :
    ValResultSoundOfDenotSem orc ρ Δ τ (.error err) := by
  intro out hout
  cases hout

end ValResultSoundOfDenotSem

/-- The FFS-`dof` of the operand's inferred space is opening-stable: opening only
    perturbs the ambient space up to `SDEq`, which the oracle respects
    (`sdeq_respect` + `openRec_respect`). The `SDEq` premise `ih` is the
    structural IH of `inferSpaceCtx_SDEq` on the operand. -/
theorem inferSpaceCtx_gsvd_ffs_aux (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ : List ValTy)
    (k : Nat) (x : VName) (σ : ValTy) (e : ValExpr) (p : ValFFSProp)
    (ih : ValSpace.SDEq orc (ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e))
            (ValExpr.inferSpaceCtx Γ e)) :
    ValSpace.dof orc (.ffs p (ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e))
                        (ValExpr.openRec k (.var x σ) e))
      = ValSpace.dof orc (.ffs p (ValExpr.inferSpaceCtx Γ e) e) := by
  have hSDEq : ValSpace.SDEq orc (ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e))
      (ValSpace.openRec k (.var x σ) (ValExpr.inferSpaceCtx Γ e)) :=
    Eq.trans ih (ValSpace.SDEq_openRec orc k (.var x σ) (ValExpr.inferSpaceCtx Γ e))
  have horc : orc p (ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e))
        (ValExpr.openRec k (.var x σ) e)
      = orc p (ValExpr.inferSpaceCtx Γ e) e :=
    (FFSOracle.sdeq_respect orc p (ValExpr.openRec k (.var x σ) e) hSDEq).trans
      (FFSOracle.openRec_respect orc k (.var x σ) p (ValExpr.inferSpaceCtx Γ e) e)
  simp only [ValSpace.dof, ValSpace.shpOf_ffs]; rw [horc]

/-! ### `inferSpaceCtx` respects `SDEq` under opening.

The denotation consults `inferSpaceCtx Γ subexpr` only through `dof` and
`.tprod`/`.dsum` destructuring (`SDEq`). Opening a bound index keeps the inferred
space `SDEq`: leaves/annotations are `openRec`-invariant in `dof`/structure
(`SDEq_openRec`, `spaceOf_openRec`), `bvar k` maps to `var x σ` with `Γ.getD k =
σ` (the raised declaration type is `SDEq` to that raw entry), and the (G)SVD/SVDS arms — which embed the
operand's inferred space into an `.ffs` — use the oracle chain
`openRec_respect` + `sdeq_respect`. Structural recursion on `e`. -/

theorem denotValTy_El_eq_carrierEl (orc : FFSOracle) :
    ∀ (ρ : ValEnvSem) (Δ : List ValValSem) (τ : ValTy),
      (denotValTy orc ρ Δ τ).El = τ.carrierEl
  | _ρ, _Δ, .space _s => rfl
  | ρ, Δ, .piTy τ₀ τ₁ => by
      show ((v : (denotValTy orc ρ Δ τ₀).El) →
              Except DimError (denotValTy orc ρ (ValValSem.fromEl
                (denotValTy orc ρ Δ τ₀) v :: Δ) τ₁).El)
          = (τ₀.carrierEl → Except DimError τ₁.carrierEl)
      have hdom : (denotValTy orc ρ Δ τ₀).El = τ₀.carrierEl :=
        denotValTy_El_eq_carrierEl orc ρ Δ τ₀
      have hcod : ∀ v, Except DimError (denotValTy orc ρ
          (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v :: Δ) τ₁).El
            = Except DimError τ₁.carrierEl :=
        fun v => congrArg (Except DimError) (denotValTy_El_eq_carrierEl orc ρ _ τ₁)
      -- The Π collapses to a plain arrow since the codomain is constant.
      rw [show ((v : (denotValTy orc ρ Δ τ₀).El) →
              Except DimError (denotValTy orc ρ (ValValSem.fromEl
                (denotValTy orc ρ Δ τ₀) v :: Δ) τ₁).El)
            = ((_v : (denotValTy orc ρ Δ τ₀).El) →
                Except DimError τ₁.carrierEl) from
          congrArg (fun F => (v : (denotValTy orc ρ Δ τ₀).El) → F v) (funext hcod)]
      rw [hdom]

namespace ValSoundOfDenot

/-- `SameShape` types have equal structural carriers. -/
theorem ValTy.SameShape.carrierEl_eq :
    ∀ {d d' : ValTy}, ValSoundOfDenot.ValTy.SameShape d d' → d.carrierEl = d'.carrierEl
  | .space _, .space _, _ => rfl
  | .piTy a b, .piTy a' b', h => by
      show (a.carrierEl → Except DimError b.carrierEl) =
        (a'.carrierEl → Except DimError b'.carrierEl)
      rw [ValTy.SameShape.carrierEl_eq h.1, ValTy.SameShape.carrierEl_eq h.2]
  | .space _, .piTy _ _, h => h.elim
  | .piTy _ _, .space _, h => h.elim

/-- `SameShape` is preserved by taking domains. -/
theorem ValTy.SameShape.domain :
    ∀ {d d' : ValTy}, ValSoundOfDenot.ValTy.SameShape d d' →
      ValSoundOfDenot.ValTy.SameShape d.domain d'.domain
  | .space _, .space _, h => h
  | .piTy _ _, .piTy _ _, h => h.1
  | .space _, .piTy _ _, h => h.elim
  | .piTy _ _, .space _, h => h.elim

end ValSoundOfDenot

/-- Lift heterogeneous equality through a successful `Except` result. -/
theorem except_ok_heq {E : Type} {A B : Type} (hAB : A = B)
    {a : A} {b : B} (hab : HEq a b) :
    HEq (Except.ok a : Except E A) (Except.ok b : Except E B) := by
  subst hAB
  exact heq_of_eq (congrArg Except.ok (eq_of_heq hab))

/-- The same error is heterogeneously equal at equal payload types. -/
theorem except_error_heq {E : Type} {A B : Type} (hAB : A = B) (e : E) :
    HEq (Except.error e : Except E A) (Except.error e : Except E B) := by
  subst hAB
  rfl

/-- `toEl ∘ denotValTy` agrees (`HEq`) on `SameShape` types, for any `ρ`/`Δ` and a
    fixed value `v`. Generalizes `toEl_denotValTy_openRec` from `openRec`-related to
    merely `SameShape` types. kindSize recursion on the shape. -/
theorem toEl_denotValTy_SameShape (orc : FFSOracle) :
    ∀ (d d' : ValTy), ValSoundOfDenot.ValTy.SameShape d d' →
      ∀ (ρ ρ' : ValEnvSem) (Δ Δ' : List ValValSem) (v : ValValSem),
      HEq (ValValSem.toEl (denotValTy orc ρ Δ d) v)
          (ValValSem.toEl (denotValTy orc ρ' Δ' d') v)
  | .space _s, .space _s', _hss, ρ, ρ', Δ, Δ', v => by
      apply heq_of_eq
      cases v <;> rfl
  | .piTy d₀ d₁, .piTy d₀' d₁', hss, ρ, ρ', Δ, Δ', v => by
      have hssAll : ValSoundOfDenot.ValTy.SameShape (.piTy d₀ d₁) (.piTy d₀' d₁') := hss
      obtain ⟨hss0, hss1⟩ := hss
      have hEl : (denotValTy orc ρ Δ d₀).El = (denotValTy orc ρ' Δ' d₀').El := by
        rw [denotValTy_El_eq_carrierEl orc ρ Δ d₀,
            denotValTy_El_eq_carrierEl orc ρ' Δ' d₀',
            ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss0]
      have hPiEl : (denotValTy orc ρ Δ (.piTy d₀ d₁)).El =
          (denotValTy orc ρ' Δ' (.piTy d₀' d₁')).El := by
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl,
          ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hssAll]
      cases v with
      | array _ =>
          simp only [denotValTy, ValValSem.toEl]
          exact except_error_heq hPiEl DimError.mismatch
      | fn T' f =>
          simp only [denotValTy, ValValSem.toEl]
          by_cases hT : (denotValTy orc ρ Δ d₀).El = T'
          · have hT' : (denotValTy orc ρ' Δ' d₀').El = T' := hEl ▸ hT
            rw [dif_pos hT, dif_pos hT']
            apply except_ok_heq hPiEl
            refine Function.hfunext hEl ?_
            intro a a' haa
            have hcast : f (hT ▸ a) = f (hT' ▸ a') := by
              congr 1
              apply eq_of_heq
              exact HEq.trans (cast_heq hT a) (HEq.trans haa (HEq.symm (cast_heq hT' a')))
            rw [hcast]
            have hCodEl : (denotValTy orc ρ
                (ValValSem.fromEl (denotValTy orc ρ Δ d₀) a :: Δ) d₁).El =
                (denotValTy orc ρ'
                  (ValValSem.fromEl (denotValTy orc ρ' Δ' d₀') a' :: Δ') d₁').El := by
              rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl,
                ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss1]
            cases hf : f (hT' ▸ a') with
            | error err => exact except_error_heq hCodEl err
            | ok out =>
                exact toEl_denotValTy_SameShape orc d₁ d₁' hss1 ρ ρ'
                  (ValValSem.fromEl (denotValTy orc ρ Δ d₀) a :: Δ)
                  (ValValSem.fromEl (denotValTy orc ρ' Δ' d₀') a' :: Δ') out
          · have hT' : ¬ (denotValTy orc ρ' Δ' d₀').El = T' := fun h => hT (hEl ▸ h)
            rw [dif_neg hT, dif_neg hT']
            exact except_error_heq hPiEl DimError.mismatch
  | .space _, .piTy _ _, hss, _, _, _, _, _ => hss.elim
  | .piTy _ _, .space _, hss, _, _, _, _, _ => hss.elim
  termination_by d _ _ _ _ _ _ _ => ValTy.kindSize d
  decreasing_by all_goals (simp only [ValTy.kindSize_piTy]; omega)

/-- The `.appV` denotation arm's domain has `SameShape` across opening: the
    function subexpression's inferred-type domain is opening-invariant up to shape.
    Mirrors `inferTypeCtx_domain_carrierEl` (same 28-arm dispatch) but lands in
    `SameShape` (finer than carrierEl-equality). -/
theorem inferTypeCtx_SameShape (Γ : List ValTy)
    (k : Nat) (x : VName) (σ : ValTy) (hΓk : Γ.getD k default = σ) :
    ∀ e : ValExpr,
      ValSoundOfDenot.ValTy.SameShape
        (ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e))
        (ValExpr.inferTypeCtx Γ e)
  | .bvar i => by
      by_cases hi : i = k
      · subst i
        simp only [ValExpr.openRec, if_pos rfl, ValExpr.inferTypeCtx, ValTyCtx.lookupUse, hΓk]
        exact (ValSoundOfDenot.ValTy.SameShape_raise (k + 1) 0 σ).symm
      · simp only [ValExpr.openRec, if_neg hi, ValExpr.inferTypeCtx]
        exact ValSoundOfDenot.ValTy.SameShape.refl _
  | .var y t => by
      exact ValSoundOfDenot.ValTy.SameShape_openRec k (.var x σ) t
  | .vlam t0 t1 e => by
      exact ValSoundOfDenot.ValTy.SameShape_openRec k (.var x σ) (.piTy t0 t1)
  | .zero s => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .rlit r => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .scale e0 e1 => by
      exact inferTypeCtx_SameShape Γ k x σ hΓk e1
  | .dsumE e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .tprodE e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .appV e0 e1 => by
      have ih := inferTypeCtx_SameShape Γ k x σ hΓk e0
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      generalize h0 : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e0) = t at ih ⊢
      generalize h1 : ValExpr.inferTypeCtx Γ e0 = t' at ih ⊢
      cases t <;> cases t' with
      | space _ => simpa [ValSoundOfDenot.ValTy.SameShape] using ih
      | piTy d c =>
          first
          | exact ih.elim
          | exact (ValSoundOfDenot.ValTy.SameShape_substBound 0 _ _).trans
              (ih.2.trans (ValSoundOfDenot.ValTy.SameShape_substBound 0 _ _).symm)
  | .vkrn e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .vblk e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .rrefRep e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .vadd s e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .delta i s => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .idelta s => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .vsum s es => by
      cases es with
      | nil => trivial
      | cons e es => exact inferTypeCtx_SameShape Γ k x σ hΓk e
  | .ttv s e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .mtm i j s0 s1 e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .reshap e t t0 => by
      exact ValSoundOfDenot.ValTy.SameShape_openRec k (.var x σ) t
  | .vtrans e => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .pinv e => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .inv e => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .svds e => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .gsvdS e a b => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .gsvdU e a b => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .gsvdUI e a b => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .gsvdV e a b => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .gsvdVI e a b => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial
  | .gpinv e a b => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      repeat' split
      all_goals trivial

/-- The inferred function domain has the same shape after opening. -/
theorem inferTypeCtx_domain_SameShape (Γ : List ValTy)
    (k : Nat) (x : VName) (σ : ValTy) (hΓk : Γ.getD k default = σ)
    (e : ValExpr) :
    ValSoundOfDenot.ValTy.SameShape
      (ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e)).domain
      (ValExpr.inferTypeCtx Γ e).domain :=
  (inferTypeCtx_SameShape Γ k x σ hΓk e).domain

/-- Transporting a successful argument into a closure domain commutes with
`Except.bind`; errors are preserved verbatim. -/
theorem except_bind_cast_eq {T A : Type} (h : T = A) (r : Except DimError A)
    (f : T → Except DimError ValValSem) :
    r.bind (fun a => f (h ▸ a)) =
      (cast (congrArg (Except DimError) h.symm) r).bind f := by
  cases h
  rfl

open scoped Classical in
/-- Dependent-`dite` congruence for the `.appV` arm: when the recovered domain
    carriers agree (`hEl`) and the coerced arguments agree (`htoEl`, an `HEq`), the
    two domain-aware applications coincide for any function value `v₀`. -/
theorem appV_dite_cong {S S' : ValTypeSem} (v₀ w w' : ValValSem)
    (hEl : S.El = S'.El)
    (htoEl : HEq (ValValSem.toEl S w) (ValValSem.toEl S' w')) :
    (match v₀ with
     | .fn T f => if h : T = S.El then
         (ValValSem.toEl S w).bind (fun arg => f (h ▸ arg))
       else (Except.error .mismatch : Except DimError ValValSem)
     | .array _ => (Except.error .mismatch : Except DimError ValValSem))
      = (match v₀ with
     | .fn T f => if h : T = S'.El then
         (ValValSem.toEl S' w').bind (fun arg => f (h ▸ arg))
       else (Except.error .mismatch : Except DimError ValValSem)
     | .array _ => (Except.error .mismatch : Except DimError ValValSem)) := by
  cases v₀ with
  | array _ => rfl
  | fn T f =>
      simp only
      by_cases hT : T = S.El
      · have hT' : T = S'.El := hT.trans hEl
        rw [dif_pos hT, dif_pos hT']
        let l : Except DimError T :=
          cast (congrArg (Except DimError) hT.symm) (ValValSem.toEl S w)
        let r : Except DimError T :=
          cast (congrArg (Except DimError) hT'.symm) (ValValSem.toEl S' w')
        have hl : HEq l (ValValSem.toEl S w) := cast_heq _ _
        have hr : HEq r (ValValSem.toEl S' w') := cast_heq _ _
        have hlr : l = r := eq_of_heq (HEq.trans hl
          (HEq.trans htoEl (HEq.symm hr)))
        clear hl hr htoEl hEl
        have hbind : l.bind f = r.bind f :=
          congrArg (fun z : Except DimError T => z.bind f) hlr
        calc
          _ = l.bind f := except_bind_cast_eq hT (ValValSem.toEl S w) f
          _ = r.bind f := hbind
          _ = _ := (except_bind_cast_eq hT' (ValValSem.toEl S' w') f).symm
      · have hT' : ¬ T = S'.El := fun h => hT (h.trans hEl.symm)
        rw [dif_neg hT, dif_neg hT']

open scoped Classical in
/-- The evaluator-facing form of `appV_dite_cong`, with `Except.bind`
expanded to the explicit match used by `denotValB_semS`.  Keeping this
conversion in one lemma avoids exposing proof-term differences between the
two dependent `if` binders at every congruence call site. -/
theorem valSound_appV_match_congr {S S' : ValTypeSem} (v₀ w w' : ValValSem)
    (hEl : S.El = S'.El)
    (htoEl : HEq (ValValSem.toEl S w) (ValValSem.toEl S' w')) :
    (match v₀ with
     | .fn T f => if h : T = S.El then
         match ValValSem.toEl S w with
         | .error err => Except.error err
         | .ok arg => f (h ▸ arg)
       else (.error .mismatch : Except DimError ValValSem)
     | .array _ => (.error .mismatch : Except DimError ValValSem))
      = (match v₀ with
     | .fn T f => if h : T = S'.El then
         match ValValSem.toEl S' w' with
         | .error err => Except.error err
         | .ok arg => f (h ▸ arg)
       else (.error .mismatch : Except DimError ValValSem)
     | .array _ => (.error .mismatch : Except DimError ValValSem)) := by
  calc
    _ = (match v₀ with
      | .fn T f => if h : T = S.El then
          (ValValSem.toEl S w).bind (fun arg => f (h ▸ arg))
        else (.error .mismatch : Except DimError ValValSem)
      | .array _ => (.error .mismatch : Except DimError ValValSem)) := by
        cases v₀ with
        | array _ => rfl
        | fn T f =>
            by_cases hT : T = S.El
            · cases hT
              cases hres : ValValSem.toEl S w <;> simp [hres, Except.bind]
            · simp [hT, Except.bind]
    _ = _ := appV_dite_cong v₀ w w' hEl htoEl
    _ = _ := by
      cases v₀ with
      | array _ => rfl
      | fn T f =>
          by_cases hT : T = S'.El
          · cases hT
            cases hres : ValValSem.toEl S' w' <;> simp [hres, Except.bind]
          · simp [hT, Except.bind]

open scoped Classical in
/-- Dependent-`dite` congruence for the `.appV` arm: when the recovered domain
    carriers agree (`hEl`) and the coerced arguments agree (`htoEl`, an `HEq`), the
    two domain-aware applications coincide for any function value `v₀`. -/
theorem appV_dite_cong_domainChecked {S S' : ValTypeSem} (v₀ w w' : ValValSem)
    (hEl : S.El = S'.El)
    (htoEl : HEq (ValValSem.toElDomainChecked S w) (ValValSem.toElDomainChecked S' w')) :
    (match v₀ with
     | .fn T f => if h : T = S.El then
         (ValValSem.toElDomainChecked S w).bind (fun arg => f (h ▸ arg))
       else (Except.error .mismatch : Except DimError ValValSem)
     | .array _ => (Except.error .mismatch : Except DimError ValValSem))
      = (match v₀ with
     | .fn T f => if h : T = S'.El then
         (ValValSem.toElDomainChecked S' w').bind (fun arg => f (h ▸ arg))
       else (Except.error .mismatch : Except DimError ValValSem)
     | .array _ => (Except.error .mismatch : Except DimError ValValSem)) := by
  cases v₀ with
  | array _ => rfl
  | fn T f =>
      simp only
      by_cases hT : T = S.El
      · have hT' : T = S'.El := hT.trans hEl
        rw [dif_pos hT, dif_pos hT']
        let l : Except DimError T :=
          cast (congrArg (Except DimError) hT.symm) (ValValSem.toElDomainChecked S w)
        let r : Except DimError T :=
          cast (congrArg (Except DimError) hT'.symm) (ValValSem.toElDomainChecked S' w')
        have hl : HEq l (ValValSem.toElDomainChecked S w) := cast_heq _ _
        have hr : HEq r (ValValSem.toElDomainChecked S' w') := cast_heq _ _
        have hlr : l = r := eq_of_heq (HEq.trans hl
          (HEq.trans htoEl (HEq.symm hr)))
        clear hl hr htoEl hEl
        have hbind : l.bind f = r.bind f :=
          congrArg (fun z : Except DimError T => z.bind f) hlr
        calc
          _ = l.bind f := except_bind_cast_eq hT (ValValSem.toElDomainChecked S w) f
          _ = r.bind f := hbind
          _ = _ := (except_bind_cast_eq hT' (ValValSem.toElDomainChecked S' w') f).symm
      · have hT' : ¬ T = S'.El := fun h => hT (h.trans hEl.symm)
        rw [dif_neg hT, dif_neg hT']

open scoped Classical in
/-- The evaluator-facing form of `appV_dite_cong_domainChecked`, with `Except.bind`
expanded to the explicit match used by `denotValB_semS`.  Keeping this
conversion in one lemma avoids exposing proof-term differences between the
two dependent `if` binders at every congruence call site. -/
theorem valSound_appV_match_congr_domainChecked {S S' : ValTypeSem} (v₀ w w' : ValValSem)
    (hEl : S.El = S'.El)
    (htoEl : HEq (ValValSem.toElDomainChecked S w) (ValValSem.toElDomainChecked S' w')) :
    (match v₀ with
     | .fn T f => if h : T = S.El then
         match ValValSem.toElDomainChecked S w with
         | .error err => Except.error err
         | .ok arg => f (h ▸ arg)
       else (.error .mismatch : Except DimError ValValSem)
     | .array _ => (.error .mismatch : Except DimError ValValSem))
      = (match v₀ with
     | .fn T f => if h : T = S'.El then
         match ValValSem.toElDomainChecked S' w' with
         | .error err => Except.error err
         | .ok arg => f (h ▸ arg)
       else (.error .mismatch : Except DimError ValValSem)
     | .array _ => (.error .mismatch : Except DimError ValValSem)) := by
  calc
    _ = (match v₀ with
      | .fn T f => if h : T = S.El then
          (ValValSem.toElDomainChecked S w).bind (fun arg => f (h ▸ arg))
        else (.error .mismatch : Except DimError ValValSem)
      | .array _ => (.error .mismatch : Except DimError ValValSem)) := by
        cases v₀ with
        | array _ => rfl
        | fn T f =>
            by_cases hT : T = S.El
            · cases hT
              cases hres : ValValSem.toElDomainChecked S w <;> simp [hres, Except.bind]
            · simp [hT, Except.bind]
    _ = _ := appV_dite_cong_domainChecked v₀ w w' hEl htoEl
    _ = _ := by
      cases v₀ with
      | array _ => rfl
      | fn T f =>
          by_cases hT : T = S'.El
          · cases hT
            cases hres : ValValSem.toElDomainChecked S' w' <;> simp [hres, Except.bind]
          · simp [hT, Except.bind]

namespace ValSoundOfDenot

/-- Reshape-equivalence: same `.space`/`.piTy` skeleton with equal leaf `dof`s. -/
def ValTy.ReshEq (orc : FFSOracle) : ValTy → ValTy → Prop
  | .space s, .space s' => ValSpace.dof orc s = ValSpace.dof orc s'
  | .piTy a b, .piTy a' b' => ValTy.ReshEq orc a a' ∧ ValTy.ReshEq orc b b'
  | _, _ => False

@[refl] theorem ValTy.ReshEq.refl (orc : FFSOracle) : ∀ τ : ValTy, ValTy.ReshEq orc τ τ
  | .space _ => rfl
  | .piTy a b => ⟨ValTy.ReshEq.refl orc a, ValTy.ReshEq.refl orc b⟩

theorem ValTy.ReshEq.toSameShape (orc : FFSOracle) :
    ∀ {τ τ' : ValTy}, ValTy.ReshEq orc τ τ' → ValTy.SameShape τ τ'
  | .space _, .space _, _ => trivial
  | .piTy _ _, .piTy _ _, h =>
      ⟨ValTy.ReshEq.toSameShape orc h.1, ValTy.ReshEq.toSameShape orc h.2⟩
  | .space _, .piTy _ _, h => h.elim
  | .piTy _ _, .space _, h => h.elim

/-- Opening a bound index preserves `ReshEq` (`dof` invariant by `dof_openRec`,
    skeleton unchanged). -/
theorem ValTy.ReshEq_openRec (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (k : Nat) (u : ValExpr) :
    ∀ τ : ValTy, ValTy.ReshEq orc (ValTy.openRec k u τ) τ
  | .space s => by
      show ValSpace.dof orc (ValSpace.openRec k u s) = ValSpace.dof orc s
      exact ValSpace.dof_openRec orc k u s
  | .piTy a b => ⟨ValTy.ReshEq_openRec orc k u a, ValTy.ReshEq_openRec orc (k+1) u b⟩

end ValSoundOfDenot

/-- Heterogeneous function application: equal domains/codomains + `HEq` function +
    `HEq` argument give `HEq` results. -/
theorem heq_app {α α' β β' : Type} {f : α → β} {g : α' → β'} {x : α} {y : α'}
    (hα : α = α') (hβ : β = β') (hf : HEq f g) (hx : HEq x y) : HEq (f x) (g y) := by
  subst hα; subst hβ
  rw [eq_of_heq hf, eq_of_heq hx]

/-- Map heterogeneously equal partial values through pointwise-compatible
payload maps. The error constructor is preserved unchanged. -/
theorem except_map_heq_congr {A B : Type} (hAB : A = B)
    (r : Except DimError A) (r' : Except DimError B) (hr : HEq r r')
    (f : A → ValValSem) (g : B → ValValSem)
    (hfg : ∀ a b, HEq a b → f a = g b) : r.map f = r'.map g := by
  cases hAB
  have hrr : r = r' := eq_of_heq hr
  subst r'
  cases r with
  | error _ => rfl
  | ok a => exact congrArg Except.ok (hfg a a HEq.rfl)

/-- Bind heterogeneously equal partial values through pointwise-compatible
exception-carrying continuations. -/
theorem except_bind_heq_congr {A B : Type} (hAB : A = B)
    (r : Except DimError A) (r' : Except DimError B) (hr : HEq r r')
    (f : A → Except DimError ValValSem) (g : B → Except DimError ValValSem)
    (hfg : ∀ a b, HEq a b → f a = g b) : r.bind f = r'.bind g := by
  cases hAB
  have hrr : r = r' := eq_of_heq hr
  subst r'
  cases r with
  | error _ => rfl
  | ok a => exact hfg a a HEq.rfl

/-- `carrierToVal` agrees on `SameShape` types fed `HEq`-equal carriers (it
    ignores the space at leaves and recurses on the `.piTy` skeleton). -/
theorem carrierToVal_SameShape :
    ∀ (τ τ' : ValTy), ValSoundOfDenot.ValTy.SameShape τ τ' →
      ∀ (a : τ.carrierEl) (a' : τ'.carrierEl), HEq a a' →
        ValTy.carrierToVal τ a = ValTy.carrierToVal τ' a'
  | .space _, .space _, _, a, a', haa => by
      simp only [ValTy.carrierToVal]
      rw [eq_of_heq haa]
  | .piTy τ₀ τ₁, .piTy τ₀' τ₁', hss, a, a', haa => by
      have hc : τ₀.carrierEl = τ₀'.carrierEl :=
        ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss.1
      simp only [ValTy.carrierToVal]
      congr 1
      have hcod : τ₁.carrierEl = τ₁'.carrierEl :=
        ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss.2
      refine Function.hfunext hc ?_
      intro b b' hbb
      have hab : HEq (a b) (a' b') :=
        heq_app hc (congrArg (Except DimError) hcod) haa hbb
      apply heq_of_eq
      apply except_map_heq_congr hcod (a b) (a' b') hab
      intro c c' hcc
      exact carrierToVal_SameShape τ₁ τ₁' hss.2 c c' hcc
  | .space _, .piTy _ _, hss, _, _, _ => hss.elim
  | .piTy _ _, .space _, hss, _, _, _ => hss.elim
  termination_by τ _ _ _ _ _ => ValTy.kindSize τ
  decreasing_by all_goals (simp only [ValTy.kindSize_piTy]; omega)

/-- Constructor congruence for semantic functions with partial callbacks. -/
theorem ValValSem.fn_partial_congr {A B : Type}
    (f : A → Except DimError ValValSem) (g : B → Except DimError ValValSem)
    (hAB : A = B) (h : ∀ a : A, f a = g (hAB ▸ a)) :
    ValValSem.fn A f = ValValSem.fn B g := by
  subst hAB
  exact congrArg (ValValSem.fn A) (funext h)

/-- Decoding a value at two same-shaped structural carriers gives
heterogeneously equal partial results. -/
theorem carrierFromVal_SameShape :
    ∀ (d d' : ValTy), ValSoundOfDenot.ValTy.SameShape d d' → ∀ v : ValValSem,
      HEq (ValTy.carrierFromVal d v) (ValTy.carrierFromVal d' v)
  | .space _, .space _, _, v => by cases v <;> rfl
  | .piTy d₀ d₁, .piTy d₀' d₁', hss, v => by
      have hssAll : ValSoundOfDenot.ValTy.SameShape (.piTy d₀ d₁) (.piTy d₀' d₁') := hss
      obtain ⟨hss₀, hss₁⟩ := hss
      have hdom : d₀.carrierEl = d₀'.carrierEl :=
        ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss₀
      have hcod : d₁.carrierEl = d₁'.carrierEl :=
        ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss₁
      have hcarrier : (.piTy d₀ d₁ : ValTy).carrierEl =
          (.piTy d₀' d₁' : ValTy).carrierEl :=
        ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hssAll
      cases v with
      | array _ =>
          simp only [ValTy.carrierFromVal]
          exact except_error_heq hcarrier DimError.mismatch
      | fn T f =>
          simp only [ValTy.carrierFromVal]
          by_cases hT : T = d₀.carrierEl
          · have hT' : T = d₀'.carrierEl := hT.trans hdom
            rw [dif_pos hT, dif_pos hT']
            apply except_ok_heq hcarrier
            refine Function.hfunext hdom ?_
            intro a a' haa
            have hcast : f (hT ▸ a) = f (hT' ▸ a') := by
              congr 1
              apply eq_of_heq
              exact HEq.trans (cast_heq hT.symm a)
                (HEq.trans haa (HEq.symm (cast_heq hT'.symm a')))
            rw [hcast]
            cases hf : f (hT' ▸ a') with
            | error err => exact except_error_heq hcod err
            | ok out => exact carrierFromVal_SameShape d₁ d₁' hss₁ out
          · have hT' : ¬ T = d₀'.carrierEl := fun h => hT (h.trans hdom.symm)
            rw [dif_neg hT, dif_neg hT']
            exact except_error_heq hcarrier DimError.mismatch
  | .space _, .piTy _ _, hss, _ => hss.elim
  | .piTy _ _, .space _, hss, _ => hss.elim
  termination_by d _ _ _ => ValTy.kindSize d
  decreasing_by all_goals (simp only [ValTy.kindSize_piTy]; omega)

open scoped Classical in
/-- A successful domain equality rewrites `applyCarrier` to a bind in the
function's own carrier. Keeping this proof separate hides the irrelevant
equality witness chosen by the internal dependent `if`. -/
theorem applyCarrier_fn_eq_of_domain (d : ValTy) (T : Type)
    (f : T → Except DimError ValValSem) (arg : ValValSem)
    (h : T = d.carrierEl) :
    ValValSem.applyCarrier d (.fn T f) arg =
      (cast (congrArg (Except DimError) h.symm)
        (ValTy.carrierFromVal d arg)).bind f := by
  subst h
  simp only [ValValSem.applyCarrier]
  generalize hr : ValTy.carrierFromVal d arg = r
  cases r <;> simp [Except.bind]

/-- Domain-aware application is invariant under replacement by a same-shaped
domain. All conversion and callback failures remain observable. -/
theorem applyCarrier_SameShape (d d' : ValTy)
    (hss : ValSoundOfDenot.ValTy.SameShape d d') (funVal argVal : ValValSem) :
    ValValSem.applyCarrier d funVal argVal =
      ValValSem.applyCarrier d' funVal argVal := by
  have hcarrier : d.carrierEl = d'.carrierEl :=
    ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss
  cases funVal with
  | array _ => rfl
  | fn T f =>
      by_cases hT : T = d.carrierEl
      · have hT' : T = d'.carrierEl := hT.trans hcarrier
        have hfrom := carrierFromVal_SameShape d d' hss argVal
        let l : Except DimError T :=
          cast (congrArg (Except DimError) hT.symm) (ValTy.carrierFromVal d argVal)
        let r : Except DimError T :=
          cast (congrArg (Except DimError) hT'.symm) (ValTy.carrierFromVal d' argVal)
        have hl : HEq l (ValTy.carrierFromVal d argVal) := cast_heq _ _
        have hr : HEq r (ValTy.carrierFromVal d' argVal) := cast_heq _ _
        have hlr : l = r := eq_of_heq (HEq.trans hl
          (HEq.trans hfrom (HEq.symm hr)))
        clear hl hr hfrom
        have hbind : l.bind f = r.bind f :=
          congrArg (fun z : Except DimError T => z.bind f) hlr
        rw [applyCarrier_fn_eq_of_domain d T f argVal hT,
          applyCarrier_fn_eq_of_domain d' T f argVal hT']
        simpa only [l, r] using hbind
      · have hT' : ¬ T = d'.carrierEl := fun h => hT (h.trans hcarrier.symm)
        simp [ValValSem.applyCarrier, hT, hT']

/-- Dependent heterogeneous application, placed here for the reshape
congruence below. -/
theorem heq_app_dep {α α' : Type} {β : α → Type} {β' : α' → Type}
    {f : (a : α) → β a} {g : (a : α') → β' a} {x : α} {y : α'}
    (hα : α = α') (hβ : HEq β β') (hf : HEq f g) (hx : HEq x y) : HEq (f x) (g y) := by
  subst hα
  obtain rfl : β = β' := eq_of_heq hβ
  obtain rfl : f = g := eq_of_heq hf
  obtain rfl : x = y := eq_of_heq hx
  rfl

/-- Constant-oracle denoted carriers agree for `ReshEq` types, at arbitrary
local contexts. -/
theorem denotValTyS_const_El_ReshEq (orc : FFSOracle)
    {t t' : ValTy} (h : ValSoundOfDenot.ValTy.ReshEq orc t t')
    (ρ ρ' : ValEnvSem) (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem) :
    (denotValTyS (.const orc) ρ Γ Δ t).El =
      (denotValTyS (.const orc) ρ' Γ' Δ' t').El := by
  rw [← denotValTy_eq_denotValTyS orc ρ t Γ Δ,
    ← denotValTy_eq_denotValTyS orc ρ' t' Γ' Δ',
    denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl,
    ValSoundOfDenot.ValTy.SameShape.carrierEl_eq
      (ValSoundOfDenot.ValTy.ReshEq.toSameShape orc h)]

/-- Canonical embedding through `fromEl` is invariant under `ReshEq`. -/
theorem fromEl_denotValTy_ReshEq (orc : FFSOracle) :
    ∀ (t t' : ValTy), ValSoundOfDenot.ValTy.ReshEq orc t t' →
      ∀ (ρ ρ' : ValEnvSem) (Δ Δ' : List ValValSem)
        (a : (denotValTy orc ρ Δ t).El)
        (a' : (denotValTy orc ρ' Δ' t').El),
        HEq a a' →
        ValValSem.fromEl (denotValTy orc ρ Δ t) a =
          ValValSem.fromEl (denotValTy orc ρ' Δ' t') a'
  | .space s, .space s', h, ρ, ρ', Δ, Δ', a, a', haa => by
      obtain rfl : a = a' := eq_of_heq haa
      simp only [denotValTy, ValValSem.fromEl]
      rw [h]
  | .piTy t₀ t₁, .piTy t₀' t₁', h, ρ, ρ', Δ, Δ', a, a', haa => by
      have hss := ValSoundOfDenot.ValTy.ReshEq.toSameShape orc h
      have hdom : (denotValTy orc ρ Δ t₀).El =
          (denotValTy orc ρ' Δ' t₀').El := by
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl,
          ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss.1]
      have hcodFam : HEq
          (fun y : (denotValTy orc ρ Δ t₀).El =>
            Except DimError
              (denotValTy orc ρ
                (ValValSem.fromEl (denotValTy orc ρ Δ t₀) y :: Δ) t₁).El)
          (fun y' : (denotValTy orc ρ' Δ' t₀').El =>
            Except DimError
              (denotValTy orc ρ'
                (ValValSem.fromEl (denotValTy orc ρ' Δ' t₀') y' :: Δ') t₁').El) := by
        refine Function.hfunext hdom ?_
        intro y y' _
        apply heq_of_eq
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl,
          ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss.2]
      simp only [denotValTy, ValValSem.fromEl]
      apply ValValSem.fn_partial_congr _ _ hdom
      intro y
      have hay : HEq (a y) (a' (hdom ▸ y)) :=
        heq_app_dep hdom hcodFam haa (cast_heq hdom y).symm
      have hcod :
          (denotValTy orc ρ
            (ValValSem.fromEl (denotValTy orc ρ Δ t₀) y :: Δ) t₁).El =
          (denotValTy orc ρ'
            (ValValSem.fromEl (denotValTy orc ρ' Δ' t₀') (hdom ▸ y) :: Δ') t₁').El := by
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl,
          ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss.2]
      apply except_map_heq_congr hcod (a y) (a' (hdom ▸ y)) hay
      intro z z' hzz
      exact fromEl_denotValTy_ReshEq orc t₁ t₁' h.2 ρ ρ'
        (ValValSem.fromEl (denotValTy orc ρ Δ t₀) y :: Δ)
        (ValValSem.fromEl (denotValTy orc ρ' Δ' t₀') (hdom ▸ y) :: Δ')
        z z' hzz
  | .space _, .piTy _ _, h, _, _, _, _, _, _, _ => h.elim
  | .piTy _ _, .space _, h, _, _, _, _, _, _, _ => h.elim
  termination_by t _ _ _ _ _ _ _ _ _ => ValTy.kindSize t
  decreasing_by all_goals simp only [ValTy.kindSize_piTy]; omega

/-- `fromEl` congruence stated directly for the context-indexed type
denotation.  Constant-oracle contexts may differ; `ReshEq` supplies exactly
the leaf resize equalities. -/
theorem fromEl_denotValTyS_const_ReshEq (orc : FFSOracle) :
    ∀ (t t' : ValTy), ValSoundOfDenot.ValTy.ReshEq orc t t' →
      ∀ (ρ ρ' : ValEnvSem) (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem)
        (a : (denotValTyS (.const orc) ρ Γ Δ t).El)
        (a' : (denotValTyS (.const orc) ρ' Γ' Δ' t').El),
        HEq a a' →
        ValValSem.fromEl (denotValTyS (.const orc) ρ Γ Δ t) a =
          ValValSem.fromEl (denotValTyS (.const orc) ρ' Γ' Δ' t') a'
  | .space s, .space s', h, ρ, ρ', Γ, Γ', Δ, Δ', a, a', haa => by
      obtain rfl : a = a' := eq_of_heq haa
      simp only [denotValTyS, ValValSem.fromEl]
      rw [h]
  | .piTy t₀ t₁, .piTy t₀' t₁', h,
      ρ, ρ', Γ, Γ', Δ, Δ', a, a', haa => by
      have hdom := denotValTyS_const_El_ReshEq orc h.1
        ρ ρ' Γ Γ' Δ Δ'
      have hcodFam : HEq
          (fun y : (denotValTyS (.const orc) ρ Γ Δ t₀).El =>
            Except DimError
              (denotValTyS (.const orc) ρ (t₀ :: Γ)
                (ValValSem.fromEl
                  (denotValTyS (.const orc) ρ Γ Δ t₀) y :: Δ) t₁).El)
          (fun y' : (denotValTyS (.const orc) ρ' Γ' Δ' t₀').El =>
            Except DimError
              (denotValTyS (.const orc) ρ' (t₀' :: Γ')
                (ValValSem.fromEl
                  (denotValTyS (.const orc) ρ' Γ' Δ' t₀') y' :: Δ') t₁').El) := by
        refine Function.hfunext hdom ?_
        intro y y' _
        apply heq_of_eq
        exact congrArg (Except DimError)
          (denotValTyS_const_El_ReshEq orc h.2 ρ ρ'
            (t₀ :: Γ) (t₀' :: Γ')
            (ValValSem.fromEl
              (denotValTyS (.const orc) ρ Γ Δ t₀) y :: Δ)
            (ValValSem.fromEl
              (denotValTyS (.const orc) ρ' Γ' Δ' t₀') y' :: Δ'))
      simp only [denotValTyS, ValValSem.fromEl]
      apply ValValSem.fn_partial_congr _ _ hdom
      intro y
      have hay : HEq (a y) (a' (hdom ▸ y)) :=
        heq_app_dep hdom hcodFam haa (cast_heq hdom y).symm
      have hcod := denotValTyS_const_El_ReshEq orc h.2 ρ ρ'
        (t₀ :: Γ) (t₀' :: Γ')
        (ValValSem.fromEl
          (denotValTyS (.const orc) ρ Γ Δ t₀) y :: Δ)
        (ValValSem.fromEl
          (denotValTyS (.const orc) ρ' Γ' Δ' t₀') (hdom ▸ y) :: Δ')
      apply except_map_heq_congr hcod (a y) (a' (hdom ▸ y)) hay
      intro z z' hzz
      exact fromEl_denotValTyS_const_ReshEq orc t₁ t₁' h.2 ρ ρ'
        (t₀ :: Γ) (t₀' :: Γ')
        (ValValSem.fromEl
          (denotValTyS (.const orc) ρ Γ Δ t₀) y :: Δ)
        (ValValSem.fromEl
          (denotValTyS (.const orc) ρ' Γ' Δ' t₀') (hdom ▸ y) :: Δ')
        z z' hzz
  | .space _, .piTy _ _, h, _, _, _, _, _, _, _, _, _ => h.elim
  | .piTy _ _, .space _, h, _, _, _, _, _, _, _, _, _ => h.elim
  termination_by t _ _ _ _ _ _ _ _ _ _ _ => ValTy.kindSize t
  decreasing_by all_goals simp only [ValTy.kindSize_piTy]; omega

/-- The no-resize checked reifier is invariant under `ReshEq`.  At a space,
`ReshEq` makes the two exact-length guards identical; at a Π, successful
callback results are checked recursively. -/
theorem fromElChecked_denotValTyS_const_ReshEq (orc : FFSOracle) :
    ∀ (t t' : ValTy), ValSoundOfDenot.ValTy.ReshEq orc t t' →
      ∀ (ρ ρ' : ValEnvSem) (Γ Γ' : List ValTy) (Δ Δ' : List ValValSem)
        (a : (denotValTyS (.const orc) ρ Γ Δ t).El)
        (a' : (denotValTyS (.const orc) ρ' Γ' Δ' t').El),
        HEq a a' →
        ValValSem.fromElChecked (denotValTyS (.const orc) ρ Γ Δ t) a =
          ValValSem.fromElChecked (denotValTyS (.const orc) ρ' Γ' Δ' t') a'
  | .space s, .space s', h, ρ, ρ', Γ, Γ', Δ, Δ', a, a', haa => by
      obtain rfl : a = a' := eq_of_heq haa
      simp only [denotValTyS, ValValSem.fromElChecked]
      rw [h]
  | .piTy t₀ t₁, .piTy t₀' t₁', h,
      ρ, ρ', Γ, Γ', Δ, Δ', a, a', haa => by
      have hdom := denotValTyS_const_El_ReshEq orc h.1
        ρ ρ' Γ Γ' Δ Δ'
      have hcodFam : HEq
          (fun y : (denotValTyS (.const orc) ρ Γ Δ t₀).El =>
            Except DimError
              (denotValTyS (.const orc) ρ (t₀ :: Γ)
                (ValValSem.fromEl
                  (denotValTyS (.const orc) ρ Γ Δ t₀) y :: Δ) t₁).El)
          (fun y' : (denotValTyS (.const orc) ρ' Γ' Δ' t₀').El =>
            Except DimError
              (denotValTyS (.const orc) ρ' (t₀' :: Γ')
                (ValValSem.fromEl
                  (denotValTyS (.const orc) ρ' Γ' Δ' t₀') y' :: Δ') t₁').El) := by
        refine Function.hfunext hdom ?_
        intro y y' _
        apply heq_of_eq
        exact congrArg (Except DimError)
          (denotValTyS_const_El_ReshEq orc h.2 ρ ρ'
            (t₀ :: Γ) (t₀' :: Γ')
            (ValValSem.fromEl
              (denotValTyS (.const orc) ρ Γ Δ t₀) y :: Δ)
            (ValValSem.fromEl
              (denotValTyS (.const orc) ρ' Γ' Δ' t₀') y' :: Δ'))
      simp only [denotValTyS, ValValSem.fromElChecked]
      apply congrArg Except.ok
      apply ValValSem.fn_partial_congr _ _ hdom
      intro y
      have hay : HEq (a y) (a' (hdom ▸ y)) :=
        heq_app_dep hdom hcodFam haa (cast_heq hdom y).symm
      have hcod := denotValTyS_const_El_ReshEq orc h.2 ρ ρ'
        (t₀ :: Γ) (t₀' :: Γ')
        (ValValSem.fromEl
          (denotValTyS (.const orc) ρ Γ Δ t₀) y :: Δ)
        (ValValSem.fromEl
          (denotValTyS (.const orc) ρ' Γ' Δ' t₀') (hdom ▸ y) :: Δ')
      apply except_bind_heq_congr hcod (a y) (a' (hdom ▸ y)) hay
      intro z z' hzz
      exact fromElChecked_denotValTyS_const_ReshEq orc t₁ t₁' h.2 ρ ρ'
        (t₀ :: Γ) (t₀' :: Γ')
        (ValValSem.fromEl
          (denotValTyS (.const orc) ρ Γ Δ t₀) y :: Δ)
        (ValValSem.fromEl
          (denotValTyS (.const orc) ρ' Γ' Δ' t₀') (hdom ▸ y) :: Δ')
        z z' hzz
  | .space _, .piTy _ _, h, _, _, _, _, _, _, _, _, _ => h.elim
  | .piTy _ _, .space _, h, _, _, _, _, _, _, _, _, _ => h.elim
  termination_by t _ _ _ _ _ _ _ _ _ _ _ => ValTy.kindSize t
  decreasing_by all_goals simp only [ValTy.kindSize_piTy]; omega

/-- Decode an argument and apply an untyped function, retaining every runtime
error in the same `Except` layer. -/
noncomputable def ValValSem.applyTypedExcept {A : Type} (funVal : ValValSem)
    (r : Except DimError A) : Except DimError ValValSem :=
  r.bind funVal.applyTyped

/-- The explicit two-match callback is the bind form of `applyTypedExcept`. -/
theorem ValValSem.applyTypedExcept_bind {A : Type} {C : Type 1} (funVal : ValValSem)
    (r : Except DimError A) (k : ValValSem → Except DimError C) :
    (match r with
     | .error err => Except.error err
     | .ok arg =>
         match funVal.applyTyped arg with
         | .error err => Except.error err
         | .ok out => k out) =
      (funVal.applyTypedExcept r).bind k := by
  cases r with
  | error _ => rfl
  | ok arg =>
      unfold ValValSem.applyTypedExcept
      dsimp only [Except.bind]
      generalize happ : funVal.applyTyped arg = appResult
      cases appResult <;> rfl

/-- Typed application maps heterogeneously equal partial arguments at equal
payload types to the same untyped result. -/
theorem applyTyped_except_heq_congr {A B : Type} (funVal : ValValSem)
    (r : Except DimError A) (r' : Except DimError B)
    (hAB : A = B) (hr : HEq r r') :
    funVal.applyTypedExcept r = funVal.applyTypedExcept r' := by
  cases hAB
  have hrr : r = r' := eq_of_heq hr
  exact congrArg funVal.applyTypedExcept hrr

/-- Decoding followed by typed application is invariant under an equal
decoded carrier and heterogeneous equality of the decode results. -/
theorem applyTyped_toEl_congr (funVal w w' : ValValSem) {S S' : ValTypeSem}
    (hEl : S.El = S'.El)
    (hto : HEq (ValValSem.toEl S w) (ValValSem.toEl S' w')) :
    funVal.applyTypedExcept (ValValSem.toEl S w) =
      funVal.applyTypedExcept (ValValSem.toEl S' w') :=
  applyTyped_except_heq_congr funVal _ _ hEl hto

/-- `reshapDenotSem` is invariant under `ReshEq` of BOTH its target and source
    types (for a fixed value `v`). kindSize recursion mirroring `reshapDenotSem`'s
    own measure; the arrow case aligns the `.fn` carriers (`carrierEl_eq`), the
    inner argument-reshapes (`carrierToVal_SameShape` + IH at `(τ₄,τ₂)`), and the
    result-reshapes (IH at `(τ₃,τ₅)`). -/
theorem reshapDenotSem_ReshEq (orc : FFSOracle) :
    ∀ (t t' s s' : ValTy), ValSoundOfDenot.ValTy.ReshEq orc t t' →
      ValSoundOfDenot.ValTy.ReshEq orc s s' → ∀ (v : ValValSem),
      reshapDenotSem orc v t s = reshapDenotSem orc v t' s'
  | .space sₜ, .space sₜ', s, s', ht, hs, v => by
      cases s <;> cases s' <;> cases v <;>
        simp_all [ValSoundOfDenot.ValTy.ReshEq, reshapDenotSem,
          reshapDenotSemS, reshapArrayBetweenS, FFSOracleSem.const]
  | .piTy τ₂ τ₃, .piTy τ₂' τ₃', .piTy τ₄ τ₅, .piTy τ₄' τ₅', ht, hs, v => by
      rw [reshapDenotSem_eq_piTy, reshapDenotSem_eq_piTy,
        reshapDenotSemS.eq_3, reshapDenotSemS.eq_3]
      apply congrArg Except.ok
      have hT := denotValTyS_const_El_ReshEq orc ht.1
        ValEnvSem.empty ValEnvSem.empty [] [] [] []
      apply ValValSem.fn_partial_congr _ _ hT
      intro a
      dsimp only
      let a' := hT ▸ a
      have haa : HEq a a' := (cast_heq hT a).symm
      have hcheck :
          ValValSem.fromElChecked
              (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₂) a =
            ValValSem.fromElChecked
              (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₂') a' := by
        exact fromElChecked_denotValTyS_const_ReshEq orc τ₂ τ₂' ht.1
          ValEnvSem.empty ValEnvSem.empty [] [] [] [] a a' haa
      rw [hcheck]
      generalize hchecked : ValValSem.fromElChecked
        (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₂') a' = checkResult
      cases checkResult with
      | error err => rfl
      | ok argT =>
          simp only
          have hinner :
              reshapDenotSemBetweenS (.const orc) ValEnvSem.empty [] [] [] []
                  argT τ₄ τ₂ =
                reshapDenotSemBetweenS (.const orc) ValEnvSem.empty [] [] [] []
                  argT τ₄' τ₂' := by
            rw [← reshapDenotSemS_eq_between, ← reshapDenotSemS_eq_between]
            exact reshapDenotSem_ReshEq orc τ₄ τ₄' τ₂ τ₂' hs.1 ht.1 argT
          rw [hinner]
          generalize harg : reshapDenotSemBetweenS (.const orc) ValEnvSem.empty
            [] [] [] [] argT τ₄' τ₂' = argResult
          cases argResult with
          | error err => rfl
          | ok argS =>
              dsimp [a'] at *
              have hS := denotValTyS_const_El_ReshEq orc hs.1
                ValEnvSem.empty ValEnvSem.empty [] [] [] []
              have hto : HEq
                  (ValValSem.toEl
                    (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₄) argS)
                  (ValValSem.toEl
                    (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₄') argS) := by
                rw [← denotValTy_eq_denotValTyS orc ValEnvSem.empty τ₄ [] [],
                  ← denotValTy_eq_denotValTyS orc ValEnvSem.empty τ₄' [] []]
                exact toEl_denotValTy_SameShape orc τ₄ τ₄'
                  (ValSoundOfDenot.ValTy.ReshEq.toSameShape orc hs.1)
                  ValEnvSem.empty ValEnvSem.empty [] [] argS
              let decodeL := ValValSem.toEl
                (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₄) argS
              let decodeR := ValValSem.toEl
                (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₄') argS
              let kL : ValValSem → Except DimError ValValSem := fun res =>
                reshapDenotSemBetweenS (.const orc) ValEnvSem.empty
                  [τ₂] [argT] [τ₄] [argS] res τ₃ τ₅
              let kR : ValValSem → Except DimError ValValSem := fun res =>
                reshapDenotSemBetweenS (.const orc) ValEnvSem.empty
                  [τ₂'] [argT] [τ₄'] [argS] res τ₃' τ₅'
              have happ : v.applyTypedExcept decodeL = v.applyTypedExcept decodeR :=
                applyTyped_toEl_congr v argS argS hS hto
              have hk : kL = kR := by
                funext res
                dsimp only [kL, kR]
                exact
                  (reshapDenotSemBetweenS_const_env orc res τ₃ τ₅
                    ValEnvSem.empty ValEnvSem.empty
                    [τ₂] [] [τ₄] [] [argT] [] [argS] []).trans <|
                  (reshapDenotSemS_eq_between (.const orc) ValEnvSem.empty
                    [] [] res τ₃ τ₅).symm.trans <|
                  (reshapDenotSem_ReshEq orc τ₃ τ₃' τ₅ τ₅' ht.2 hs.2 res).trans <|
                  (reshapDenotSemS_eq_between (.const orc) ValEnvSem.empty
                    [] [] res τ₃' τ₅').trans <|
                  reshapDenotSemBetweenS_const_env orc res τ₃' τ₅'
                    ValEnvSem.empty ValEnvSem.empty
                    [] [τ₂'] [] [τ₄'] [] [argT] [] [argS]
              calc
                _ = (v.applyTypedExcept decodeL).bind kL :=
                  by
                    dsimp only [decodeL, kL]
                    generalize hdecode : ValValSem.toEl
                      (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₄) argS =
                        decodeResult
                    cases decodeResult with
                    | error _ => rfl
                    | ok arg =>
                        unfold ValValSem.applyTypedExcept
                        dsimp only [Except.bind]
                        generalize happ' : v.applyTyped arg = appResult
                        cases appResult <;> rfl
                _ = (v.applyTypedExcept decodeR).bind kL :=
                  congrArg (fun r => r.bind kL) happ
                _ = (v.applyTypedExcept decodeR).bind kR :=
                  congrArg (fun k => (v.applyTypedExcept decodeR).bind k) hk
                _ = _ := by
                  dsimp only [decodeR, kR]
                  generalize hdecode : ValValSem.toEl
                    (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₄') argS =
                      decodeResult
                  cases decodeResult with
                  | error _ => rfl
                  | ok arg =>
                      unfold ValValSem.applyTypedExcept
                      dsimp only [Except.bind]
                      generalize happ' : v.applyTyped arg = appResult
                      cases appResult <;> rfl
  | .piTy _ _, .piTy _ _, .space _, .space _, _, _, v => by
      simp only [reshapDenotSem, reshapDenotSemS]
  | .piTy _ _, .piTy _ _, .space _, .piTy _ _, _, hs, _ => hs.elim
  | .piTy _ _, .piTy _ _, .piTy _ _, .space _, _, hs, _ => hs.elim
  | .space _, .piTy _ _, _, _, ht, _, _ => ht.elim
  | .piTy _ _, .space _, _, _, ht, _, _ => ht.elim
  termination_by t _ s _ _ _ _ => ValTy.kindSize t + ValTy.kindSize s
  decreasing_by all_goals (simp only [ValTy.kindSize_piTy]; omega)

/-! ### Type shape-and-`dof` equivalence (`TyEq`) — the `inferTypeCtx_ReshEq` engine.

`ReshEq` (dof-only at leaves) is too weak to be PRODUCED by the matching arms of
`inferTypeCtx` (`ttv`/`mtm`/(G)SVD/…), which destructure on the `.tprod`/`.dsum`
*structure* of the inferred type's space — the branch taken must be opening-stable.
`TyEq` is the stronger invariant: equality of a *type-skeleton* (`ValSpace.Skel`
at `.space` leaves, identical `.piTy` skeleton). It is an `Eq` (refl/symm/trans
free), refines `ReshEq` (`TyEq.toReshEq`), and — at `.space` leaves — yields the
`SDEq` the matching arms need. `inferTypeCtx_TyEq` is the type-level mirror of
`inferSpaceCtx_SDEq`; `inferTypeCtx_ReshEq` is its `toReshEq` image. -/

namespace ValSoundOfDenot

/-- Type-skeleton: the `.piTy` tree with `ValSpace.Skel` at the `.space` leaves. -/
inductive ValTy.TySkel : Type
  | space : ValSpace.Skel → ValTy.TySkel
  | piTy  : ValTy.TySkel → ValTy.TySkel → ValTy.TySkel
  deriving DecidableEq

/-- The type-skeleton of a `ValTy`. -/
def ValTy.tyskel (orc : FFSOracle) : ValTy → ValTy.TySkel
  | .space s  => .space (ValSpace.skel orc s)
  | .piTy a b => .piTy (ValTy.tyskel orc a) (ValTy.tyskel orc b)

/-- Type shape-and-`dof` equivalence: equal type-skeletons. -/
abbrev ValTy.TyEq (orc : FFSOracle) (t t' : ValTy) : Prop :=
  ValTy.tyskel orc t = ValTy.tyskel orc t'

@[refl] theorem ValTy.TyEq.refl (orc : FFSOracle) (t : ValTy) : ValTy.TyEq orc t t := rfl

/-- `TyEq` refines `ReshEq`: equal type-skeletons give equal leaf `dof`s. -/
theorem ValTy.TyEq.toReshEq (orc : FFSOracle) :
    ∀ {t t' : ValTy}, ValTy.TyEq orc t t' → ValTy.ReshEq orc t t'
  | .space s, .space s', h => by
      have hsd : ValSpace.SDEq orc s s' := by
        simp only [ValTy.TyEq, ValTy.tyskel, ValTy.TySkel.space.injEq] at h; exact h
      exact ValSpace.SDEq.dof_eq orc hsd
  | .piTy a b, .piTy a' b', h => by
      simp only [ValTy.TyEq, ValTy.tyskel, ValTy.TySkel.piTy.injEq] at h
      exact ⟨ValTy.TyEq.toReshEq orc h.1, ValTy.TyEq.toReshEq orc h.2⟩
  | .space _, .piTy _ _, h => by simp [ValTy.TyEq, ValTy.tyskel] at h
  | .piTy _ _, .space _, h => by simp [ValTy.TyEq, ValTy.tyskel] at h

/-- `TyEq` refines `SameShape` (equal `.piTy` skeletons). -/
theorem ValTy.TyEq.toSameShape (orc : FFSOracle) :
    ∀ {t t' : ValTy}, ValTy.TyEq orc t t' → ValTy.SameShape t t'
  | .space _, .space _, _ => trivial
  | .piTy a b, .piTy a' b', h => by
      simp only [ValTy.TyEq, ValTy.tyskel, ValTy.TySkel.piTy.injEq] at h
      exact ⟨ValTy.TyEq.toSameShape orc h.1, ValTy.TyEq.toSameShape orc h.2⟩
  | .space _, .piTy _ _, h => by simp [ValTy.TyEq, ValTy.tyskel] at h
  | .piTy _ _, .space _, h => by simp [ValTy.TyEq, ValTy.tyskel] at h

/-- At `.space` leaves, `TyEq` yields `SDEq` of the projected spaces (and `SDEq`
    of the junk `.empty` at `.piTy`). The matching arms read this off the operand
    to align their `.tprod`/`.dsum` destructuring. -/
theorem ValTy.TyEq.spaceOf_SDEq (orc : FFSOracle) :
    ∀ {t t' : ValTy}, ValTy.TyEq orc t t' →
      ValSpace.SDEq orc (ValTy.spaceOf t) (ValTy.spaceOf t')
  | .space _, .space _, h => by
      simp only [ValTy.TyEq, ValTy.tyskel, ValTy.TySkel.space.injEq] at h; exact h
  | .piTy _ _, .piTy _ _, _ => rfl
  | .space _, .piTy _ _, h => by simp [ValTy.TyEq, ValTy.tyskel] at h
  | .piTy _ _, .space _, h => by simp [ValTy.TyEq, ValTy.tyskel] at h

/-- Opening a bound index preserves the type-skeleton (`skel_openRec` at leaves,
    `.piTy` structure unchanged). -/
theorem ValTy.tyskel_openRec (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (k : Nat) (u : ValExpr) :
    ∀ τ : ValTy, ValTy.tyskel orc (ValTy.openRec k u τ) = ValTy.tyskel orc τ
  | .space s => by
      simp only [ValTy.openRec, ValTy.tyskel, ValSpace.skel_openRec]
  | .piTy a b => by
      simp only [ValTy.openRec, ValTy.tyskel,
        ValTy.tyskel_openRec orc k u a, ValTy.tyskel_openRec orc (k+1) u b]

theorem ValTy.tyskel_substBound (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (k : Nat) (u : ValExpr) :
    ∀ t : ValTy, ValTy.tyskel orc (ValTy.substBound k u t) = ValTy.tyskel orc t
  | .space s => by simp only [ValTy.substBound, ValTy.tyskel, GLang.ValSpace.skel_substBound]
  | .piTy a b => by simp only [ValTy.substBound, ValTy.tyskel,
      ValTy.tyskel_substBound orc k u a, ValTy.tyskel_substBound orc (k + 1) u b]

theorem ValTy.TyEq_applyCodomain (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    {t t' : ValTy} (a a' : ValExpr) :
    ValTy.TyEq orc t t' → ValTy.TyEq orc
      (match t with | .piTy _ c => GLang.ValTy.applyCodomain a c | .space _ => .space .empty)
      (match t' with | .piTy _ c => GLang.ValTy.applyCodomain a' c | .space _ => .space .empty) := by
  intro h
  cases t <;> cases t' <;>
    simp_all [ValTy.TyEq, ValTy.tyskel, GLang.ValTy.applyCodomain, ValTy.tyskel_substBound]

/-- Opening a bound index keeps a type `TyEq` to itself. -/
theorem ValTy.TyEq_openRec (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (k : Nat) (u : ValExpr) (τ : ValTy) :
    ValTy.TyEq orc (ValTy.openRec k u τ) τ :=
  ValTy.tyskel_openRec orc k u τ

/-- Raising declaration-relative de Bruijn indices is semantically invisible
at the type skeleton.  This is derived from the oracle's existing opening law;
it does not require local closure or another oracle field. -/
theorem ValTy.tyskel_raise (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (n cutoff : Nat) : ∀ τ : ValTy,
    ValTy.tyskel orc (ValTy.raise n cutoff τ) = ValTy.tyskel orc τ
  | .space s => by
      simp only [ValTy.raise, ValTy.tyskel, ValRaise.skel_raise orc n cutoff s]
  | .piTy τ₀ τ₁ => by
      simp only [ValTy.raise, ValTy.tyskel,
        ValTy.tyskel_raise orc n cutoff τ₀,
        ValTy.tyskel_raise orc n (cutoff + 1) τ₁]

theorem ValTy.TyEq_raise (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (n cutoff : Nat) (τ : ValTy) :
    ValTy.TyEq orc (ValTy.raise n cutoff τ) τ :=
  ValTy.tyskel_raise orc n cutoff τ

/-- The type recovered from a local telescope entry is `TyEq` to the
declaration-level type stored in that entry. -/
theorem ValTyCtx.lookupUse_TyEq_raw (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] (Gamma : List ValTy) (k : Nat) :
    ValSoundOfDenot.ValTy.TyEq orc
      (ValTyCtx.lookupUse Gamma k) (Gamma.getD k default) := by
  simpa [ValTyCtx.lookupUse] using
    ValSoundOfDenot.ValTy.TyEq_raise orc (k + 1) 0 (Gamma.getD k default)

/-- Pointwise `TyEq` of declaration contexts remains pointwise `TyEq` after
realizing both entries at their common use depth. -/
theorem ValTyCtx.lookupUse_TyEq (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] {Gamma Gamma' : List ValTy}
    (hGamma : ∀ j, ValSoundOfDenot.ValTy.TyEq orc
      (Gamma.getD j default) (Gamma'.getD j default)) (k : Nat) :
    ValSoundOfDenot.ValTy.TyEq orc
      (ValTyCtx.lookupUse Gamma k) (ValTyCtx.lookupUse Gamma' k) :=
  (ValTyCtx.lookupUse_TyEq_raw orc Gamma k).trans
    ((hGamma k).trans (ValTyCtx.lookupUse_TyEq_raw orc Gamma' k).symm)

end ValSoundOfDenot

/-- Type-level FFS-`dof` opening-stability (mirrors `inferSpaceCtx_gsvd_ffs_aux`):
    the FFS dimension of the operand's projected inferred space is opening-stable.
    `ih` is the `SDEq` projection of the structural `TyEq` IH (`spaceOf_SDEq`). -/
theorem inferTypeCtx_gsvd_ffs_aux (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ : List ValTy)
    (k : Nat) (x : VName) (σ : ValTy) (e : ValExpr) (p : ValFFSProp)
    (ih : ValSpace.SDEq orc
            (ValTy.spaceOf (ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e)))
            (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e))) :
    orc p (ValTy.spaceOf (ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e)))
          (ValExpr.openRec k (.var x σ) e)
      = orc p (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e)) e := by
  have hsd2 : ValSpace.SDEq orc
      (ValTy.spaceOf (ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e)))
      (ValSpace.openRec k (.var x σ) (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e))) :=
    ValSpace.SDEq.trans orc ih
      (ValSpace.SDEq_openRec orc k (.var x σ) (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e)))
  rw [FFSOracle.sdeq_respect orc p (ValExpr.openRec k (.var x σ) e) hsd2,
      FFSOracle.openRec_respect orc k (.var x σ) p
        (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e)) e]

/-! The inferred type is `TyEq`-invariant under opening (the type-level mirror of
    `inferSpaceCtx_SDEq`): `.space`-typed constructors give `SDEq`-equal projected
    spaces, the matching arms align their `.tprod` destructuring via the `TyEq` IH,
    the (G)SVD arms close the embedded FFS `dof` via `inferTypeCtx_gsvd_ffs_aux`,
    and the binder/annotation arms recurse via `TyEq_openRec` / the de Bruijn
    context. -/
set_option maxHeartbeats 1600000 in
theorem inferTypeCtx_TyEq (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ : List ValTy)
    (k : Nat) (x : VName) (σ : ValTy) (hΓk : Γ.getD k default = σ) :
    ∀ e : ValExpr,
      ValSoundOfDenot.ValTy.TyEq orc
        (ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e))
        (ValExpr.inferTypeCtx Γ e)
  | .bvar j => by
      by_cases h : j = k
      · subst j
        simp only [ValExpr.openRec, ↓reduceIte, ValExpr.inferTypeCtx]
        rw [← hΓk]
        exact (ValSoundOfDenot.ValTyCtx.lookupUse_TyEq_raw orc Γ k).symm
      · simp only [ValExpr.openRec, if_neg h, ValExpr.inferTypeCtx]
  | .var y τ => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      exact ValSoundOfDenot.ValTy.TyEq_openRec orc k (.var x σ) τ
  | .rlit r => by simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
  | .zero s => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      exact ValSoundOfDenot.ValTy.TyEq_openRec orc k (.var x σ) (.space s)
  | .delta n s => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      exact ValSoundOfDenot.ValTy.TyEq_openRec orc k (.var x σ) (.space s)
  | .idelta s => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      exact ValSoundOfDenot.ValTy.TyEq_openRec orc k (.var x σ) (.space (.tprod s s))
  | .vlam τ₀ τ₁ e => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      exact ValSoundOfDenot.ValTy.TyEq_openRec orc k (.var x σ) (.piTy τ₀ τ₁)
  | .appV e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      exact ValSoundOfDenot.ValTy.TyEq_applyCodomain orc (ValExpr.openRec k (.var x σ) e₁) e₁
        (inferTypeCtx_TyEq orc Γ k x σ hΓk e₀)
  | .reshap e τ τ₀ => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      exact ValSoundOfDenot.ValTy.TyEq_openRec orc k (.var x σ) τ
  | .scale e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      exact inferTypeCtx_TyEq orc Γ k x σ hΓk e₁
  | .vadd s _ _ => by
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx]
      exact ValSoundOfDenot.ValTy.TyEq_openRec orc k (.var x σ) (.space s)
  | .vsum s es => by
      cases es with
      | nil => simp only [ValExpr.openRec, ValExpr.openRecList, ValExpr.inferTypeCtx]
      | cons e es =>
          simp only [ValExpr.openRec, ValExpr.openRecList, ValExpr.inferTypeCtx]
          exact inferTypeCtx_TyEq orc Γ k x σ hΓk e
  | .dsumE e₀ e₁ => by
      have ih₀ := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_TyEq orc Γ k x σ hΓk e₀)
      have ih₁ := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_TyEq orc Γ k x σ hΓk e₁)
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx, ValSoundOfDenot.ValTy.TyEq,
        ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
      rw [ih₀, ih₁]
  | .tprodE e₀ e₁ => by
      have ih₀ := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_TyEq orc Γ k x σ hΓk e₀)
      have ih₁ := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_TyEq orc Γ k x σ hΓk e₁)
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx, ValSoundOfDenot.ValTy.TyEq,
        ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
      rw [ih₀, ih₁]
  | .ttv s e₀ e₁ => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁ => by
      have ihT0 := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      have ihT1 := inferTypeCtx_TyEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT0 ihT1 ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hA' : ValExpr.inferTypeCtx Γ e₀ with sA' | ⟨aA', bA'⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₁) with sB | ⟨aB, bB⟩ <;>
        rcases hB' : ValExpr.inferTypeCtx Γ e₁ with sB' | ⟨aB', bB'⟩ <;>
          rw [hA, hA'] at ihT0 <;> rw [hB, hB'] at ihT1 <;>
          first
            | (rcases sA with _|_|⟨c0,c1⟩|⟨c0,c1⟩|⟨cp,cs,ce⟩ <;>
               rcases sA' with _|_|⟨d0,d1⟩|⟨d0,d1⟩|⟨dp,ds,de⟩ <;>
               rcases sB with _|_|⟨g0,g1⟩|⟨g0,g1⟩|⟨gp,gs,ge⟩ <;>
               rcases sB' with _|_|⟨h0,h1⟩|⟨h0,h1⟩|⟨hp,hs,he⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .vkrn e₀ e₁ => by
      have ihT0 := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      have ihT1 := inferTypeCtx_TyEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT0 ihT1 ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hA' : ValExpr.inferTypeCtx Γ e₀ with sA' | ⟨aA', bA'⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₁) with sB | ⟨aB, bB⟩ <;>
        rcases hB' : ValExpr.inferTypeCtx Γ e₁ with sB' | ⟨aB', bB'⟩ <;>
          rw [hA, hA'] at ihT0 <;> rw [hB, hB'] at ihT1 <;>
          first
            | (rcases sA with _|_|⟨c0,c1⟩|⟨c0,c1⟩|⟨cp,cs,ce⟩ <;>
               rcases sA' with _|_|⟨d0,d1⟩|⟨d0,d1⟩|⟨dp,ds,de⟩ <;>
               rcases sB with _|_|⟨g0,g1⟩|⟨g0,g1⟩|⟨gp,gs,ge⟩ <;>
               rcases sB' with _|_|⟨h0,h1⟩|⟨h0,h1⟩|⟨hp,hs,he⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .vblk e₀ e₁ => by
      have ihT0 := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      have ihT1 := inferTypeCtx_TyEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT0 ihT1 ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hA' : ValExpr.inferTypeCtx Γ e₀ with sA' | ⟨aA', bA'⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₁) with sB | ⟨aB, bB⟩ <;>
        rcases hB' : ValExpr.inferTypeCtx Γ e₁ with sB' | ⟨aB', bB'⟩ <;>
          rw [hA, hA'] at ihT0 <;> rw [hB, hB'] at ihT1 <;>
          first
            | (rcases sA with _|_|⟨c0,c1⟩|⟨c0,c1⟩|⟨cp,cs,ce⟩ <;>
               rcases sA' with _|_|⟨d0,d1⟩|⟨d0,d1⟩|⟨dp,ds,de⟩ <;>
               rcases sB with _|_|⟨g0,g1⟩|⟨g0,g1⟩|⟨gp,gs,ge⟩ <;>
               rcases sB' with _|_|⟨h0,h1⟩|⟨h0,h1⟩|⟨hp,hs,he⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .vtrans e₀ => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .pinv e₀ => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .inv e₀ => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .gpinv e₀ a b => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .rrefRep e₀ e₁ => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₁) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₁ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .gsvdU e₀ a b => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxC := inferTypeCtx_gsvd_ffs_aux orc Γ k x σ e₀ .cokernel ih
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT hauxC ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxC <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .gsvdUI e₀ a b => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxK := inferTypeCtx_gsvd_ffs_aux orc Γ k x σ e₀ .kernel ih
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT hauxK ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxK <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .gsvdV e₀ a b => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxI := inferTypeCtx_gsvd_ffs_aux orc Γ k x σ e₀ .image ih
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT hauxI ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxI <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .gsvdVI e₀ a b => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxCo := inferTypeCtx_gsvd_ffs_aux orc Γ k x σ e₀ .coimage ih
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT hauxCo ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxCo <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .gsvdS e₀ a b => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxC := inferTypeCtx_gsvd_ffs_aux orc Γ k x σ e₀ .cokernel ih
      have hauxI := inferTypeCtx_gsvd_ffs_aux orc Γ k x σ e₀ .image ih
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT hauxC hauxI ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxC hauxI <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .svds e₀ => by
      have ihT := inferTypeCtx_TyEq orc Γ k x σ hΓk e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxC := inferTypeCtx_gsvd_ffs_aux orc Γ k x σ e₀ .cokernel ih
      have hauxI := inferTypeCtx_gsvd_ffs_aux orc Γ k x σ e₀ .image ih
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx] at ihT hauxC hauxI ⊢
      rcases hA : ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀) with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxC hauxI <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]

set_option maxHeartbeats 1600000 in
theorem inferSpaceCtx_SDEq (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ : List ValTy)
    (k : Nat) (x : VName) (σ : ValTy) (hΓk : Γ.getD k default = σ) :
    ∀ e : ValExpr,
      ValSpace.SDEq orc (ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e))
        (ValExpr.inferSpaceCtx Γ e)
  | .bvar j => by
      by_cases h : j = k
      · subst j
        simp only [ValExpr.openRec, ↓reduceIte, ValExpr.inferSpaceCtx]
        unfold ValTyCtx.lookupUse
        rw [hΓk, ValTy.spaceOf_raise]
        exact (ValRaise.SDEq_raise orc (k + 1) 0 (ValTy.spaceOf σ)).symm
      · simp only [ValExpr.openRec, if_neg h, ValExpr.inferSpaceCtx, ValSpace.SDEq]
  | .var y τ => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValTy.spaceOf_openRec]
      exact (ValSpace.SDEq_openRec orc k (.var x σ) (ValTy.spaceOf τ)).symm
  | .rlit r => by simp only [ValExpr.openRec, ValExpr.inferSpaceCtx]
  | .zero s => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx]
      exact (ValSpace.SDEq_openRec orc k (.var x σ) s).symm
  | .delta n s => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx]
      exact (ValSpace.SDEq_openRec orc k (.var x σ) s).symm
  | .idelta s => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq, ValSpace.skel]
      rw [ValSpace.skel_openRec]
  | .vlam τ₀ τ₁ e => by simp only [ValExpr.openRec, ValExpr.inferSpaceCtx]
  | .appV e₀ e₁ =>
      ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_TyEq orc Γ k x σ hΓk (.appV e₀ e₁))
  | .reshap e τ τ₀ => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValTy.spaceOf_openRec]
      exact (ValSpace.SDEq_openRec orc k (.var x σ) (ValTy.spaceOf τ)).symm
  | .scale e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx]
      exact inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁
  | .vadd s e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx]
      exact (ValSpace.SDEq_openRec orc k (.var x σ) s).symm
  | .dsumE e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq, ValSpace.skel]
      rw [inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀, inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁]
  | .tprodE e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq, ValSpace.skel]
      rw [inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀, inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁]
  | .vsum s es => by
      cases es with
      | nil => simp only [ValExpr.openRec, ValExpr.openRecList, ValExpr.inferSpaceCtx]
      | cons e es =>
          simp only [ValExpr.openRec, ValExpr.openRecList, ValExpr.inferSpaceCtx]
          exact inferSpaceCtx_SDEq orc Γ k x σ hΓk e
  | .ttv s e₀ e₁ => by
      have ih₀ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁ => by
      have ih₀ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have ih₁ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ih₁ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h1 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₁) <;>
      cases h1' : ValExpr.inferSpaceCtx Γ e₁ <;>
        rw [h0, h0'] at ih₀ <;> rw [h1, h1'] at ih₁ <;> simp_all [ValSpace.skel]
  | .vkrn e₀ e₁ => by
      have ih₀ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have ih₁ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ih₁ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h1 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₁) <;>
      cases h1' : ValExpr.inferSpaceCtx Γ e₁ <;>
        rw [h0, h0'] at ih₀ <;> rw [h1, h1'] at ih₁ <;> simp_all [ValSpace.skel]
  | .vblk e₀ e₁ => by
      have ih₀ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have ih₁ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ih₁ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h1 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₁) <;>
      cases h1' : ValExpr.inferSpaceCtx Γ e₁ <;>
        rw [h0, h0'] at ih₀ <;> rw [h1, h1'] at ih₁ <;> simp_all [ValSpace.skel]
  | .vtrans e₀ => by
      have ih₀ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .pinv e₀ => by
      have ih₀ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .gpinv e₀ a b => by
      have ih₀ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .inv e₀ => by
      have ih₀ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .gsvdU e₀ a b => by
      have ih := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have haux := inferSpaceCtx_gsvd_ffs_aux orc Γ k x σ e₀ .cokernel ih
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
        rw [h0, h0'] at ih haux <;> simp_all [ValSpace.skel]
  | .gsvdUI e₀ a b => by
      have ih := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have haux := inferSpaceCtx_gsvd_ffs_aux orc Γ k x σ e₀ .kernel ih
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
        rw [h0, h0'] at ih haux <;> simp_all [ValSpace.skel]
  | .gsvdV e₀ a b => by
      have ih := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have haux := inferSpaceCtx_gsvd_ffs_aux orc Γ k x σ e₀ .image ih
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
        rw [h0, h0'] at ih haux <;> simp_all [ValSpace.skel]
  | .gsvdVI e₀ a b => by
      have ih := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have haux := inferSpaceCtx_gsvd_ffs_aux orc Γ k x σ e₀ .coimage ih
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
      cases h0' : ValExpr.inferSpaceCtx Γ e₀ <;>
        rw [h0, h0'] at ih haux <;> simp_all [ValSpace.skel]
  | .rrefRep e₀ e₁ => by
      have ih₁ := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₁ ⊢
      cases h1 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₁) <;>
      cases h1' : ValExpr.inferSpaceCtx Γ e₁ <;>
        rw [h1, h1'] at ih₁ <;> simp_all [ValSpace.skel]
  | .gsvdS e₀ a b => by
      have ih := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq, ValSpace.skel]
      rw [inferSpaceCtx_gsvd_ffs_aux orc Γ k x σ e₀ .cokernel ih,
          inferSpaceCtx_gsvd_ffs_aux orc Γ k x σ e₀ .image ih]
  | .svds e₀ => by
      have ih := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.SDEq, ValSpace.skel]
      rw [inferSpaceCtx_gsvd_ffs_aux orc Γ k x σ e₀ .cokernel ih,
          inferSpaceCtx_gsvd_ffs_aux orc Γ k x σ e₀ .image ih]

/-- The inferred type is `ReshEq`-invariant under opening (skeleton + leaf dofs
    preserved): the `toReshEq` image of `inferTypeCtx_TyEq` (the type-level
    mirror of `inferSpaceCtx_SDEq`). -/
theorem inferTypeCtx_ReshEq (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ : List ValTy)
    (k : Nat) (x : VName) (σ : ValTy) (hΓk : Γ.getD k default = σ) (e : ValExpr) :
    ValSoundOfDenot.ValTy.ReshEq orc
      (ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e))
      (ValExpr.inferTypeCtx Γ e) :=
  ValSoundOfDenot.ValTy.TyEq.toReshEq orc (inferTypeCtx_TyEq orc Γ k x σ hΓk e)

/-! ### Γ-congruence of `inferSpaceCtx`/`inferTypeCtx` (for the `.vlam` bridge arm).

The `.vlam` bridge arm pushes `openRec τ₀ :: Γ` (RHS) against `τ₀ :: Γ` (LHS) —
the two type contexts differ at the head by an opening, hence are per-entry
`TyEq`. The denotation reads `Γ` only through `inferSpaceCtx` (via `dof`/`SDEq`)
and `inferTypeCtx` (via the `.appV` domain, up to `TyEq`), so both must be
congruent under a per-entry-`TyEq` change of `Γ`. These mirror
`inferSpaceCtx_SDEq` / `inferTypeCtx_TyEq` but vary `Γ` (not `e`): the operand
expression is unchanged, so the FFS arms close by `sdeq_respect` alone (no
`openRec_respect`), and the `.bvar` arm reads the per-entry hypothesis. -/

/-- FFS-`dof` Γ-congruence: the operand expression is fixed, so opening-stability
    reduces to `sdeq_respect`. -/
theorem inferSpaceCtx_gsvd_ffs_Gamma_aux (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ Γ' : List ValTy)
    (e : ValExpr) (p : ValFFSProp)
    (ih : ValSpace.SDEq orc (ValExpr.inferSpaceCtx Γ e) (ValExpr.inferSpaceCtx Γ' e)) :
    ValSpace.dof orc (.ffs p (ValExpr.inferSpaceCtx Γ e) e)
      = ValSpace.dof orc (.ffs p (ValExpr.inferSpaceCtx Γ' e) e) := by
  simp only [ValSpace.dof, ValSpace.shpOf_ffs]
  rw [FFSOracle.sdeq_respect orc p e ih]

/-- Type-level FFS-`dof` Γ-congruence (fixed operand ⇒ `sdeq_respect` alone). -/
theorem inferTypeCtx_gsvd_ffs_Gamma_aux (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ Γ' : List ValTy)
    (e : ValExpr) (p : ValFFSProp)
    (ih : ValSpace.SDEq orc
            (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e))
            (ValTy.spaceOf (ValExpr.inferTypeCtx Γ' e))) :
    orc p (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e)) e
      = orc p (ValTy.spaceOf (ValExpr.inferTypeCtx Γ' e)) e :=
  FFSOracle.sdeq_respect orc p e ih

set_option maxHeartbeats 2400000 in
theorem inferTypeCtx_Gamma_cong (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ Γ' : List ValTy)
    (hΓ : ∀ j, ValSoundOfDenot.ValTy.TyEq orc (Γ.getD j default) (Γ'.getD j default)) :
    ∀ e : ValExpr,
      ValSoundOfDenot.ValTy.TyEq orc
        (ValExpr.inferTypeCtx Γ e) (ValExpr.inferTypeCtx Γ' e)
  | .bvar j => ValSoundOfDenot.ValTyCtx.lookupUse_TyEq orc hΓ j
  | .var y τ => by simp only [ValExpr.inferTypeCtx]
  | .rlit r => by simp only [ValExpr.inferTypeCtx]
  | .zero s => by simp only [ValExpr.inferTypeCtx]
  | .delta n s => by simp only [ValExpr.inferTypeCtx]
  | .idelta s => by simp only [ValExpr.inferTypeCtx]
  | .vlam τ₀ τ₁ e => by simp only [ValExpr.inferTypeCtx]
  | .appV e₀ e₁ => by
      simp only [ValExpr.inferTypeCtx]
      exact ValSoundOfDenot.ValTy.TyEq_applyCodomain orc e₁ e₁
        (inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀)
  | .reshap e τ τ₀ => by simp only [ValExpr.inferTypeCtx]
  | .scale e₀ e₁ => by
      simp only [ValExpr.inferTypeCtx]; exact inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₁
  | .vadd _ _ _ => by
      simp only [ValExpr.inferTypeCtx]
  | .vsum s es => by
      cases es with
      | nil => simp only [ValExpr.inferTypeCtx]
      | cons e es =>
          simp only [ValExpr.inferTypeCtx]; exact inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e
  | .dsumE e₀ e₁ => by
      have ih₀ := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀)
      have ih₁ := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₁)
      simp only [ValExpr.inferTypeCtx, ValSoundOfDenot.ValTy.TyEq,
        ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
      rw [ih₀, ih₁]
  | .tprodE e₀ e₁ => by
      have ih₀ := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀)
      have ih₁ := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₁)
      simp only [ValExpr.inferTypeCtx, ValSoundOfDenot.ValTy.TyEq,
        ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
      rw [ih₀, ih₁]
  | .ttv s e₀ e₁ => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁ => by
      have ihT0 := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ihT1 := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₁
      simp only [ValExpr.inferTypeCtx] at ihT0 ihT1 ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hA' : ValExpr.inferTypeCtx Γ' e₀ with sA' | ⟨aA', bA'⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₁ with sB | ⟨aB, bB⟩ <;>
        rcases hB' : ValExpr.inferTypeCtx Γ' e₁ with sB' | ⟨aB', bB'⟩ <;>
          rw [hA, hA'] at ihT0 <;> rw [hB, hB'] at ihT1 <;>
          first
            | (rcases sA with _|_|⟨c0,c1⟩|⟨c0,c1⟩|⟨cp,cs,ce⟩ <;>
               rcases sA' with _|_|⟨d0,d1⟩|⟨d0,d1⟩|⟨dp,ds,de⟩ <;>
               rcases sB with _|_|⟨g0,g1⟩|⟨g0,g1⟩|⟨gp,gs,ge⟩ <;>
               rcases sB' with _|_|⟨h0,h1⟩|⟨h0,h1⟩|⟨hp,hs,he⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .vkrn e₀ e₁ => by
      have ihT0 := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ihT1 := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₁
      simp only [ValExpr.inferTypeCtx] at ihT0 ihT1 ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hA' : ValExpr.inferTypeCtx Γ' e₀ with sA' | ⟨aA', bA'⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₁ with sB | ⟨aB, bB⟩ <;>
        rcases hB' : ValExpr.inferTypeCtx Γ' e₁ with sB' | ⟨aB', bB'⟩ <;>
          rw [hA, hA'] at ihT0 <;> rw [hB, hB'] at ihT1 <;>
          first
            | (rcases sA with _|_|⟨c0,c1⟩|⟨c0,c1⟩|⟨cp,cs,ce⟩ <;>
               rcases sA' with _|_|⟨d0,d1⟩|⟨d0,d1⟩|⟨dp,ds,de⟩ <;>
               rcases sB with _|_|⟨g0,g1⟩|⟨g0,g1⟩|⟨gp,gs,ge⟩ <;>
               rcases sB' with _|_|⟨h0,h1⟩|⟨h0,h1⟩|⟨hp,hs,he⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .vblk e₀ e₁ => by
      have ihT0 := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ihT1 := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₁
      simp only [ValExpr.inferTypeCtx] at ihT0 ihT1 ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hA' : ValExpr.inferTypeCtx Γ' e₀ with sA' | ⟨aA', bA'⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ e₁ with sB | ⟨aB, bB⟩ <;>
        rcases hB' : ValExpr.inferTypeCtx Γ' e₁ with sB' | ⟨aB', bB'⟩ <;>
          rw [hA, hA'] at ihT0 <;> rw [hB, hB'] at ihT1 <;>
          first
            | (rcases sA with _|_|⟨c0,c1⟩|⟨c0,c1⟩|⟨cp,cs,ce⟩ <;>
               rcases sA' with _|_|⟨d0,d1⟩|⟨d0,d1⟩|⟨dp,ds,de⟩ <;>
               rcases sB with _|_|⟨g0,g1⟩|⟨g0,g1⟩|⟨gp,gs,ge⟩ <;>
               rcases sB' with _|_|⟨h0,h1⟩|⟨h0,h1⟩|⟨hp,hs,he⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .vtrans e₀ => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .pinv e₀ => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .inv e₀ => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .gpinv e₀ a b => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .rrefRep e₀ e₁ => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₁
      simp only [ValExpr.inferTypeCtx] at ihT ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₁ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₁ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel]
  | .gsvdU e₀ a b => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxC := inferTypeCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .cokernel ih
      simp only [ValExpr.inferTypeCtx] at ihT hauxC ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxC <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .gsvdUI e₀ a b => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxK := inferTypeCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .kernel ih
      simp only [ValExpr.inferTypeCtx] at ihT hauxK ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxK <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .gsvdV e₀ a b => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxI := inferTypeCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .image ih
      simp only [ValExpr.inferTypeCtx] at ihT hauxI ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxI <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .gsvdVI e₀ a b => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxCo := inferTypeCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .coimage ih
      simp only [ValExpr.inferTypeCtx] at ihT hauxCo ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxCo <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .gsvdS e₀ a b => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxC := inferTypeCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .cokernel ih
      have hauxI := inferTypeCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .image ih
      simp only [ValExpr.inferTypeCtx] at ihT hauxC hauxI ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxC hauxI <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]
  | .svds e₀ => by
      have ihT := inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ih := ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc ihT
      have hauxC := inferTypeCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .cokernel ih
      have hauxI := inferTypeCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .image ih
      simp only [ValExpr.inferTypeCtx] at ihT hauxC hauxI ⊢
      rcases hA : ValExpr.inferTypeCtx Γ e₀ with sA | ⟨aA, bA⟩ <;>
        rcases hB : ValExpr.inferTypeCtx Γ' e₀ with sB | ⟨aB, bB⟩ <;>
          rw [hA, hB] at ihT hauxC hauxI <;>
          first
            | (rcases sA with _ | _ | ⟨c0, c1⟩ | ⟨c0, c1⟩ | ⟨cp, cs, ce⟩ <;>
               rcases sB with _ | _ | ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨dp, ds, de⟩ <;>
               simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                 ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf])
            | simp_all [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel, ValSpace.skel,
                ValSpace.dof, ValSpace.shpOf, ValTy.spaceOf]

set_option maxHeartbeats 1600000 in
theorem inferSpaceCtx_Gamma_cong (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ Γ' : List ValTy)
    (hΓ : ∀ j, ValSoundOfDenot.ValTy.TyEq orc (Γ.getD j default) (Γ'.getD j default)) :
    ∀ e : ValExpr,
      ValSpace.SDEq orc (ValExpr.inferSpaceCtx Γ e) (ValExpr.inferSpaceCtx Γ' e)
  | .bvar j => ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
      (ValSoundOfDenot.ValTyCtx.lookupUse_TyEq orc hΓ j)
  | .var y τ => by simp only [ValExpr.inferSpaceCtx]
  | .rlit r => by simp only [ValExpr.inferSpaceCtx]
  | .zero s => by simp only [ValExpr.inferSpaceCtx]
  | .delta n s => by simp only [ValExpr.inferSpaceCtx]
  | .idelta s => by simp only [ValExpr.inferSpaceCtx]
  | .vlam τ₀ τ₁ e => by simp only [ValExpr.inferSpaceCtx]
  | .appV e₀ e₁ =>
      ValSoundOfDenot.ValTy.TyEq.spaceOf_SDEq orc
        (inferTypeCtx_Gamma_cong orc Γ Γ' hΓ (.appV e₀ e₁))
  | .reshap e τ τ₀ => by simp only [ValExpr.inferSpaceCtx]
  | .scale e₀ e₁ => by
      simp only [ValExpr.inferSpaceCtx]; exact inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁
  | .vadd _ _ _ => by
      simp only [ValExpr.inferSpaceCtx]
  | .dsumE e₀ e₁ => by
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq, ValSpace.skel]
      rw [inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀, inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁]
  | .tprodE e₀ e₁ => by
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq, ValSpace.skel]
      rw [inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀, inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁]
  | .vsum s es => by
      cases es with
      | nil => simp only [ValExpr.inferSpaceCtx]
      | cons e es =>
          simp only [ValExpr.inferSpaceCtx]; exact inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e
  | .ttv s e₀ e₁ => by
      have ih₀ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁ => by
      have ih₀ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ih₁ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ih₁ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
      cases h1 : ValExpr.inferSpaceCtx Γ e₁ <;>
      cases h1' : ValExpr.inferSpaceCtx Γ' e₁ <;>
        rw [h0, h0'] at ih₀ <;> rw [h1, h1'] at ih₁ <;> simp_all [ValSpace.skel]
  | .vkrn e₀ e₁ => by
      have ih₀ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ih₁ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ih₁ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
      cases h1 : ValExpr.inferSpaceCtx Γ e₁ <;>
      cases h1' : ValExpr.inferSpaceCtx Γ' e₁ <;>
        rw [h0, h0'] at ih₀ <;> rw [h1, h1'] at ih₁ <;> simp_all [ValSpace.skel]
  | .vblk e₀ e₁ => by
      have ih₀ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have ih₁ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ih₁ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
      cases h1 : ValExpr.inferSpaceCtx Γ e₁ <;>
      cases h1' : ValExpr.inferSpaceCtx Γ' e₁ <;>
        rw [h0, h0'] at ih₀ <;> rw [h1, h1'] at ih₁ <;> simp_all [ValSpace.skel]
  | .vtrans e₀ => by
      have ih₀ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .pinv e₀ => by
      have ih₀ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .gpinv e₀ a b => by
      have ih₀ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .inv e₀ => by
      have ih₀ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₀ ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [h0, h0'] at ih₀ <;> simp_all [ValSpace.skel]
  | .gsvdU e₀ a b => by
      have ih := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have haux := inferSpaceCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .cokernel ih
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [h0, h0'] at ih haux <;> simp_all [ValSpace.skel]
  | .gsvdUI e₀ a b => by
      have ih := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have haux := inferSpaceCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .kernel ih
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [h0, h0'] at ih haux <;> simp_all [ValSpace.skel]
  | .gsvdV e₀ a b => by
      have ih := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have haux := inferSpaceCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .image ih
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [h0, h0'] at ih haux <;> simp_all [ValSpace.skel]
  | .gsvdVI e₀ a b => by
      have ih := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have haux := inferSpaceCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .coimage ih
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih ⊢
      cases h0 : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases h0' : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [h0, h0'] at ih haux <;> simp_all [ValSpace.skel]
  | .rrefRep e₀ e₁ => by
      have ih₁ := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq] at ih₁ ⊢
      cases h1 : ValExpr.inferSpaceCtx Γ e₁ <;>
      cases h1' : ValExpr.inferSpaceCtx Γ' e₁ <;>
        rw [h1, h1'] at ih₁ <;> simp_all [ValSpace.skel]
  | .gsvdS e₀ a b => by
      have ih := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq, ValSpace.skel]
      rw [inferSpaceCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .cokernel ih,
          inferSpaceCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .image ih]
  | .svds e₀ => by
      have ih := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      simp only [ValExpr.inferSpaceCtx, ValSpace.SDEq, ValSpace.skel]
      rw [inferSpaceCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .cokernel ih,
          inferSpaceCtx_gsvd_ffs_Gamma_aux orc Γ Γ' e₀ .image ih]

/-- `carrierEl` is invariant under opening a bound index. `ValTy.openRec`
    recurses through `.piTy` without changing the `.space`/`.piTy` head. -/
theorem ValTy.carrierEl_openRec (k : Nat) (u : ValExpr) :
    ∀ (τ : ValTy), (ValTy.openRec k u τ).carrierEl = τ.carrierEl
  | .space _s => rfl
  | .piTy τ₀ τ₁ => by
      unfold ValTy.openRec
      simp only [ValTy.carrierEl]
      rw [ValTy.carrierEl_openRec k u τ₀, ValTy.carrierEl_openRec (k+1) u τ₁]

/-- `.fn`-congruence: equal carriers + cast-compatible families give equal `.fn`
    values. The cast `hAB ▸ y` reconciles the dependent families. -/
theorem ValValSem.fn_congr {A B : Type}
    (f : A → Except DimError ValValSem) (g : B → Except DimError ValValSem)
    (hAB : A = B) (h : ∀ (y : A), f y = g (hAB ▸ y)) :
    ValValSem.fn A f = ValValSem.fn B g := by
  subst hAB
  simp only at h
  exact congrArg (ValValSem.fn A) (funext h)

/-- `fromEl ∘ denotValTy` is opening-invariant (on `HEq`-equal carriers). The
    `.space` leaf uses opening-invariance of `dof`, so its finite `FlatArray`
    resize is unchanged; the `.piTy` arm reconciles dependent `.fn` families via
    `fn_congr` + a `kindSize`-smaller recursion at the codomain (index `k+1`).
    The `fromEl` companion to `toEl_denotValTy_SameShape`, for the `.vlam` bridge
    arm's domain-value reconciliation. -/
theorem fromEl_denotValTy_openRec (orc : FFSOracle)
    [FFSOracle.SubstOpenLaws orc] (u : ValExpr) :
    ∀ (τ : ValTy) (k : Nat) (ρ ρ' : ValEnvSem) (Δ Δ' : List ValValSem)
      (v : (denotValTy orc ρ Δ τ).El)
      (v' : (denotValTy orc ρ' Δ' (ValTy.openRec k u τ)).El),
      HEq v v' →
      ValValSem.fromEl (denotValTy orc ρ Δ τ) v
        = ValValSem.fromEl (denotValTy orc ρ' Δ' (ValTy.openRec k u τ)) v'
  | .space s, k, ρ, ρ', Δ, Δ', v, v', hv => by
      have hvv : v = v' := eq_of_heq hv
      subst hvv
      simp only [ValTy.openRec, denotValTy, ValValSem.fromEl]
      rw [ValSpace.dof_openRec]
  | .piTy τ₀ τ₁, k, ρ, ρ', Δ, Δ', v, v', hv => by
      have hEl : (denotValTy orc ρ Δ τ₀).El
          = (denotValTy orc ρ' Δ' (ValTy.openRec k u τ₀)).El := by
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl, ValTy.carrierEl_openRec]
      have hβ : HEq
          (fun y : (denotValTy orc ρ Δ τ₀).El =>
            Except DimError
              (denotValTy orc ρ
                (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) y :: Δ) τ₁).El)
          (fun y' : (denotValTy orc ρ' Δ' (ValTy.openRec k u τ₀)).El =>
            Except DimError
              (denotValTy orc ρ'
                (ValValSem.fromEl
                    (denotValTy orc ρ' Δ' (ValTy.openRec k u τ₀)) y' :: Δ')
                (ValTy.openRec (k+1) u τ₁)).El) := by
        refine Function.hfunext hEl ?_
        intro y y' _
        apply heq_of_eq
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl, ValTy.carrierEl_openRec]
      simp only [ValTy.openRec, denotValTy, ValValSem.fromEl]
      refine ValValSem.fn_congr _ _ hEl ?_
      intro y
      have hvy : HEq (v y) (v' (hEl ▸ y)) := heq_app_dep hEl hβ hv (cast_heq hEl y).symm
      have hCod :
          (denotValTy orc ρ
            (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) y :: Δ) τ₁).El =
          (denotValTy orc ρ'
            (ValValSem.fromEl (denotValTy orc ρ' Δ' (ValTy.openRec k u τ₀))
              (hEl ▸ y) :: Δ') (ValTy.openRec (k+1) u τ₁)).El := by
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl,
          ValTy.carrierEl_openRec]
      apply except_map_heq_congr hCod (v y) (v' (hEl ▸ y)) hvy
      intro z z' hzz
      exact fromEl_denotValTy_openRec orc u τ₁ (k+1) ρ ρ'
        (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) y :: Δ)
        (ValValSem.fromEl (denotValTy orc ρ' Δ' (ValTy.openRec k u τ₀))
          (hEl ▸ y) :: Δ') z z' hzz
  termination_by τ _ _ _ _ _ _ _ _ => ValTy.kindSize τ
  decreasing_by all_goals (simp only [ValTy.kindSize_piTy]; omega)

/-! ### `denotValB_sem` Γ-head-congruence (for the `.vlam` bridge arm).

`denotValB_sem` reads the de Bruijn TYPE context `Γ` only through `inferSpaceCtx`
(via `dof`/`SDEq`) and `inferTypeCtx` (the `.appV` domain, up to `TyEq`). Hence
it is invariant under a per-entry-`TyEq` change of `Γ` (the
`Δ` value context and `ρ` are untouched). A 27-arm structural induction mirroring
the bridge's arm split — the routing arms close via `inferSpaceCtx_Gamma_cong`,
the `.appV` arm via `inferTypeCtx_Gamma_cong` and `appV_dite_cong`, and `.vlam`
pushes the *unchanged* `τ₀` onto both
contexts. The `.vlam` bridge arm uses this to swap `τ₀::Γ` for `(openRec τ₀)::Γ`
under the binder. -/

 theorem ValueShape.tensor_congr (orc : FFSOracle) {s t : ValSpace}
    (h : ValSpace.SDEq orc s t) (a : FlatArray) :
    ValueShape.tensor orc s a = ValueShape.tensor orc t a := by
  cases s <;> cases t <;>
    simp only [ValueShape.tensor, ValSpace.SDEq, ValSpace.skel] at h ⊢ <;>
    first
    | rfl
    | contradiction
    | (injection h with h0 h1
       rw [ValSpace.SDEq.dof_eq orc h0, ValSpace.SDEq.dof_eq orc h1])

 theorem ValueShape.ttv_congr (orc : FFSOracle) {c c' s s' t t' : ValSpace}
    (hc : ValSpace.dof orc c = ValSpace.dof orc c')
    (hs : ValSpace.SDEq orc s s') (ht : ValSpace.SDEq orc t t') (a b : FlatArray) :
    ValueShape.ttv orc c s t a b = ValueShape.ttv orc c' s' t' a b := by
  unfold ValueShape.ttv ValueShape.pair
  rw [ValSpace.SDEq.dof_eq orc hs, ValSpace.SDEq.dof_eq orc ht, hc]
  cases s <;> cases s' <;>
    simp only [ValSpace.SDEq, ValSpace.skel] at hs ⊢ <;>
    first
    | rfl
    | contradiction
    | (injection hs with h0 h1
       rw [ValSpace.SDEq.dof_eq orc h0])

 theorem ValueShape.mtm_congr (orc : FFSOracle) {c c' s s' t t' : ValSpace}
    (hc : ValSpace.dof orc c = ValSpace.dof orc c')
    (hs : ValSpace.SDEq orc s s') (ht : ValSpace.SDEq orc t t') (a b : FlatArray) :
    ValueShape.mtm orc c s t a b = ValueShape.mtm orc c' s' t' a b := by
  unfold ValueShape.mtm ValueShape.matrices
  rw [ValueShape.tensor_congr orc hs, ValueShape.tensor_congr orc ht]
  cases s <;> cases s' <;> cases t <;> cases t' <;>
    simp only [ValSpace.SDEq, ValSpace.skel] at hs ht ⊢ <;>
    first
    | rfl
    | contradiction
    | (injection hs with h0 h1; injection ht with h2 h3
       rw [ValSpace.SDEq.dof_eq orc h0, ValSpace.SDEq.dof_eq orc h3, hc])

/-- Domain selection preserves the dimension-sensitive type equivalence. -/
theorem ValSoundOfDenot.ValTy.TyEq.domain (orc : FFSOracle)
    {t t' : ValTy} (h : ValSoundOfDenot.ValTy.TyEq orc t t') :
    ValSoundOfDenot.ValTy.TyEq orc t.domain t'.domain := by
  cases t <;> cases t' <;>
    simp_all [ValTy.domain, ValSoundOfDenot.ValTy.TyEq,
      ValSoundOfDenot.ValTy.tyskel, ValSoundOfDenot.ValTy.TySkel.piTy.injEq]

/-- Immediate-domain decoding respects both carrier shape and base dimensions. -/
theorem toElDomainChecked_denotValTy_TyEq (orc : FFSOracle)
    (d d' : ValTy) (h : ValSoundOfDenot.ValTy.TyEq orc d d')
    (ρ ρ' : ValEnvSem) (Δ Δ' : List ValValSem) (v : ValValSem) :
    HEq (ValValSem.toElDomainChecked (denotValTy orc ρ Δ d) v)
        (ValValSem.toElDomainChecked (denotValTy orc ρ' Δ' d') v) := by
  cases d with
  | space s =>
      cases d' with
      | space s' =>
          have hd := ValSoundOfDenot.ValTy.TyEq.toReshEq orc h
          change ValSpace.dof orc s = ValSpace.dof orc s' at hd
          cases v <;>
            simp only [denotValTy, ValValSem.toElDomainChecked, ValValSem.toElChecked, hd] <;> rfl
      | piTy a b => simp [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel] at h
  | piTy a b =>
      cases d' with
      | space s' => simp [ValSoundOfDenot.ValTy.TyEq, ValSoundOfDenot.ValTy.tyskel] at h
      | piTy a' b' =>
          exact toEl_denotValTy_SameShape orc _ _
            (ValSoundOfDenot.ValTy.TyEq.toSameShape orc h) ρ ρ' Δ Δ' v

/-- The finite output length inferred for an expression is invariant under a
pointwise shape-equivalent de Bruijn type context. -/
theorem denotArrayLength_Gamma_cong (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ Γ' : List ValTy)
    (hΓ : ∀ j, ValSoundOfDenot.ValTy.TyEq orc
      (Γ.getD j default) (Γ'.getD j default)) (e : ValExpr) :
    ValSpace.dof orc (ValExpr.inferSpaceCtx Γ e) =
      ValSpace.dof orc (ValExpr.inferSpaceCtx Γ' e) :=
  ValSpace.SDEq.dof_eq orc (inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e)

set_option maxHeartbeats 1600000 in
theorem denotValB_semS_Gamma_cong (orc : FFSOracle) [FFSOracle.Laws orc]
    (ρ : ValEnvSem) :
    ∀ (e : ValExpr) (Γ Γ' : List ValTy) (Δ : List ValValSem),
      (∀ j, ValSoundOfDenot.ValTy.TyEq orc (Γ.getD j default) (Γ'.getD j default)) →
      denotValB_semS (.const orc) ρ Γ Δ e =
        denotValB_semS (.const orc) ρ Γ' Δ e
  | .bvar n, Γ, Γ', Δ => fun _ => by
      simp only [denotValB_sem, denotValB_semS]
  | .var y τ, Γ, Γ', Δ => fun _ => by
      simp only [denotValB_sem, denotValB_semS]
  | .rlit r, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.rlit r)]
  | .zero s, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.zero s)]
  | .delta n s, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.delta n s)]
  | .idelta s, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.idelta s)]
  | .scale e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.scale e₀ e₁),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ]
      simp only [ValueShape.scale, (denotArrayLength_Gamma_cong orc Γ Γ' hΓ e₁)]
  | .vadd s e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      have he₀ := denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ
      have he₁ := denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ
      simp only [denotValB_sem, denotValB_semS]
      simpa only [denotValB_sem] using congrArg₂ (fun r₀ r₁ =>
        ValValSem.bindArrays r₀ r₁ fun a₀ a₁ =>
          let n := ValSpace.dof orc s
          if h₀ : a₀.length = n then
            if h₁ : a₁.length = n then
              .ok (.array (FlatArray.zipWith n (fun x y => x + y) a₀ a₁ h₀ h₁))
            else .error .mismatch
          else .error .mismatch) he₀ he₁
  | .tprodE e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.tprodE e₀ e₁),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ,
        ValSpace.SDEq.dof_eq orc (inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁)]
      simp only [ValueShape.pair, (denotArrayLength_Gamma_cong orc Γ Γ' hΓ e₀), (denotArrayLength_Gamma_cong orc Γ Γ' hΓ e₁)]
  | .dsumE e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.dsumE e₀ e₁),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ,
        ValSpace.SDEq.dof_eq orc (inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀)]
      simp only [ValueShape.pair, (denotArrayLength_Gamma_cong orc Γ Γ' hΓ e₀), (denotArrayLength_Gamma_cong orc Γ Γ' hΓ e₁)]
  | .vsum s es, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS]
      rw [denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.vsum s es)]
      by_cases hcount : ValSpace.dof orc s ≤ es.length
      · simp only [hcount, ↓reduceIte]
        congr 1
        apply congrArg ValValSem.sequenceArrays
        apply List.map_congr_left
        intro e he
        have hmem : e.1 ∈ es := List.mem_of_mem_take e.2
        exact denotValB_semS_Gamma_cong orc ρ e.1 Γ Γ' Δ hΓ
      · simp only [hcount, ↓reduceIte]
  | .reshap e τ τ₀, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS,
        denotValB_semS_Gamma_cong orc ρ e Γ Γ' Δ hΓ]
      generalize hv : denotValB_semS (.const orc) ρ Γ' Δ e = result
      cases result with
      | error _ => rfl
      | ok v =>
          simp only
          have hleft := reshapDenotSemS_const_env orc ρ ValEnvSem.empty
            Γ [] Δ [] v τ τ₀
          have hright := reshapDenotSemS_const_env orc ρ ValEnvSem.empty
            Γ' [] Δ [] v τ τ₀
          rw [hleft, hright]
  | .vtrans e₀, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ]
      rw [denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.vtrans e₀)]
      simp only [FFSOracleSem.const]
      congr 1
      funext a
      simp only [ValueShape.tensor_congr orc hsd]
      split
      ·
        cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
          rw [hL, hR] at hsd <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
          first
          | rfl
          | (injection hsd with h0 h1
             simp only [ValSpace.SDEq.dof_eq orc h0, ValSpace.SDEq.dof_eq orc h1])
          | injection hsd
      · rfl
  | .ttv s e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.ttv s e₀ e₁),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ]
      simp only [FFSOracleSem.const]
      congr 1
      funext a₀ a₁
      simp only [ValueShape.ttv_congr orc rfl hsd (inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁)]
      split
      ·
        cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
          rw [hL, hR] at hsd <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
          first
          | rfl
          | (injection hsd with h0' h1'
             simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
             rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
          | (injection hsd with h0' h1'
             simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
          | injection hsd
      · rfl
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      have hsd0 := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have hsd1 := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.mtm n₀ n₁ s₀ s₁ e₀ e₁),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ]
      simp only [FFSOracleSem.const]
      congr 1
      funext a₀ a₁
      simp only [ValueShape.mtm_congr orc rfl hsd0 hsd1]
      split
      ·
        cases hL0 : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR0 : ValExpr.inferSpaceCtx Γ' e₀ <;>
        cases hL1 : ValExpr.inferSpaceCtx Γ e₁ <;>
        cases hR1 : ValExpr.inferSpaceCtx Γ' e₁ <;>
          rw [hL0, hR0] at hsd0 <;> rw [hL1, hR1] at hsd1 <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd0 hsd1 <;>
          first
          | rfl
          | (injection hsd0 with a0 a1; injection hsd1 with b0 b1
             simp only [ValSpace.SDEq.dof_eq orc a0, ValSpace.SDEq.dof_eq orc a1,
               ValSpace.SDEq.dof_eq orc b0, ValSpace.SDEq.dof_eq orc b1])
          | cases hsd0
          | cases hsd1
      · rfl
  | .vkrn e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      have hsd0 := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have hsd1 := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.vkrn e₀ e₁),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ]
      simp only [FFSOracleSem.const]
      congr 1
      funext a₀ a₁
      simp only [ValueShape.matrices, ValueShape.tensor_congr orc hsd0, ValueShape.tensor_congr orc hsd1]
      split
      ·
        cases hL0 : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR0 : ValExpr.inferSpaceCtx Γ' e₀ <;>
        cases hL1 : ValExpr.inferSpaceCtx Γ e₁ <;>
        cases hR1 : ValExpr.inferSpaceCtx Γ' e₁ <;>
          rw [hL0, hR0] at hsd0 <;> rw [hL1, hR1] at hsd1 <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd0 hsd1 <;>
          first
          | rfl
          | (injection hsd0 with a0 a1; injection hsd1 with b0 b1
             simp only [ValSpace.SDEq.dof_eq orc a0, ValSpace.SDEq.dof_eq orc a1,
               ValSpace.SDEq.dof_eq orc b0, ValSpace.SDEq.dof_eq orc b1])
          | cases hsd0
          | cases hsd1
      · rfl
  | .vblk e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      have hsd0 := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      have hsd1 := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.vblk e₀ e₁),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ]
      simp only [FFSOracleSem.const]
      congr 1
      funext a₀ a₁
      simp only [ValueShape.matrices, ValueShape.tensor_congr orc hsd0, ValueShape.tensor_congr orc hsd1]
      split
      ·
        cases hL0 : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR0 : ValExpr.inferSpaceCtx Γ' e₀ <;>
        cases hL1 : ValExpr.inferSpaceCtx Γ e₁ <;>
        cases hR1 : ValExpr.inferSpaceCtx Γ' e₁ <;>
          rw [hL0, hR0] at hsd0 <;> rw [hL1, hR1] at hsd1 <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd0 hsd1 <;>
          first
          | rfl
          | (injection hsd0 with a0 a1; injection hsd1 with b0 b1
             simp only [ValSpace.SDEq.dof_eq orc a0, ValSpace.SDEq.dof_eq orc a1,
               ValSpace.SDEq.dof_eq orc b0, ValSpace.SDEq.dof_eq orc b1])
          | cases hsd0
          | cases hsd1
      · rfl
  | .pinv e₀, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.pinv e₀),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [hL, hR] at hsd <;>
        first
        | cases hsd
        | (simp only [ValSpace.SDEq, ValSpace.skel] at hsd
           injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (simp only [ValSpace.SDEq.dof_eq orc hsd]
           rw [ValSpace.SDEq.dof_eq orc hsd])
  | .gpinv e₀ a b, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.gpinv e₀ a b),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ a Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ b Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | injection hsd
  | .inv e₀, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.inv e₀),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [hL, hR] at hsd <;>
        first
        | cases hsd
        | (simp only [ValSpace.SDEq, ValSpace.skel] at hsd
           injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (simp only [ValSpace.SDEq.dof_eq orc hsd]
           rw [ValSpace.SDEq.dof_eq orc hsd])
  | .svds e₀, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.svds e₀),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | injection hsd
  | .gsvdS e₀ a b, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.gsvdS e₀ a b),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ a Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ b Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | injection hsd
  | .gsvdU e₀ a b, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.gsvdU e₀ a b),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ a Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ b Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | injection hsd
  | .gsvdUI e₀ a b, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.gsvdUI e₀ a b),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ a Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ b Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | injection hsd
  | .gsvdV e₀ a b, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.gsvdV e₀ a b),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ a Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ b Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | injection hsd
  | .gsvdVI e₀ a b, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₀
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.gsvdVI e₀ a b),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ a Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ b Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₀ <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | injection hsd
  | .rrefRep e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      have hsd := inferSpaceCtx_Gamma_cong orc Γ Γ' hΓ e₁
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_Gamma_cong orc Γ Γ' hΓ (.rrefRep e₀ e₁),
        denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ,
        denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ]
      congr 1
      funext i
      cases hL : ValExpr.inferSpaceCtx Γ e₁ <;>
      cases hR : ValExpr.inferSpaceCtx Γ' e₁ <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | injection hsd
  | .vlam τ₀ τ₁ body, Γ, Γ', Δ => fun hΓ => by
      rw [denotValB_semS, denotValB_semS]
      apply congrArg Except.ok
      rw [← denotValTy_eq_denotValTyS orc ρ τ₀ Γ Δ,
        ← denotValTy_eq_denotValTyS orc ρ τ₀ Γ' Δ]
      refine ValValSem.fn_congr _ _ rfl ?_
      intro v
      simp only []
      exact denotValB_semS_Gamma_cong orc ρ body (τ₀ :: Γ) (τ₀ :: Γ')
        (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v :: Δ)
        (fun j => by
          cases j with
          | zero => exact ValSoundOfDenot.ValTy.TyEq.refl orc τ₀
          | succ j => exact hΓ j)
  | .appV e₀ e₁, Γ, Γ', Δ => fun hΓ => by
      have hv0 := denotValB_semS_Gamma_cong orc ρ e₀ Γ Γ' Δ hΓ
      have hv1 := denotValB_semS_Gamma_cong orc ρ e₁ Γ Γ' Δ hΓ
      have hss : ValSoundOfDenot.ValTy.SameShape
          (ValExpr.inferTypeCtx Γ e₀).domain
          (ValExpr.inferTypeCtx Γ' e₀).domain :=
        ValSoundOfDenot.ValTy.SameShape.domain
          (ValSoundOfDenot.ValTy.TyEq.toSameShape orc (inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀))
      have hEl : (denotValTy orc ρ Δ (ValExpr.inferTypeCtx Γ e₀).domain).El
          = (denotValTy orc ρ Δ (ValExpr.inferTypeCtx Γ' e₀).domain).El := by
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl,
            ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss]
      rw [denotValB_semS, denotValB_semS, hv0, hv1]
      generalize hfun : denotValB_semS (.const orc) ρ Γ' Δ e₀ = funResult
      cases funResult with
      | error _ => rfl
      | ok funVal =>
          cases funVal with
          | array _ => rfl
          | fn T f =>
              generalize harg : denotValB_semS (.const orc) ρ Γ' Δ e₁ = argResult
              cases argResult with
              | error _ => rfl
              | ok arg =>
                  simp only
                  have htoEl : HEq
                      (ValValSem.toElDomainChecked
                        (denotValTy orc ρ Δ (ValExpr.inferTypeCtx Γ e₀).domain) arg)
                      (ValValSem.toElDomainChecked
                        (denotValTy orc ρ Δ (ValExpr.inferTypeCtx Γ' e₀).domain) arg) :=
                    toElDomainChecked_denotValTy_TyEq orc _ _
                      (ValSoundOfDenot.ValTy.TyEq.domain orc
                        (inferTypeCtx_Gamma_cong orc Γ Γ' hΓ e₀)) ρ ρ Δ Δ arg
                  have hElS :
                      (denotValTyS (.const orc) ρ Γ Δ
                        (ValExpr.inferTypeCtx Γ e₀).domain).El =
                      (denotValTyS (.const orc) ρ Γ' Δ
                        (ValExpr.inferTypeCtx Γ' e₀).domain).El := by
                    rw [← denotValTy_eq_denotValTyS,
                      ← denotValTy_eq_denotValTyS]
                    exact hEl
                  have htoElS : HEq
                      (ValValSem.toElDomainChecked
                        (denotValTyS (.const orc) ρ Γ Δ
                          (ValExpr.inferTypeCtx Γ e₀).domain) arg)
                      (ValValSem.toElDomainChecked
                        (denotValTyS (.const orc) ρ Γ' Δ
                          (ValExpr.inferTypeCtx Γ' e₀).domain) arg) := by
                    rw [← denotValTy_eq_denotValTyS,
                      ← denotValTy_eq_denotValTyS]
                    exact htoEl
                  exact valSound_appV_match_congr_domainChecked (.fn T f) arg arg hElS htoElS
  termination_by e _ _ _ => ValExpr.size e
  decreasing_by
    all_goals
      first
      | (simp only [ValExpr.size]; omega)
      | (simp only [ValExpr.size]
         have := ValExpr.size_le_sizeList hmem; omega)

theorem denotValB_sem_Gamma_cong (orc : FFSOracle) [FFSOracle.Laws orc]
    (ρ : ValEnvSem)
    (e : ValExpr) (Γ Γ' : List ValTy) (Δ : List ValValSem)
    (hΓ : ∀ j, ValSoundOfDenot.ValTy.TyEq orc
      (Γ.getD j default) (Γ'.getD j default)) :
    denotValB_sem orc ρ Γ Δ e = denotValB_sem orc ρ Γ' Δ e :=
  denotValB_semS_Gamma_cong orc ρ e Γ Γ' Δ hΓ

/-! ### The D1 ↔ named-opening bridge (the LN soundness keystone).

The `vlam`/`appV` soundness arms connect the cofinite-NAMED typing IH (on
`openVar x body`, typed in `ε.insert x τ₀`) to the D1 denotation `denot ρ (v::Δ)
body`. The correct, off-by-one-free relation keeps `v` in `Δ` on BOTH sides and
binds `x ↦ Δ.getD k` in `ρ`, requiring `k < Δ.length`; stated generally over the de Bruijn index `k` so it
is closed under binders (`k ↦ k+1`, `Δ ↦ v'::Δ`, `(v'::Δ).getD (k+1) = Δ.getD k`).
The `vlam` arm uses the `k = 0`, `Δ ↦ v::Δ` instance. -/
/-- Opening a value expression at a type-correct de Bruijn slot preserves its
inferred finite array length. -/
theorem denotArrayLength_openRec (orc : FFSOracle) [FFSOracle.Laws orc]
    (Γ : List ValTy)
    (k : Nat) (x : VName) (σ : ValTy) (hΓk : Γ.getD k default = σ)
    (e : ValExpr) :
    ValSpace.dof orc (ValExpr.inferSpaceCtx Γ e) =
      ValSpace.dof orc
        (ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e)) :=
  (ValSpace.SDEq.dof_eq orc (inferSpaceCtx_SDEq orc Γ k x σ hΓk e)).symm

set_option maxHeartbeats 1600000 in
theorem denotValB_semS_openRec_bridge (orc : FFSOracle) [FFSOracle.Laws orc]
    (ρ : ValEnvSem)
    (x : VName) (σ : ValTy) :
    ∀ (e : ValExpr) (Γ : List ValTy) (Δ : List ValValSem) (k : Nat),
      x ∉ ValExpr.fv e → Γ.getD k default = σ → k < Δ.length →
      denotValB_semS (.const orc) ρ Γ Δ e
        = denotValB_semS (.const orc)
            (ρ.update x (Δ.getD k ValValSem.default)) Γ Δ
            (ValExpr.openRec k (.var x σ) e)
  -- Structural recursion on `e` (well-founded on `ValExpr.size`, so the
  -- `.vsum` list family + the binder arms recurse on size-smaller subterms).
  -- The de Bruijn TYPE context `Γ` makes `inferSpaceCtx` of the unopened body
  -- agree (up to `SDEq`, via `inferSpaceCtx_SDEq`) with the opened body; the
  -- annotation openings are denotationally irrelevant except where the
  -- denotation reads a type (handled by the carrier enablers in the binder
  -- arms).
  | .bvar n, Γ, Δ, k => fun _ hΓk hkΔ => by
      by_cases h : n = k
      · subst n
        simp only [ValExpr.openRec, ↓reduceIte]
        rw [denotValB_semS, denotValB_semS, ValEnvSem.update_same,
          StrictValueAccess.lookup_eq_getD_of_lt Δ k ValValSem.default hkΔ]
      · simp only [ValExpr.openRec, if_neg h]
        rw [denotValB_semS, denotValB_semS]
  | .var y τ, Γ, Δ, k => fun hfv _ hkΔ => by
      simp only [ValExpr.fv, Finset.mem_insert, not_or] at hfv
      obtain ⟨hxy, _⟩ := hfv
      rw [ValExpr.openRec, denotValB_semS, denotValB_semS,
        ValEnvSem.update_other _ _ _ _ (Ne.symm hxy)]
  | .rlit r, Γ, Δ, k => fun _ hΓk hkΔ => by
      rw [ValExpr.openRec, denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.rlit r)]
  | .zero s, Γ, Δ, k => fun _ hΓk hkΔ => by
      rw [ValExpr.openRec, denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.zero s)]
      simp only [ValExpr.openRec]
  | .delta n s, Γ, Δ, k => fun _ hΓk hkΔ => by
      rw [ValExpr.openRec, denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.delta n s), ValSpace.dof_openRec]
      simp only [ValExpr.openRec]
  | .idelta s, Γ, Δ, k => fun _ hΓk hkΔ => by
      rw [ValExpr.openRec, denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.idelta s), ValSpace.dof_openRec]
      simp only [ValExpr.openRec]
  | .scale e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨h0, h1⟩ := hfv
      rw [ValExpr.openRec, denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.scale e₀ e₁),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ]
      simp only [ValExpr.openRec]
      simp only [ValueShape.scale, (denotArrayLength_openRec orc Γ k x σ hΓk e₁)]
  | .vadd s e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨_hs, h0⟩, h1⟩ := hfv
      have he₀ := denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ
      have he₁ := denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ
      simp only [ValExpr.openRec, denotValB_sem, denotValB_semS]
      rw [ValSpace.dof_openRec]
      simpa only [denotValB_sem] using congrArg₂ (fun r₀ r₁ =>
        ValValSem.bindArrays r₀ r₁ fun a₀ a₁ =>
          let n := ValSpace.dof orc s
          if h₀ : a₀.length = n then
            if h₁ : a₁.length = n then
              .ok (.array (FlatArray.zipWith n (fun x y => x + y) a₀ a₁ h₀ h₁))
            else .error .mismatch
          else .error .mismatch) he₀ he₁
  | .tprodE e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨h0, h1⟩ := hfv
      rw [ValExpr.openRec, denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.tprodE e₀ e₁),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ,
        ValSpace.SDEq.dof_eq orc (inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁)]
      simp only [ValExpr.openRec]
      simp only [ValueShape.pair, (denotArrayLength_openRec orc Γ k x σ hΓk e₀), (denotArrayLength_openRec orc Γ k x σ hΓk e₁)]
  | .dsumE e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨h0, h1⟩ := hfv
      rw [ValExpr.openRec, denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.dsumE e₀ e₁),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ,
        ValSpace.SDEq.dof_eq orc (inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀)]
      simp only [ValExpr.openRec]
      simp only [ValueShape.pair, (denotArrayLength_openRec orc Γ k x σ hΓk e₀), (denotArrayLength_openRec orc Γ k x σ hΓk e₁)]
  | .vsum s es, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨_, hes⟩ := hfv
      have hlen := denotArrayLength_openRec orc Γ k x σ hΓk (.vsum s es)
      simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hlen
      simp only [ValExpr.openRec, ValExpr.openRecList_eq_map]
      rw [denotValB_semS, denotValB_semS, ValSpace.dof_openRec, hlen]
      simp only [List.length_map]
      by_cases hcount : ValSpace.dof orc s ≤ es.length
      · simp only [hcount, ↓reduceIte]
        congr 1
        apply congrArg ValValSem.sequenceArrays
        simp only [List.attach_map_val, ← List.map_take, List.map_map,
          Function.comp_apply]
        apply List.map_congr_left
        intro e he
        have hmem : e ∈ es := List.mem_of_mem_take he
        have hfve : x ∉ ValExpr.fv e := fun hc =>
          hes (ValExpr.mem_fvList.mpr ⟨e, hmem, hc⟩)
        exact denotValB_semS_openRec_bridge orc ρ x σ e Γ Δ k hfve hΓk hkΔ
      · simp only [hcount, ↓reduceIte]
  | .reshap e τ τ₀, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨he, _⟩, _⟩ := hfv
      have he_bridge := denotValB_semS_openRec_bridge orc ρ x σ e Γ Δ k he hΓk hkΔ
      have htgt : ValSoundOfDenot.ValTy.ReshEq orc
          (ValTy.openRec k (.var x σ) τ) τ :=
        ValSoundOfDenot.ValTy.ReshEq_openRec orc k (.var x σ) τ
      have hsrc : ValSoundOfDenot.ValTy.ReshEq orc
          (ValTy.openRec k (.var x σ) τ₀) τ₀ :=
        ValSoundOfDenot.ValTy.ReshEq_openRec orc k (.var x σ) τ₀
      rw [ValExpr.openRec, denotValB_semS, denotValB_semS, ← he_bridge]
      generalize hv : denotValB_semS (.const orc) ρ Γ Δ e = result
      cases result with
      | error _ => rfl
      | ok v =>
          simp only
          have hleft := reshapDenotSemS_const_env orc ρ ValEnvSem.empty
            Γ [] Δ [] v τ τ₀
          have hright := reshapDenotSemS_const_env orc
            (ρ.update x (Δ.getD k ValValSem.default)) ValEnvSem.empty
            Γ [] Δ [] v (ValTy.openRec k (.var x σ) τ)
            (ValTy.openRec k (.var x σ) τ₀)
          rw [hleft, hright]
          simpa only [reshapDenotSem] using
            (reshapDenotSem_ReshEq orc _ _ _ _ htgt hsrc v).symm
  | .vtrans e₀, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv] at hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.vtrans e₀),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k hfv hΓk hkΔ]
      simp only [FFSOracleSem.const]
      congr 1
      funext a
      simp only [ValueShape.tensor_congr orc hsd]
      split
      ·
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
          rw [hL, hR] at hsd <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
          first
          | rfl
          | (injection hsd with h0 h1
             simp only [ValSpace.SDEq.dof_eq orc h0, ValSpace.SDEq.dof_eq orc h1])
          | injection hsd
      · rfl
  | .ttv s e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨_, h0⟩, h1⟩ := hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.ttv s e₀ e₁),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ]
      simp only [ValSpace.dof_openRec]
      simp only [FFSOracleSem.const]
      congr 1
      funext a₀ a₁
      simp only [ValueShape.ttv_congr orc (ValSpace.dof_openRec orc k (.var x σ) s) hsd (inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁)]
      split
      ·
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
          rw [hL, hR] at hsd <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
          first
          | rfl
          | (injection hsd with h0' h1'
             simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
             rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
          | (injection hsd with h0' h1'
             simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
          | injection hsd
      · rfl
  | .vkrn e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨h0, h1⟩ := hfv
      have hsd0 := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have hsd1 := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.vkrn e₀ e₁),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ]
      simp only [FFSOracleSem.const]
      congr 1
      funext a₀ a₁
      simp only [ValueShape.matrices, ValueShape.tensor_congr orc hsd0, ValueShape.tensor_congr orc hsd1]
      split
      ·
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        cases hL0 : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        cases hL1 : ValExpr.inferSpaceCtx Γ e₁ <;>
        cases hR1 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₁) <;>
          rw [hL0, hR0] at hsd0 <;> rw [hL1, hR1] at hsd1 <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd0 hsd1 <;>
          first
          | rfl
          | (injection hsd0 with a0 a1; injection hsd1 with b0 b1
             simp only [ValSpace.SDEq.dof_eq orc a0, ValSpace.SDEq.dof_eq orc a1,
               ValSpace.SDEq.dof_eq orc b0, ValSpace.SDEq.dof_eq orc b1])
          | cases hsd0
          | cases hsd1
      · rfl
  | .vblk e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨h0, h1⟩ := hfv
      have hsd0 := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have hsd1 := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.vblk e₀ e₁),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ]
      simp only [FFSOracleSem.const]
      congr 1
      funext a₀ a₁
      simp only [ValueShape.matrices, ValueShape.tensor_congr orc hsd0, ValueShape.tensor_congr orc hsd1]
      split
      ·
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        cases hL0 : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        cases hL1 : ValExpr.inferSpaceCtx Γ e₁ <;>
        cases hR1 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₁) <;>
          rw [hL0, hR0] at hsd0 <;> rw [hL1, hR1] at hsd1 <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd0 hsd1 <;>
          first
          | rfl
          | (injection hsd0 with a0 a1; injection hsd1 with b0 b1
             simp only [ValSpace.SDEq.dof_eq orc a0, ValSpace.SDEq.dof_eq orc a1,
               ValSpace.SDEq.dof_eq orc b0, ValSpace.SDEq.dof_eq orc b1])
          | cases hsd0
          | cases hsd1
      · rfl
  | .mtm n₀ n₁ s₀ s₁ e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨⟨_, _⟩, h0⟩, h1⟩ := hfv
      have hsd0 := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      have hsd1 := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.mtm n₀ n₁ s₀ s₁ e₀ e₁),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ]
      simp only [ValSpace.dof_openRec]
      simp only [FFSOracleSem.const]
      congr 1
      funext a₀ a₁
      simp only [ValueShape.mtm_congr orc (ValSpace.dof_openRec orc k (.var x σ) s₀) hsd0 hsd1]
      split
      ·
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        cases hL0 : ValExpr.inferSpaceCtx Γ e₀ <;>
        cases hR0 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        cases hL1 : ValExpr.inferSpaceCtx Γ e₁ <;>
        cases hR1 : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₁) <;>
          rw [hL0, hR0] at hsd0 <;> rw [hL1, hR1] at hsd1 <;>
          simp only [ValSpace.SDEq, ValSpace.skel] at hsd0 hsd1 <;>
          first
          | rfl
          | (injection hsd0 with a0 a1; injection hsd1 with b0 b1
             simp only [ValSpace.SDEq.dof_eq orc a0, ValSpace.SDEq.dof_eq orc a1,
               ValSpace.SDEq.dof_eq orc b0, ValSpace.SDEq.dof_eq orc b1])
          | cases hsd0
          | cases hsd1
      · rfl
  | .pinv e₀, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv] at hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.pinv e₀),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k hfv hΓk hkΔ]
      congr 1
      funext a
      simp only [FFSOracleSem.const, ValExpr.openRec]
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        rw [hL, hR] at hsd <;>
        first
        | cases hsd
        | (simp only [ValSpace.SDEq, ValSpace.skel] at hsd
           injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (simp only [ValSpace.SDEq.dof_eq orc hsd]
           rw [ValSpace.SDEq.dof_eq orc hsd])
  | .gpinv e₀ a b, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨he, ha⟩, hb⟩ := hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.gpinv e₀ a b),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k he hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ a Γ Δ k ha hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ b Γ Δ k hb hΓk hkΔ]
      congr 1
      funext ae aa ab
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           simp only [FFSOracleSem.const, ValExpr.openRec])
        | injection hsd
  | .inv e₀, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv] at hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.inv e₀),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k hfv hΓk hkΔ]
      congr 1
      funext a
      simp only [FFSOracleSem.const, ValExpr.openRec]
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        rw [hL, hR] at hsd <;>
        first
        | cases hsd
        | (simp only [ValSpace.SDEq, ValSpace.skel] at hsd
           injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | (simp only [ValSpace.SDEq.dof_eq orc hsd]
           rw [ValSpace.SDEq.dof_eq orc hsd])
  | .svds e₀, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv] at hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.svds e₀),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k hfv hΓk hkΔ]
      congr 1
      funext a
      simp only [FFSOracleSem.const, ValExpr.openRec]
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rw [ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1'])
        | injection hsd
  | .gsvdS e₀ a b, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨he, ha⟩, hb⟩ := hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.gsvdS e₀ a b),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k he hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ a Γ Δ k ha hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ b Γ Δ k hb hΓk hkΔ]
      congr 1
      funext ae aa ab
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [FFSOracleSem.const, ValExpr.openRec,
             ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rfl)
        | injection hsd
  | .gsvdU e₀ a b, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨he, ha⟩, hb⟩ := hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.gsvdU e₀ a b),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k he hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ a Γ Δ k ha hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ b Γ Δ k hb hΓk hkΔ]
      congr 1
      funext ae aa ab
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [FFSOracleSem.const, ValExpr.openRec,
             ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rfl)
        | injection hsd
  | .gsvdUI e₀ a b, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨he, ha⟩, hb⟩ := hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.gsvdUI e₀ a b),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k he hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ a Γ Δ k ha hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ b Γ Δ k hb hΓk hkΔ]
      congr 1
      funext ae aa ab
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [FFSOracleSem.const, ValExpr.openRec,
             ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rfl)
        | injection hsd
  | .gsvdV e₀ a b, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨he, ha⟩, hb⟩ := hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.gsvdV e₀ a b),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k he hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ a Γ Δ k ha hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ b Γ Δ k hb hΓk hkΔ]
      congr 1
      funext ae aa ab
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [FFSOracleSem.const, ValExpr.openRec,
             ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rfl)
        | injection hsd
  | .gsvdVI e₀ a b, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨he, ha⟩, hb⟩ := hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₀
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.gsvdVI e₀ a b),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k he hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ a Γ Δ k ha hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ b Γ Δ k hb hΓk hkΔ]
      congr 1
      funext ae aa ab
      cases hL : ValExpr.inferSpaceCtx Γ e₀ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₀) <;>
        rw [hL, hR] at hsd <;>
        simp only [ValSpace.SDEq, ValSpace.skel] at hsd <;>
        first
        | rfl
        | (injection hsd with h0' h1'
           simp only [FFSOracleSem.const, ValExpr.openRec,
             ValSpace.SDEq.dof_eq orc h0', ValSpace.SDEq.dof_eq orc h1']
           rfl)
        | injection hsd
  | .rrefRep e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨h0, h1⟩ := hfv
      have hsd := inferSpaceCtx_SDEq orc Γ k x σ hΓk e₁
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS,
        denotArrayLength_openRec orc Γ k x σ hΓk (.rrefRep e₀ e₁),
        ← denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ,
        ← denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ]
      congr 1
      funext a₀ a₁
      cases hL : ValExpr.inferSpaceCtx Γ e₁ <;>
      cases hR : ValExpr.inferSpaceCtx Γ (ValExpr.openRec k (.var x σ) e₁) <;>
        rw [hL, hR] at hsd <;>
        first
        | rfl
        | cases hsd
        | (simp only [ValSpace.SDEq, ValSpace.skel] at hsd
           injection hsd with h0' h1'
           simp only [ValSpace.SDEq.dof_eq orc h0',
             ValSpace.SDEq.dof_eq orc h1']
           rfl)
  | .vlam τ₀ τ₁ body, Γ, Δ, k => fun hfv hΓk hkΔ => by

      -- ρ (τ₀::Γ) (fromEl τ₀_sem v :: Δ) body)`; RHS = `.fn τ₀'_sem.El (fun v =>
      -- denot ρ' (openRec τ₀ :: Γ) (fromEl τ₀'_sem v :: Δ) (openRec_{k+1} body))`.
      -- Carriers agree (`hElτ`: denotValTy_El_eq_carrierEl + carrierEl_openRec).
      -- For the bodies (per `v`): bridge IH on `body` at `k+1` (Γ↦τ₀::Γ, Δ↦w::Δ;
      -- side condition (τ₀::Γ).getD (k+1) = Γ.getD k = σ); then the Γ-head swap
      -- τ₀ ↦ openRec τ₀ via `denotValB_sem_Gamma_cong` (the entries are `TyEq`);
      -- then the domain value `w = fromEl (…τ₀) v` vs `w'' = fromEl (…openRec τ₀)
      -- (hElτ ▸ v)` reconciled by `fromEl_denotValTy_openRec`.
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨⟨_, _⟩, hbody⟩ := hfv
      have hElτ : (denotValTy orc ρ Δ τ₀).El
          = (denotValTy orc (ρ.update x (Δ.getD k ValValSem.default)) Δ
              (ValTy.openRec k (.var x σ) τ₀)).El := by
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl, ValTy.carrierEl_openRec]
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS]
      apply congrArg Except.ok
      rw [← denotValTy_eq_denotValTyS orc ρ τ₀ Γ Δ,
        ← denotValTy_eq_denotValTyS orc
          (ρ.update x (Δ.getD k ValValSem.default))
          (ValTy.openRec k (.var x σ) τ₀) Γ Δ]
      refine ValValSem.fn_congr _ _ hElτ ?_
      intro v
      dsimp only
      have ha := denotValB_semS_openRec_bridge orc ρ x σ body (τ₀ :: Γ)
        (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v :: Δ) (k+1) hbody
        (by simpa using hΓk) (by simpa using Nat.succ_lt_succ hkΔ)
      have hb := denotValB_semS_Gamma_cong orc (ρ.update x (Δ.getD k ValValSem.default))
        (ValExpr.openRec (k+1) (.var x σ) body)
        (τ₀ :: Γ) (ValTy.openRec k (.var x σ) τ₀ :: Γ)
        (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v :: Δ)
        (fun j => by
          cases j with
          | zero => exact (ValSoundOfDenot.ValTy.TyEq_openRec orc k (.var x σ) τ₀).symm
          | succ j => exact ValSoundOfDenot.ValTy.TyEq.refl orc _)
      have hc := fromEl_denotValTy_openRec orc (.var x σ) τ₀ k ρ
        (ρ.update x (Δ.getD k ValValSem.default)) Δ Δ v (hElτ ▸ v) (cast_heq hElτ v).symm
      rw [ha]
      simp only [List.getD_cons_succ]
      rw [hb, hc]
  | .appV e₀ e₁, Γ, Δ, k => fun hfv hΓk hkΔ => by
      -- DEPENDENT ARM. Share v₀/v₁ via the bridge IH, then the two domain-aware
      -- applications agree by `appV_dite_cong` (carriers equal via
      -- `inferTypeCtx_domain_SameShape`+`SameShape.carrierEl_eq`, coerced args
      -- `HEq`-equal via `toEl_denotValTy_SameShape`).
      simp only [ValExpr.fv, Finset.mem_union, not_or] at hfv
      obtain ⟨h0, h1⟩ := hfv
      have hv0 := denotValB_semS_openRec_bridge orc ρ x σ e₀ Γ Δ k h0 hΓk hkΔ
      have hv1 := denotValB_semS_openRec_bridge orc ρ x σ e₁ Γ Δ k h1 hΓk hkΔ
      have hss : ValSoundOfDenot.ValTy.SameShape
          (ValExpr.inferTypeCtx Γ e₀).domain
          (ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀)).domain :=
        (inferTypeCtx_domain_SameShape Γ k x σ hΓk e₀).symm
      have hEl : (denotValTy orc ρ Δ (ValExpr.inferTypeCtx Γ e₀).domain).El
          = (denotValTy orc (ρ.update x (Δ.getD k ValValSem.default)) Δ
              (ValExpr.inferTypeCtx Γ (ValExpr.openRec k (.var x σ) e₀)).domain).El := by
        rw [denotValTy_El_eq_carrierEl, denotValTy_El_eq_carrierEl,
            ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hss]
      simp only [ValExpr.openRec]
      rw [denotValB_semS, denotValB_semS, ← hv0, ← hv1]
      generalize hfun : denotValB_semS (.const orc) ρ Γ Δ e₀ = funResult
      cases funResult with
      | error _ => rfl
      | ok funVal =>
          cases funVal with
          | array _ => rfl
          | fn T f =>
              generalize harg : denotValB_semS (.const orc) ρ Γ Δ e₁ = argResult
              cases argResult with
              | error _ => rfl
              | ok arg =>
                  simp only
                  have htoEl : HEq
                      (ValValSem.toElDomainChecked
                        (denotValTy orc ρ Δ (ValExpr.inferTypeCtx Γ e₀).domain) arg)
                      (ValValSem.toElDomainChecked
                        (denotValTy orc (ρ.update x (Δ.getD k ValValSem.default)) Δ
                          (ValExpr.inferTypeCtx Γ
                            (ValExpr.openRec k (.var x σ) e₀)).domain) arg) :=
                    toElDomainChecked_denotValTy_TyEq orc _ _
                      (ValSoundOfDenot.ValTy.TyEq.domain orc
                        (inferTypeCtx_TyEq orc Γ k x σ hΓk e₀).symm) ρ _ Δ Δ arg
                  have hElS :
                      (denotValTyS (.const orc) ρ Γ Δ
                        (ValExpr.inferTypeCtx Γ e₀).domain).El =
                      (denotValTyS (.const orc)
                        (ρ.update x (Δ.getD k ValValSem.default)) Γ Δ
                        (ValExpr.inferTypeCtx Γ
                          (ValExpr.openRec k (.var x σ) e₀)).domain).El := by
                    rw [← denotValTy_eq_denotValTyS,
                      ← denotValTy_eq_denotValTyS]
                    exact hEl
                  have htoElS : HEq
                      (ValValSem.toElDomainChecked
                        (denotValTyS (.const orc) ρ Γ Δ
                          (ValExpr.inferTypeCtx Γ e₀).domain) arg)
                      (ValValSem.toElDomainChecked
                        (denotValTyS (.const orc)
                          (ρ.update x (Δ.getD k ValValSem.default)) Γ Δ
                          (ValExpr.inferTypeCtx Γ
                            (ValExpr.openRec k (.var x σ) e₀)).domain) arg) := by
                    rw [← denotValTy_eq_denotValTyS,
                      ← denotValTy_eq_denotValTyS]
                    exact htoEl
                  exact valSound_appV_match_congr_domainChecked (.fn T f) arg arg hElS htoElS
  termination_by e _ _ _ => ValExpr.size e
  decreasing_by
    all_goals
      first
      | (simp only [ValExpr.size]; omega)
      | (simp only [ValExpr.size]
         have := ValExpr.size_le_sizeList hmem; omega)

/-- Constant-oracle opening bridge at an existing runtime stack slot. -/
theorem denotValB_sem_openRec_bridge (orc : FFSOracle) [FFSOracle.Laws orc]
    (ρ : ValEnvSem)
    (x : VName) (σ : ValTy) (e : ValExpr) (Γ : List ValTy)
    (Δ : List ValValSem) (k : Nat) (hfv : x ∉ ValExpr.fv e)
    (hΓk : Γ.getD k default = σ) (hkΔ : k < Δ.length) :
    denotValB_sem orc ρ Γ Δ e =
      denotValB_sem orc (ρ.update x (Δ.getD k ValValSem.default)) Γ Δ
        (ValExpr.openRec k (.var x σ) e) :=
  denotValB_semS_openRec_bridge orc ρ x σ e Γ Δ k hfv hΓk hkΔ

/-- The `vlam`-arm instance (`k = 0`, heads of `Γ`/`Δ`): `denot ρ (τ₀::Γ) (v::Δ)
    body = denot (ρ.update x v) (τ₀::Γ) (v::Δ) (openVar x τ₀ body)` for
    `x ∉ fv body`. The `Γ.getD 0 = τ₀` side condition is `rfl`. -/
theorem denotValB_sem_openVar_bridge (orc : FFSOracle) [FFSOracle.Laws orc]
    (ρ : ValEnvSem)
    (x : VName) (τ₀ : ValTy) (v : ValValSem) (Γ : List ValTy) (Δ : List ValValSem)
    (body : ValExpr) (hx : x ∉ ValExpr.fv body) :
    denotValB_sem orc ρ (τ₀ :: Γ) (v :: Δ) body
      = denotValB_sem orc (ρ.update x v) (τ₀ :: Γ) (v :: Δ)
          (ValExpr.openVar x τ₀ body) := by
  have := denotValB_sem_openRec_bridge orc ρ x τ₀ body (τ₀ :: Γ) (v :: Δ) 0 hx rfl (by simp)
  simpa [ValExpr.openVar] using this

/-! ### `inferSpaceCtx`/`inferTypeCtx` agree with the context-free versions on
    well-typed terms.

The context-aware inferers differ from `inferSpace`/`inferType` ONLY in the
`bvar` arm. A well-typed term has no spine `bvar` (there is NO `bvar` typing
rule), so the de Bruijn context is never consulted: `inferSpaceCtx Γ e =
inferSpace e` and `inferTypeCtx Γ e = inferType e` for any `ValHasType ε e τ`.
Proved DIRECTLY by induction on the typing derivation (the 3-motive recursor),
which avoids any local-closure / context-validity side condition — note a bare
`ValHasType ε e τ ⇒ ValExpr.lc e` is FALSE without context validity, because the
`.var` rule does not force its annotation to be locally closed.

This lets the soundness proof reuse the context-free agreement lemmas
(`inferSpace_eq_of_space`, `inferType_eq_of_typed`) on the terms it processes. -/

/-- `inferTypeCtx Γ e = inferType e` for any well-typed `e` (the `.bvar` arm —
    the only difference — has no typing rule). Induction on the derivation. -/
theorem inferTypeCtx_eq_inferType_of_typed (Γ : List ValTy) {ε : ValCtx}
    {e : ValExpr} {τ : ValTy} (h : ValHasType ε e τ) :
    ValExpr.inferTypeCtx Γ e = ValExpr.inferType e := by
  exact (ValExpr.inferTypeCtx_eq_of_typed (Gamma := Γ) h).trans
    (ValHasType.inferType_eq_of_typed h).symm

/-- `inferSpaceCtx Γ e = inferSpace e` for any well-typed `e`. -/
theorem inferSpaceCtx_eq_inferSpace_of_typed (Γ : List ValTy) {ε : ValCtx}
    {e : ValExpr} {s : ValSpace} (h : ValHasType ε e (.space s)) :
    ValExpr.inferSpaceCtx Γ e = ValExpr.inferSpace e := by
  exact (ValExpr.inferSpaceCtx_eq_of_typed (Gamma := Γ) h).trans
    (ValHasType.inferSpace_eq_of_space h).symm

theorem inferTypeCtx_of_lc (Γ : List ValTy) :
    ∀ {e : ValExpr}, ValExpr.lc e →
      ValExpr.inferTypeCtx Γ e = ValExpr.inferType e
  | .zero _, _ => rfl
  | .rlit _, _ => rfl
  | .delta _ _, _ => rfl
  | .idelta _, _ => rfl
  | .var _ _, _ => rfl
  | .vlam _ _ _, _ => rfl
  | .appV f a, h => by
      cases h with | appV hf ha =>
        simp only [ValExpr.inferTypeCtx, ValExpr.inferType, inferTypeCtx_of_lc Γ hf]
  | .reshap _ _ _, _ => rfl
  | .bvar _, h => by cases h
  | .scale e₀ e₁, h => by
      cases h with | scale _ h₁ =>
        change ValExpr.inferTypeCtx Γ e₁ = ValExpr.inferType e₁
        exact inferTypeCtx_of_lc Γ h₁
  | .vadd _ _ _, _ => rfl
  | .dsumE e₀ e₁, h => by
      cases h with | dsumE h₀ h₁ =>
        change ValTy.space (.dsum (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e₀))
            (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e₁))) =
          ValTy.space (.dsum (ValTy.spaceOf (ValExpr.inferType e₀))
            (ValTy.spaceOf (ValExpr.inferType e₁)))
        rw [inferTypeCtx_of_lc Γ h₀, inferTypeCtx_of_lc Γ h₁]
  | .tprodE e₀ e₁, h => by
      cases h with | tprodE h₀ h₁ =>
        change ValTy.space (.tprod (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e₀))
            (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e₁))) =
          ValTy.space (.tprod (ValTy.spaceOf (ValExpr.inferType e₀))
            (ValTy.spaceOf (ValExpr.inferType e₁)))
        rw [inferTypeCtx_of_lc Γ h₀, inferTypeCtx_of_lc Γ h₁]
  | .ttv _ e₀ _, h => by
      cases h with | ttv _ h₀ _ =>
        change (match ValExpr.inferTypeCtx Γ e₀ with
          | .space (.tprod _ s_out) => ValTy.space s_out
          | _ => ValTy.space .real) =
          (match ValExpr.inferType e₀ with
          | .space (.tprod _ s_out) => ValTy.space s_out
          | _ => ValTy.space .real)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .mtm _ _ _ _ e₀ e₁, h => by
      cases h with | mtm _ _ h₀ h₁ =>
        change (match ValExpr.inferTypeCtx Γ e₀, ValExpr.inferTypeCtx Γ e₁ with
          | .space (.tprod _ s₀), .space (.tprod s₂ _) => ValTy.space (.tprod s₂ s₀)
          | _, _ => ValTy.space .empty) =
          (match ValExpr.inferType e₀, ValExpr.inferType e₁ with
          | .space (.tprod _ s₀), .space (.tprod s₂ _) => ValTy.space (.tprod s₂ s₀)
          | _, _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀, inferTypeCtx_of_lc Γ h₁]
  | .vkrn e₀ e₁, h => by
      cases h with | vkrn h₀ h₁ =>
        change (match ValExpr.inferTypeCtx Γ e₀, ValExpr.inferTypeCtx Γ e₁ with
          | .space (.tprod s₀ s₂), .space (.tprod s₁ s₃) =>
              ValTy.space (.tprod (.tprod s₀ s₁) (.tprod s₂ s₃))
          | _, _ => ValTy.space .empty) =
          (match ValExpr.inferType e₀, ValExpr.inferType e₁ with
          | .space (.tprod s₀ s₂), .space (.tprod s₁ s₃) =>
              ValTy.space (.tprod (.tprod s₀ s₁) (.tprod s₂ s₃))
          | _, _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀, inferTypeCtx_of_lc Γ h₁]
  | .vblk e₀ e₁, h => by
      cases h with | vblk h₀ h₁ =>
        change (match ValExpr.inferTypeCtx Γ e₀, ValExpr.inferTypeCtx Γ e₁ with
          | .space (.tprod s₀ s₂), .space (.tprod s₁ s₃) =>
              ValTy.space (.tprod (.dsum s₀ s₁) (.dsum s₂ s₃))
          | _, _ => ValTy.space .empty) =
          (match ValExpr.inferType e₀, ValExpr.inferType e₁ with
          | .space (.tprod s₀ s₂), .space (.tprod s₁ s₃) =>
              ValTy.space (.tprod (.dsum s₀ s₁) (.dsum s₂ s₃))
          | _, _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀, inferTypeCtx_of_lc Γ h₁]
  | .vtrans e, h => by
      cases h with | vtrans h₀ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ s₀)
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ s₀)
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .pinv e, h => by
      cases h with | pinv h₀ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ s₀)
          | .space s => ValTy.space (.tprod .real s)
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ s₀)
          | .space s => ValTy.space (.tprod .real s)
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .gpinv e _ _, h => by
      cases h with | gpinv h₀ _ _ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ s₀)
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ s₀)
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .gsvdS e _ _, h => by
      cases h with | gsvdS h₀ _ _ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod
              (.ffs .cokernel (.tprod s₀ s₁) e) (.ffs .image (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod
              (.ffs .cokernel (.tprod s₀ s₁) e) (.ffs .image (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .gsvdU e _ _, h => by
      cases h with | gsvdU h₀ _ _ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₀ (.ffs .cokernel (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₀ (.ffs .cokernel (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .gsvdUI e _ _, h => by
      cases h with | gsvdUI h₀ _ _ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₀ (.ffs .kernel (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₀ (.ffs .kernel (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .gsvdV e _ _, h => by
      cases h with | gsvdV h₀ _ _ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ (.ffs .image (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ (.ffs .image (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .gsvdVI e _ _, h => by
      cases h with | gsvdVI h₀ _ _ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ (.ffs .coimage (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ (.ffs .coimage (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .rrefRep _ e₁, h => by
      cases h with | rrefRep _ h₁ =>
        change (match ValExpr.inferTypeCtx Γ e₁ with
          | .space (.tprod p₀ p₁) => ValTy.space (.tprod p₁ p₀)
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e₁ with
          | .space (.tprod p₀ p₁) => ValTy.space (.tprod p₁ p₀)
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₁]
  | .inv e, h => by
      cases h with | inv h₀ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ s₀)
          | .space s => ValTy.space (.tprod .real s)
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod s₁ s₀)
          | .space s => ValTy.space (.tprod .real s)
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .svds e, h => by
      cases h with | svds h₀ =>
        change (match ValExpr.inferTypeCtx Γ e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod
              (.ffs .cokernel (.tprod s₀ s₁) e) (.ffs .image (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty) =
          (match ValExpr.inferType e with
          | .space (.tprod s₀ s₁) => ValTy.space (.tprod
              (.ffs .cokernel (.tprod s₀ s₁) e) (.ffs .image (.tprod s₀ s₁) e))
          | _ => ValTy.space .empty)
        rw [inferTypeCtx_of_lc Γ h₀]
  | .vsum _ es, h => by
      cases h with | vsum _ hes =>
        cases es with
        | nil => rfl
        | cons e es =>
            change ValExpr.inferTypeCtx Γ e = ValExpr.inferType e
            exact inferTypeCtx_of_lc Γ (hes e (by simp))

theorem inferSpaceCtx_of_lc (Γ : List ValTy) :
    ∀ {e : ValExpr}, ValExpr.lc e →
      ValExpr.inferSpaceCtx Γ e = ValExpr.inferSpace e
  | .zero _, _ => rfl
  | .rlit _, _ => rfl
  | .delta _ _, _ => rfl
  | .idelta _, _ => rfl
  | .var _ _, _ => rfl
  | .vlam _ _ _, _ => rfl
  | .appV f a, h => by
      simpa only [ValExpr.inferSpaceCtx, ValExpr.inferSpace] using
        congrArg GLang.ValTy.spaceOf (inferTypeCtx_of_lc Γ h)
  | .reshap _ _ _, _ => rfl
  | .bvar _, h => by cases h
  | .scale _ _, h => by
      cases h with | scale _ h₁ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₁]
  | .vadd _ _ _, _ => rfl
  | .dsumE _ _, h => by
      cases h with | dsumE h₀ h₁ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace,
          inferSpaceCtx_of_lc Γ h₀, inferSpaceCtx_of_lc Γ h₁]
  | .tprodE _ _, h => by
      cases h with | tprodE h₀ h₁ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace,
          inferSpaceCtx_of_lc Γ h₀, inferSpaceCtx_of_lc Γ h₁]
  | .ttv _ _ _, h => by
      cases h with | ttv _ h₀ _ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .mtm _ _ _ _ _ _, h => by
      cases h with | mtm _ _ h₀ h₁ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace,
          inferSpaceCtx_of_lc Γ h₀, inferSpaceCtx_of_lc Γ h₁]
  | .vkrn _ _, h => by
      cases h with | vkrn h₀ h₁ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace,
          inferSpaceCtx_of_lc Γ h₀, inferSpaceCtx_of_lc Γ h₁]
  | .vblk _ _, h => by
      cases h with | vblk h₀ h₁ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace,
          inferSpaceCtx_of_lc Γ h₀, inferSpaceCtx_of_lc Γ h₁]
  | .vtrans _, h => by
      cases h with | vtrans h₀ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .pinv _, h => by
      cases h with | pinv h₀ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .gpinv _ _ _, h => by
      cases h with | gpinv h₀ _ _ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .gsvdS _ _ _, h => by
      cases h with | gsvdS h₀ _ _ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .gsvdU _ _ _, h => by
      cases h with | gsvdU h₀ _ _ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .gsvdUI _ _ _, h => by
      cases h with | gsvdUI h₀ _ _ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .gsvdV _ _ _, h => by
      cases h with | gsvdV h₀ _ _ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .gsvdVI _ _ _, h => by
      cases h with | gsvdVI h₀ _ _ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .rrefRep _ _, h => by
      cases h with | rrefRep _ h₁ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₁]
  | .inv _, h => by
      cases h with | inv h₀ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .svds _, h => by
      cases h with | svds h₀ =>
        simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace, inferSpaceCtx_of_lc Γ h₀]
  | .vsum _ es, h => by
      cases h with | vsum _ hes =>
        cases es with
        | nil => rfl
        | cons e es =>
            simp only [ValExpr.inferSpaceCtx, ValExpr.inferSpace,
              inferSpaceCtx_of_lc Γ (hes e (by simp))]

/-- `inferSpaceCtx Γ e = s` for `e : .space s` (any context `Γ`). -/
theorem ValHasType.inferSpaceCtx_eq_of_space {ε : ValCtx} {Γ : List ValTy}
    {e : ValExpr} {s : ValSpace} (h : ValHasType ε e (.space s)) :
    ValExpr.inferSpaceCtx Γ e = s :=
  (inferSpaceCtx_eq_inferSpace_of_typed Γ h).trans
    (ValHasType.inferSpace_eq_of_space h)

/-- `dof (inferSpaceCtx Γ e) = dof s` for `e : .space s`. -/
theorem ValHasType.inferSpaceCtx_dof_eq_of_space {orc : FFSOracle} {ε : ValCtx}
    {Γ : List ValTy} {e : ValExpr} {s : ValSpace}
    (h : ValHasType ε e (.space s)) :
    ValSpace.dof orc (ValExpr.inferSpaceCtx Γ e) = ValSpace.dof orc s := by
  rw [ValHasType.inferSpaceCtx_eq_of_space h]

/-- `inferTypeCtx Γ e = τ` for `e : τ` (any context `Γ`). -/
theorem ValHasType.inferTypeCtx_eq_of_typed {ε : ValCtx} {Γ : List ValTy}
    {e : ValExpr} {τ : ValTy} (h : ValHasType ε e τ) :
    ValExpr.inferTypeCtx Γ e = τ :=
  (inferTypeCtx_eq_inferType_of_typed Γ h).trans
    (ValHasType.inferType_eq_of_typed h)

/-! ### Trivial introduction lemmas. -/

/-- Introduce `.space`-soundness from an array zero outside the shape. -/
theorem ValSoundOfDenotSem.space_array {orc : FFSOracle} {ρ : ValEnvSem}
    {Δ : List ValValSem} {s : ValSpace} {f : FlatArray}
    (hz : ∀ i : ValIdx, ¬ ValSpace.shapeInBounds orc s i → f.get i = 0) :
    ValSoundOfDenotSem orc ρ Δ (.space s) (.array f) := hz

/-- An array whose finite storage has exactly the semantic dimension is sound:
its zero-extended lookup vanishes outside the target shape. -/
theorem ValSoundOfDenotSem.space_array_length {orc : FFSOracle} {ρ : ValEnvSem}
    {Δ : List ValValSem} {s : ValSpace} {a : FlatArray}
    (hlen : a.length = ValSpace.dof orc s) :
    ValSoundOfDenotSem orc ρ Δ (.space s) (.array a) := by
  refine ValSoundOfDenotSem.space_array ?_
  intro i hi
  have hge : a.length ≤ i := by
    rw [hlen]
    exact Nat.le_of_not_lt fun hlt =>
      hi (ValSpace.shapeInBounds_of_lt_dof orc s i hlt)
  simp [FlatArray.get, Nat.not_lt.mpr hge]

/-- Exact finite storage at `dof s` implies the public zero-extension
invariant without inspecting the stored coordinate formula. -/
theorem ValSoundOfDenotSem.space_arrayOf {orc : FFSOracle} {ρ : ValEnvSem}
    {Δ : List ValValSem} {s : ValSpace} {n : Nat} {f : Nat → ℝ}
    (hlen : n = ValSpace.dof orc s) :
    ValSoundOfDenotSem orc ρ Δ (.space s) (ValValSem.arrayOf n f) := by
  refine ValSoundOfDenotSem.space_array ?_
  intro i hi
  apply FlatArray.get_ofFn_ge
  rw [hlen]
  exact Nat.le_of_not_lt fun hlt =>
      hi (ValSpace.shapeInBounds_of_lt_dof orc s i hlt)

namespace ValResultSoundOfDenotSem

/-- Partial correctness is closed under elimination of an array result. -/
theorem bindArray {orc : FFSOracle} {ρ : ValEnvSem} {Δ : List ValValSem}
    {τ : ValTy} (r : Except DimError ValValSem)
    (k : FlatArray → Except DimError ValValSem)
    (hk : ∀ a, ValResultSoundOfDenotSem orc ρ Δ τ (k a)) :
    ValResultSoundOfDenotSem orc ρ Δ τ (ValValSem.bindArray r k) := by
  intro out hout
  cases hr : r with
  | error err => simp [ValValSem.bindArray, hr] at hout
  | ok v =>
      cases v with
      | fn T f => simp [ValValSem.bindArray, hr] at hout
      | array a =>
          exact hk a out (by simpa [ValValSem.bindArray, hr] using hout)

/-- Binary array elimination preserves partial correctness. -/
theorem bindArrays {orc : FFSOracle} {ρ : ValEnvSem} {Δ : List ValValSem}
    {τ : ValTy} (r₀ r₁ : Except DimError ValValSem)
    (k : FlatArray → FlatArray → Except DimError ValValSem)
    (hk : ∀ a₀ a₁, ValResultSoundOfDenotSem orc ρ Δ τ (k a₀ a₁)) :
    ValResultSoundOfDenotSem orc ρ Δ τ (ValValSem.bindArrays r₀ r₁ k) := by
  unfold ValValSem.bindArrays
  apply bindArray
  intro a₀
  apply bindArray
  exact hk a₀

/-- Ternary array elimination preserves partial correctness. -/
theorem bindArrays3 {orc : FFSOracle} {ρ : ValEnvSem} {Δ : List ValValSem}
    {τ : ValTy} (r₀ r₁ r₂ : Except DimError ValValSem)
    (k : FlatArray → FlatArray → FlatArray → Except DimError ValValSem)
    (hk : ∀ a₀ a₁ a₂,
      ValResultSoundOfDenotSem orc ρ Δ τ (k a₀ a₁ a₂)) :
    ValResultSoundOfDenotSem orc ρ Δ τ
      (ValValSem.bindArrays3 r₀ r₁ r₂ k) := by
  unfold ValValSem.bindArrays3
  apply bindArray
  intro a₀
  apply bindArray
  intro a₁
  apply bindArray
  exact hk a₀ a₁

end ValResultSoundOfDenotSem

/-- Introduce `.piTy`-soundness from the carrier-match witness `rfl`
    (the well-typed construction site has `T = (denotValTy …).El`
    definitionally) plus the pointwise codomain-soundness family. LN (D1):
    the body family is sound at the codomain under the LOCAL env `Δ` extended
    by the domain value (push onto `Δ`). -/
theorem ValSoundOfDenotSem.piTy_fn {orc : FFSOracle} {ρ : ValEnvSem}
    {Δ : List ValValSem} {τ₀ τ₁ : ValTy}
    {fam : (denotValTy orc ρ Δ τ₀).El → Except DimError ValValSem}
    (hbody : ∀ (v : (denotValTy orc ρ Δ τ₀).El) (out : ValValSem),
      fam v = .ok out →
      ValSoundOfDenotSem orc ρ
        (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v :: Δ) τ₁ out) :
    ValSoundOfDenotSem orc ρ Δ (.piTy τ₀ τ₁)
      (.fn (denotValTy orc ρ Δ τ₀).El fam) :=
  ⟨rfl, hbody⟩

/-- The carrier `(denotValTy orc ρ Δ τ).El` does not depend on `ρ` or `Δ`. -/
theorem denotValTy_El_env_irrel (orc : FFSOracle) (τ : ValTy)
    (ρ₁ ρ₂ : ValEnvSem) (Δ₁ Δ₂ : List ValValSem) :
    (denotValTy orc ρ₁ Δ₁ τ).El = (denotValTy orc ρ₂ Δ₂ τ).El := by
  rw [denotValTy_El_eq_carrierEl orc ρ₁ Δ₁ τ, denotValTy_El_eq_carrierEl orc ρ₂ Δ₂ τ]

theorem ValSoundOfDenotSem.eps_irrelevant (orc : FFSOracle) (ρ : ValEnvSem) :
    ∀ (τ : ValTy) (v : ValValSem) (Δ Δ' : List ValValSem),
      ValSoundOfDenotSem orc ρ Δ τ v ↔ ValSoundOfDenotSem orc ρ Δ' τ v
  | .space _s, .array _f, _Δ, _Δ' => Iff.rfl
  | .space _s, .fn _ _, _Δ, _Δ' => Iff.rfl
  | .piTy _ _, .array _, _Δ, _Δ' => Iff.rfl
  | .piTy τ₀ τ₁, .fn T fam, Δ, Δ' => by
      have hcarr : (denotValTy orc ρ Δ τ₀).El = (denotValTy orc ρ Δ' τ₀).El := by
        rw [denotValTy_El_eq_carrierEl orc ρ Δ τ₀, denotValTy_El_eq_carrierEl orc ρ Δ' τ₀]
      unfold ValSoundOfDenotSem
      constructor
      · rintro ⟨h, hbody⟩
        refine ⟨h.trans hcarr, ?_⟩
        intro v out hout
        exact (eps_irrelevant orc ρ τ₁ out _ _).mp (hbody v out hout)
      · rintro ⟨h, hbody⟩
        refine ⟨h.trans hcarr.symm, ?_⟩
        intro v out hout
        exact (eps_irrelevant orc ρ τ₁ out _ _).mp (hbody v out hout)
  termination_by τ _ _ _ => ValTy.kindSize τ
  decreasing_by
    all_goals simp_wf
    all_goals (simp [ValTy.kindSize_piTy]; omega)

theorem ValSoundOfDenotSem.env_irrel (orc : FFSOracle) :
    ∀ (τ : ValTy) (v : ValValSem) (ρ ρ' : ValEnvSem) (Δ Δ' : List ValValSem),
      ValSoundOfDenotSem orc ρ Δ τ v ↔ ValSoundOfDenotSem orc ρ' Δ' τ v
  | .space _s, .array _f, _ρ, _ρ', _Δ, _Δ' => Iff.rfl
  | .space _s, .fn _ _, _ρ, _ρ', _Δ, _Δ' => Iff.rfl
  | .piTy _ _, .array _, _ρ, _ρ', _Δ, _Δ' => Iff.rfl
  | .piTy τ₂ τ₃, .fn _T fam, ρ, ρ', Δ, Δ' => by
      have hcarr : (denotValTy orc ρ Δ τ₂).El = (denotValTy orc ρ' Δ' τ₂).El :=
        denotValTy_El_env_irrel orc τ₂ ρ ρ' Δ Δ'
      constructor
      · rintro ⟨h, hbody⟩
        refine ⟨h.trans hcarr, ?_⟩
        intro v out hout
        exact (ValSoundOfDenotSem.env_irrel orc τ₃ out _ _ _ _).mp
          (hbody v out hout)
      · rintro ⟨h, hbody⟩
        refine ⟨h.trans hcarr.symm, ?_⟩
        intro v out hout
        exact (ValSoundOfDenotSem.env_irrel orc τ₃ out _ _ _ _).mp
          (hbody v out hout)
  termination_by τ _ _ _ _ _ => ValTy.kindSize τ
  decreasing_by
    all_goals simp_wf
    all_goals (simp [ValTy.kindSize_piTy]; omega)

/-! ### Soundness of lifted carrier elements (`fromEl`).

At a `.space` leaf the carrier is a finite `FlatArray`, and `fromEl` resizes it
to the semantic dimension. Therefore **every** carrier element lifts to a
sound value: indices beyond the resized length read as zero. The `.piTy` step
is the predicate's own clause, with the body family lifted recursively. This
is the lemma used by `update_full_carrier` for every element of the finite
carrier represented by `T.El`. -/
theorem ValSoundOfDenotSem.fromEl_sound (orc : FFSOracle) :
    ∀ (τ : ValTy) (ρ : ValEnvSem) (Δ : List ValValSem)
      (v : (denotValTy orc ρ Δ τ).El),
      ValSoundOfDenotSem orc ρ Δ τ
        (ValValSem.fromEl (denotValTy orc ρ Δ τ) v)
  | .space s, ρ, Δ, v => by
      show ValSoundOfDenotSem orc ρ Δ (.space s)
        (.array (v.resize (ValSpace.dof orc s)))
      refine ValSoundOfDenotSem.space_array ?_
      intro i hi
      have hge : ValSpace.dof orc s ≤ i := Nat.le_of_not_lt fun hlt =>
        hi (ValSpace.shapeInBounds_of_lt_dof orc s i hlt)
      simp [FlatArray.resize, hge]
  | .piTy τ₀ τ₁, ρ, Δ, v => by
      -- `denotValTy ρ Δ (.piTy ..) = .piTy (denotValTy ρ Δ τ₀).El (fun w => ..)`,
      -- and `fromEl (.piTy T fam) v = .fn T (fun w => fromEl (fam w) (v w))`.
      -- This is the predicate's `.piTy` clause with the carrier-match `rfl`;
      -- the body family is sound by the IH on `τ₁` at the extended local env.
      refine ⟨rfl, ?_⟩
      intro w out hout
      -- The body value is `fromEl (denotValTy ρ (fromEl … w :: Δ) τ₁) (v w)`
      -- on successful callbacks; failures remain failures and make the partial-
      -- correctness premise impossible.
      cases hvw : v w with
      | error err =>
          simp only [hvw, Except.map] at hout
          cases hout
      | ok z =>
          simp only [hvw, Except.map] at hout
          injection hout with hout
          subst out
          exact ValSoundOfDenotSem.fromEl_sound orc τ₁ ρ
            (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) w :: Δ) z
  termination_by τ _ _ _ => ValTy.kindSize τ
  decreasing_by
    all_goals simp_wf
    all_goals (simp [ValTy.kindSize_piTy]; omega)

def ValEnvSoundSem (orc : FFSOracle) (ε : ValCtx) (ρ_sem : ValEnvSem) : Prop :=
  ∀ x τ, ε.lookup x = some τ →
      ValSoundOfDenotSem orc ρ_sem [] τ (ρ_sem x)

theorem ValEnvSoundSem.native {orc : FFSOracle} {ε : ValCtx}
    {ρ_sem : ValEnvSem} (h : ValEnvSoundSem orc ε ρ_sem)
    {x : VName} {τ : ValTy} (hlookup : ε.lookup x = some τ) :
    ValSoundOfDenotSem orc ρ_sem [] τ (ρ_sem x) :=
  h x τ hlookup

/-- **Environment extension over the full finite carrier.**

    A `ValEnvSoundSem`-sound env `ρ`, extended at the binder `x` by
    `fromEl (denotValTy orc ρ τ₀) v` for *any* carrier element
    `v : (denotValTy orc ρ τ₀).El`, is `ValEnvSoundSem`-sound under
    `Finmap.insert x τ₀ ε`. -/
theorem ValEnvSoundSem.update_full_carrier (orc : FFSOracle) (ε : ValCtx)
    (ρ : ValEnvSem) (x : VName) (τ₀ : ValTy) (Δ : List ValValSem)
    (henv : ValEnvSoundSem orc ε ρ)
    (v : (denotValTy orc ρ Δ τ₀).El) :
    ValEnvSoundSem orc (Finmap.insert x τ₀ ε)
      (ρ.update x (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v)) := by
  intro y τ hy
  by_cases hxy : y = x
  · -- y = x: the new binding `fromEl (denotValTy ρ Δ τ₀) v` at type `τ₀`.
    subst hxy
    rw [Finmap.lookup_insert] at hy
    obtain rfl : τ₀ = τ := (Option.some.inj hy)
    rw [ValEnvSem.update_same]
    -- Sound by `fromEl_sound`, transported to the extended env / empty local env.
    exact (ValSoundOfDenotSem.env_irrel orc τ₀ _ _ _ _ _).mp
      (ValSoundOfDenotSem.fromEl_sound orc τ₀ ρ Δ v)
  · -- y ≠ x: pre-existing binding `ρ y`, sound by `henv.native`.
    rw [Finmap.lookup_insert_of_ne _ hxy] at hy
    rw [ValEnvSem.update_other _ _ _ _ hxy]
    exact (ValSoundOfDenotSem.env_irrel orc τ _ _ _ _ _).mp
      (henv.native hy)

namespace ValSoundOfDenotSem

theorem asArray_OOB_zero {orc : FFSOracle} {ρ : ValEnvSem} {Δ : List ValValSem}
    {s : ValSpace} {v : ValValSem}
    (h : ValSoundOfDenotSem orc ρ Δ (.space s) v) :
    ∀ i, ¬ ValSpace.shapeInBounds orc s i → v.asArray i = 0 := by
  intro i hi
  cases v with
  | array f =>
      -- `ValSoundOfDenotSem … (.space s) (.array f)` unfolds to the
      -- OOB-zero clause; apply it.
      exact h i hi
  | fn _ _ =>
      -- `ValSoundOfDenotSem … (.space s) (.fn …)` is `False`.
      exact h.elim

theorem openRec_respect_iff (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc] :
    ∀ (τ₁ : ValTy) (v : ValValSem) (ρ ρ' : ValEnvSem) (Δ Δ' : List ValValSem)
      (k : Nat) (u : ValExpr),
      ValSoundOfDenotSem orc ρ' Δ' (ValTy.openRec k u τ₁) v ↔
      ValSoundOfDenotSem orc ρ Δ τ₁ v
  | .space s, .array f, _ρ, _ρ', _Δ, _Δ', k, u => by
      show (∀ i, ¬ ValSpace.shapeInBounds orc (ValSpace.openRec k u s) i → f i = 0)
            ↔ (∀ i, ¬ ValSpace.shapeInBounds orc s i → f i = 0)
      constructor
      · intro h i hi
        exact h i (by rw [ValSpace.shapeInBounds_openRec orc]; exact hi)
      · intro h i hi
        exact h i (by
          rw [← ValSpace.shapeInBounds_openRec orc (k := k) (u := u)]
          exact hi)
  | .space _s, .fn _ _, _ρ, _ρ', _Δ, _Δ', _k, _u => Iff.rfl
  | .piTy _τ₂ _τ₃, .array _, _ρ, _ρ', _Δ, _Δ', _k, _u => by
      -- `ValTy.openRec k u (.piTy …)` is again a `.piTy`; both sides `False`.
      unfold ValTy.openRec; exact Iff.rfl
  | .piTy τ₂ τ₃, .fn _T fam, ρ, ρ', Δ, Δ', k, u => by
      -- Carrier equality shared by both witness types (env/Δ/open-invariant).
      have hcarr : (denotValTy orc ρ' Δ' (ValTy.openRec k u τ₂)).El
            = (denotValTy orc ρ Δ τ₂).El := by
        rw [denotValTy_El_eq_carrierEl orc ρ' Δ' (ValTy.openRec k u τ₂),
            denotValTy_El_eq_carrierEl orc ρ Δ τ₂, ValTy.carrierEl_openRec]
      unfold ValTy.openRec
      constructor
      · rintro ⟨h', hbody⟩
        refine ⟨h'.trans hcarr, ?_⟩
        intro v out hout
        exact (openRec_respect_iff orc τ₃ out _ _ _ _ (k+1) u).mp
          (hbody v out hout)
      · rintro ⟨h, hbody⟩
        refine ⟨h.trans hcarr.symm, ?_⟩
        intro v out hout
        exact (openRec_respect_iff orc τ₃ out _ _ _ _ (k+1) u).mpr
          (hbody v out hout)
  termination_by τ₁ _ _ _ _ _ _ _ => ValTy.kindSize τ₁
  decreasing_by
    all_goals simp_wf
    all_goals (simp [ValTy.kindSize_piTy]; omega)

/-! Capture-avoiding substitution satisfies the same semantic relation. -/
theorem substBound_respect_iff (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc] :
    ∀ (τ₁ : ValTy) (v : ValValSem) (ρ ρ' : ValEnvSem) (Δ Δ' : List ValValSem)
      (k : Nat) (u : ValExpr),
      ValSoundOfDenotSem orc ρ' Δ' (ValTy.substBound k u τ₁) v ↔
      ValSoundOfDenotSem orc ρ Δ τ₁ v
  | .space s, .array f, _ρ, _ρ', _Δ, _Δ', k, u => by
      show (∀ i, ¬ ValSpace.shapeInBounds orc (ValSpace.substBound k u s) i → f i = 0)
            ↔ (∀ i, ¬ ValSpace.shapeInBounds orc s i → f i = 0)
      constructor
      · intro h i hi
        exact h i (by rw [ValSpace.shapeInBounds_substBound orc]; exact hi)
      · intro h i hi
        exact h i (by
          rw [← ValSpace.shapeInBounds_substBound orc (k := k) (u := u)]
          exact hi)
  | .space _s, .fn _ _, _ρ, _ρ', _Δ, _Δ', _k, _u => Iff.rfl
  | .piTy _τ₂ _τ₃, .array _, _ρ, _ρ', _Δ, _Δ', _k, _u => by
      -- `ValTy.substBound k u (.piTy …)` is again a `.piTy`; both sides `False`.
      unfold ValTy.substBound; exact Iff.rfl
  | .piTy τ₂ τ₃, .fn _T fam, ρ, ρ', Δ, Δ', k, u => by
      -- Carrier equality shared by both witness types (env/Δ/open-invariant).
      have hcarr : (denotValTy orc ρ' Δ' (ValTy.substBound k u τ₂)).El
            = (denotValTy orc ρ Δ τ₂).El := by
        rw [denotValTy_El_eq_carrierEl orc ρ' Δ' (ValTy.substBound k u τ₂),
            denotValTy_El_eq_carrierEl orc ρ Δ τ₂, (ValSoundOfDenot.ValTy.SameShape_substBound k u τ₂).carrierEl_eq]
      unfold ValTy.substBound
      constructor
      · rintro ⟨h', hbody⟩
        refine ⟨h'.trans hcarr, ?_⟩
        intro v out hout
        exact (substBound_respect_iff orc τ₃ out _ _ _ _ (k+1) u).mp
          (hbody v out hout)
      · rintro ⟨h, hbody⟩
        refine ⟨h.trans hcarr.symm, ?_⟩
        intro v out hout
        exact (substBound_respect_iff orc τ₃ out _ _ _ _ (k+1) u).mpr
          (hbody v out hout)
  termination_by τ₁ _ _ _ _ _ _ _ => ValTy.kindSize τ₁
  decreasing_by
    all_goals simp_wf
    all_goals (simp [ValTy.kindSize_piTy]; omega)

/-- The `instantiate` corollary (`k = 0`): the predicate is invariant under
    `ValTy.instantiate u τ₁ = ValTy.openRec 0 u τ₁` (the appV codomain). -/
theorem instantiate_respect_iff (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (τ₁ : ValTy) (v : ValValSem) (ρ ρ' : ValEnvSem) (Δ Δ' : List ValValSem)
    (u : ValExpr) :
    ValSoundOfDenotSem orc ρ' Δ' (ValTy.instantiate u τ₁) v ↔
    ValSoundOfDenotSem orc ρ Δ τ₁ v :=
  openRec_respect_iff orc τ₁ v ρ ρ' Δ Δ' 0 u

/-! `csize` is invariant under opening a bound index to a free `.var` (whose own
    `csize` is `1`, matching the `bvar` it replaces). The opening-invariant
    measure fact for the value-soundness `.vlam` recursion. -/
mutual
theorem ValExpr.csize_openRec (x : VName) (σ : ValTy) :
    ∀ (k : Nat) (e : ValExpr), (ValExpr.openRec k (.var x σ) e).csize = e.csize
  | k, .bvar j => by by_cases h : j = k <;> simp [ValExpr.openRec, h, ValExpr.csize]
  | _, .var _ _ => rfl
  | _, .rlit _ => rfl
  | _, .zero _ => rfl
  | _, .delta _ _ => rfl
  | _, .idelta _ => rfl
  | k, .scale e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .vadd _ e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .dsumE e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .tprodE e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .ttv _ e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .mtm _ _ _ _ e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .vkrn e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .vblk e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .appV e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .rrefRep e₀ e₁ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e₀,
        ValExpr.csize_openRec x σ k e₁]
  | k, .gsvdS e a b => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e,
        ValExpr.csize_openRec x σ k a, ValExpr.csize_openRec x σ k b]
  | k, .gsvdU e a b => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e,
        ValExpr.csize_openRec x σ k a, ValExpr.csize_openRec x σ k b]
  | k, .gsvdUI e a b => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e,
        ValExpr.csize_openRec x σ k a, ValExpr.csize_openRec x σ k b]
  | k, .gsvdV e a b => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e,
        ValExpr.csize_openRec x σ k a, ValExpr.csize_openRec x σ k b]
  | k, .gsvdVI e a b => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e,
        ValExpr.csize_openRec x σ k a, ValExpr.csize_openRec x σ k b]
  | k, .gpinv e a b => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e,
        ValExpr.csize_openRec x σ k a, ValExpr.csize_openRec x σ k b]
  | k, .pinv e => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e]
  | k, .inv e => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e]
  | k, .svds e => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e]
  | k, .vtrans e => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e]
  | k, .reshap e _ _ => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ k e]
  | k, .vlam _ _ body => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csize_openRec x σ (k+1) body]
  | k, .vsum _ es => by
      simp only [ValExpr.openRec, ValExpr.csize, ValExpr.csizeList_openRecList x σ k es]

theorem ValExpr.csizeList_openRecList (x : VName) (σ : ValTy) :
    ∀ (k : Nat) (es : List ValExpr),
      ValExpr.csizeList (ValExpr.openRecList k (.var x σ) es) = ValExpr.csizeList es
  | _, [] => rfl
  | k, e :: es => by
      simp only [ValExpr.openRecList, ValExpr.csizeList, ValExpr.csize_openRec x σ k e,
        ValExpr.csizeList_openRecList x σ k es]
end

/-- `csize` is invariant under `openVar` (the `k = 0` instance). -/
theorem ValExpr.csize_openVar (x : VName) (τ₀ : ValTy) (body : ValExpr) :
    (ValExpr.openVar x τ₀ body).csize = body.csize :=
  ValExpr.csize_openRec x τ₀ 0 body

/-! ## Result-indexed soundness for checked denotations

The evaluator may return `DimError`; the theorems below assert only that every
successful payload is sound.  Success itself is established later by adequacy. -/

/-- A checked reshape is partially sound at every same-shaped target.  The
base case accepts only arrays having exactly the target dimension.  The arrow
case promises soundness only for successful callback results, so failures in
argument reshaping, carrier application, or result reshaping remain observable. -/
theorem reshapDenotSem_sound (orc : FFSOracle) :
    ∀ (τ_tgt τ_src : ValTy) (v : ValValSem) (ρ : ValEnvSem)
      (Δ : List ValValSem),
      ValSoundOfDenot.ValTy.SameShape τ_tgt τ_src →
      ValResultSoundOfDenotSem orc ρ Δ τ_tgt
        (reshapDenotSem orc v τ_tgt τ_src)
  | .space s, .space ss, v, ρ, Δ, _hshape => by
      intro out hout
      cases v with
      | fn T f =>
          simp [reshapDenotSem, reshapDenotSemS] at hout
      | array a =>
          by_cases hlen : a.length = ValSpace.dof orc ss
          · by_cases hdim : ValSpace.dof orc ss = ValSpace.dof orc s
            · simp [reshapDenotSem, reshapDenotSemS, reshapArrayBetweenS,
                hlen, hdim] at hout
              subst out
              exact ValSoundOfDenotSem.space_array_length (hlen.trans hdim)
            · simp [reshapDenotSem, reshapDenotSemS, reshapArrayBetweenS,
                hlen, hdim] at hout
          · simp [reshapDenotSem, reshapDenotSemS, reshapArrayBetweenS,
              hlen] at hout
  | .space _, .piTy _ _, _v, _ρ, _Δ, hshape => hshape.elim
  | .piTy _ _, .space _, _v, _ρ, _Δ, hshape => hshape.elim
  | .piTy τ₂ τ₃, .piTy τ₄ τ₅, v, ρ, Δ, hshape => by
      rw [reshapDenotSem, reshapDenotSemS]
      have hT : denotValTyS (.const orc) ValEnvSem.empty [] [] τ₂ =
          denotValTy orc ρ Δ τ₂ :=
        (denotValTyS_const_env orc τ₂ ValEnvSem.empty ρ [] [] [] Δ).trans
          (denotValTy_eq_denotValTyS orc ρ τ₂ [] Δ).symm
      rw [hT]
      apply ValResultSoundOfDenotSem.ok
      refine ⟨rfl, ?_⟩
      intro a out hout
      generalize hcheck : ValValSem.fromElChecked
        (denotValTy orc ρ Δ τ₂) a = checkResult at hout
      cases checkResult with
      | error err =>
          simp only [hcheck] at hout
          cases hout
      | ok argT =>
          generalize harg : reshapDenotSemBetweenS (.const orc) ValEnvSem.empty
            [] [] [] [] argT τ₄ τ₂ = argResult at hout
          cases argResult with
          | error err =>
              simp only [hcheck, harg] at hout
              cases hout
          | ok argS =>
              generalize hdecode : ValValSem.toEl
                (denotValTyS (.const orc) ValEnvSem.empty [] [] τ₄) argS =
                  decodeResult at hout
              cases decodeResult with
              | error err =>
                  simp only [hcheck, harg, hdecode] at hout
                  cases hout
              | ok argEl =>
                  generalize happ : v.applyTyped argEl = appResult at hout
                  cases appResult with
                  | error err =>
                      simp only [hcheck, harg, hdecode, happ] at hout
                      cases hout
                  | ok res =>
                      simp only [hcheck, harg, hdecode, happ] at hout
                      have hout' : reshapDenotSem orc res τ₃ τ₅ = .ok out := by
                        calc
                          reshapDenotSem orc res τ₃ τ₅ =
                              reshapDenotSemBetweenS (.const orc) ValEnvSem.empty
                                [] [] [] [] res τ₃ τ₅ :=
                            reshapDenotSemS_eq_between (.const orc) ValEnvSem.empty
                              [] [] res τ₃ τ₅
                          _ = reshapDenotSemBetweenS (.const orc) ValEnvSem.empty
                                [τ₂] [argT] [τ₄] [argS] res τ₃ τ₅ :=
                            (reshapDenotSemBetweenS_const_env orc res τ₃ τ₅
                              ValEnvSem.empty ValEnvSem.empty
                              [τ₂] [] [τ₄] [] [argT] [] [argS] []).symm
                          _ = .ok out := hout
                      exact reshapDenotSem_sound orc τ₃ τ₅ res ρ
                        (ValValSem.fromEl (denotValTy orc ρ Δ τ₂) a :: Δ)
                        hshape.2 out hout'
  termination_by τ_tgt τ_src _ _ _ _ =>
    ValTy.kindSize τ_tgt + ValTy.kindSize τ_src
  decreasing_by
    all_goals (simp only [ValTy.kindSize_piTy]; omega)

/-- Expression-level checked reshape soundness.  A failed source evaluation is
preserved; a successful source value is handed to `reshapDenotSem_sound`. -/
theorem reshap_result_sound (orc : FFSOracle) (ε : ValCtx) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e : ValExpr)
    (τ_tgt τ_src : ValTy) (k : ValKind)
    (he : ValHasType ε e τ_src)
    (hsrc : ValTValid ε τ_src k) (htgt : ValTValid ε τ_tgt k) :
    ValResultSoundOfDenotSem orc ρ Δ τ_tgt
      (denotValB_sem orc ρ Γ Δ (.reshap e τ_tgt τ_src)) := by
  have hshape : ValSoundOfDenot.ValTy.SameShape τ_tgt τ_src :=
    ValSoundOfDenot.ValTy.SameShape_of_sameKind k htgt hsrc
  change ValResultSoundOfDenotSem orc ρ Δ τ_tgt
    (denotValB_semS (.const orc) ρ Γ Δ (.reshap e τ_tgt τ_src))
  rw [denotValB_semS]
  generalize heval : denotValB_semS (.const orc) ρ Γ Δ e = evalResult
  cases evalResult with
  | error err => exact ValResultSoundOfDenotSem.error err
  | ok v =>
      simp only
      rw [reshapDenotSemS_const_env orc ρ ValEnvSem.empty Γ [] Δ []
        v τ_tgt τ_src]
      exact reshapDenotSem_sound orc τ_tgt τ_src v ρ Δ hshape

/-- Application preserves partial soundness.  Only the function subexpression's
result soundness is needed: a successful application has already established
that the argument evaluated and decoded at the recovered domain, and the
function predicate promises soundness for every successful callback result. -/
theorem appV_result_sound (orc : FFSOracle) [FFSOracle.SubstOpenLaws orc]
    (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (e₀ e₁ : ValExpr) (τ₀ τ₁ τ_out : ValTy)
    { ε : ValCtx } (_h₀ : ValHasType ε e₀ (.piTy τ₀ τ₁))
    (hsub : τ_out = ValTy.applyCodomain e₁ τ₁)
    (hfun : ValResultSoundOfDenotSem orc ρ Δ (.piTy τ₀ τ₁)
      (denotValB_sem orc ρ Γ Δ e₀)) :
    ValResultSoundOfDenotSem orc ρ Δ τ_out
      (denotValB_sem orc ρ Γ Δ (.appV e₀ e₁)) := by
  intro out hout
  have houtS := hout
  change denotValB_semS (.const orc) ρ Γ Δ (.appV e₀ e₁) =
    .ok out at houtS
  rw [denotValB_semS] at houtS
  cases hv₀S : denotValB_semS (.const orc) ρ Γ Δ e₀ with
  | error err =>
      rw [hv₀S] at houtS
      cases houtS
  | ok funVal =>
      rw [hv₀S] at houtS
      cases funVal with
      | array a =>
          simp only at houtS
          cases houtS
      | fn T fam =>
          simp only at houtS
          cases hv₁S : denotValB_semS (.const orc) ρ Γ Δ e₁ with
          | error err =>
              rw [hv₁S] at houtS
              cases houtS
          | ok v₁ =>
              rw [hv₁S] at houtS
              simp only at houtS
              by_cases hcarrier : T =
                (denotValTyS (.const orc) ρ Γ Δ
                  (ValExpr.inferTypeCtx Γ e₀).domain).El
              · simp only [dif_pos hcarrier] at houtS
                cases hto : ValValSem.toElDomainChecked
                  (denotValTyS (.const orc) ρ Γ Δ
                    (ValExpr.inferTypeCtx Γ e₀).domain) v₁ with
                | error err =>
                    rw [hto] at houtS
                    cases houtS
                | ok arg =>
                    rw [hto] at houtS
                    have hv₀ : denotValB_sem orc ρ Γ Δ e₀ =
                        .ok (.fn T fam) := hv₀S
                    obtain ⟨hT, hfam⟩ := hfun (.fn T fam) hv₀
                    have hbody := hfam (hcarrier ▸ arg) out houtS
                    rw [hsub]
                    exact (substBound_respect_iff orc τ₁ out ρ ρ
                      (ValValSem.fromEl (denotValTy orc ρ Δ τ₀)
                        (hT ▸ (hcarrier ▸ arg)) :: Δ) Δ 0 e₁).mpr hbody
              · simp only [dif_neg hcarrier] at houtS
                cases houtS

/-- Checked vector addition is partially sound without a success premise:
either an operand/length check fails, or the successful zip has exactly the
declared result dimension. -/
theorem vadd_result_sound (orc : FFSOracle) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (s : ValSpace) (e₀ e₁ : ValExpr) :
    ValResultSoundOfDenotSem orc ρ Δ (.space s)
      (denotValB_sem orc ρ Γ Δ (.vadd s e₀ e₁)) := by
  rw [denotValB_sem, denotValB_semS]
  apply ValResultSoundOfDenotSem.bindArrays
  intro a₀ a₁
  dsimp only
  split
  · rename_i h₀
    split
    · rename_i h₁
      exact ValResultSoundOfDenotSem.ok
        (ValSoundOfDenotSem.space_array_length
          (a := FlatArray.zipWith (ValSpace.dof orc s)
            (fun x y => x + y) a₀ a₁ h₀ h₁) rfl)
    · exact ValResultSoundOfDenotSem.error .mismatch
  · exact ValResultSoundOfDenotSem.error .mismatch

/-- A successful finite sum is allocated at the inferred result dimension;
failure of any active summand remains an error. -/
theorem vsum_result_sound (orc : FFSOracle) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (s₀ s : ValSpace)
    (es : List ValExpr)
    (hlen : ValSpace.dof orc (ValExpr.inferSpaceCtx Γ (.vsum s₀ es)) =
      ValSpace.dof orc s) :
    ValResultSoundOfDenotSem orc ρ Δ (.space s)
      (denotValB_sem orc ρ Γ Δ (.vsum s₀ es)) := by
  rw [denotValB_sem, denotValB_semS]
  simp only [FFSOracleSem.const]
  split
  · generalize hs : ValValSem.sequenceArrays
      ((es.take (ValSpace.dof orc s₀)).attach.map
        (fun e => denotValB_semS (.const orc) ρ Γ Δ e.1)) = seq
    cases seq with
    | error err =>
        simp only
        exact ValResultSoundOfDenotSem.error err
    | ok arrays =>
        simp only
        split
        · exact ValResultSoundOfDenotSem.ok
            (ValSoundOfDenotSem.space_arrayOf hlen)
        · exact ValResultSoundOfDenotSem.error .mismatch

  · exact ValResultSoundOfDenotSem.error .mismatch

/-- Canonical FSV checks its actual matrix shape against the annotated output. -/
theorem canonicalFSV_result_sound (orc : FFSOracle) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (which : ValFFSProp)
    (e a b : ValExpr) (s : ValSpace)
    (hlen : ValSpace.dof orc (ValExpr.inferSpaceCtx Γ (.canonicalFSV which e a b)) =
      ValSpace.dof orc s) :
    ValResultSoundOfDenotSem orc ρ Δ (.space s)
      (denotValB_sem orc ρ Γ Δ (.canonicalFSV which e a b)) := by
  rw [GLang.denotValB_sem.eq_def, denotValB_semS_canonicalFSV]
  apply ValResultSoundOfDenotSem.bindArrays3
  intro ae aa ab
  cases hinfer : ValExpr.inferSpaceCtx Γ e <;> simp only <;>
    try exact ValResultSoundOfDenotSem.error .mismatch
  rename_i s0 s1
  dsimp only [FFSOracleSem.const]
  split
  · exact ValResultSoundOfDenotSem.error _
  · split
    · rename_i hdim
      exact ValResultSoundOfDenotSem.ok
        (ValSoundOfDenotSem.space_array_length (hdim.trans hlen))
    · exact ValResultSoundOfDenotSem.error .mismatch

theorem svdS_result_sound (orc : FFSOracle) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (e a b : ValExpr) (s : ValSpace)
    (hlen : ValSpace.dof orc (ValExpr.inferSpaceCtx Γ (.gsvdS e a b)) =
      ValSpace.dof orc s) :
    ValResultSoundOfDenotSem orc ρ Δ (.space s)
      (denotValB_sem orc ρ Γ Δ (.gsvdS e a b)) := by
  rw [GLang.denotValB_sem.eq_def, denotValB_semS.eq_19]
  apply ValResultSoundOfDenotSem.bindArrays3
  intro ae aa ab
  cases hinfer : ValExpr.inferSpaceCtx Γ e <;> simp only <;>
    try exact ValResultSoundOfDenotSem.error .mismatch
  rename_i s0 s1
  dsimp only [FFSOracleSem.const]
  split
  · exact ValResultSoundOfDenotSem.error _
  · split
    · rename_i hdim
      exact ValResultSoundOfDenotSem.ok
        (ValSoundOfDenotSem.space_array_length (hdim.trans hlen))
    · exact ValResultSoundOfDenotSem.error .mismatch

/-- Every space-typed expression is partially sound.  Except for variables,
reshape, and application, this follows solely from the exact finite length of
the evaluator's successful array allocation. -/
theorem space_sound {orc : FFSOracle} [FFSOracle.SubstOpenLaws orc]
    {ε : ValCtx} {ρ : ValEnvSem}
    {Γ : List ValTy} {Δ : List ValValSem}
    (henv : ValEnvSoundSem orc ε ρ) {e : ValExpr} {s : ValSpace}
    (htype : ValHasType ε e (.space s))
    (ih : ∀ {e' : ValExpr} {τ' : ValTy} {ρ' : ValEnvSem} {ε' : ValCtx}
        {Γ' : List ValTy} {Δ' : List ValValSem},
      ValExpr.csize e' < ValExpr.csize e →
      ValEnvSoundSem orc ε' ρ' → ValHasType ε' e' τ' →
      ValResultSoundOfDenotSem orc ρ' Δ' τ'
        (denotValB_sem orc ρ' Γ' Δ' e')) :
    ValResultSoundOfDenotSem orc ρ Δ (.space s)
      (denotValB_sem orc ρ Γ Δ e) := by
  have hlen_all :=
    ValHasType.inferSpaceCtx_dof_eq_of_space (orc := orc) (Γ := Γ) htype
  cases htype with
  | @var _ x _ hlookup =>
      rw [denotValB_sem, denotValB_semS]
      exact ValResultSoundOfDenotSem.ok
        ((ValSoundOfDenotSem.env_irrel orc (.space s) (ρ x) ρ ρ [] Δ).mp
          (henv.native hlookup))
  | zero _ =>
      rw [denotValB_sem, denotValB_semS]
      exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
  | rlit _ =>
      rw [denotValB_sem, denotValB_semS]
      exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
  | scale _ _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays
      intro a₀ a₁
      split
      · exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · exact ValResultSoundOfDenotSem.error .mismatch
  | @vadd _ e₀ e₁ _ _ _ _ _ _ =>
      exact vadd_result_sound orc ρ Γ Δ s e₀ e₁
  | dsumE _ _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays
      intro a₀ a₁
      split
      · exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · exact ValResultSoundOfDenotSem.error .mismatch
  | tprodE _ _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays
      intro a₀ a₁
      split
      · exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · exact ValResultSoundOfDenotSem.error .mismatch
  | delta _ =>
      rw [denotValB_sem, denotValB_semS]
      exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
  | idelta _ =>
      rw [denotValB_sem, denotValB_semS]
      exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
  | ttv_space _ _ _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays
      intro a₀ a₁
      split
      · exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · exact ValResultSoundOfDenotSem.error .mismatch
  | ttv_real _ _ _ _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays
      intro a₀ a₁
      split
      · exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · exact ValResultSoundOfDenotSem.error .mismatch
  | mtm _ _ _ _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays
      intro a₀ a₁
      split
      · exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · exact ValResultSoundOfDenotSem.error .mismatch
  | @vsum _ s₀ _ es _ _ _ _ =>
      exact vsum_result_sound orc ρ Γ Δ s₀ s es hlen_all
  | @reshap _ e' τ_src _ k he hsrc htgt =>
      exact reshap_result_sound orc ε ρ Γ Δ e' (.space s) τ_src k he hsrc htgt
  | @appV _ e₀ e₁ τ₀ τ₁ _ _ h₀ _h₁ hsub _hvalid =>
      exact appV_result_sound orc ρ Γ Δ e₀ e₁ τ₀ τ₁ (.space s)
        h₀ hsub (ih (e' := e₀) (Γ' := Γ) (Δ' := Δ)
          (by simp only [ValExpr.csize]; omega) henv h₀)
  | vkrn _ _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays
      intro a₀ a₁
      split
      · exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · exact ValResultSoundOfDenotSem.error .mismatch
  | vblk _ _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays
      intro a₀ a₁
      split
      · exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · exact ValResultSoundOfDenotSem.error .mismatch
  | vtrans _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArray
      intro a
      split
      · exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · exact ValResultSoundOfDenotSem.error .mismatch
  | @gsvdS _ e a b s0 s1 _ _ _ _ he _ _ =>
      exact svdS_result_sound orc ρ Γ Δ e a b _ hlen_all
  | @gsvdU _ e a b s0 s1 _ _ _ _ he _ _ =>
      exact canonicalFSV_result_sound orc ρ Γ Δ .cokernel e a b _ hlen_all
  | @gsvdUI _ e a b s0 s1 _ _ _ _ he _ _ =>
      exact canonicalFSV_result_sound orc ρ Γ Δ .kernel e a b _ hlen_all
  | @gsvdV _ e a b s0 s1 _ _ _ _ he _ _ =>
      exact canonicalFSV_result_sound orc ρ Γ Δ .image e a b _ hlen_all
  | @gsvdVI _ e a b s0 s1 _ _ _ _ he _ _ =>
      exact canonicalFSV_result_sound orc ρ Γ Δ .coimage e a b _ hlen_all
  | @pinv_tensor _ e s0 s1 he =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArray
      intro a
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only [FFSOracleSem.const]
      by_cases hshape : a.length = ValSpace.dof orc s0 * ValSpace.dof orc s1
      · rw [if_pos hshape]
        exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValResultSoundOfDenotSem.error .mismatch
  | @pinv_raw _ e s0 he hnontensor =>
      cases s0 with
      | tprod a b => exact (hnontensor a b rfl).elim
      | empty | real | dsum | ffs =>
          rw [denotValB_sem, denotValB_semS]
          apply ValResultSoundOfDenotSem.bindArray
          intro a
          rw [ValExpr.inferSpaceCtx_eq_of_typed he]
          dsimp only [FFSOracleSem.const]
          split
          · exact ValResultSoundOfDenotSem.ok
              (ValSoundOfDenotSem.space_arrayOf hlen_all)
          · exact ValResultSoundOfDenotSem.error .mismatch
  | @gpinv _ e a b s0 s1 _ _ _ _ he _ _ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays3
      intro ae aa ab
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only [FFSOracleSem.const]
      by_cases hshape : GSVDInputsShape
          (ValSpace.dof orc s0) (ValSpace.dof orc s1) ae aa ab
      · rw [if_pos hshape]
        exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValResultSoundOfDenotSem.error .mismatch
  | @rrefRep _ _ _ _ p₀ p₁ _ h₁ =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArrays
      intro a₀ a₁
      rw [ValExpr.inferSpaceCtx_eq_of_typed h₁]
      dsimp only [FFSOracleSem.const]
      by_cases hshape :
          ValSpace.dof orc p₀ = ValSpace.dof orc p₁ ∧
            a₀.length = (a₀.length / ValSpace.dof orc p₀) *
              ValSpace.dof orc p₀ ∧
            a₁.length = ValSpace.dof orc p₀ * ValSpace.dof orc p₀
      · rw [if_pos hshape]
        exact ValResultSoundOfDenotSem.ok
          (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValResultSoundOfDenotSem.error .mismatch
  | @inv_tensor _ e s0 s1 he =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArray
      intro a
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only [FFSOracleSem.const]
      by_cases hshape : a.length = ValSpace.dof orc s0 * ValSpace.dof orc s1
      · rw [if_pos hshape]
        exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValResultSoundOfDenotSem.error .mismatch
  | @inv_raw _ e s0 he hnontensor =>
      cases s0 with
      | tprod a b => exact (hnontensor a b rfl).elim
      | empty | real | dsum | ffs =>
          rw [denotValB_sem, denotValB_semS]
          apply ValResultSoundOfDenotSem.bindArray
          intro a
          rw [ValExpr.inferSpaceCtx_eq_of_typed he]
          dsimp only [FFSOracleSem.const]
          split
          · exact ValResultSoundOfDenotSem.ok
              (ValSoundOfDenotSem.space_arrayOf hlen_all)
          · exact ValResultSoundOfDenotSem.error .mismatch
  | @svds _ e s0 s1 he =>
      rw [denotValB_sem, denotValB_semS]
      apply ValResultSoundOfDenotSem.bindArray
      intro a
      rw [ValExpr.inferSpaceCtx_eq_of_typed he]
      dsimp only [FFSOracleSem.const]
      by_cases hshape : a.length = ValSpace.dof orc s0 * ValSpace.dof orc s1
      · rw [if_pos hshape]
        exact ValResultSoundOfDenotSem.ok (ValSoundOfDenotSem.space_arrayOf hlen_all)
      · rw [if_neg hshape]
        exact ValResultSoundOfDenotSem.error .mismatch

end ValSoundOfDenotSem

/-- Generic value soundness for the constant-oracle wrapper `denotValB_sem` is
partial correctness: evaluation may return `DimError`, and every successful
payload is sound at its static type. Base soundness provides the required
out-of-bounds-zero behavior, but does not imply that a returned `FlatArray`
has exactly the semantic dimension. The adequacy layer proves success and
exact lengths where needed. There is no corresponding theorem here for an
arbitrary `FFSOracleSem`. -/
theorem valHasType_denotValB_sem_sound
    {orc : FFSOracle} [FFSOracle.Laws orc] {ε : ValCtx} {ρ : ValEnvSem}
    (Γ : List ValTy) (Δ : List ValValSem)
    {e : ValExpr} {τ : ValTy}
    (henv : ValEnvSoundSem orc ε ρ)
    (htype : ValHasType ε e τ) :
    ValResultSoundOfDenotSem orc ρ Δ τ
      (denotValB_sem orc ρ Γ Δ e) := by
  cases hτ : τ with
  | space s =>
      subst hτ
      exact ValSoundOfDenotSem.space_sound henv htype
        (fun {e' τ' ρ' ε' Γ' Δ'} _hsize henv' h =>
          valHasType_denotValB_sem_sound Γ' Δ' henv' h)
  | piTy τ₀ τ₁ =>
      subst hτ
      cases htype with
      | @var _ x _ hlookup =>
          rw [denotValB_sem, denotValB_semS]
          exact ValResultSoundOfDenotSem.ok
            ((ValSoundOfDenotSem.env_irrel orc (.piTy τ₀ τ₁) (ρ x)
              ρ ρ [] Δ).mp (henv.native hlookup))
      | @reshap _ e' τ_src _ k he hsrc htgt =>
          exact ValSoundOfDenotSem.reshap_result_sound orc ε ρ Γ Δ e'
            (.piTy τ₀ τ₁) τ_src k he hsrc htgt
      | @vlam _ _ _ _ _ body L _htval hbody =>
          change ValResultSoundOfDenotSem orc ρ Δ (.piTy τ₀ τ₁)
            (denotValB_semS (.const orc) ρ Γ Δ (.vlam τ₀ τ₁ body))
          rw [denotValB_semS]
          apply ValResultSoundOfDenotSem.ok
          rw [← denotValTy_eq_denotValTyS orc ρ τ₀ Γ Δ]
          refine ValSoundOfDenotSem.piTy_fn ?_
          intro v out hout
          have hx : freshFor (L ∪ ValExpr.fv body) ∉ L ∪ ValExpr.fv body :=
            freshFor_notMem _
          set xf := freshFor (L ∪ ValExpr.fv body) with hxdef
          have hxL : xf ∉ L := fun h => hx (Finset.mem_union_left _ h)
          have hxfv : xf ∉ ValExpr.fv body :=
            fun h => hx (Finset.mem_union_right _ h)
          have hbr := denotValB_sem_openVar_bridge orc ρ xf τ₀
            (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v) Γ Δ body hxfv
          have ihbody := valHasType_denotValB_sem_sound (τ₀ :: Γ)
            (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v :: Δ)
            (ValEnvSoundSem.update_full_carrier orc ε ρ xf τ₀ Δ henv v)
            (hbody xf hxL)
          rw [← hbr] at ihbody
          have hopen := ihbody out hout
          exact (ValSoundOfDenotSem.openRec_respect_iff orc τ₁ out ρ
            (ρ.update xf (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v))
            (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v :: Δ)
            (ValValSem.fromEl (denotValTy orc ρ Δ τ₀) v :: Δ)
            0 (.var xf τ₀)).mp hopen
      | @appV _ e₀ e₁ τ₀' τ₁' _ _ h₀ _h₁ hsub _hvalid =>
          exact ValSoundOfDenotSem.appV_result_sound orc ρ Γ Δ e₀ e₁
            τ₀' τ₁' (.piTy τ₀ τ₁) h₀ hsub
            (valHasType_denotValB_sem_sound Γ Δ henv h₀)
  termination_by ValExpr.csize e
  decreasing_by
    all_goals first
      | assumption
      | (simp only [ValExpr.csize, ValSoundOfDenotSem.ValExpr.csize_openVar,
          ValSoundOfDenotSem.ValExpr.csize_openRec]; omega)
      | (subst_vars; simp only [ValExpr.csize,
          ValSoundOfDenotSem.ValExpr.csize_openVar,
          ValSoundOfDenotSem.ValExpr.csize_openRec]; omega)

end GLang
