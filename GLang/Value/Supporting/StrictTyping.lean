import GLang.Value.Context
/- Typing judgments for the value language. -/

import GLang.Value.Binding
import GLang.Proofs.Value.Binding.ValueLN
import Mathlib.Data.Finmap

namespace GLang

mutual

  /-- `⊢ \lsv : svalid` (value-space well-formedness, `fig:valChecking`). -/
  inductive ValSValid : ValCtx → ValSpace → Type
    -- `\vdash \lR : svalid`
    | real {ε} : ValSValid ε .real
    -- `\vdash \lsempty : svalid`
    | empty {ε} : ValSValid ε .empty
    -- `\forall i. \vdash \lsnv{i} : svalid` ⊢ `\vdash \lsnv{0} \losum \lsnv{1} : svalid`
    | dsum {ε s₀ s₁} :
        ValSValid ε s₀ → ValSValid ε s₁ → ValSValid ε (.dsum s₀ s₁)
    -- `\forall i. \vdash \lsnv{i} : svalid` ⊢ `\vdash \lsnv{0} \loprod \lsnv{1} : svalid`
    | tprod {ε s₀ s₁} :
        ValSValid ε s₀ → ValSValid ε s₁ → ValSValid ε (.tprod s₀ s₁)
    -- `lsv = lsnv₀ ⊗ lsnv₁`, `\vdash leev : lsv` ⊢ `\vdash ℝ^{leev, p, lsv} : svalid`
    | ffs {ε p s₀ s₁ leev}
        : ValSValid ε s₀
        → ValSValid ε s₁
        → ValHasType ε leev (.space (.tprod s₀ s₁))
        → ValSValid ε (.ffs p (.tprod s₀ s₁) leev)

  inductive ValTValid : ValCtx → ValTy → ValKind → Type
    -- `\vdash \lsv : svalid` ⊢ `\vdash \lsv : tvalid` at kind `\lkbase`.
    | space {ε s} : ValSValid ε s → ValTValid ε (.space s) .base

    | piTy {ε τ₀ τ₁ k₀ k₁} (L : Finset VName)
        : ValTValid ε τ₀ k₀
        → (∀ x, x ∉ L →
            ValTValid (Finmap.insert x τ₀ ε) (ValTy.openVar x τ₀ τ₁) k₁)
        → ValTValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁)

  /-- `⊢ \leev : \ltyv` (value-typing, `fig:valChecking`). -/
  inductive ValHasType : ValCtx → ValExpr → ValTy → Type

    | var {ε x τ} : ε.lookup x = some τ → ValHasType ε (.var x τ) τ

    -- `\vdash \lsv : svalid` ⊢ `\vdash 0_\lsv : \lsv`.
    | zero {ε s} : ValSValid ε s → ValHasType ε (.zero s) (.space s)

    -- `\vdash r : ℝ` (rlit).
    | rlit {ε} (r : ℝ) : ValHasType ε (.rlit r) (.space .real)

    -- Scale: `\vdash \lenv{1} : \lsv`, `\vdash \lenv{0} : \lR`.
    | scale {ε e₀ e₁ s}
        : ValHasType ε e₀ (.space .real)
        → ValHasType ε e₁ (.space s)
        → ValHasType ε (.scale e₀ e₁) (.space s)

    -- Addition accepts arbitrary array spaces. The partial evaluator checks
    -- both operand lengths against the well-formed result space s.
    | vadd {ε e₀ e₁ s s₀ s₁}
        : ValHasType ε e₀ (.space s₀)
        → ValHasType ε e₁ (.space s₁)
        → ValSValid ε s
        → ValHasType ε (.vadd s e₀ e₁) (.space s)

    -- Direct sum constructor.
    | dsumE {ε e₀ e₁ s₀ s₁}
        : ValHasType ε e₀ (.space s₀)
        → ValHasType ε e₁ (.space s₁)
        → ValHasType ε (.dsumE e₀ e₁) (.space (.dsum s₀ s₁))

    -- Tensor product constructor.
    | tprodE {ε e₀ e₁ s₀ s₁}
        : ValHasType ε e₀ (.space s₀)
        → ValHasType ε e₁ (.space s₁)
        → ValHasType ε (.tprodE e₀ e₁) (.space (.tprod s₀ s₁))

    -- Delta basis vector. `\vdash \lsv : svalid` ⊢ `\vdash \ldelta{n}{\lsv} : \lsv`.
    | delta {ε n s} : ValSValid ε s → ValHasType ε (.delta n s) (.space s)

    | idelta {ε s}
        : ValSValid ε s
        → ValHasType ε (.idelta s) (.space (.tprod s s))

    | ttv_space {ε s0p s0pp s1 s0 e₀ e₁}
        : ValSValid ε s0pp
        → ValHasType ε e₀ (.space (.tprod s0p s1))
        → ValHasType ε e₁ (.space s0)
        → ValHasType ε (.ttv s0pp e₀ e₁) (.space s1)

    | ttv_real {ε s0p s0pp s0 e₀ e₁}
        : ValSValid ε s0pp
        → ValHasType ε e₀ (.space s0p)
        → ValHasType ε e₁ (.space s0)
        → (∀ a b, s0p ≠ .tprod a b)
        → ValHasType ε (.ttv s0pp e₀ e₁) (.space .real)

    | mtm {ε n₀ n₁ s0 s1 s1p s1pp s2 e₀ e₁}
        : ValSValid ε s1pp
        → ValSValid ε s1
        → ValHasType ε e₀ (.space (.tprod s1p s0))
        → ValHasType ε e₁ (.space (.tprod s2 s1))
        → ValHasType ε (.mtm n₀ n₁ s1pp s1 e₀ e₁)
                       (.space (.tprod s2 s0))

    | vsum {ε s0 s es}
        : ValSValid ε s0
        → (∀ e ∈ es, ValHasType ε e (.space s))
        → ValSValid ε s
        → (es = [] → s = .empty)
        → ValHasType ε (.vsum s0 es) (.space s)

    | vlam {ε τ₀ τ₁ k₀ k₁ e} (L : Finset VName)
        : ValTValid ε (.piTy τ₀ τ₁) (.arrow k₀ k₁)
        → (∀ x, x ∉ L →
            ValHasType (Finmap.insert x τ₀ ε) (ValExpr.openVar x τ₀ e) (ValTy.openVar x τ₀ τ₁))
        → ValHasType ε (.vlam τ₀ τ₁ e) (.piTy τ₀ τ₁)

    -- Application: `\vdash \lenv{0} : (x : \ltynv{0}) \fnto \ltynv{1}`,
    --              `\vdash \lenv{1} : \ltynv{0}` ⊢
    --              `\vdash \lenv{0}(\lenv{1}) : \ltynv{1}\subst{x}{\lenv{1}}`.
    -- Application has no output annotation. Its result is the dependent
    -- codomain instantiated at the argument. Result formation is retained
    -- as an internal premise for the existing regularity induction.
    | appV {ε e₀ e₁ τ₀ τ₁ τ_out k_out}
        : ValHasType ε e₀ (.piTy τ₀ τ₁)
        → ValHasType ε e₁ τ₀
        -- LN: codomain instantiation `τ₁[x ↦ e₁]` is `instantiate e₁ τ₁`.
        → τ_out = ValTy.applyCodomain e₁ τ₁
        → ValTValid ε τ_out k_out
        → ValHasType ε (.appV e₀ e₁) τ_out

    | vkrn {ε e e' s0 s1 s2 s3}
        : ValHasType ε e  (.space (.tprod s0 s2))
        → ValHasType ε e' (.space (.tprod s1 s3))
        → ValHasType ε (.vkrn e e')
              (.space (.tprod (.tprod s0 s1) (.tprod s2 s3)))

    | vblk {ε e e' s0 s1 s2 s3}
        : ValHasType ε e  (.space (.tprod s0 s2))
        → ValHasType ε e' (.space (.tprod s1 s3))
        → ValHasType ε (.vblk e e')
              (.space (.tprod (.dsum s0 s1) (.dsum s2 s3)))

    | reshap {ε e τ₀ τ k}
        : ValHasType ε e τ₀
        → ValTValid ε τ₀ k
        → ValTValid ε τ k
        → ValHasType ε (.reshap e τ τ₀) τ

    -- Transpose: `\vdash \leev : \lsnv{0} \loprod \lsnv{1}` ⊢
    --            `\vdash Trans(\leev) : \lsnv{1} \loprod \lsnv{0}`.
    | vtrans {ε e s₀ s₁}
        : ValHasType ε e (.space (.tprod s₀ s₁))
        → ValHasType ε (.vtrans e) (.space (.tprod s₁ s₀))

    -- (G)SVD rules. All five share the same premises:
    --   `\vdash \leev : \lsnv{0} \loprod \lsnv{1}`
    --   `\vdash \lenv{0} : \lsnvp{0} \loprod \lsnvpp{0}`
    --   `\vdash \lenv{1} : \lsnvp{1} \loprod \lsnvpp{1}`
    -- The output types differ per SVD component.
    | gsvdS {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdS e a b)
            (.space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                            (.ffs .image    (.tprod s0 s1) e)))

    | gsvdU {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdU e a b)
            (.space (.tprod s0 (.ffs .cokernel (.tprod s0 s1) e)))

    | gsvdUI {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdUI e a b)
            (.space (.tprod s0 (.ffs .kernel (.tprod s0 s1) e)))

    | gsvdV {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdV e a b)
            (.space (.tprod s1 (.ffs .image (.tprod s0 s1) e)))

    | gsvdVI {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gsvdVI e a b)
            (.space (.tprod s1 (.ffs .coimage (.tprod s0 s1) e)))

    -- Pseudo-inverse on a tensor:
    --   `\vdash \leev : \lsnv{0} \loprod \lsnv{1}` ⊢
    --   `\vdash PINV(\leev) : \lsnv{1} \loprod \lsnv{0}`.
    | pinv_tensor {ε e s₀ s₁}
        : ValHasType ε e (.space (.tprod s₀ s₁))
        → ValHasType ε (.pinv e) (.space (.tprod s₁ s₀))

    | pinv_raw {ε e s₀}
        : ValHasType ε e (.space s₀)
        → (∀ a b, s₀ ≠ .tprod a b)
        → ValHasType ε (.pinv e) (.space (.tprod .real s₀))

    -- Generalized pseudo-inverse:
    --   `\vdash \leev : \lsnv{0} \loprod \lsnv{1}`
    --   `\vdash \lenv{0} : \lsnvp{0} \loprod \lsnvpp{0}`
    --   `\vdash \lenv{1} : \lsnvp{1} \loprod \lsnvpp{1}`
    --   ⊢ `\vdash GPINV(\leev, \lenv{0}, \lenv{1}) : \lsnv{1} \loprod \lsnv{0}`.
    | gpinv {ε e a b s0 s1 a0 a1 b0 b1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε a (.space (.tprod a0 a1))
        → ValHasType ε b (.space (.tprod b0 b1))
        → ValHasType ε (.gpinv e a b) (.space (.tprod s1 s0))

    | rrefRep {ε e₀ e₁ s p0 p1}
        : ValHasType ε e₀ (.space s)
        → ValHasType ε e₁ (.space (.tprod p0 p1))
        → ValHasType ε (.rrefRep e₀ e₁) (.space (.tprod p1 p0))

    -- Inverse-form `INV`. Shares the `(P)INV` typing shape with `pinv`
    -- (`fig:valChecking` :183-191 writes `(P)INV`): tensor and raw rules.
    -- The value evaluator totalizes this with the SVD pseudoinverse; checked
    -- change-of-basis uses additionally establish the square/bijective facts
    -- under which it is the true inverse.
    | inv_tensor {ε e s₀ s₁}
        : ValHasType ε e (.space (.tprod s₀ s₁))
        → ValHasType ε (.inv e) (.space (.tprod s₁ s₀))

    -- Raw variant, with the same `pinv_raw` discriminator (rule out the
    -- tprod-arity overlap for typing uniqueness).
    | inv_raw {ε e s₀}
        : ValHasType ε e (.space s₀)
        → (∀ a b, s₀ ≠ .tprod a b)
        → ValHasType ε (.inv e) (.space (.tprod .real s₀))

    -- Standard-basis singular-value block `SVDS`. The 1-argument
    -- standard-basis specialization of `gsvdS`; same result type.
    | svds {ε e s0 s1}
        : ValHasType ε e (.space (.tprod s0 s1))
        → ValHasType ε (.svds e)
            (.space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                            (.ffs .image    (.tprod s0 s1) e)))

end

def ValHasType.canonicalFSV {which ε e a b s0 s1 a0 a1 b0 b1}
    (he : ValHasType ε e (.space (.tprod s0 s1)))
    (ha : ValHasType ε a (.space (.tprod a0 a1)))
    (hb : ValHasType ε b (.space (.tprod b0 b1))) :
    ValHasType ε (.canonicalFSV which e a b)
      (.space (.tprod (which.ambient s0 s1) (.ffs which (.tprod s0 s1) e))) := by
  cases which with
  | kernel => exact .gsvdUI he ha hb
  | cokernel => exact .gsvdU he ha hb
  | image => exact .gsvdV he ha hb
  | coimage => exact .gsvdVI he ha hb

/-! ## Easy structural constructors.

`ValHasType` is `Type`-valued (a derivation, not a proposition) — same
choice as `GLang.HasType` in `Typing.lean`. So "lemmas" here are
constructors / smart constructors at `def`-level. -/

namespace ValHasType

/-- Smart constructor for the `.rlit` form. -/
def rlit_typed {ε : ValCtx} (r : ℝ) :
    ValHasType ε (.rlit r) (.space .real) :=
  ValHasType.rlit r

end ValHasType

/-- Helper: invert a `.var x τ'` typing derivation to extract the lookup. -/
private theorem var_inv {ε : ValCtx} {x : VName} {τ' τ'' : ValTy}
    (h : ValHasType ε (.var x τ') τ'') :
    τ' = τ'' ∧ ε.lookup x = some τ' := by
  cases h with
  | var hl => exact ⟨rfl, hl⟩

/-- **Typing uniqueness.** Every value expression has at most one
    type under any typing context. -/
theorem ValHasType.unique {ε : ValCtx} {e : ValExpr} {τ τ' : ValTy}
    (h₁ : ValHasType ε e τ) (h₂ : ValHasType ε e τ') : τ = τ' := by
  -- 3-motive recursor; motive_1/motive_2 trivial, motive_3 carries
  -- the uniqueness claim parametrized by an alternate derivation.
  revert τ' h₂
  refine @ValHasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun ε e τ _ => ∀ τ', ValHasType ε e τ' → τ = τ')
    ?_ ?_ ?_ ?_ ?_       -- ValSValid arms (5)
    ?_ ?_                 -- ValTValid arms (2)
    ?_ ?_ ?_              -- var, zero, rlit
    ?_ ?_ ?_ ?_           -- scale, vadd, dsumE, tprodE
    ?_ ?_                 -- delta, idelta
    ?_ ?_ ?_              -- ttv_space, ttv_real, mtm
    ?_                    -- vsum
    ?_ ?_                 -- vlam, appV
    ?_ ?_                 -- vkrn, vblk
    ?_ ?_                 -- reshap, vtrans
    ?_ ?_ ?_ ?_ ?_     -- gsvdS, U, UI, canonicalFSV, V, VI
    ?_ ?_ ?_              -- pinv_tensor, pinv_raw, gpinv
    ?_                    -- rrefRep
    ?_ ?_ ?_              -- inv_tensor, inv_raw, svds
    _ _ _ h₁
  all_goals first | (intros; trivial) | skip
  -- VAR
  · intro _ε x τ hlookup τ' h₂
    obtain ⟨heq, hlookup'⟩ := var_inv h₂
    -- hlookup : ε.lookup x = some τ, hlookup' : ε.lookup x = some heq's τ' = some τ
    -- and heq : τ = τ'. So τ = τ'.
    exact heq
  -- ZERO
  · intro _ε s _hsv _ih τ' h₂
    cases h₂; rfl
  -- RLIT
  · intro _ε r τ' h₂
    cases h₂; rfl
  -- SCALE
  · intro _ε _e₀ _e₁ _s _h₀ _h₁ _ih₀ ih₁ τ' h₂
    -- result type is .space _s; alternate must equal .space _s'.
    -- Invert h₂: only `.scale` constructor produces `.space s'`, with
    -- e₁'s type the conclusion. IH₁ gives the equality.
    cases h₂ with
    | scale _h₀' h₁' =>
        exact ih₁ _ h₁'
  -- VADD: the result space is fixed by the expression annotation.
  · intro _ε _e₀ _e₁ _s _s₀ _s₁ _h₀ _h₁ _hs _ih₀ _ih₁ _ihs τ' h₂
    cases h₂
    rfl
  -- DSUME
  · intro _ε _e₀ _e₁ s₀ s₁ _h₀ _h₁ ih₀ ih₁ τ' h₂
    cases h₂ with
    | dsumE h₀' h₁' =>
        have e0 := ih₀ _ h₀'
        have e1 := ih₁ _ h₁'
        -- e0 : .space s₀ = .space _, e1 : .space s₁ = .space _
        injection e0 with e0'
        injection e1 with e1'
        subst e0'; subst e1'; rfl
  -- TPRODE
  · intro _ε _e₀ _e₁ s₀ s₁ _h₀ _h₁ ih₀ ih₁ τ' h₂
    cases h₂ with
    | tprodE h₀' h₁' =>
        have e0 := ih₀ _ h₀'
        have e1 := ih₁ _ h₁'
        injection e0 with e0'
        injection e1 with e1'
        subst e0'; subst e1'; rfl
  -- DELTA
  · intro _ε _n _s _hsv _ih τ' h₂
    cases h₂; rfl
  -- IDELTA
  · intro _ε _s _hsv _ih τ' h₂
    cases h₂; rfl
  -- TTV_SPACE
  · intro _ε s0p _s0pp s1 _sArg _e₀ _e₁ _hsv _h₀ _h₁ _ihsv ih₀ _ih₁ τ' h₂
    cases h₂ with
    | ttv_space _hsv' h₀' _h₁' =>
        -- IH on e₀: (.space (.tprod s0p s1)) = (.space (.tprod s0p' s1'))
        have e0 := ih₀ _ h₀'
        injection e0 with e0'
        -- e0' : .tprod s0p s1 = .tprod s0p' s1'
        injection e0' with _ es1
        subst es1; rfl
    | ttv_real _hsv' h₀' _h₁' hd =>
        -- e₀'s type forced to .space (.tprod s0p s1) by IH₀ and to .space s0p' by alt.
        -- That gives s0p' = .tprod s0p s1 — contradiction with hd.
        have e0 := ih₀ _ h₀'
        injection e0 with e0'
        exact absurd e0'.symm (hd s0p s1)
  -- TTV_REAL
  · intro _ε _s0p _s0pp _sArg _e₀ _e₁ _hsv _h₀ _h₁ hd _ihsv ih₀ _ih₁ τ' h₂
    cases h₂ with
    | ttv_space _hsv' h₀' _h₁' =>
        -- IH on e₀: (.space _s0p) = (.space (.tprod s0p' s1')).
        -- That gives _s0p = .tprod s0p' s1' — contradiction with hd.
        have e0 := ih₀ _ h₀'
        injection e0 with e0'
        exact absurd e0' (hd _ _)
    | ttv_real _hsv' _h₀' _h₁' _hd' =>
        rfl
  -- MTM
  · intro _ε _n₀ _n₁ s0 _s1 _s1p _s1pp s2 _e₀ _e₁ _hsv _hsv1 _h₀ _h₁ _ihsv _ihsv1 ih₀ ih₁ τ' h₂
    cases h₂ with
    | mtm _hsv' _hsv1' h₀' h₁' =>
        have e0 := ih₀ _ h₀'
        have e1 := ih₁ _ h₁'
        injection e0 with e0'
        injection e1 with e1'
        injection e0' with _ es0
        injection e1' with es2 _
        subst es0; subst es2; rfl
  -- VSUM (list family). Result type is `.space s`. For a nonempty list the
  -- head's IH pins `s`; for the empty list both derivations' `hdet` force
  -- `s = .empty = s'`.
  · intro _ε s0 s es _hsv hbody _hsvr hdet _ihsv ihbody _ihsvr τ' h₂
    cases h₂ with
    | @vsum _ _ s' _ _hsv' hbody' _hsvr' hdet' =>
        cases es with
        | nil =>
            rw [hdet rfl, hdet' rfl]
        | cons e tl =>
            -- IH on the head gives `.space s = .space s'`.
            have := ihbody e (List.mem_cons_self)
                      (.space s') (hbody' e (List.mem_cons_self))
            exact this
  -- VLAM
  · intro _ε _τ₀ _τ₁ _k₀ _k₁ _e _L _htval _hbody _ihtval _ih τ' h₂
    cases h₂ with
    | vlam _L' _htval' _hbody' => rfl
  -- APPV: function typing fixes the codomain; both rules substitute the
  -- same argument into it.
  · intro _ε _e₀ _e₁ _τ₀ _τ₁ τ_out _k_out _h₀ _h₁ heq _htval ih₀ _ih₁ _ihtval τ' h₂
    cases h₂ with
    | appV h₀' _h₁' heq' _htval' =>
        have hfun := ih₀ _ h₀'
        cases hfun
        exact heq.trans heq'.symm
  -- VKRN
  · intro _ε _e _e' s0 s1 s2 s3 _h _h' ih ih' τ' h₂
    cases h₂ with
    | vkrn h_alt h'_alt =>
        have e0 := ih _ h_alt
        have e1 := ih' _ h'_alt
        injection e0 with e0'
        injection e1 with e1'
        injection e0' with es0 es2
        injection e1' with es1 es3
        subst es0; subst es1; subst es2; subst es3; rfl
  -- VBLK
  · intro _ε _e _e' s0 s1 s2 s3 _h _h' ih ih' τ' h₂
    cases h₂ with
    | vblk h_alt h'_alt =>
        have e0 := ih _ h_alt
        have e1 := ih' _ h'_alt
        injection e0 with e0'
        injection e1 with e1'
        injection e0' with es0 es2
        injection e1' with es1 es3
        subst es0; subst es1; subst es2; subst es3; rfl
  -- RESHAP
  · intro _ε _e _τ₀ τ _k _he _hτ₀ _hτ _ih _ihτ₀ _ihτ τ' h₂
    cases h₂ with
    | reshap _he' _hτ₀' _hτ' => rfl
  -- VTRANS
  · intro _ε _e s₀ s₁ _h ih τ' h₂
    cases h₂ with
    | vtrans h_alt =>
        have e0 := ih _ h_alt
        injection e0 with e0'
        injection e0' with es₀ es₁
        subst es₀; subst es₁; rfl
  -- GSVDS, GSVDU, GSVDUI, GSVDV, GSVDVI all have similar structure
  -- GSVDS
  · intro _ε _e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb τ' h₂
    cases h₂ with
    | gsvdS he' _ha' _hb' =>
        have e0 := ihe _ he'
        injection e0 with e0'
        injection e0' with es0 es1
        subst es0; subst es1; rfl
  -- GSVDU
  · intro _ε _e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb τ' h₂
    cases h₂ with
    | gsvdU he' _ha' _hb' =>
        have e0 := ihe _ he'
        injection e0 with e0'
        injection e0' with es0 es1
        subst es0; subst es1; rfl
  -- GSVDUI
  · intro _ε _e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb τ' h₂
    cases h₂ with
    | gsvdUI he' _ha' _hb' =>
        have e0 := ihe _ he'
        injection e0 with e0'
        injection e0' with es0 es1
        subst es0; subst es1; rfl
  -- GSVDV
  · intro _ε _e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb τ' h₂
    cases h₂ with
    | gsvdV he' _ha' _hb' =>
        have e0 := ihe _ he'
        injection e0 with e0'
        injection e0' with es0 es1
        subst es0; subst es1; rfl
  -- GSVDVI
  · intro _ε _e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb τ' h₂
    cases h₂ with
    | gsvdVI he' _ha' _hb' =>
        have e0 := ihe _ he'
        injection e0 with e0'
        injection e0' with es0 es1
        subst es0; subst es1; rfl
  -- PINV_TENSOR
  · intro _ε _e s₀ s₁ _h ih τ' h₂
    cases h₂ with
    | pinv_tensor h_alt =>
        have e0 := ih _ h_alt
        injection e0 with e0'
        injection e0' with es₀ es₁
        subst es₀; subst es₁; rfl
    | pinv_raw _h_alt hd =>
        -- IH on e: .space (.tprod s₀ s₁) = .space s_alt.
        -- pinv_raw's hd: ∀ a b, s_alt ≠ .tprod a b. Contradiction.
        have e0 := ih _ _h_alt
        injection e0 with e0'
        -- e0' : .tprod s₀ s₁ = s_alt
        exact absurd e0'.symm (hd s₀ s₁)
  -- PINV_RAW
  · intro _ε _e _s₀ _h hd ih τ' h₂
    cases h₂ with
    | pinv_tensor h_alt =>
        have e0 := ih _ h_alt
        injection e0 with e0'
        -- e0' : _s₀ = .tprod s₀' s₁'.
        exact absurd e0' (hd _ _)
    | pinv_raw h_alt _hd_alt =>
        -- IH on _e: (.space _s₀) = (.space s_alt). Equate s_alt = _s₀.
        have e0 := ih _ h_alt
        injection e0 with e0'
        subst e0'; rfl
  -- GPINV
  · intro _ε _e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb τ' h₂
    cases h₂ with
    | gpinv he' _ha' _hb' =>
        have e0 := ihe _ he'
        injection e0 with e0'
        injection e0' with es0 es1
        subst es0; subst es1; rfl
  -- RREFREP
  · intro _ε _e₀ _e₁ _s p0 p1 _h₀ _h₁ _ih₀ ih₁ τ' h₂
    cases h₂ with
    | rrefRep _h₀' h₁' =>
        have e1 := ih₁ _ h₁'
        injection e1 with e1'
        injection e1' with ep0 ep1
        subst ep0; subst ep1; rfl
  -- INV_TENSOR (mirrors PINV_TENSOR)
  · intro _ε _e s₀ s₁ _h ih τ' h₂
    cases h₂ with
    | inv_tensor h_alt =>
        have e0 := ih _ h_alt
        injection e0 with e0'
        injection e0' with es₀ es₁
        subst es₀; subst es₁; rfl
    | inv_raw _h_alt hd =>
        have e0 := ih _ _h_alt
        injection e0 with e0'
        exact absurd e0'.symm (hd s₀ s₁)
  -- INV_RAW (mirrors PINV_RAW)
  · intro _ε _e _s₀ _h hd ih τ' h₂
    cases h₂ with
    | inv_tensor h_alt =>
        have e0 := ih _ h_alt
        injection e0 with e0'
        exact absurd e0' (hd _ _)
    | inv_raw h_alt _hd_alt =>
        have e0 := ih _ h_alt
        injection e0 with e0'
        subst e0'; rfl
  -- SVDS (mirrors GSVDS, single operand)
  · intro _ε _e s0 s1 _he ihe τ' h₂
    cases h₂ with
    | svds he' =>
        have e0 := ihe _ he'
        injection e0 with e0'
        injection e0' with es0 es1
        subst es0; subst es1; rfl

end GLang
