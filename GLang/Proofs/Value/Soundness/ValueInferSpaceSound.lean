

import GLang.Value.Inference

namespace GLang

/-! ## Motive helper.

The recursor's motive on `ValHasType` is "conditional" on the typing
shape: for `.space s` types we want the equality `inferSpace e = s`;
for `.piTy …` types the motive is trivially `True`. We expose this
as a top-level `Prop` so Lean's elaborator doesn't silently lift the
motive to depend on the derivation. -/

/-- Motive helper for `inferSpace_eq_of_space`. -/
def ValTy.inferSpaceConclusion (e : ValExpr) : ValTy → Prop
  | .space s  => ValExpr.inferSpace e = s
  | .piTy _ _ => True

@[simp] theorem ValTy.inferSpaceConclusion_space (e : ValExpr) (s : ValSpace) :
    ValTy.inferSpaceConclusion e (.space s) = (ValExpr.inferSpace e = s) := rfl

@[simp] theorem ValTy.inferSpaceConclusion_piTy (e : ValExpr)
    (τ₀ τ₁ : ValTy) :
    ValTy.inferSpaceConclusion e (.piTy τ₀ τ₁) = True := rfl

/-! ## `inferType` agreement with typing.

Symmetrical with `inferSpace_eq_of_space`: for every well-typed `e`,
the syntactic type inferer `ValExpr.inferType` returns the typing-
derivation's conclusion type. Used by the higher-kinded `.reshap`
(arrow case) to recover `τ₀`'s structure from `e` syntactically.

The motive on `ValHasType` is unconditional: `inferType e = τ` for
every well-typed pair. (Compare `inferSpace_eq_of_space`'s motive,
which had to branch on `τ`'s shape.) -/

/-- **`inferType` agrees with the typing-assigned type.**

For every well-typed value expression `e : τ`, the syntactic type
inferer returns exactly `τ`. -/
theorem ValHasType.inferType_eq_of_typed
    {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (h : ValHasType ε e τ) :
    ValExpr.inferType e = τ := by
  refine @ValHasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ε e τ _ => ValExpr.inferType e = τ)
    ?_ ?_ ?_ ?_ ?_       -- ValSValid: real, empty, dsum, tprod, ffs
    ?_ ?_                 -- ValTValid: space, piTy
    ?_ ?_ ?_              -- var, zero, rlit
    ?_ ?_ ?_ ?_           -- scale, vadd, dsumE, tprodE
    ?_ ?_                 -- delta, idelta
    ?_ ?_ ?_              -- ttv_space, ttv_real, mtm
    ?_                    -- vsum
    ?_ ?_                 -- vlam, appV
    ?_ ?_                 -- vkrn, vblk
    ?_ ?_                 -- reshap, vtrans
    ?_ ?_ ?_ ?_ ?_     -- gsvdS, gsvdU, gsvdUI, canonicalFSV, gsvdV, gsvdVI
    ?_ ?_ ?_              -- pinv_tensor, pinv_raw, gpinv
    ?_                    -- rrefRep
    ?_ ?_ ?_              -- inv_tensor, inv_raw, svds
    _ _ _ h
  -- ValSValid arms (5): trivial motive.
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  -- ValTValid arms (2): trivial motive.
  · intros; trivial
  · intros; trivial
  -- `.var x τ` — annotation-faithful: inferType (.var x τ) = τ by rfl.
  · intro _ε _x τ _hlookup
    rfl
  -- `.zero s` — inferType = .space s by rfl.
  · intros; rfl
  -- `.rlit r` — inferType = .space .real by rfl.
  · intros; rfl
  -- `.scale e₀ e₁ s` — inferType (.scale _ e₁) = inferType e₁ = .space s by IH₁.
  · intro _ε _e₀ e₁ s _h₀ _h₁ _ih₀ ih₁
    show ValExpr.inferType e₁ = ValTy.space s
    exact ih₁
  -- `.vadd s e₀ e₁` — the result annotation is authoritative.
  · intro _ε e₀ e₁ s _s₀ _s₁ _h₀ _h₁ _hs _ih₀ _ih₁ _ihs
    show ValExpr.inferType (.vadd s e₀ e₁) = ValTy.space s
    rfl
  -- `.dsumE e₀ e₁ s₀ s₁` — IHs give types `.space s₀`, `.space s₁`.
  · intro _ε e₀ e₁ s₀ s₁ _h₀ _h₁ ih₀ ih₁
    have he₀ : ValExpr.inferType e₀ = ValTy.space s₀ := ih₀
    have he₁ : ValExpr.inferType e₁ = ValTy.space s₁ := ih₁
    show ValExpr.inferType (.dsumE e₀ e₁) = ValTy.space (.dsum s₀ s₁)
    unfold ValExpr.inferType
    rw [he₀, he₁]
    rfl
  -- `.tprodE e₀ e₁ s₀ s₁` — same.
  · intro _ε e₀ e₁ s₀ s₁ _h₀ _h₁ ih₀ ih₁
    have he₀ : ValExpr.inferType e₀ = ValTy.space s₀ := ih₀
    have he₁ : ValExpr.inferType e₁ = ValTy.space s₁ := ih₁
    show ValExpr.inferType (.tprodE e₀ e₁) = ValTy.space (.tprod s₀ s₁)
    unfold ValExpr.inferType
    rw [he₀, he₁]
    rfl
  -- `.delta n s` — inferType = .space s by rfl.
  · intros; rfl
  -- `.idelta s` — inferType = .space (.tprod s s) by rfl.
  · intros; rfl
  -- `.ttv_space ε s0p s0pp s1 e₀ e₁` — output `.space s1`.
  --   IH₀ : inferType e₀ = .space (.tprod s0p s1).
  · intro _ε s0p _s0pp s1 _sArg e₀ _e₁ _hsv _h₀ _h₁ _ihsv ih₀ _ih₁
    have he : ValExpr.inferType e₀ = ValTy.space (.tprod s0p s1) := ih₀
    show ValExpr.inferType (.ttv _s0pp e₀ _e₁) = ValTy.space s1
    unfold ValExpr.inferType
    rw [he]
  -- `.ttv_real ε s0p s0pp e₀ e₁` — output `.space .real`. Discriminator
  --   hd : ∀ a b, s0p ≠ .tprod a b rules out the overlap.
  · intro _ε s0p _s0pp _sArg e₀ _e₁ _hsv _h₀ _h₁ hd _ihsv ih₀ _ih₁
    have he : ValExpr.inferType e₀ = ValTy.space s0p := ih₀
    show ValExpr.inferType (.ttv _s0pp e₀ _e₁) = ValTy.space .real
    unfold ValExpr.inferType
    rw [he]
    cases s0p with
    | empty => rfl
    | real  => rfl
    | dsum _ _ => rfl
    | tprod a b => exact absurd rfl (hd a b)
    | ffs _ _ _ => rfl
  -- `.mtm` — IHs on both subterms.
  · intro _ε _n₀ _n₁ s0 s1 s1p s1pp s2 e₀ e₁ _hsv _hsv1 _h₀ _h₁ _ihsv _ihsv1 ih₀ ih₁
    have he₀ : ValExpr.inferType e₀ = ValTy.space (.tprod s1p s0) := ih₀
    have he₁ : ValExpr.inferType e₁ = ValTy.space (.tprod s2 s1) := ih₁
    show ValExpr.inferType (.mtm _n₀ _n₁ s1pp s1 e₀ e₁)
        = ValTy.space (.tprod s2 s0)
    unfold ValExpr.inferType
    rw [he₀, he₁]
  -- `.vsum s0 es` (list family). NONEMPTY: `inferType` reads the head, whose
  -- IH gives `.space s`. EMPTY: `inferType` returns `.space .empty`, and the
  -- typing rule's determinism premise `hdet : es = [] → s = .empty` forces
  -- `s = .empty`, so both sides are `.space .empty`.
  · intro _ε s0 s es _hsv hbody _hsvr hdet _ihsv ihbody _ihsvr
    cases es with
    | nil =>
        show ValExpr.inferType (.vsum s0 []) = ValTy.space s
        rw [hdet rfl]; rfl
    | cons e tl =>
        show ValExpr.inferType (.vsum s0 (e :: tl)) = ValTy.space s
        exact ihbody e (List.mem_cons_self)
  -- `.vlam x τ₀ τ₁ k₀ k₁ e` — output `.piTy x τ₀ τ₁` by rfl.
  · intros; rfl
  -- Application computes the substituted codomain of the inferred function type.
  · intro ε e0 e1 τ0 τ1 τout k h0 h1 heq ht ih0 ih1 iht
    simp [ValExpr.inferType, ih0, heq]
  -- `.vkrn` — IHs on both.
  · intro _ε e e' s0 s1 s2 s3 _h _h' ih ih'
    have he : ValExpr.inferType e = ValTy.space (.tprod s0 s2) := ih
    have he' : ValExpr.inferType e' = ValTy.space (.tprod s1 s3) := ih'
    show ValExpr.inferType (.vkrn e e')
        = ValTy.space (.tprod (.tprod s0 s1) (.tprod s2 s3))
    unfold ValExpr.inferType
    rw [he, he']
  -- `.vblk` — IHs on both.
  · intro _ε e e' s0 s1 s2 s3 _h _h' ih ih'
    have he : ValExpr.inferType e = ValTy.space (.tprod s0 s2) := ih
    have he' : ValExpr.inferType e' = ValTy.space (.tprod s1 s3) := ih'
    show ValExpr.inferType (.vblk e e')
        = ValTy.space (.tprod (.dsum s0 s1) (.dsum s2 s3))
    unfold ValExpr.inferType
    rw [he, he']
  -- `.reshap e τ τ₀` — output `τ` by rfl.
  · intros; rfl
  -- `.vtrans` — IH on e.
  · intro _ε e s₀ s₁ _h ih
    have he : ValExpr.inferType e = ValTy.space (.tprod s₀ s₁) := ih
    show ValExpr.inferType (.vtrans e) = ValTy.space (.tprod s₁ s₀)
    unfold ValExpr.inferType
    rw [he]
  -- `.gsvdS` — IH on e.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    have he : ValExpr.inferType e = ValTy.space (.tprod s0 s1) := ihe
    show ValExpr.inferType (.gsvdS e _a _b)
        = ValTy.space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                              (.ffs .image    (.tprod s0 s1) e))
    unfold ValExpr.inferType
    rw [he]
  -- `.gsvdU` — IH on e.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    have he : ValExpr.inferType e = ValTy.space (.tprod s0 s1) := ihe
    show ValExpr.inferType (.gsvdU e _a _b)
        = ValTy.space (.tprod s0 (.ffs .cokernel (.tprod s0 s1) e))
    unfold ValExpr.inferType
    rw [he]
  -- `.gsvdUI` — IH on e.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    have he : ValExpr.inferType e = ValTy.space (.tprod s0 s1) := ihe
    show ValExpr.inferType (.gsvdUI e _a _b)
        = ValTy.space (.tprod s0 (.ffs .kernel (.tprod s0 s1) e))
    unfold ValExpr.inferType
    rw [he]
  -- `.gsvdV` — IH on e.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    have he : ValExpr.inferType e = ValTy.space (.tprod s0 s1) := ihe
    show ValExpr.inferType (.gsvdV e _a _b)
        = ValTy.space (.tprod s1 (.ffs .image (.tprod s0 s1) e))
    unfold ValExpr.inferType
    rw [he]
  -- `.gsvdVI` — IH on e.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    have he : ValExpr.inferType e = ValTy.space (.tprod s0 s1) := ihe
    show ValExpr.inferType (.gsvdVI e _a _b)
        = ValTy.space (.tprod s1 (.ffs .coimage (.tprod s0 s1) e))
    unfold ValExpr.inferType
    rw [he]
  -- `.pinv_tensor` — IH on e.
  · intro _ε e s₀ s₁ _h ih
    have he : ValExpr.inferType e = ValTy.space (.tprod s₀ s₁) := ih
    show ValExpr.inferType (.pinv e) = ValTy.space (.tprod s₁ s₀)
    unfold ValExpr.inferType
    rw [he]
  -- `.pinv_raw` — IH on e; discriminator rules out tprod.
  · intro _ε e s₀ _h hd ih
    have he : ValExpr.inferType e = ValTy.space s₀ := ih
    show ValExpr.inferType (.pinv e) = ValTy.space (.tprod .real s₀)
    unfold ValExpr.inferType
    rw [he]
    cases s₀ with
    | empty => rfl
    | real  => rfl
    | dsum _ _ => rfl
    | tprod a b => exact absurd rfl (hd a b)
    | ffs _ _ _ => rfl
  -- `.gpinv` — IH on e.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    have he : ValExpr.inferType e = ValTy.space (.tprod s0 s1) := ihe
    show ValExpr.inferType (.gpinv e _a _b) = ValTy.space (.tprod s1 s0)
    unfold ValExpr.inferType
    rw [he]
  -- `.rrefRep` — IH on e₁.
  · intro _ε _e₀ e₁ _s p0 p1 _h₀ _h₁ _ih₀ ih₁
    have he : ValExpr.inferType e₁ = ValTy.space (.tprod p0 p1) := ih₁
    show ValExpr.inferType (.rrefRep _e₀ e₁) = ValTy.space (.tprod p1 p0)
    unfold ValExpr.inferType
    rw [he]
  -- `.inv_tensor` — IH on e (mirrors `pinv_tensor`).
  · intro _ε e s₀ s₁ _h ih
    have he : ValExpr.inferType e = ValTy.space (.tprod s₀ s₁) := ih
    show ValExpr.inferType (.inv e) = ValTy.space (.tprod s₁ s₀)
    unfold ValExpr.inferType
    rw [he]
  -- `.inv_raw` — IH on e; discriminator rules out tprod (mirrors `pinv_raw`).
  · intro _ε e s₀ _h hd ih
    have he : ValExpr.inferType e = ValTy.space s₀ := ih
    show ValExpr.inferType (.inv e) = ValTy.space (.tprod .real s₀)
    unfold ValExpr.inferType
    rw [he]
    cases s₀ with
    | empty => rfl
    | real  => rfl
    | dsum _ _ => rfl
    | tprod a b => exact absurd rfl (hd a b)
    | ffs _ _ _ => rfl
  -- `.svds` — IH on e (mirrors `gsvdS`, single operand).
  · intro _ε e s0 s1 _he ihe
    have he : ValExpr.inferType e = ValTy.space (.tprod s0 s1) := ihe
    show ValExpr.inferType (.svds e)
        = ValTy.space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                              (.ffs .image    (.tprod s0 s1) e))
    unfold ValExpr.inferType
    rw [he]

/-! ## Main lemma — typing-syntactic agreement.

Proved by `@ValHasType.rec` with three motives (matching the
`valHasType_denot_sound` pattern in `ValueSoundness.lean`):

* `motive_1` (on `ValSValid`) and `motive_2` (on `ValTValid`) are
  trivial (`True`).
* `motive_3` (on `ValHasType ε e τ`) is conditional on `τ`'s shape:
  `match τ with | .space s => inferSpace e = s | _ => True`. The
  arrow-typed constructors (`.vlam`) discharge with `trivial`; the
  `.space`-typed ones unfold `inferSpace` and match the typing
  derivation. -/

theorem ValHasType.inferSpace_eq_of_space
    {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (h : ValHasType ε e (.space s)) :
    ValExpr.inferSpace e = s := by
  -- Three-motive recursor: motive_3 is conditional on `τ`'s shape.
  -- We define the motive as a top-level helper to avoid Lean's matcher
  -- silently extending it to depend on the derivation. The motive only
  -- depends on `e` and `τ` (not on the derivation witness).
  let motive3 : (ε : ValCtx) → (e : ValExpr) → (τ : ValTy) →
      ValHasType ε e τ → Prop :=
    fun _ε e τ _ => ValTy.inferSpaceConclusion e τ
  refine @ValHasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := motive3)
    ?_ ?_ ?_ ?_ ?_       -- ValSValid: real, empty, dsum, tprod, ffs
    ?_ ?_                 -- ValTValid: space, piTy
    ?_ ?_ ?_              -- var, zero, rlit
    ?_ ?_ ?_ ?_           -- scale, vadd, dsumE, tprodE
    ?_ ?_                 -- delta, idelta
    ?_ ?_ ?_              -- ttv_space, ttv_real, mtm
    ?_                    -- vsum
    ?_ ?_                 -- vlam, appV
    ?_ ?_                 -- vkrn, vblk
    ?_ ?_                 -- reshap, vtrans
    ?_ ?_ ?_ ?_ ?_     -- gsvdS, gsvdU, gsvdUI, canonicalFSV, gsvdV, gsvdVI
    ?_ ?_ ?_              -- pinv_tensor, pinv_raw, gpinv
    ?_                    -- rrefRep
    ?_ ?_ ?_              -- inv_tensor, inv_raw, svds
    _ _ _ h
  -- ValSValid arms (5): trivial motive.
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  · intros; trivial
  -- ValTValid arms (2): trivial motive.
  · intros; trivial
  · intros; trivial

  · intro _ε _x τ _hlookup
    -- Goal: `ValTy.inferSpaceConclusion (.var _x τ) τ`.
    cases τ with
    | space _s =>
        show ValExpr.inferSpace (.var _x (.space _s)) = _s
        rfl
    | piTy _ _ => trivial
  -- `.zero s` — direct: inferSpace .zero = s.
  · intro _ε s _hsv _ih
    show ValExpr.inferSpace (.zero s) = s
    rfl
  -- `.rlit r` — direct: inferSpace .rlit = .real.
  · intro _ε r
    show ValExpr.inferSpace (.rlit r) = ValSpace.real
    rfl
  -- `.scale e₀ e₁` — inferSpace = inferSpace e₁. IH gives inferSpace e₁ = s.
  · intro _ε _e₀ e₁ s _h₀ _h₁ _ih₀ ih₁
    -- ih₁ : match (.space s) with | .space s' => inferSpace e₁ = s' | _ => True
    -- which reduces to inferSpace e₁ = s.
    show ValExpr.inferSpace (.scale _e₀ e₁) = s
    show ValExpr.inferSpace e₁ = s
    exact ih₁
  -- `.vadd s e₀ e₁` — the result annotation is authoritative.
  · intro _ε e₀ e₁ s _s₀ _s₁ _h₀ _h₁ _hs _ih₀ _ih₁ _ihs
    show ValExpr.inferSpace (.vadd s e₀ e₁) = s
    rfl
  -- `.dsumE e₀ e₁ s₀ s₁` — inferSpace = .dsum (inferSpace e₀) (inferSpace e₁).
  --   IH₀ : inferSpace e₀ = s₀.  IH₁ : inferSpace e₁ = s₁.
  · intro _ε e₀ e₁ s₀ s₁ _h₀ _h₁ ih₀ ih₁
    show ValExpr.inferSpace (.dsumE e₀ e₁) = .dsum s₀ s₁
    show ValSpace.dsum (ValExpr.inferSpace e₀) (ValExpr.inferSpace e₁)
       = ValSpace.dsum s₀ s₁
    -- IHs have type `ValTy.inferSpaceConclusion eᵢ (.space sᵢ)` which is
    -- definitionally `inferSpace eᵢ = sᵢ`.
    have h0 : ValExpr.inferSpace e₀ = s₀ := ih₀
    have h1 : ValExpr.inferSpace e₁ = s₁ := ih₁
    rw [h0, h1]
  -- `.tprodE e₀ e₁ s₀ s₁` — same shape.
  · intro _ε e₀ e₁ s₀ s₁ _h₀ _h₁ ih₀ ih₁
    show ValExpr.inferSpace (.tprodE e₀ e₁) = .tprod s₀ s₁
    show ValSpace.tprod (ValExpr.inferSpace e₀) (ValExpr.inferSpace e₁)
       = ValSpace.tprod s₀ s₁
    have h0 : ValExpr.inferSpace e₀ = s₀ := ih₀
    have h1 : ValExpr.inferSpace e₁ = s₁ := ih₁
    rw [h0, h1]
  -- `.delta n s` — direct.
  · intro _ε _n s _hsv _ih
    show ValExpr.inferSpace (.delta _n s) = s
    rfl
  -- `.idelta s` — inferSpace = .tprod s s.
  · intro _ε s _hsv _ih
    show ValExpr.inferSpace (.idelta s) = .tprod s s
    rfl
  -- `.ttv_space ε s0p s0pp s1 e₀ e₁` — output `.space s1`.
  --   IH₀ : inferSpace e₀ = .tprod s0p s1.
  --   inferSpace (.ttv ..) = match (.tprod s0p s1) with | .tprod _ s_out => s_out = s1.
  · intro _ε s0p _s0pp s1 _sArg e₀ e₁ _hsv _h₀ _h₁ _ihsv ih₀ _ih₁
    show ValExpr.inferSpace (.ttv _s0pp e₀ e₁) = s1
    show (match ValExpr.inferSpace e₀ with
          | ValSpace.tprod _ s_out => s_out
          | _ => ValSpace.real) = s1
    -- Rewrite inferSpace e₀ using IH.
    have h_ie : ValExpr.inferSpace e₀ = ValSpace.tprod s0p s1 := ih₀
    rw [h_ie]
  -- `.ttv_real ε s0p s0pp e₀ e₁` — output `.space .real`.
  --   IH₀ : inferSpace e₀ = s0p (NOT necessarily a tprod).

  --     rules out the overlap with `ttv_space`.
  --   inferSpace (.ttv ..) = match inferSpace e₀ with | .tprod _ s_out => s_out | _ => .real.
  --   By IH₀ and the discriminator, s0p is non-tprod, so the match falls
  --   through to .real ✓.
  · intro _ε s0p _s0pp _sArg e₀ _e₁ _hsv _h₀ _h₁ hd _ihsv ih₀ _ih₁
    show ValExpr.inferSpace (.ttv _s0pp e₀ _e₁) = ValSpace.real
    show (match ValExpr.inferSpace e₀ with
          | ValSpace.tprod _ s_out => s_out
          | _ => ValSpace.real) = ValSpace.real
    rw [show ValExpr.inferSpace e₀ = s0p from ih₀]
    cases s0p with
    | empty => rfl
    | real  => rfl
    | dsum _ _ => rfl
    | tprod a b =>
        -- Discriminator says s0p ≠ .tprod a b — contradiction.
        exact absurd rfl (hd a b)
    | ffs _ _ _ => rfl
  -- `.mtm n₀ n₁ s1pp s1 e₀ e₁ s0 s1p s2` — output `.tprod s2 s0`.
  --   IH₀ : inferSpace e₀ = .tprod s1p s0.
  --   IH₁ : inferSpace e₁ = .tprod s2 s1.
  --   inferSpace (.mtm ...) = match (.tprod s1p s0), (.tprod s2 s1) with
  --     | .tprod _ s_0, .tprod s_2 _ => .tprod s_2 s_0 = .tprod s2 s0. ✓
  · intro _ε _n₀ _n₁ s0 s1 s1p s1pp s2 e₀ e₁ _hsv _hsv1 _h₀ _h₁ _ihsv _ihsv1 ih₀ ih₁
    show ValExpr.inferSpace (.mtm _n₀ _n₁ s1pp s1 e₀ e₁) = .tprod s2 s0
    show (match ValExpr.inferSpace e₀, ValExpr.inferSpace e₁ with
          | ValSpace.tprod _ s_0, ValSpace.tprod s_2 _ => ValSpace.tprod s_2 s_0
          | _, _ => ValSpace.empty) = .tprod s2 s0
    rw [show ValExpr.inferSpace e₀ = .tprod s1p s0 from ih₀,
        show ValExpr.inferSpace e₁ = .tprod s2 s1 from ih₁]
  -- `.vsum s0 es` (list family). NONEMPTY: head's IH gives `inferSpace = s`.
  -- EMPTY: `inferSpace (.vsum s0 []) = .empty` and `hdet` forces `s = .empty`.
  · intro _ε s0 s es _hsv hbody _hsvr hdet _ihsv ihbody _ihsvr
    cases es with
    | nil =>
        show ValExpr.inferSpace (.vsum s0 []) = s
        rw [hdet rfl]; rfl
    | cons e tl =>
        show ValExpr.inferSpace (.vsum s0 (e :: tl)) = s
        exact ihbody e (List.mem_cons_self)
  -- `.vlam x τ₀ τ₁ e` — output `.piTy x τ₀ τ₁`. Motive is `True`.
  · intros; trivial
  -- Application uses the same codomain substitution as type inference.
  · intro ε e0 e1 τ0 τ1 τout k h0 h1 heq ht ih0 ih1 iht
    have hf := ValHasType.inferType_eq_of_typed h0
    cases τout with
    | space s =>
        change (ValExpr.inferType (.appV e0 e1)).spaceOf = s
        simp only [ValExpr.inferType, hf]
        change (ValTy.applyCodomain e1 τ1).spaceOf = s
        rw [← heq]
        rfl
    | piTy _ _ => trivial
  -- `.vkrn e e' s0 s1 s2 s3` — output `.tprod (.tprod s0 s1) (.tprod s2 s3)`.
  --   IH : inferSpace e = .tprod s0 s2.  IH' : inferSpace e' = .tprod s1 s3.
  · intro _ε e e' s0 s1 s2 s3 _h _h' ih ih'
    show ValExpr.inferSpace (.vkrn e e') = .tprod (.tprod s0 s1) (.tprod s2 s3)
    show (match ValExpr.inferSpace e, ValExpr.inferSpace e' with
          | ValSpace.tprod s0_ s2_, ValSpace.tprod s1_ s3_ =>
              ValSpace.tprod (.tprod s0_ s1_) (.tprod s2_ s3_)
          | _, _ => ValSpace.empty) = .tprod (.tprod s0 s1) (.tprod s2 s3)
    rw [show ValExpr.inferSpace e = .tprod s0 s2 from ih,
        show ValExpr.inferSpace e' = .tprod s1 s3 from ih']
  -- `.vblk e e' s0 s1 s2 s3` — output `.tprod (.dsum s0 s1) (.dsum s2 s3)`.
  · intro _ε e e' s0 s1 s2 s3 _h _h' ih ih'
    show ValExpr.inferSpace (.vblk e e') = .tprod (.dsum s0 s1) (.dsum s2 s3)
    show (match ValExpr.inferSpace e, ValExpr.inferSpace e' with
          | ValSpace.tprod s0_ s2_, ValSpace.tprod s1_ s3_ =>
              ValSpace.tprod (.dsum s0_ s1_) (.dsum s2_ s3_)
          | _, _ => ValSpace.empty) = .tprod (.dsum s0 s1) (.dsum s2 s3)
    rw [show ValExpr.inferSpace e = .tprod s0 s2 from ih,
        show ValExpr.inferSpace e' = .tprod s1 s3 from ih']
  -- `.reshap e τ τ₀` — output `τ`. If τ = .space s, inferSpace =
  -- ValTy.spaceOf (.space s) = s. The stored source `τ₀` is ignored by inference.
  -- If τ = .piTy …, motive is True.
  · intro _ε e τ₀ τ _k _h _hτ₀ _hτ _ih _ihτ₀ _ihτ
    -- Goal: `ValTy.inferSpaceConclusion (.reshap e τ τ₀) τ`.
    cases τ with
    | space s =>
        show ValExpr.inferSpace (.reshap e (.space s) τ₀) = s
        rfl
    | piTy _ _ => trivial
  -- `.vtrans e s₀ s₁` — output `.tprod s₁ s₀`.
  --   IH : inferSpace e = .tprod s₀ s₁.
  · intro _ε e s₀ s₁ _h ih
    show ValExpr.inferSpace (.vtrans e) = .tprod s₁ s₀
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod s0_ s1_ => ValSpace.tprod s1_ s0_
          | _ => ValSpace.empty) = .tprod s₁ s₀
    rw [show ValExpr.inferSpace e = .tprod s₀ s₁ from ih]
  -- `.gsvdS e a b s0 s1 a0 a1 b0 b1` — output `.tprod (.ffs cokernel … e) (.ffs image … e)`.
  --   IH on e : inferSpace e = .tprod s0 s1.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    show ValExpr.inferSpace (.gsvdS e _a _b)
        = .tprod (.ffs .cokernel (.tprod s0 s1) e)
                 (.ffs .image    (.tprod s0 s1) e)
    show ValSpace.tprod
          (ValSpace.ffs .cokernel (ValExpr.inferSpace e) e)
          (ValSpace.ffs .image    (ValExpr.inferSpace e) e)
        = .tprod (.ffs .cokernel (.tprod s0 s1) e)
                 (.ffs .image    (.tprod s0 s1) e)
    rw [show ValExpr.inferSpace e = .tprod s0 s1 from ihe]
  -- `.gsvdU e a b s0 s1 a0 a1 b0 b1` — output `.tprod s0 (.ffs cokernel … e)`.
  --   IH on e : inferSpace e = .tprod s0 s1.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    show ValExpr.inferSpace (.gsvdU e _a _b)
        = .tprod s0 (.ffs .cokernel (.tprod s0 s1) e)
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod s0_ _ =>
              ValSpace.tprod s0_ (ValSpace.ffs .cokernel (ValExpr.inferSpace e) e)
          | _ => ValSpace.empty)
        = .tprod s0 (.ffs .cokernel (.tprod s0 s1) e)
    rw [show ValExpr.inferSpace e = .tprod s0 s1 from ihe]
  -- `.gsvdUI` — output `.tprod s0 (.ffs .kernel … e)`.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    show ValExpr.inferSpace (.gsvdUI e _a _b)
        = .tprod s0 (.ffs .kernel (.tprod s0 s1) e)
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod s0_ _ =>
              ValSpace.tprod s0_ (ValSpace.ffs .kernel (ValExpr.inferSpace e) e)
          | _ => ValSpace.empty)
        = .tprod s0 (.ffs .kernel (.tprod s0 s1) e)
    rw [show ValExpr.inferSpace e = .tprod s0 s1 from ihe]
  -- `.gsvdV` — output `.tprod s1 (.ffs .image … e)` (E5: codomain factor left).
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    show ValExpr.inferSpace (.gsvdV e _a _b)
        = .tprod s1 (.ffs .image (.tprod s0 s1) e)
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod _ s1_ =>
              ValSpace.tprod s1_ (ValSpace.ffs .image (ValExpr.inferSpace e) e)
          | _ => ValSpace.empty)
        = .tprod s1 (.ffs .image (.tprod s0 s1) e)
    rw [show ValExpr.inferSpace e = .tprod s0 s1 from ihe]
  -- `.gsvdVI` — output `.tprod s1 (.ffs .coimage … e)` (E5).
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    show ValExpr.inferSpace (.gsvdVI e _a _b)
        = .tprod s1 (.ffs .coimage (.tprod s0 s1) e)
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod _ s1_ =>
              ValSpace.tprod s1_ (ValSpace.ffs .coimage (ValExpr.inferSpace e) e)
          | _ => ValSpace.empty)
        = .tprod s1 (.ffs .coimage (.tprod s0 s1) e)
    rw [show ValExpr.inferSpace e = .tprod s0 s1 from ihe]
  -- `.pinv_tensor e s₀ s₁` — output `.tprod s₁ s₀`.
  --   IH : inferSpace e = .tprod s₀ s₁.
  · intro _ε e s₀ s₁ _h ih
    show ValExpr.inferSpace (.pinv e) = .tprod s₁ s₀
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod s0_ s1_ => ValSpace.tprod s1_ s0_
          | s_other => ValSpace.tprod .real s_other) = .tprod s₁ s₀
    rw [show ValExpr.inferSpace e = .tprod s₀ s₁ from ih]
  -- `.pinv_raw e s₀` — output `.tprod .real s₀`.
  --   IH : inferSpace e = s₀ (any space).

  --     the overlap with `pinv_tensor`.
  --   inferSpace (.pinv e) = match s₀ with .tprod a b => .tprod b a | s => .tprod .real s.
  --   By hd, s₀ is non-tprod, so the match returns `.tprod .real s₀` ✓.
  · intro _ε e s₀ _h hd ih
    show ValExpr.inferSpace (.pinv e) = .tprod .real s₀
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod s0_ s1_ => ValSpace.tprod s1_ s0_
          | s_other => ValSpace.tprod .real s_other) = .tprod .real s₀
    rw [show ValExpr.inferSpace e = s₀ from ih]
    cases s₀ with
    | empty => rfl
    | real  => rfl
    | dsum _ _ => rfl
    | tprod a b =>
        exact absurd rfl (hd a b)
    | ffs _ _ _ => rfl
  -- `.gpinv e a b s0 s1 a0 a1 b0 b1` — output `.tprod s1 s0`.
  --   IH on e : inferSpace e = .tprod s0 s1.
  --   inferSpace (.gpinv e _ _) = match inferSpace e with .tprod s0 s1 => .tprod s1 s0 | _ => .empty.
  · intro _ε e _a _b s0 s1 _a0 _a1 _b0 _b1 _he _ha _hb ihe _iha _ihb
    show ValExpr.inferSpace (.gpinv e _a _b) = .tprod s1 s0
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod s0_ s1_ => ValSpace.tprod s1_ s0_
          | _ => ValSpace.empty) = .tprod s1 s0
    rw [show ValExpr.inferSpace e = .tprod s0 s1 from ihe]
  -- `.rrefRep e₀ e₁ s p0 p1` — output `.tprod p1 p0`.
  --   IH on e₁ : inferSpace e₁ = .tprod p0 p1.
  · intro _ε _e₀ e₁ _s p0 p1 _h₀ _h₁ _ih₀ ih₁
    show ValExpr.inferSpace (.rrefRep _e₀ e₁) = .tprod p1 p0
    show (match ValExpr.inferSpace e₁ with
          | ValSpace.tprod p0_ p1_ => ValSpace.tprod p1_ p0_
          | _ => ValSpace.empty) = .tprod p1 p0
    rw [show ValExpr.inferSpace e₁ = .tprod p0 p1 from ih₁]
  -- `.inv_tensor e s₀ s₁` — output `.tprod s₁ s₀` (mirrors `pinv_tensor`).
  · intro _ε e s₀ s₁ _h ih
    show ValExpr.inferSpace (.inv e) = .tprod s₁ s₀
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod s0_ s1_ => ValSpace.tprod s1_ s0_
          | s_other => ValSpace.tprod .real s_other) = .tprod s₁ s₀
    rw [show ValExpr.inferSpace e = .tprod s₀ s₁ from ih]
  -- `.inv_raw e s₀` — output `.tprod .real s₀` (mirrors `pinv_raw`).
  · intro _ε e s₀ _h hd ih
    show ValExpr.inferSpace (.inv e) = .tprod .real s₀
    show (match ValExpr.inferSpace e with
          | ValSpace.tprod s0_ s1_ => ValSpace.tprod s1_ s0_
          | s_other => ValSpace.tprod .real s_other) = .tprod .real s₀
    rw [show ValExpr.inferSpace e = s₀ from ih]
    cases s₀ with
    | empty => rfl
    | real  => rfl
    | dsum _ _ => rfl
    | tprod a b => exact absurd rfl (hd a b)
    | ffs _ _ _ => rfl
  -- `.svds e s0 s1` — output `.tprod (.ffs cokernel … e) (.ffs image … e)`
  --   (mirrors `gsvdS`, single operand).
  · intro _ε e s0 s1 _he ihe
    show ValExpr.inferSpace (.svds e)
        = .tprod (.ffs .cokernel (.tprod s0 s1) e)
                 (.ffs .image    (.tprod s0 s1) e)
    show ValSpace.tprod
          (ValSpace.ffs .cokernel (ValExpr.inferSpace e) e)
          (ValSpace.ffs .image    (ValExpr.inferSpace e) e)
        = .tprod (.ffs .cokernel (.tprod s0 s1) e)
                 (.ffs .image    (.tprod s0 s1) e)
    rw [show ValExpr.inferSpace e = .tprod s0 s1 from ihe]

/-! ## Immediate corollaries. -/

theorem ValHasType.inferSpace_dof_le_of_space
    {orc : FFSOracle} {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (h : ValHasType ε e (.space s)) :
    ValSpace.dof orc (ValExpr.inferSpace e) ≤ ValSpace.dof orc s := by
  rw [ValHasType.inferSpace_eq_of_space h]

/-- **Dimension equality.** Stronger than the `≤` form; useful for
    rewriting `dof (inferSpace e)` to `dof s` in per-case `_sound`
    proofs that branch on the inferred split point. -/
theorem ValHasType.inferSpace_dof_eq_of_space
    {orc : FFSOracle} {ε : ValCtx} {e : ValExpr} {s : ValSpace}
    (h : ValHasType ε e (.space s)) :
    ValSpace.dof orc (ValExpr.inferSpace e) = ValSpace.dof orc s := by
  rw [ValHasType.inferSpace_eq_of_space h]

/-! ## Smoke tests.

These small lemmas exercise the API at the call sites the
`ValueSoundness.lean` per-case stubs will eventually consume them.
They confirm the lemma's shape composes with `denotB`'s
`inferSpace`-driven splits without further plumbing. -/

/-- For a well-typed `e : .space s`, the `dof` used by `.dsumE`'s
    denotation to compute the split point equals `dof s`. This is the
    exact rewrite `dsumE_sound` will perform. -/
theorem ValHasType.dsumE_split_dof_eq
    {orc : FFSOracle} {ε : ValCtx} {e₀ : ValExpr} {s₀ : ValSpace}
    (h : ValHasType ε e₀ (.space s₀)) :
    ValSpace.dof orc (ValExpr.inferSpace e₀) = ValSpace.dof orc s₀ :=
  ValHasType.inferSpace_dof_eq_of_space h

/-- For a well-typed `e : .space (.tprod s₀ s₁)`, `inferSpace e` is a
    `.tprod`. The `match`-on-`inferSpace` branches in
    `denotB (.vtrans …)`, `denotB (.ttv …)`, etc. all collapse to the
    `.tprod` arm. -/
theorem ValHasType.inferSpace_tprod_of_tprod
    {ε : ValCtx} {e : ValExpr} {s₀ s₁ : ValSpace}
    (h : ValHasType ε e (.space (.tprod s₀ s₁))) :
    ValExpr.inferSpace e = .tprod s₀ s₁ :=
  ValHasType.inferSpace_eq_of_space h

end GLang
