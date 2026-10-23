import GLang.Proofs.Value.Typing.ValueInferenceClosure
import GLang.Proofs.Value.Typing.ValueSumAt
/-
GLang.ValueRealizeLc — the value-realization local-closedness invariant.

`OpStep Ψ e b v → ValExpr.lc v` (and the `EvalS`/`EvalT`/`EvalBB` analogues),
given that `Ψ` stores locally-closed values (`EvalCtxLc Ψ`). This is the missing
realization invariant behind dependent value substitution: building an `ESubst`
for the dependent-preservation substitution needs `lc env₁` for the argument
realization, which has no other source.

The four judgments are mutually recursive, so this is one shared `EvalS.rec`
call with four motives (mirroring `eval_fv_joint`/`preservation_joint`). The
binder arms (`EvalT.piTy`, `OpStep.nllam`) extend the context with a fresh
`.var y τv₀`, which is `lc` iff `τv₀` is — supplied by the domain IH.
-/
import GLang.Operational.Ordinary

namespace GLang

/-- `Ψ` stores only locally-closed values. -/
def EvalCtxLc (Ψ : EvalCtx) : Prop :=
  ∀ k v, EvalCtx.lookup Ψ k = some v → ValExpr.lc v

/-- Extending an `EvalCtxLc` context with a `lc` value keeps it `EvalCtxLc`. -/
theorem EvalCtxLc.extend {Ψ : EvalCtx} {y : VName} {b : Basis} {v : ValExpr}
    (h : EvalCtxLc Ψ) (hv : ValExpr.lc v) :
    EvalCtxLc (EvalCtx.extend Ψ y b v) := by
  intro k v' hl
  by_cases hk : k = (y, b)
  · subst hk
    rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert, Option.some.injEq] at hl
    exact hl ▸ hv
  · rw [EvalCtx.extend, EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hk] at hl
    exact h k v' hl

theorem ValExpr.inferSpaceCtx_nil (e : ValExpr) :
    ValExpr.inferSpaceCtx [] e = ValExpr.inferSpace e := by
  apply ValExpr.rec
    (motive_1 := fun _ => True)
    (motive_2 := fun _ => True)
    (motive_3 := fun e => ValExpr.inferSpaceCtx [] e = ValExpr.inferSpace e)
    (motive_4 := fun es => ∀ e ∈ es,
      ValExpr.inferSpaceCtx [] e = ValExpr.inferSpace e)
  all_goals intros
  all_goals try trivial
  all_goals simp_all [ValExpr.inferSpaceCtx, ValExpr.inferSpace, ValExpr.inferTypeCtx_nil]
  case vsum =>
    rename_i s es ih
    cases es with
    | nil => rfl
    | cons head tail =>
        simpa only [ValExpr.inferSpaceCtx, ValExpr.inferSpace] using
          ih head (by simp)
  all_goals aesop

/-- Context-aware space inference preserves local closedness when run at the
empty de Bruijn context.  This is the regularity fact needed when an
operational rule records an expression's actual inferred space as a reshape
source annotation. -/
theorem ValExpr.lc.inferSpaceCtx_nil {e : ValExpr} (h : ValExpr.lc e) :
    ValSpace.lc (ValExpr.inferSpaceCtx [] e) := by
  exact h.rec
    (motive_1 := fun s _ => ValSpace.lc s)
    (motive_2 := fun τ _ => ValSpace.lc (ValTy.spaceOf τ))
    (motive_3 := fun e _ => ValSpace.lc (ValExpr.inferSpaceCtx [] e))
    (by exact .empty)
    (by exact .real)
    (by intros; rename_i ih₀ ih₁; exact .dsum ih₀ ih₁)
    (by intros; rename_i ih₀ ih₁; exact .tprod ih₀ ih₁)
    (by
      intros
      rename_i ihs _
      exact .ffs ihs (by assumption))
    (by intros; rename_i ih; exact ih)
    (by intros; exact .empty)
    (by intros; rename_i ih; exact ih)
    (by intros; exact .empty)
    (by intros; rename_i ih; exact ih)
    (by exact .real)
    (by intros; rename_i _ ih₁; exact ih₁)
    (by intros; rename_i ihs _ _; exact ihs)
    (by intros; rename_i ih₀ ih₁; exact .dsum ih₀ ih₁)
    (by intros; rename_i ih₀ ih₁; exact .tprod ih₀ ih₁)
    (by intros; rename_i ih; exact ih)
    (by intros; rename_i ih; exact .tprod ih ih)
    (by
      intro s es hs hes ihs ihes
      cases es with
      | nil => exact .empty
      | cons e es => exact ihes e (by simp))
    (by
      intros
      rename_i _ _ ih₀ _
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] _ with
      | tprod a b =>
          rw [heq] at ih₀
          cases ih₀ with
          | tprod ha hb => exact hb
      | empty | real | dsum | ffs => exact .real)
    (by
      intros
      rename_i _ _ ih₀ ih₁
      simp only [ValExpr.inferSpaceCtx]
      cases heq₀ : ValExpr.inferSpaceCtx [] _ with
      | tprod a b =>
          rw [heq₀] at ih₀
          cases ih₀ with
          | tprod ha hb =>
              cases heq₁ : ValExpr.inferSpaceCtx [] _ with
              | tprod c d =>
                  rw [heq₁] at ih₁
                  cases ih₁ with
                  | tprod hc hd => exact .tprod hc hb
              | empty | real | dsum | ffs => exact .empty
      | empty | real | dsum | ffs => exact .empty)
    (by
      intro f a hf ha _ _
      change ValSpace.lc (ValExpr.inferTypeCtx [] (.appV f a)).spaceOf
      rw [ValExpr.inferTypeCtx_nil]
      exact (ValExpr.lc.appV hf ha).inferType.spaceOf)
    (by
      intros
      rename_i ih₀ ih₁
      simp only [ValExpr.inferSpaceCtx]
      cases heq₀ : ValExpr.inferSpaceCtx [] _ with
      | tprod a b =>
          rw [heq₀] at ih₀
          cases ih₀ with
          | tprod ha hb =>
              cases heq₁ : ValExpr.inferSpaceCtx [] _ with
              | tprod c d =>
                  rw [heq₁] at ih₁
                  cases ih₁ with
                  | tprod hc hd => exact .tprod (.tprod ha hc) (.tprod hb hd)
              | empty | real | dsum | ffs => exact .empty
      | empty | real | dsum | ffs => exact .empty)
    (by
      intros
      rename_i ih₀ ih₁
      simp only [ValExpr.inferSpaceCtx]
      cases heq₀ : ValExpr.inferSpaceCtx [] _ with
      | tprod a b =>
          rw [heq₀] at ih₀
          cases ih₀ with
          | tprod ha hb =>
              cases heq₁ : ValExpr.inferSpaceCtx [] _ with
              | tprod c d =>
                  rw [heq₁] at ih₁
                  cases ih₁ with
                  | tprod hc hd => exact .tprod (.dsum ha hc) (.dsum hb hd)
              | empty | real | dsum | ffs => exact .empty
      | empty | real | dsum | ffs => exact .empty)
    (by intros; rename_i _ ihτ _; exact ihτ)
    (by
      intros
      rename_i ih
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] _ with
      | tprod a b =>
          rw [heq] at ih
          cases ih with
          | tprod ha hb => exact .tprod hb ha
      | empty | real | dsum | ffs => exact .empty)
    (by
      intro e a b he _ _ ihe _ _
      exact .tprod (.ffs ihe he) (.ffs ihe he))
    (by
      intro e a b he _ _ ihe _ _
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] e with
      | tprod s₀ s₁ =>
          rw [heq] at ihe
          cases ihe with
          | tprod hs₀ hs₁ => exact .tprod hs₀ (.ffs (.tprod hs₀ hs₁) he)
      | empty | real | dsum | ffs => exact .empty)
    (by
      intro e a b he _ _ ihe _ _
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] e with
      | tprod s₀ s₁ =>
          rw [heq] at ihe
          cases ihe with
          | tprod hs₀ hs₁ => exact .tprod hs₀ (.ffs (.tprod hs₀ hs₁) he)
      | empty | real | dsum | ffs => exact .empty)

    (by
      intro e a b he _ _ ihe _ _
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] e with
      | tprod s₀ s₁ =>
          rw [heq] at ihe
          cases ihe with
          | tprod hs₀ hs₁ => exact .tprod hs₁ (.ffs (.tprod hs₀ hs₁) he)
      | empty | real | dsum | ffs => exact .empty)
    (by
      intro e a b he _ _ ihe _ _
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] e with
      | tprod s₀ s₁ =>
          rw [heq] at ihe
          cases ihe with
          | tprod hs₀ hs₁ => exact .tprod hs₁ (.ffs (.tprod hs₀ hs₁) he)
      | empty | real | dsum | ffs => exact .empty)
    (by
      intro e he ihe
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] e with
      | tprod s₀ s₁ =>
          rw [heq] at ihe
          cases ihe with
          | tprod hs₀ hs₁ => exact .tprod hs₁ hs₀
      | empty => exact .tprod .real .empty
      | real => exact .tprod .real .real
      | dsum s₀ s₁ =>
          rw [heq] at ihe
          exact .tprod .real ihe
      | ffs p s w =>
          rw [heq] at ihe
          exact .tprod .real ihe)
    (by
      intro e a b he _ _ ihe _ _
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] e with
      | tprod s₀ s₁ =>
          rw [heq] at ihe
          cases ihe with
          | tprod hs₀ hs₁ => exact .tprod hs₁ hs₀
      | empty | real | dsum | ffs => exact .empty)
    (by
      intros
      rename_i _ ih₁
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] _ with
      | tprod s₀ s₁ =>
          rw [heq] at ih₁
          cases ih₁ with
          | tprod hs₀ hs₁ => exact .tprod hs₁ hs₀
      | empty | real | dsum | ffs => exact .empty)
    (by
      intro e he ihe
      simp only [ValExpr.inferSpaceCtx]
      cases heq : ValExpr.inferSpaceCtx [] e with
      | tprod s₀ s₁ =>
          rw [heq] at ihe
          cases ihe with
          | tprod hs₀ hs₁ => exact .tprod hs₁ hs₀
      | empty => exact .tprod .real .empty
      | real => exact .tprod .real .real
      | dsum s₀ s₁ =>
          rw [heq] at ihe
          exact .tprod .real ihe
      | ffs p s w =>
          rw [heq] at ihe
          exact .tprod .real ihe)
    (by
      intro e he ihe
      exact .tprod (.ffs ihe he) (.ffs ihe he))

/-- The canonical base-space reshape is locally closed whenever its payload
    and (shared source/target) space are locally closed. -/
theorem ValExpr.lc.reshapBase {e : ValExpr} {s : ValSpace}
    (he : ValExpr.lc e) (hs : ValSpace.lc s) :
    ValExpr.lc (ValExpr.reshapBase e s) :=
  .reshap he (.space hs) (.space hs)

/-- The composed canonical image conversion preserves local closure. -/
theorem ValExpr.lc.imageCoords {e : ValExpr} {s : ValSpace}
    (he : ValExpr.lc e) (hs : ValSpace.lc s) : ValExpr.lc (ValExpr.imageCoords s e) := by
  cases s <;> try exact .zero .empty
  case tprod s0 s1 =>
    cases hs with
    | tprod h0 h1 =>
      have hw := he.reshapBase (.tprod h0 h1)
      exact .mtm h1 h1 (.gsvdV hw (.idelta h0) (.idelta h1))
        (.mtm h0 h0 hw (.vtrans (.gsvdU hw (.idelta h0) (.idelta h1))))

/-- **The value-realization local-closedness invariant**, jointly over all four
    judgments. A value (space/type/env/value) produced by realization from a
    context that stores `lc` values is itself `lc`. Proved via the shared mutual
    recursor (four motives; the `EvalS`/`EvalT`/`EvalBB` motives establish `lc` of
    their outputs too). The binder arms (`EvalT.piTy`, `OpStep.nllam`) extend the
    context with a fresh `lc` `.var` (`EvalCtxLc.extend`). Each arm: `intros` grabs
    the constructor fields + IHs + `hlc`; `rename_i` names only the tail (IHs, then
    `hlc`). The skeleton (`first | exact h.rec …`) mirrors `eval_fv_joint`. -/
theorem realize_lc_joint :
    (∀ {Ψ s sv}, ValSpace.EvalS Ψ s sv → EvalCtxLc Ψ → ValSpace.lc sv)
  ∧ (∀ {Ψ τ τv}, ValTy.EvalT Ψ τ τv → EvalCtxLc Ψ → ValTy.lc τv)
  ∧ (∀ {Ψ b env b'}, Basis.EvalBB Ψ b env b' → EvalCtxLc Ψ → ValExpr.lc env)
  ∧ (∀ {Ψ e b v}, ValExpr.OpStep Ψ e b v → EvalCtxLc Ψ → ValExpr.lc v) := by
  refine ⟨@fun Ψ s sv h => ?_, @fun Ψ τ τv h => ?_, @fun Ψ b env b' h => ?_,
          @fun Ψ e b v h => ?_⟩
  all_goals
    first
    | exact h.rec
        (motive_1 := fun Ψ _ sv _ => EvalCtxLc Ψ → ValSpace.lc sv)
        (motive_2 := fun Ψ _ τv _ => EvalCtxLc Ψ → ValTy.lc τv)
        (motive_3 := fun Ψ _ env _ _ => EvalCtxLc Ψ → ValExpr.lc env)
        (motive_4 := fun Ψ _ _ v _ => EvalCtxLc Ψ → ValExpr.lc v)
        -- EvalS
        (by intros; intro hlc; exact .real)
        (by intros; intro hlc; exact .empty)
        (by intros; rename_i ih; intro hlc; exact ih hlc)
        (by intros; rename_i ih_he ih_hsvb; intro hlc;
            exact .ffs (ih_hsvb hlc) (.reshap (ih_he hlc)
              (.space (ih_hsvb hlc)) (.space (ih_hsvb hlc))))
        (by intros; rename_i ih_he ih_hsvb; intro hlc;
            exact .ffs (ih_hsvb hlc) (.reshap (ih_he hlc)
              (.space (ih_hsvb hlc)) (.space (ih_hsvb hlc))))
        (by intros; rename_i ih_he ih_hsvb; intro hlc;
            exact .ffs (ih_hsvb hlc) (.reshap (ih_he hlc)
              (.space (ih_hsvb hlc)) (.space (ih_hsvb hlc))))
        (by intros; rename_i ih_he ih_hsvb; intro hlc;
            exact .ffs (ih_hsvb hlc) (.reshap (ih_he hlc)
              (.space (ih_hsvb hlc)) (.space (ih_hsvb hlc))))
        (by intros; rename_i ih₀ ih₁; intro hlc; exact .tprod (ih₀ hlc) (ih₁ hlc))
        (by intros; rename_i ih₀ ih₁; intro hlc; exact .dsum (ih₀ hlc) (ih₁ hlc))
        -- EvalT
        (by intros; rename_i ih; intro hlc; exact .space (ih hlc))
        (by intros; rename_i ih_h₀ ih_h₁; intro hlc;
            exact .piTy _ (ih_h₀ hlc)
              (fun x hx => ih_h₁ x hx (EvalCtxLc.extend hlc (.var (ih_h₀ hlc)))))
        -- EvalBB
        (by intros; rename_i ih; intro hlc; exact .inv (ih hlc))
        (by intros; rename_i ih₀ ih₁ ih_sv; intro hlc;
            exact .mtm (ih_sv hlc) (ih_sv hlc) (ih₁ hlc)
              (.reshapBase (ih₀ hlc) (.tprod (ih_sv hlc) (ih_sv hlc))))
        (by intros; rename_i ih₀ ih₁; intro hlc; exact .vkrn (ih₀ hlc) (ih₁ hlc))
        (by intros; rename_i ih₀ ih₁; intro hlc; exact .vblk (ih₀ hlc) (ih₁ hlc))
        (by intros; rename_i ih; intro hlc; exact .vtrans (.inv (ih hlc)))
        (by intros; rename_i ih; intro hlc; exact ih hlc)
        (by intros; rename_i ih_he ih_hsvb; intro hlc;
            refine .reshap ((ih_he hlc).imageCoords (ih_hsvb hlc)) ?_ ?_
            · exact .space (.tprod
                (.ffs (ih_hsvb hlc) (.reshap (ih_he hlc)
                  (.space (ih_hsvb hlc)) (.space (ih_hsvb hlc))))
                (.ffs (ih_hsvb hlc) (.reshap (ih_he hlc)
                  (.space (ih_hsvb hlc)) (.space (ih_hsvb hlc)))))
            · exact .space (((ih_he hlc).imageCoords (ih_hsvb hlc)).inferSpaceCtx_nil))
        (by intros; rename_i ih_sv₀ ih_sv₁ ih_sv ih_sv' ih_sv₀' ih_cob ih_embd ih_proj;
            intro hlc;
            exact .mtm (ih_sv₀' hlc) (ih_sv₀' hlc)
              (.reshap (ih_proj hlc) (.space (.tprod (ih_sv₀' hlc) (ih_sv' hlc)))
                (.space (.tprod (ih_sv₀' hlc) (ih_sv' hlc))))
              (.mtm (ih_sv₀ hlc) (ih_sv₀ hlc)
                (.reshapBase (ih_cob hlc) (.tprod (ih_sv₀ hlc) (ih_sv₀' hlc)))
                (.reshap (ih_embd hlc) (.space (.tprod (ih_sv hlc) (ih_sv₀ hlc)))
                  (.space (.tprod (ih_sv hlc) (ih_sv₀ hlc))))))
        (by intros; rename_i ih_sv₀ ih_sv₁ ih_sv ih_sv' ih_sv₁' ih_cob ih_embd ih_proj;
            intro hlc;
            exact .mtm (ih_sv₁' hlc) (ih_sv₁' hlc)
              (.reshap (ih_proj hlc) (.space (.tprod (ih_sv₁' hlc) (ih_sv' hlc)))
                (.space (.tprod (ih_sv₁' hlc) (ih_sv' hlc))))
              (.mtm (ih_sv₁ hlc) (ih_sv₁ hlc)
                (.reshapBase (ih_cob hlc) (.tprod (ih_sv₁ hlc) (ih_sv₁' hlc)))
                (.reshap (ih_embd hlc) (.space (.tprod (ih_sv hlc) (ih_sv₁ hlc)))
                  (.space (.tprod (ih_sv hlc) (ih_sv₁ hlc))))))
        (by intros; rename_i ih_bb ih_ch ih_sv; intro hlc;
            exact .reshap
              (.rrefRep (ih_ch hlc)
                (.reshapBase (ih_bb hlc) (.tprod (ih_sv hlc) (ih_sv hlc))))
              (.space (.tprod (ih_sv hlc) (ih_sv hlc)))
              (.space (.tprod (ih_sv hlc) (ih_sv hlc))))
        -- refl (erratum-fix reflexivity): the idelta witness is lc via the
        -- realization IH.
        (by intros; rename_i ih; intro hlc;
            exact .reshap (.idelta (ih hlc)) (.space (.tprod (ih hlc) (ih hlc)))
              (.space (.tprod (ih hlc) (ih hlc))))
        -- proj_ker_coker_cod (P6a): 2-factor mtm sandwich — proj_ker_coker
        -- minus the COB factor.
        (by intros; rename_i ih_sv₀ ih_sv ih_sv' ih_embd ih_proj; intro hlc;
            exact .mtm (ih_sv₀ hlc) (ih_sv₀ hlc)
              (.reshap (ih_proj hlc) (.space (.tprod (ih_sv₀ hlc) (ih_sv' hlc)))
                (.space (.tprod (ih_sv₀ hlc) (ih_sv' hlc))))
              (.reshap (ih_embd hlc) (.space (.tprod (ih_sv hlc) (ih_sv₀ hlc)))
                (.space (.tprod (ih_sv hlc) (ih_sv₀ hlc)))))
        -- proj_img_coimg_dom (P6a): codomain mirror of proj_ker_coker_cod.
        (by intros; rename_i ih_sv₁ ih_sv ih_sv' ih_embd ih_proj; intro hlc;
            exact .mtm (ih_sv₁ hlc) (ih_sv₁ hlc)
              (.reshap (ih_proj hlc) (.space (.tprod (ih_sv₁ hlc) (ih_sv' hlc)))
                (.space (.tprod (ih_sv₁ hlc) (ih_sv' hlc))))
              (.reshap (ih_embd hlc) (.space (.tprod (ih_sv hlc) (ih_sv₁ hlc)))
                (.space (.tprod (ih_sv hlc) (ih_sv₁ hlc)))))
        -- OpStep
        (by intros; rename_i hlk; intro hlc; exact hlc _ _ hlk)
        (by intros; rename_i ih_he ih_hbb ih_hes; intro hlc;
            exact .ttv (ih_hes hlc)
              (.reshapBase (ih_hbb hlc) (.tprod (ih_hes hlc) (ih_hes hlc)))
              (.reshapBase (ih_he hlc) (ih_hes hlc)))
        (by intros; rename_i ih₀ ih₁; intro hlc; exact .scale (ih₀ hlc) (ih₁ hlc))
        (by intros; rename_i ih_s ih₀ ih₁; intro hlc;
            exact .vadd (ih_s hlc) (ih₀ hlc) (ih₁ hlc))
        (by intros; rename_i ih₀ ih₁; intro hlc; exact .dsumE (ih₀ hlc) (ih₁ hlc))
        (by intros; rename_i ih₀ ih₁; intro hlc; exact .tprodE (ih₀ hlc) (ih₁ hlc))
        (by intros; rename_i ih_he; intro hlc; exact .pinv (ih_he hlc))
        -- pinvT_gpinv (E3: Gram slots domain-first).
        (by intros; rename_i ih_he ih_hi₀ ih_hi₁; intro hlc;
            exact .gpinv (ih_he hlc) (ih_hi₁ hlc) (ih_hi₀ hlc))
        -- pinvD_std / pinvD_gpinv (E4/E7: operand reshaped to `sv₁ ⊗ ℝ`).
        (by intros; rename_i ih_he ih_hsv; intro hlc;
            exact .pinv (.reshap (ih_he hlc) (.space (.tprod (ih_hsv hlc) .real))
              (.space (ih_hsv hlc))))
        (by intros; rename_i ih_he ih_hi₀ ih_hi₁ ih_hsv; intro hlc;
            exact .gpinv (.reshap (ih_he hlc) (.space (.tprod (ih_hsv hlc) .real))
              (.space (ih_hsv hlc)))
              (ih_hi₁ hlc) (ih_hi₀ hlc))
        (by intros; rename_i ih_hsv; intro hlc; exact .idelta (ih_hsv hlc))
        -- embed_* (E1/E2: transposed GSVD blocks).
        (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hlc;
            exact .vtrans (.gsvdUI (ih_he hlc) (ih_hi₀ hlc) (ih_hi₁ hlc)))
        (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hlc;
            exact .vtrans (.gsvdU (ih_he hlc) (ih_hi₀ hlc) (ih_hi₁ hlc)))
        (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hlc;
            exact .vtrans (.gsvdV (ih_he hlc) (ih_hi₀ hlc) (ih_hi₁ hlc)))
        (by intros; rename_i ih_hi₀ ih_hi₁ ih_he; intro hlc;
            exact .vtrans (.gsvdVI (ih_he hlc) (ih_hi₀ hlc) (ih_hi₁ hlc)))
        (by intros; rename_i ih_h₀ ih_hsv₀ ih_h₁ ih_hsv₁; intro hlc;
            exact .reshapBase
              (.ttv (ih_hsv₀ hlc) (ih_h₀ hlc) (ih_h₁ hlc))
              (ih_hsv₁ hlc))
        -- appI_lin (E7: functional reshaped to `sv ⊗ ℝ`).
        (by intros; rename_i ih_h₀ ih_hsv ih_h₁; intro hlc;
            exact .ttv (ih_hsv hlc)
              (.reshap (ih_h₀ hlc) (.space (.tprod (ih_hsv hlc) .real))
                (.space (ih_hsv hlc))) (ih_h₁ hlc))
        (by intros; rename_i ih_h₀ ih_he ih_h₁; intro hlc;
            exact .vlam _ (ih_h₀ hlc)
              (fun x hx => ih_h₁ x hx (EvalCtxLc.extend hlc (.var (ih_h₀ hlc))))
              (fun x hx => .reshap
                (ih_he x hx (EvalCtxLc.extend hlc (.var (ih_h₀ hlc))))
                (ih_h₁ x hx (EvalCtxLc.extend hlc (.var (ih_h₀ hlc))))
                (ih_h₁ x hx (EvalCtxLc.extend hlc (.var (ih_h₀ hlc))))))
        (by intros; rename_i ih_h₀ ih_h₁ ih_hout; intro hlc;
            have hc : ValExpr.lc (.applyValue _ _) := .appV (ih_h₀ hlc)
              (.reshap (ih_h₁ hlc) (ih_h₀ hlc).inferType.domain (ih_h₁ hlc).inferType)
            exact .reshap hc (ih_hout hlc) hc.inferType)
        -- frame_reanchor: the leev/τv₀' components are closed (`lc` via their
        -- IHs), so the body-opening is identity on them (`openRec_lc`); the
        -- bvar-bound components come from the cofinite IHs.
        (by intro Ψ b₀ b₀' b₁ n₀ leev env₁ τv₀ τv₀' τv₁' h₀ htof hfn hdom L hx hcod
              ih_h₀ ih_hfn ih_hdom ih_hx ih_hcod
            intro hlc
            refine .vlam L (ih_h₀ hlc)
              (fun y hy => ih_hcod y hy (EvalCtxLc.extend hlc (.var (ih_h₀ hlc))))
              (fun y hy => ?_)
            have hcl : EvalCtxLc (EvalCtx.extend Ψ y b₀ (.var y τv₀)) :=
              EvalCtxLc.extend hlc (.var (ih_h₀ hlc))
            have hf := ih_hfn hlc
            have hd := ih_hdom hlc
            simp only [ValExpr.openVar, ValExpr.applyValue, ValExpr.openRec,
              ValExpr.inferType, ValExpr.openRec_lc hf, ValTy.openRec_lc hd,
              ValTy.openRec_lc hf.inferType.domain]
            exact .reshap (.appV hf
                (.reshap (.reshap (ih_hx y hy hcl) hd hd) hf.inferType.domain hd))
              (ih_hcod y hy hcl) (ih_hcod y hy hcl))
        -- frame_eta: identical shape to the nllam arm.
        (by intros; rename_i ih_h₀ ih_he ih_h₁; intro hlc;
            exact .vlam _ (ih_h₀ hlc)
              (fun y hy => ih_h₁ y hy (EvalCtxLc.extend hlc (.var (ih_h₀ hlc))))
              (fun y hy => .reshap
                (ih_he y hy (EvalCtxLc.extend hlc (.var (ih_h₀ hlc))))
                (ih_h₁ y hy (EvalCtxLc.extend hlc (.var (ih_h₀ hlc))))
                (ih_h₁ y hy (EvalCtxLc.extend hlc (.var (ih_h₀ hlc))))))
        (by intros; rename_i ih_he ih_hsrc ih_htgt; intro hlc;
            exact .reshap (ih_he hlc) (ih_htgt hlc) (ih_hsrc hlc))
        -- llam_assemble: every summand is lc — `δᵢ` from the index-space IH,
        -- the body factor from the family IH at one fresh `y` (env i is
        -- y-independent), the reshape annotation from the codomain-space IH;
        -- the outer S1 space annotation from both space IHs.
        (by intro Ψ b' b e sv' sv env htof' hsv' hsv L hfam ih_hsv' ih_hsv ih_hfam
            intro hlc
            refine .sumAt ?_ (.tprod (ih_hsv' hlc) (ih_hsv hlc))
            refine .vsum (ih_hsv' hlc) (fun el hel => ?_)
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hel
            obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset L
            exact .tprodE (.delta (ih_hsv' hlc))
              (.reshap (ih_hfam y hy i (EvalCtxLc.extend hlc (.delta (ih_hsv' hlc))))
                (.space (ih_hsv hlc)) (.space (ih_hsv hlc))))
        (by intro Ψ b' e sv' env htof' hsv' L hfam ih_hsv' ih_hfam
            intro hlc
            refine .sumAt ?_ (ih_hsv' hlc)
            refine .vsum (ih_hsv' hlc) (fun el hel => ?_)
            obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hel
            obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset L
            exact .scale
              (.reshap (ih_hfam y hy i (EvalCtxLc.extend hlc (.delta (ih_hsv' hlc))))
                (.space .real) (.space .real))
              (.delta (ih_hsv' hlc)))
        -- zero (erratum-fix literal): lc of the realized index space.
        (by intros; rename_i ih; intro hlc; exact .zero (ih hlc))
        -- rlit (erratum-fix literal): a literal is lc.
        (by intros; intro _hlc; exact .rlit)

/-- Realization of a type from an `lc`-storing context yields an `lc` type.
    (Projection of `realize_lc_joint`; the domain feeder for
    `evalCtxValidPlus_extend`.) -/
theorem evalT_lc {Ψ : EvalCtx} {τ : Ty} {τv : ValTy}
    (h : ValTy.EvalT Ψ τ τv) : EvalCtxLc Ψ → ValTy.lc τv :=
  realize_lc_joint.2.1 h

/-- A value produced by an `OpStep` from a context that stores `lc` values is
    itself `lc`. (Projection of `realize_lc_joint`.) -/
theorem opStep_lc {Ψ : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ e b v) : EvalCtxLc Ψ → ValExpr.lc v :=
  realize_lc_joint.2.2.2 h

end GLang
