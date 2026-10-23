/- Ordinary operational semantics. The four mutually inductive judgments compile
source spaces (`EvalS`), types (`EvalT`), changes of basis (`EvalBB`), and terms
(`OpStep`) to value syntax. `EvalCtx` maps variable/basis pairs to value programs.
Checked judgments retain source typing and basis validity and erase to these
ordinary judgments. Execution is specified by the partial value denotation. -/

import GLang.Annotated.Binding
import GLang.Value.Binding
import GLang.Proofs.Basis.Binding
import GLang.Numerics.SVD.ValueImageCoords
import Mathlib.Data.Finmap

namespace GLang

/-! The evaluation context maps variable/basis pairs to value expressions. -/

/-- Classical equality on bases, used for finite-map keys. -/
noncomputable scoped instance instDecidableEqBasis : DecidableEq Basis :=
  Classical.decEq Basis

abbrev EvalCtx : Type := @Finmap (VName × Basis) (fun _ => ValExpr)

noncomputable def EvalCtx.lookup (Ψ : EvalCtx) (xb : VName × Basis) : Option ValExpr :=
  Finmap.lookup xb Ψ

noncomputable def EvalCtx.extend (Ψ : EvalCtx) (x : VName) (b : Basis) (v : ValExpr) :
    EvalCtx :=
  Finmap.insert (x, b) v Ψ

/-- `EvalCtx.avoid Ψ` collects every name appearing in `Ψ`: the key-NAMES
(`Ψ.keys.image Prod.fst`) and the `allNames` of every `Ψ`-entry value (a finite
`biUnion` over the keys, reading each value off `Ψ.lookup`). -/
noncomputable def EvalCtx.avoid (Ψ : EvalCtx) : Finset VName :=
  Ψ.keys.image Prod.fst ∪
    Ψ.keys.biUnion (fun kb => (Ψ.lookup kb).elim ∅ ValExpr.fv)

/-- Avoiding `EvalCtx.avoid Ψ` discharges both freshness facts the binder
co-extension needs: the name is fresh as a KEY (no `(y,b)` in `Ψ`) and fresh in
every entry VALUE. -/
theorem EvalCtx.avoid_spec {Ψ : EvalCtx} {y : VName} (hy : y ∉ EvalCtx.avoid Ψ) :
    (∀ b, (y, b) ∉ Ψ) ∧
    (∀ k v, Ψ.lookup k = some v → y ∉ ValExpr.fv v) := by
  rw [EvalCtx.avoid, Finset.mem_union, not_or] at hy
  obtain ⟨hkeys, hvals⟩ := hy
  constructor
  · intro b hmem
    exact hkeys (Finset.mem_image.mpr ⟨(y, b), Finmap.mem_keys.mpr hmem, rfl⟩)
  · intro k v hl hmem
    refine hvals (Finset.mem_biUnion.mpr ⟨k, Finmap.mem_keys.mpr ?_, ?_⟩)
    · exact Finmap.mem_iff.mpr ⟨v, hl⟩
    · rw [hl]; exact hmem

/-- Every value-language expression is a value form. -/
def ValExpr.IsValue (_ : ValExpr) : Prop := True

@[simp] theorem ValExpr.IsValue_def (e : ValExpr) :
    ValExpr.IsValue e ↔ True := Iff.rfl

theorem ValExpr.isValue (e : ValExpr) : ValExpr.IsValue e := trivial

theorem ValExpr.isValue_appV (e₀ e₁ : ValExpr) (τ : ValTy) :
    ValExpr.IsValue (.appV e₀ e₁) := trivial

theorem ValExpr.isValue_mtm (n₀ n₁ : Nat) (s₀ s₁ : ValSpace)
    (e₀ e₁ : ValExpr) : ValExpr.IsValue (.mtm n₀ n₁ s₀ s₁ e₀ e₁) := trivial

theorem ValExpr.isValue_pinv (e : ValExpr) :
    ValExpr.IsValue (.pinv e) := trivial

def Basis.isStd : Basis → Prop
  | .empty           => True
  | .one             => True
  | .dual b          => Basis.isStd b
  | .dsum b₀ b₁      => Basis.isStd b₀ ∧ Basis.isStd b₁
  | .tprod b₀ b₁     => Basis.isStd b₀ ∧ Basis.isStd b₁
  | .proj _ b₀ b₁    => Basis.isStd b₀ ∧ Basis.isStd b₁
  | .image _         => False
  | .terms _ _ _     => False
  | .frame b₀ b₁     => Basis.isStd b₀ ∧ Basis.isStd b₁

mutual

inductive ValSpace.EvalS : EvalCtx → Space → ValSpace → Prop where

  | real {Ψ : EvalCtx} : ValSpace.EvalS Ψ .real .real

  | empty {Ψ : EvalCtx} : ValSpace.EvalS Ψ .empty .empty

  | dual {Ψ : EvalCtx} {s : Space} {sv : ValSpace}
      (h : ValSpace.EvalS Ψ s sv) :
      ValSpace.EvalS Ψ (.dual s) sv

  | ker {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {b : Basis}
        {leev : ValExpr} {svb : ValSpace}
      (he   : ValExpr.OpStep Ψ e b leev)
      (hb   : Basis.sof b = .tprod (.dual s₀) s₁)
      (hcompat : Basis.FFSMatrixCompatible b)
      (hsvb : ValSpace.EvalS Ψ (Basis.sof b) svb) :
      ValSpace.EvalS Ψ (.ker s₀ s₁ e)
        (.ffs .kernel svb (.reshap leev (.space svb) (.space svb)))

  | coker {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {b : Basis}
          {leev : ValExpr} {svb : ValSpace}
      (he   : ValExpr.OpStep Ψ e b leev)
      (hb   : Basis.sof b = .tprod (.dual s₀) s₁)
      (hcompat : Basis.FFSMatrixCompatible b)
      (hsvb : ValSpace.EvalS Ψ (Basis.sof b) svb) :
      ValSpace.EvalS Ψ (.coker s₀ s₁ e)
        (.ffs .cokernel svb (.reshap leev (.space svb) (.space svb)))

  | img {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {b : Basis}
        {leev : ValExpr} {svb : ValSpace}
      (he   : ValExpr.OpStep Ψ e b leev)
      (hb   : Basis.sof b = .tprod (.dual s₀) s₁)
      (hcompat : Basis.FFSMatrixCompatible b)
      (hsvb : ValSpace.EvalS Ψ (Basis.sof b) svb) :
      ValSpace.EvalS Ψ (.img s₀ s₁ e)
        (.ffs .image svb (.reshap leev (.space svb) (.space svb)))

  | coimg {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {b : Basis}
          {leev : ValExpr} {svb : ValSpace}
      (he   : ValExpr.OpStep Ψ e b leev)
      (hb   : Basis.sof b = .tprod (.dual s₀) s₁)
      (hcompat : Basis.FFSMatrixCompatible b)
      (hsvb : ValSpace.EvalS Ψ (Basis.sof b) svb) :
      ValSpace.EvalS Ψ (.coimg s₀ s₁ e)
        (.ffs .coimage svb (.reshap leev (.space svb) (.space svb)))

  | tprod {Ψ : EvalCtx} {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace}
      (h₀ : ValSpace.EvalS Ψ s₀ sv₀)
      (h₁ : ValSpace.EvalS Ψ s₁ sv₁) :
      ValSpace.EvalS Ψ (.tprod s₀ s₁) (.tprod sv₀ sv₁)

  | dsum {Ψ : EvalCtx} {s₀ s₁ : Space} {sv₀ sv₁ : ValSpace}
      (h₀ : ValSpace.EvalS Ψ s₀ sv₀)
      (h₁ : ValSpace.EvalS Ψ s₁ sv₁) :
      ValSpace.EvalS Ψ (.dsum s₀ s₁) (.dsum sv₀ sv₁)

inductive ValTy.EvalT : EvalCtx → Ty → ValTy → Prop where
  /-- A space evaluates as a type via its `EvalS` value space. -/
  | space {Ψ : EvalCtx} {s : Space} {sv : ValSpace}
      (h : ValSpace.EvalS Ψ s sv) :
      ValTy.EvalT Ψ (.space s) (.space sv)

  | piTy {Ψ : EvalCtx} {b₀ : Basis} {τ₀ τ₁ : Ty}
         {τv₀ τv₁ : ValTy}
      (h₀ : ValTy.EvalT Ψ τ₀ τv₀)
      (hb : Basis.tof b₀ = τ₀)

      -- COFINITELY-many fresh binder names `y`. LN: the SOURCE codomain `τ₁` binds
      -- `bvar 0` and is opened by `Ty.openVar y`; the VALUE codomain `τv₁` is
      -- locally-nameless and opened by `ValTy.openVar y τv₀`.
      (L : Finset VName)
      (h₁ : ∀ y, y ∉ L → ValTy.EvalT (Ψ.extend y b₀ (.var y τv₀))
              (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁)) :

      ValTy.EvalT Ψ (.piTy τ₀ τ₁) (.piTy τv₀ τv₁)

inductive Basis.EvalBB : EvalCtx → Basis → ValExpr → Basis → Prop where

  | inverse {Ψ : EvalCtx} {b₀ b₁ : Basis} {leev : ValExpr}
      (h : Basis.EvalBB Ψ b₁ leev b₀) :
      Basis.EvalBB Ψ b₀ (.inv leev) b₁

  | trans {Ψ : EvalCtx} {b₀ b₁ b₂ : Basis} {env₀ env₁ : ValExpr}
          {sv : ValSpace}
      (h₀ : Basis.EvalBB Ψ b₀ env₀ b₁)
      (h₁ : Basis.EvalBB Ψ b₁ env₁ b₂)
      (hsv : ValSpace.EvalS Ψ (Basis.sof b₀) sv) :

      -- erroneous (`sv⊗sv`); the `mtm` typing rule pins it to `env₀`'s inner
      -- edge, which is `sv` (`env₀` is a basis-change matrix `sv⊗sv`). Since
      -- `EvalS` is FFS-non-deterministic, `env₀`'s typed realization need not
      -- literally be `sv⊗sv`, so we RESHAPE `env₀` to the canonical `sv⊗sv`
      -- (the `reshap_cob` coercion, §9.17 — sound by FFS dimension-invariance).
      Basis.EvalBB Ψ b₀
        (.mtm 0 0 sv sv env₁ (.reshapBase env₀ (.tprod sv sv))) b₂

  | tprod {Ψ : EvalCtx} {b₀ b₁ b₀' b₁' : Basis} {env₀ env₁ : ValExpr}
      (h₀ : Basis.EvalBB Ψ b₀' env₀ b₀)
      (h₁ : Basis.EvalBB Ψ b₁' env₁ b₁) :
      Basis.EvalBB Ψ (.tprod b₀' b₁') (.vkrn env₀ env₁) (.tprod b₀ b₁)

  | dsum {Ψ : EvalCtx} {b₀ b₁ b₀' b₁' : Basis} {env₀ env₁ : ValExpr}
      (h₀ : Basis.EvalBB Ψ b₀' env₀ b₀)
      (h₁ : Basis.EvalBB Ψ b₁' env₁ b₁) :
      Basis.EvalBB Ψ (.dsum b₀' b₁') (.vblk env₀ env₁) (.dsum b₀ b₁)

  | dual_std {Ψ : EvalCtx} {b₀ : Basis} {leev : ValExpr}

      -- dualized), so `std (tof b₀) = stdSpace (sof b₀)` reduces — needed for
      -- preservation to thread basis-validity through this arm.
      (htof : Basis.tof b₀ = .space (Basis.sof b₀))
      (hb₁ : Basis.EvalBB Ψ b₀ leev (Basis.std (Basis.tof b₀))) :
      Basis.EvalBB Ψ (.dual b₀) (.vtrans (.inv leev))
        (Basis.std (Basis.tof (.dual b₀)))

  | image {Ψ : EvalCtx} {b₀ b₀' : Basis} {leev : ValExpr}

      (hcoker : ∃ s₀ s₁ e, Basis.sof b₀ = .coker s₀ s₁ e)
      (h : Basis.EvalBB Ψ b₀ leev b₀') :
      Basis.EvalBB Ψ (.image b₀) leev (.image b₀')
  /-- **Image-from-cokernel coordinate conversion.** In standard ambient
      bases, convert the image of the canonical cokernel basis into the
      independently canonical image basis. `imageCoords` computes the full
      signed matrix by two tensor contractions; a positive singular-value
      diagonal alone does not identify these independent basis choices.
      The outer reshape retains the canonical FFS result annotations. -/
  | image_svds {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
               {leev : ValExpr} {s₀ s₁ : Space} {svb : ValSpace}
      (hs₀ : Basis.sof b₀ = s₀)
      (hs₁ : Basis.sof b₁ = s₁)
      (hb₀ : Basis.isStd b₀)
      (hb₁ : Basis.isStd b₁)
      (he  : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) leev)
      (hsvb : ValSpace.EvalS Ψ (Basis.sof (.tprod (.dual b₀) b₁)) svb) :
      Basis.EvalBB Ψ
        (.image (.proj (.coker s₀ s₁ e) b₀ b₁))
        (.reshap (.imageCoords svb leev)
          (.space (.tprod
            (.ffs .cokernel svb (.reshap leev (.space svb) (.space svb)))
            (.ffs .image svb (.reshap leev (.space svb) (.space svb)))))
          (.space (ValExpr.inferSpaceCtx [] (.imageCoords svb leev))))
        (.proj (.img s₀ s₁ e) b₀ b₁)

  | proj_ker_coker {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {s : Space}
      {b₀ b₁ b₀' : Basis} {env₁ env₂ env₃ : ValExpr}
      {sv₀ sv₁ sv sv' sv₀' : ValSpace}
      (hs    : s = Space.ker s₀ s₁ e ∨ s = Space.coker s₀ s₁ e)

      (hsofb₀ : Basis.sof b₀ = s₀)
      (hsofb₁ : Basis.sof b₁ = s₁)
      (hsv₀  : ValSpace.EvalS Ψ (Basis.sof b₀) sv₀)
      (hsv₁  : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
      (hsv   : ValSpace.EvalS Ψ s sv)
      (hsv'  : ValSpace.EvalS Ψ s sv')
      (hsv₀' : ValSpace.EvalS Ψ (Basis.sof b₀') sv₀')
      (hcob  : Basis.EvalBB Ψ b₀ env₂ b₀')
      (hembd : ValExpr.OpStep Ψ (Term.lembd s)
                 (.tprod (.dual (.proj s b₀ b₁)) b₀) env₃)
      (hproj : ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₀'))
                 (.tprod (.dual b₀') (.proj s b₀' b₁)) env₁) :
      Basis.EvalBB Ψ (.proj s b₀ b₁)
        (.mtm 0 0 sv₀' sv₀'
          (.reshap env₁ (.space (.tprod sv₀' sv')) (.space (.tprod sv₀' sv')))
          (.mtm 0 0 sv₀ sv₀ (.reshapBase env₂ (.tprod sv₀ sv₀'))
            (.reshap env₃ (.space (.tprod sv sv₀)) (.space (.tprod sv sv₀)))))
        (.proj s b₀' b₁)

  -- codomain-side conversion — mirror of `proj_ker_coker`'s `b₁ = b₁'`).
  | proj_img_coimg {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {s : Space}
      {b₀ b₁ b₁' : Basis} {env₁ env₂ env₃ : ValExpr}
      {sv₀ sv₁ sv sv' sv₁' : ValSpace}
      (hs    : s = Space.img s₀ s₁ e ∨ s = Space.coimg s₀ s₁ e)
      -- Sub-basis/ambient-space alignment (see `proj_ker_coker`).
      (hsofb₀ : Basis.sof b₀ = s₀)
      (hsofb₁ : Basis.sof b₁ = s₁)
      (hsv₀  : ValSpace.EvalS Ψ (Basis.sof b₀) sv₀)
      (hsv₁  : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
      (hsv   : ValSpace.EvalS Ψ s sv)
      (hsv'  : ValSpace.EvalS Ψ s sv')
      (hsv₁' : ValSpace.EvalS Ψ (Basis.sof b₁') sv₁')
      (hcob  : Basis.EvalBB Ψ b₁ env₂ b₁')
      (hembd : ValExpr.OpStep Ψ (Term.lembd s)
                 (.tprod (.dual (.proj s b₀ b₁)) b₁) env₃)
      (hproj : ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₁'))
                 (.tprod (.dual b₁') (.proj s b₀ b₁')) env₁) :
      Basis.EvalBB Ψ (.proj s b₀ b₁)
        (.mtm 0 0 sv₁' sv₁'
          (.reshap env₁ (.space (.tprod sv₁' sv')) (.space (.tprod sv₁' sv')))
          (.mtm 0 0 sv₁ sv₁ (.reshapBase env₂ (.tprod sv₁ sv₁'))
            (.reshap env₃ (.space (.tprod sv sv₁)) (.space (.tprod sv sv₁)))))
        (.proj s b₀ b₁')

  | terms_rref {Ψ : EvalCtx} {b b' : Basis} {e : Term} {es : List Term}
               {env₀ env₁ : ValExpr} {sv : ValSpace}
      (hbb : Basis.EvalBB Ψ b env₁ b')
      (hch : ValExpr.OpStep Ψ (Term.dsumChain e es)
               (Basis.dsumChain b' es.length) env₀)
      (hsv : ValSpace.EvalS Ψ (Basis.sof b) sv) :
      Basis.EvalBB Ψ b
        (.reshap (.rrefRep env₀ (.reshapBase env₁ (.tprod sv sv)))
          (.space (.tprod sv sv)) (.space (.tprod sv sv)))
        (.terms (Basis.sof b') (e :: es) b')

  -- canonical `sv ⊗ sv` realization (§9.17 reshape-to-canonical device) so its
  -- `inferType` is STRUCTURALLY `.space (.tprod sv sv)` and the
  -- `preservation_cob` arm (`CobShapeT`) is read-off; `htof` pins `b` to a
  -- SPACE basis (a COB is between space bases — §9.16 device).
  | refl {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
      (htof : Basis.tof b = .space (Basis.sof b))
      (hsv  : ValSpace.EvalS Ψ (Basis.sof b) sv) :
      Basis.EvalBB Ψ b
        (.reshap (.idelta sv) (.space (.tprod sv sv)) (.space (.tprod sv sv))) b
  /-- **Projected-basis ker/coker conversion, CODOMAIN side** (progress plan
      P6a). -/

  | proj_ker_coker_cod {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {s : Space}
      {b₀ b₁ b₁' : Basis} {env₁ env₃ : ValExpr} {sv₀ sv sv' : ValSpace}
      (hs : s = Space.ker s₀ s₁ e ∨ s = Space.coker s₀ s₁ e)
      -- Sub-basis/ambient-space alignment (see `proj_ker_coker`).
      (hsofb₀ : Basis.sof b₀ = s₀)
      (hsofb₁ : Basis.sof b₁ = s₁)
      (hsofb₁' : Basis.sof b₁' = s₁)
      (hsv₀ : ValSpace.EvalS Ψ (Basis.sof b₀) sv₀)
      (hsv  : ValSpace.EvalS Ψ s sv)
      (hsv' : ValSpace.EvalS Ψ s sv')
      (hembd : ValExpr.OpStep Ψ (Term.lembd s)
                 (.tprod (.dual (.proj s b₀ b₁)) b₀) env₃)
      (hproj : ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₀))
                 (.tprod (.dual b₀) (.proj s b₀ b₁')) env₁) :
      Basis.EvalBB Ψ (.proj s b₀ b₁)
        (.mtm 0 0 sv₀ sv₀
          (.reshap env₁ (.space (.tprod sv₀ sv')) (.space (.tprod sv₀ sv')))
          (.reshap env₃ (.space (.tprod sv sv₀)) (.space (.tprod sv sv₀))))
        (.proj s b₀ b₁')

  | proj_img_coimg_dom {Ψ : EvalCtx} {s₀ s₁ : Space} {e : Term} {s : Space}
      {b₀ b₁ b₀' : Basis} {env₁ env₃ : ValExpr} {sv₁ sv sv' : ValSpace}
      (hs : s = Space.img s₀ s₁ e ∨ s = Space.coimg s₀ s₁ e)
      -- Sub-basis/ambient-space alignment (see `proj_ker_coker`).
      (hsofb₀ : Basis.sof b₀ = s₀)
      (hsofb₁ : Basis.sof b₁ = s₁)
      (hsofb₀' : Basis.sof b₀' = s₀)
      (hsv₁ : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
      (hsv  : ValSpace.EvalS Ψ s sv)
      (hsv' : ValSpace.EvalS Ψ s sv')
      (hembd : ValExpr.OpStep Ψ (Term.lembd s)
                 (.tprod (.dual (.proj s b₀ b₁)) b₁) env₃)
      (hproj : ValExpr.OpStep Ψ (Term.lproj s (Basis.sof b₁))
                 (.tprod (.dual b₁) (.proj s b₀' b₁)) env₁) :
      Basis.EvalBB Ψ (.proj s b₀ b₁)
        (.mtm 0 0 sv₁ sv₁
          (.reshap env₁ (.space (.tprod sv₁ sv')) (.space (.tprod sv₁ sv')))
          (.reshap env₃ (.space (.tprod sv sv₁)) (.space (.tprod sv sv₁))))
        (.proj s b₀' b₁)

inductive ValExpr.OpStep : EvalCtx → Term → Basis → ValExpr → Prop where

  | var {Ψ : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
      (h : EvalCtx.lookup Ψ (x, b) = some v) :
      ValExpr.OpStep Ψ (.var x) b v

  -- (1) basis-kind premises `htof₀`/`htof₁` make `b₀`/`b₁` SPACE bases (a COB is
  -- between space bases), so `tof bᵢ = .space (sof bᵢ)` reduces — needed for
  -- preservation to retarget the source typing across `sof b₀ = sof b₁` and to
  -- type the result at `.space sv`. (2) the operands are RESHAPED to the
  -- canonical realization `sv` of `sof b₀ = sof b₁` (the COB matrix `env₀` to
  -- `sv⊗sv`, the vector `v` to `sv`), since `EvalS` is FFS-non-deterministic so
  -- `env₀`'s/`v`'s typed realizations need not literally be `sv` — sound by FFS
  -- dimension-invariance, blast-radius operational-only.
  | cob {Ψ : EvalCtx} {e : Term} {b₀ b₁ : Basis}
        {v env₀ : ValExpr} {sv : ValSpace}
      (htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
      (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
      (he   : ValExpr.OpStep Ψ e b₁ v)
      (hbb  : Basis.EvalBB Ψ b₁ env₀ b₀)
      (hes  : ValSpace.EvalS Ψ (Basis.sof b₀) sv) :
      ValExpr.OpStep Ψ e b₀
        (.ttv sv (.reshapBase env₀ (.tprod sv sv)) (.reshapBase v sv))

  | scale {Ψ : EvalCtx} {e₀ e₁ : Term} {b : Basis} {v₀ v₁ : ValExpr}
      (he₀ : ValExpr.OpStep Ψ e₀ .one v₀)
      (he₁ : ValExpr.OpStep Ψ e₁ b   v₁) :
      ValExpr.OpStep Ψ (.smul e₀ e₁) b (.scale v₀ v₁)

  | add {Ψ : EvalCtx} {e₀ e₁ : Term} {b : Basis} {sv : ValSpace}
      {v₀ v₁ : ValExpr}
      (htof : Basis.tof b = .space (Basis.sof b))
      (hsv : ValSpace.EvalS Ψ (Basis.sof b) sv)
      (he₀ : ValExpr.OpStep Ψ e₀ b v₀)
      (he₁ : ValExpr.OpStep Ψ e₁ b v₁) :
      ValExpr.OpStep Ψ (.add e₀ e₁) b (.vadd sv v₀ v₁)

  | dsumE {Ψ : EvalCtx} {e₀ e₁ : Term} {b₀ b₁ : Basis} {v₀ v₁ : ValExpr}
      (he₀   : ValExpr.OpStep Ψ e₀ b₀ v₀)
      (he₁   : ValExpr.OpStep Ψ e₁ b₁ v₁)
      (htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
      (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁)) :
      ValExpr.OpStep Ψ (.dsumE e₀ e₁) (.dsum b₀ b₁) (.dsumE v₀ v₁)

  | tprodE {Ψ : EvalCtx} {e₀ e₁ : Term} {b₀ b₁ : Basis} {v₀ v₁ : ValExpr}
      (he₀   : ValExpr.OpStep Ψ e₀ b₀ v₀)
      (he₁   : ValExpr.OpStep Ψ e₁ b₁ v₁)
      (htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
      (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁)) :
      ValExpr.OpStep Ψ (.tprodE e₀ e₁) (.tprod b₀ b₁) (.tprodE v₀ v₁)

  | pinvT_std {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term} {v : ValExpr}
      (he   : ValExpr.OpStep Ψ e (.tprod (.dual b₁) b₀) v)
      (hb₀  : Basis.isStd b₀)
      (hb₁  : Basis.isStd b₁) :
      ValExpr.OpStep Ψ (.pinvT (Basis.sof b₁) (Basis.sof b₀) e)
                        (.tprod (.dual b₀) b₁) (.pinv v)

  | pinvT_gpinv {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
                {v env₀ env₁ : ValExpr}
      (he   : ValExpr.OpStep Ψ e (.tprod (.dual b₁) b₀) v)
      (hi₀  : ValExpr.OpStep Ψ (.inner (Basis.sof b₀))
                  (.tprod (.dual b₀) (.dual b₀)) env₀)
      (hi₁  : ValExpr.OpStep Ψ (.inner (Basis.sof b₁))
                  (.tprod (.dual b₁) (.dual b₁)) env₁) :
      ValExpr.OpStep Ψ (.pinvT (Basis.sof b₁) (Basis.sof b₀) e)
                        (.tprod (.dual b₀) b₁) (.gpinv v env₁ env₀)

  | pinvD_std {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term} {v : ValExpr} {sv₁ : ValSpace}
      (he      : ValExpr.OpStep Ψ e (.dual b₁) v)
      (hsofb₀  : Basis.sof b₀ = .real)
      (hb₀     : Basis.isStd b₀)
      (hb₁     : Basis.isStd b₁)
      (hsv₁    : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁) :
      ValExpr.OpStep Ψ (.pinvD (Basis.sof b₁) e)
                        (.tprod (.dual b₀) b₁)
                        (.pinv (.reshap v (.space (.tprod sv₁ .real)) (.space sv₁)))

  | pinvD_gpinv {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
                {v env₀ env₁ : ValExpr} {sv₁ : ValSpace}
      (he      : ValExpr.OpStep Ψ e (.dual b₁) v)
      (hsofb₀  : Basis.sof b₀ = .real)
      (hb₀     : Basis.isStd b₀)
      (hi₀     : ValExpr.OpStep Ψ (.inner (Basis.sof b₀))
                    (.tprod (.dual b₀) (.dual b₀)) env₀)
      (hi₁     : ValExpr.OpStep Ψ (.inner (Basis.sof b₁))
                    (.tprod (.dual b₁) (.dual b₁)) env₁)
      (hsv₁    : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁) :
      ValExpr.OpStep Ψ (.pinvD (Basis.sof b₁) e)
                        (.tprod (.dual b₀) b₁)
                        (.gpinv
                          (.reshap v (.space (.tprod sv₁ .real)) (.space sv₁)) env₁ env₀)

  | inner_std {Ψ : EvalCtx} {b₀ : Basis} {s : Space} {sv : ValSpace}
      (hb₀     : Basis.isStd b₀)
      (hsv     : ValSpace.EvalS Ψ s sv)
      (hsof    : Basis.sof b₀ = s) :
      ValExpr.OpStep Ψ (.inner s)
                        (.tprod (.dual b₀) (.dual b₀))
                        (.idelta sv)

  | embed_ker {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
              {v env₀ env₁ : ValExpr} {s₀ s₁ : Space}
      (hs₀    : Basis.sof b₀ = s₀)
      (hs₁    : Basis.sof b₁ = s₁)
      (hi₀    : ValExpr.OpStep Ψ (.inner s₀)
                  (.tprod (.dual b₀) (.dual b₀)) env₀)
      (hi₁    : ValExpr.OpStep Ψ (.inner s₁)
                  (.tprod (.dual b₁) (.dual b₁)) env₁)
      (he     : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v) :
      ValExpr.OpStep Ψ (.embed (Space.ker s₀ s₁ e))
                        (.tprod (.dual (.proj (.ker s₀ s₁ e) b₀ b₁)) b₀)
                        (.vtrans (.gsvdUI v env₀ env₁))

  | embed_coker {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
                {v env₀ env₁ : ValExpr} {s₀ s₁ : Space}
      (hs₀    : Basis.sof b₀ = s₀)
      (hs₁    : Basis.sof b₁ = s₁)
      (hi₀    : ValExpr.OpStep Ψ (.inner s₀)
                  (.tprod (.dual b₀) (.dual b₀)) env₀)
      (hi₁    : ValExpr.OpStep Ψ (.inner s₁)
                  (.tprod (.dual b₁) (.dual b₁)) env₁)
      (he     : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v) :
      ValExpr.OpStep Ψ (.embed (Space.coker s₀ s₁ e))
                        (.tprod (.dual (.proj (.coker s₀ s₁ e) b₀ b₁)) b₀)
                        (.vtrans (.gsvdU v env₀ env₁))

  | embed_img {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
              {v env₀ env₁ : ValExpr} {s₀ s₁ : Space}
      (hs₀    : Basis.sof b₀ = s₀)
      (hs₁    : Basis.sof b₁ = s₁)
      (hi₀    : ValExpr.OpStep Ψ (.inner s₀)
                  (.tprod (.dual b₀) (.dual b₀)) env₀)
      (hi₁    : ValExpr.OpStep Ψ (.inner s₁)
                  (.tprod (.dual b₁) (.dual b₁)) env₁)
      (he     : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v) :
      ValExpr.OpStep Ψ (.embed (Space.img s₀ s₁ e))
                        (.tprod (.dual (.proj (.img s₀ s₁ e) b₀ b₁)) b₁)
                        (.vtrans (.gsvdV v env₀ env₁))

  | embed_coimg {Ψ : EvalCtx} {b₀ b₁ : Basis} {e : Term}
                {v env₀ env₁ : ValExpr} {s₀ s₁ : Space}
      (hs₀    : Basis.sof b₀ = s₀)
      (hs₁    : Basis.sof b₁ = s₁)
      (hi₀    : ValExpr.OpStep Ψ (.inner s₀)
                  (.tprod (.dual b₀) (.dual b₀)) env₀)
      (hi₁    : ValExpr.OpStep Ψ (.inner s₁)
                  (.tprod (.dual b₁) (.dual b₁)) env₁)
      (he     : ValExpr.OpStep Ψ e (.tprod (.dual b₀) b₁) v) :
      ValExpr.OpStep Ψ (.embed (Space.coimg s₀ s₁ e))
                        (.tprod (.dual (.proj (.coimg s₀ s₁ e) b₀ b₁)) b₁)
                        (.vtrans (.gsvdVI v env₀ env₁))

  | appL_lin {Ψ : EvalCtx} {b₀ b₁ : Basis} {n₀ n₁ : Term}
             {env₀ env₁ : ValExpr} {sv₀ sv₁ : ValSpace}
      (h₀  : ValExpr.OpStep Ψ n₀ (.tprod (.dual b₀) b₁) env₀)
      (hsv₀ : ValSpace.EvalS Ψ (Basis.sof b₀) sv₀)
      (h₁  : ValExpr.OpStep Ψ n₁ b₀ env₁)
      (hsv₁ : ValSpace.EvalS Ψ (Basis.sof b₁) sv₁)
      (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁)) :
      ValExpr.OpStep Ψ (.appL (Basis.sof b₀) (Basis.sof b₁) n₀ n₁) b₁
        (ValExpr.reshapBase (.ttv sv₀ env₀ env₁) sv₁)

  | appI_lin {Ψ : EvalCtx} {b₀ : Basis} {n₀ n₁ : Term}
             {env₀ env₁ : ValExpr} {sv : ValSpace}
      (h₀  : ValExpr.OpStep Ψ n₀ (.dual b₀) env₀)
      (hsv : ValSpace.EvalS Ψ (Basis.sof b₀) sv)
      (h₁  : ValExpr.OpStep Ψ n₁ b₀ env₁) :
      ValExpr.OpStep Ψ (.appI (Basis.sof b₀) n₀ n₁) .one
        (.ttv sv (.reshap env₀ (.space (.tprod sv .real)) (.space sv)) env₁)

  | nllam {Ψ : EvalCtx} {b₀ b₁ : Basis} {τ₀ τ₁ : Ty}
          {e : Term} {τv₀ τv₁ : ValTy} {env : ValExpr}
      (hb₀ : Basis.tof b₀ = τ₀)
      (hb₁ : Basis.tof b₁ = τ₁)
      (h₀  : ValTy.EvalT Ψ τ₀ τv₀)

      -- freshness premise): the body `e` (→ `env`, under codomain basis `b₁`) and
      -- the codomain type `τ₁` (→ `τv₁`) are evaluated for COFINITELY-many fresh
      -- binder names `y`, opened via subst. Barendregt made explicit — lets
      -- EvalCtx-weakening compose past the binder.
      (L : Finset VName)
      (he  : ∀ y, y ∉ L → ValExpr.OpStep (Ψ.extend y b₀ (.var y τv₀))
                (Term.openVar y e) (Basis.openVar y b₁)
                (ValExpr.openVar y τv₀ env))
      (h₁  : ∀ y, y ∉ L → ValTy.EvalT (Ψ.extend y b₀ (.var y τv₀))
                (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁)) :

      ValExpr.OpStep Ψ (.nllam τ₀ e) (.frame b₀ b₁)
        (.vlam τv₀ τv₁ (.reshap env τv₁ τv₁))

  -- Convert the argument to the function's inferred domain. The application
  -- result is the substituted codomain; `hout` records a source realization
  -- independently of the representation chosen for that value.
  | appN_val {Ψ : EvalCtx} {b₀ b₁ : Basis} {n₀ n₁ : Term}
             {env₀ env₁ : ValExpr} {τ_out : ValTy}
      (h₀ : ValExpr.OpStep Ψ n₀ (.frame b₀ b₁) env₀)
      (h₁ : ValExpr.OpStep Ψ n₁ b₀ env₁)
      (hout : ValTy.EvalT Ψ (Basis.instantiate n₁ b₁).tof τ_out) :
      ValExpr.OpStep Ψ (.appN n₀ n₁) (Basis.instantiate n₁ b₁)
        (.applyAt env₀ env₁ τ_out)

  | frame_reanchor {Ψ : EvalCtx} {b₀ b₀' b₁ : Basis} {n₀ : Term}
                   {leev env₁ : ValExpr} {τv₀ τv₀' τv₁' : ValTy}
      (h₀   : ValTy.EvalT Ψ (Basis.tof b₀) τv₀)
      (htof : Basis.tof b₀' = Basis.tof b₀)
      (hfn  : ValExpr.OpStep Ψ n₀ (.frame b₀' b₁) leev)
      (hdom : ValTy.EvalT Ψ (Basis.tof b₀') τv₀')
      (L : Finset VName)
      (hx   : ∀ y, y ∉ L → ValExpr.OpStep (Ψ.extend y b₀ (.var y τv₀))
                (.var y) b₀' (ValExpr.openVar y τv₀ env₁))
      (hcod : ∀ y, y ∉ L → ValTy.EvalT (Ψ.extend y b₀ (.var y τv₀))
                (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁')) :
      ValExpr.OpStep Ψ n₀ (.frame b₀ b₁)
        (.vlam τv₀ τv₁'
          (.reshap
            (.applyValue leev (.reshap env₁ τv₀' τv₀'))
            τv₁' τv₁'))

  | frame_eta {Ψ : EvalCtx} {b₀ b₁ : Basis} {n₀ : Term}
              {τv₀ τv₁ : ValTy} {env : ValExpr}
      (h₀ : ValTy.EvalT Ψ (Basis.tof b₀) τv₀)
      (L : Finset VName)
      (he : ∀ y, y ∉ L → ValExpr.OpStep (Ψ.extend y b₀ (.var y τv₀))
                (.appN n₀ (.var y)) (Basis.openVar y b₁)
                (ValExpr.openVar y τv₀ env))
      (h₁ : ∀ y, y ∉ L → ValTy.EvalT (Ψ.extend y b₀ (.var y τv₀))
                (Ty.openVar y (Basis.tof b₁)) (ValTy.openVar y τv₀ τv₁)) :
      ValExpr.OpStep Ψ n₀ (.frame b₀ b₁)
        (.vlam τv₀ τv₁ (.reshap env τv₁ τv₁))

  | reshape_cob {Ψ : EvalCtx} {e : Term} {b : Basis} {v : ValExpr}
      {τv_src τv_tgt : ValTy}
      (he  : ValExpr.OpStep Ψ e b v)
      (hsrc : ValTy.EvalT Ψ (Basis.tof b) τv_src)
      (htgt : ValTy.EvalT Ψ (Basis.tof b) τv_tgt) :
      ValExpr.OpStep Ψ e b (.reshap v τv_tgt τv_src)

  | llam_assemble {Ψ : EvalCtx} {b' b : Basis} {e : Term} {sv' sv : ValSpace}
                  {env : Fin (ValSpace.dofUB sv') → ValExpr}
      (htof' : Basis.tof b' = .space (Basis.sof b'))
      (hsv'  : ValSpace.EvalS Ψ (Basis.sof b') sv')
      (hsv   : ValSpace.EvalS Ψ (Basis.sof b) sv)
      (L : Finset VName)
      (hfam  : ∀ y, y ∉ L → ∀ i : Fin (ValSpace.dofUB sv'),
                 ValExpr.OpStep (Ψ.extend y b' (.delta i.val sv'))
                   (Term.openVar y e) b (env i)) :
      ValExpr.OpStep Ψ (.llam (Basis.sof b') (Basis.sof b) e)
        (.tprod (.dual b') b)
        (.sumAt sv' (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
          .tprodE (.delta i.val sv') (.reshap (env i) (.space sv) (.space sv)))
          (.tprod sv' sv))

  | llam_assemble_real {Ψ : EvalCtx} {b' : Basis} {e : Term} {sv' : ValSpace}
                       {env : Fin (ValSpace.dofUB sv') → ValExpr}
      (htof' : Basis.tof b' = .space (Basis.sof b'))
      (hsv'  : ValSpace.EvalS Ψ (Basis.sof b') sv')
      (L : Finset VName)
      (hfam  : ∀ y, y ∉ L → ∀ i : Fin (ValSpace.dofUB sv'),
                 ValExpr.OpStep (Ψ.extend y b' (.delta i.val sv'))
                   (Term.openVar y e) .one (env i)) :
      ValExpr.OpStep Ψ (.llam (Basis.sof b') .real e)
        (.dual b')
        (.sumAt sv' (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
          .scale (.reshap (env i) (.space .real) (.space .real)) (.delta i.val sv')) sv')

  -- (§9.16/§9.17 device) — `htof` pins `b` to a SPACE basis and `hsv` supplies
  -- the canonical realization, so `inferType (.zero sv) = .space sv` is
  -- STRUCTURALLY a realization of `tof b` and the preservation arm reads off
  -- the premises.
  | zero {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
      (htof : Basis.tof b = .space (Basis.sof b))
      (hsv  : ValSpace.EvalS Ψ (Basis.sof b) sv) :
      ValExpr.OpStep Ψ (.zero (Basis.sof b)) b (.zero sv)

  | rlit {Ψ : EvalCtx} (r : ℝ) :
      ValExpr.OpStep Ψ (.real r) .one (.rlit r)

end

scoped notation:50 e " ↦[" Ψ ", " b "] " v => ValExpr.OpStep Ψ e b v

theorem ValExpr.OpStep.smul_inv {Ψ : EvalCtx} {e₀ e₁ : Term}
    {b : Basis} {v : ValExpr}
    (h : ValExpr.OpStep Ψ (.smul e₀ e₁) b v) :
    (∃ v₀ v₁, v = .scale v₀ v₁
        ∧ ValExpr.OpStep Ψ e₀ .one v₀
        ∧ ValExpr.OpStep Ψ e₁ b v₁)
    ∨ (∃ b₁ env₀ v' sv,
          v = .ttv sv (.reshapBase env₀ (.tprod sv sv))
            (.reshapBase v' sv)
        ∧ ValExpr.OpStep Ψ (.smul e₀ e₁) b₁ v'
        ∧ Basis.EvalBB Ψ b₁ env₀ b
        ∧ ValSpace.EvalS Ψ (Basis.sof b) sv)
    ∨ (∃ v' τv_src τv_tgt, v = .reshap v' τv_tgt τv_src
        ∧ ValExpr.OpStep Ψ (.smul e₀ e₁) b v'
        ∧ ValTy.EvalT Ψ (Basis.tof b) τv_src
        ∧ ValTy.EvalT Ψ (Basis.tof b) τv_tgt)
    ∨ (∃ b₀ b₁ τv₀ τv₁ τv_src env, b = .frame b₀ b₁
        ∧ v = .vlam τv₀ τv₁ (.reshap env τv₁ τv_src)) := by
  cases h with
  | scale he₀ he₁ => exact Or.inl ⟨_, _, rfl, he₀, he₁⟩
  | cob _ _ he hbb hes => exact Or.inr (Or.inl ⟨_, _, _, _, rfl, he, hbb, hes⟩)
  | reshape_cob he hsrc htgt =>
      exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, he, hsrc, htgt⟩))
  | frame_reanchor h₀ htof hfn hdom L hx hcod =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, rfl, rfl⟩))
  | frame_eta h₀ L he h₁ =>
      exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, _, _, rfl, rfl⟩))

end GLang
