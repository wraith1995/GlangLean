import GLang.Proofs.Adequacy.Foundations.Erasure

namespace GLang
namespace RawCertifiedOperational

open Basis (BasisValid)

mutual

inductive C.Space :
    NLCtx → EvalCtx → Space → ValSpace → Prop
  | real {Γ Ψ} : C.Space Γ Ψ .real .real
  | empty {Γ Ψ} : C.Space Γ Ψ .empty .empty
  | dual {Γ Ψ s sv}
      (hs : Nonempty (SValid Γ (.dual s)))
      (h : C.Space Γ Ψ s sv) :
      C.Space Γ Ψ (.dual s) sv

  | ker {Γ Ψ s₀ s₁ e b leev svb}
      (hs   : Nonempty (SValid Γ (.ker s₀ s₁ e)))
      (hb   : Basis.sof b = .tprod (.dual s₀) s₁)
      (hcompat : Basis.FFSMatrixCompatible b)
      (hsvb : C.Space Γ Ψ (Basis.sof b) svb)
      (he   : C.Term ∅ Γ Ψ e b leev (.space svb)) :
      C.Space Γ Ψ (.ker s₀ s₁ e)
        (.ffs .kernel svb (ValExpr.reshapBase leev svb))
  | coker {Γ Ψ s₀ s₁ e b leev svb}
      (hs   : Nonempty (SValid Γ (.coker s₀ s₁ e)))
      (hb   : Basis.sof b = .tprod (.dual s₀) s₁)
      (hcompat : Basis.FFSMatrixCompatible b)
      (hsvb : C.Space Γ Ψ (Basis.sof b) svb)
      (he   : C.Term ∅ Γ Ψ e b leev (.space svb)) :
      C.Space Γ Ψ (.coker s₀ s₁ e)
        (.ffs .cokernel svb (ValExpr.reshapBase leev svb))
  | img {Γ Ψ s₀ s₁ e b leev svb}
      (hs   : Nonempty (SValid Γ (.img s₀ s₁ e)))
      (hb   : Basis.sof b = .tprod (.dual s₀) s₁)
      (hcompat : Basis.FFSMatrixCompatible b)
      (hsvb : C.Space Γ Ψ (Basis.sof b) svb)
      (he   : C.Term ∅ Γ Ψ e b leev (.space svb)) :
      C.Space Γ Ψ (.img s₀ s₁ e)
        (.ffs .image svb (ValExpr.reshapBase leev svb))
  | coimg {Γ Ψ s₀ s₁ e b leev svb}
      (hs   : Nonempty (SValid Γ (.coimg s₀ s₁ e)))
      (hb   : Basis.sof b = .tprod (.dual s₀) s₁)
      (hcompat : Basis.FFSMatrixCompatible b)
      (hsvb : C.Space Γ Ψ (Basis.sof b) svb)
      (he   : C.Term ∅ Γ Ψ e b leev (.space svb)) :
      C.Space Γ Ψ (.coimg s₀ s₁ e)
        (.ffs .coimage svb (ValExpr.reshapBase leev svb))
  | tprod {Γ Ψ s₀ s₁ sv₀ sv₁}
      (hs : Nonempty (SValid Γ (.tprod s₀ s₁)))
      (h₀ : C.Space Γ Ψ s₀ sv₀) (h₁ : C.Space Γ Ψ s₁ sv₁) :
      C.Space Γ Ψ (.tprod s₀ s₁) (.tprod sv₀ sv₁)
  | dsum {Γ Ψ s₀ s₁ sv₀ sv₁}
      (hs : Nonempty (SValid Γ (.dsum s₀ s₁)))
      (h₀ : C.Space Γ Ψ s₀ sv₀) (h₁ : C.Space Γ Ψ s₁ sv₁) :
      C.Space Γ Ψ (.dsum s₀ s₁) (.dsum sv₀ sv₁)

inductive C.Ty :
    NLCtx → EvalCtx → Ty → ValTy → Prop
  | space {Γ Ψ s sv}
      (h : C.Space Γ Ψ s sv) :
      C.Ty Γ Ψ (.space s) (.space sv)
  | piTy {Γ Ψ b₀ τ₀ τ₁ τv₀ τv₁ k₀ k₁}
      (ht  : Nonempty (TValid Γ (.piTy τ₀ τ₁) (.arrow k₀ k₁)))
      (hb  : Basis.tof b₀ = τ₀)
      (hbv : BasisValid Γ b₀)
      (h₀  : C.Ty Γ Ψ τ₀ τv₀)
      (L : Finset Name)
      (h₁  : ∀ y, y ∉ L →
               C.Ty (Finmap.insert y τ₀ Γ) (Ψ.extend y b₀ (.var y τv₀))
                 (Ty.openVar y τ₁) (ValTy.openVar y τv₀ τv₁)) :
      C.Ty Γ Ψ (.piTy τ₀ τ₁) (.piTy τv₀ τv₁)

/-- Basis-indexed strengthened type evaluation. -/
inductive C.TyAt :
    NLCtx → EvalCtx → Basis → ValTy → Prop
  | space {Γ Ψ b sv}
      (htof : Basis.tof b = .space (Basis.sof b))
      (hbv : BasisValid Γ b)
      (hspace : C.Space Γ Ψ (Basis.sof b) sv) :
      C.TyAt Γ Ψ b (.space sv)
  | frame {Γ Ψ b₀ b₁ τv₀ τv₁}
      (hbv : BasisValid Γ (.frame b₀ b₁))
      (hdom : C.TyAt Γ Ψ b₀ τv₀)
      (L : Finset Name)
      (hcod : ∀ y, y ∉ L →
        C.TyAt (Finmap.insert y (Basis.tof b₀) Γ)
          (Ψ.extend y b₀ (.var y τv₀))
          (Basis.openVar y b₁) (ValTy.openVar y τv₀ τv₁)) :
      C.TyAt Γ Ψ (.frame b₀ b₁) (.piTy τv₀ τv₁)

inductive C.Cob :
    NLCtx → EvalCtx → Basis → ValExpr → Basis → Prop

  | inverse {Γ Ψ b₀ b₁ leev}
      (hb₀ : BasisValid Γ b₀) (hb₁ : BasisValid Γ b₁)
      (h : C.Cob Γ Ψ b₁ leev b₀) :
      C.Cob Γ Ψ b₀ (.inv leev) b₁

  | trans {Γ Ψ b₀ b₁ b₂ env₀ env₁ sv}
      (hb₀ : BasisValid Γ b₀) (hb₂ : BasisValid Γ b₂)
      (h₀ : C.Cob Γ Ψ b₀ env₀ b₁)
      (h₁ : C.Cob Γ Ψ b₁ env₁ b₂)
      (hsv : C.Space Γ Ψ (Basis.sof b₀) sv) :
      C.Cob Γ Ψ b₀
        (.mtm 0 0 sv sv env₁ (ValExpr.reshapBase env₀ (.tprod sv sv))) b₂

  | tprod {Γ Ψ b₀ b₁ b₀' b₁' env₀ env₁}
      (hbS : BasisValid Γ (.tprod b₀' b₁')) (hbT : BasisValid Γ (.tprod b₀ b₁))
      (h₀ : C.Cob Γ Ψ b₀' env₀ b₀)
      (h₁ : C.Cob Γ Ψ b₁' env₁ b₁) :
      C.Cob Γ Ψ (.tprod b₀' b₁') (.vkrn env₀ env₁) (.tprod b₀ b₁)

  | dsum {Γ Ψ b₀ b₁ b₀' b₁' env₀ env₁}
      (hbS : BasisValid Γ (.dsum b₀' b₁')) (hbT : BasisValid Γ (.dsum b₀ b₁))
      (h₀ : C.Cob Γ Ψ b₀' env₀ b₀)
      (h₁ : C.Cob Γ Ψ b₁' env₁ b₁) :
      C.Cob Γ Ψ (.dsum b₀' b₁') (.vblk env₀ env₁) (.dsum b₀ b₁)

  | dual_std {Γ Ψ b₀ leev}
      (htof : Basis.tof b₀ = .space (Basis.sof b₀))
      (hbS : BasisValid Γ (.dual b₀)) (hbT : BasisValid Γ (Basis.std (Basis.tof (.dual b₀))))
      (hb₁ : C.Cob Γ Ψ b₀ leev (Basis.std (Basis.tof b₀))) :
      C.Cob Γ Ψ (.dual b₀) (.vtrans (.inv leev)) (Basis.std (Basis.tof (.dual b₀)))

  | image {Γ Ψ b₀ b₀' leev}
      (hbS : BasisValid Γ (.image b₀)) (hbT : BasisValid Γ (.image b₀'))
      (hcoker : ∃ s₀ s₁ e, Basis.sof b₀ = .coker s₀ s₁ e)
      (h : C.Cob Γ Ψ b₀ leev b₀') :
      C.Cob Γ Ψ (.image b₀) leev (.image b₀')

  | image_svds {Γ Ψ b₀ b₁ e leev s₀ s₁ svb}
      (hbS : BasisValid Γ (.image (.proj (.coker s₀ s₁ e) b₀ b₁)))
      (hbT : BasisValid Γ (.proj (.img s₀ s₁ e) b₀ b₁))
      (hs₀ : Basis.sof b₀ = s₀) (hs₁ : Basis.sof b₁ = s₁)
      (hb₀ : Basis.isStd b₀) (hb₁ : Basis.isStd b₁)
      (hsvb : C.Space Γ Ψ (Basis.sof (.tprod (.dual b₀) b₁)) svb)
      (he  : C.Term ∅ Γ Ψ e (.tprod (.dual b₀) b₁) leev (.space svb)) :
      C.Cob Γ Ψ
        (.image (.proj (.coker s₀ s₁ e) b₀ b₁))
        (.reshap (.imageCoords svb leev)
          (.space (.tprod
            (.ffs .cokernel svb (ValExpr.reshapBase leev svb))
            (.ffs .image svb (ValExpr.reshapBase leev svb))))
          (.space (ValExpr.inferSpaceCtx [] (.imageCoords svb leev))))
        (.proj (.img s₀ s₁ e) b₀ b₁)

  | proj_ker_coker {Γ Ψ s₀ s₁ e s b₀ b₁ b₀' env₁ env₂ env₃ sv₀ sv₁ sv sv' sv₀'}
      (hbS : BasisValid Γ (.proj s b₀ b₁)) (hbT : BasisValid Γ (.proj s b₀' b₁))
      (hs    : s = Space.ker s₀ s₁ e ∨ s = Space.coker s₀ s₁ e)
      (hsofb₀ : Basis.sof b₀ = s₀) (hsofb₁ : Basis.sof b₁ = s₁)
      (hsv₀  : C.Space Γ Ψ (Basis.sof b₀) sv₀)
      (hsv₁  : C.Space Γ Ψ (Basis.sof b₁) sv₁)
      (hsv   : C.Space Γ Ψ s sv)
      (hsv'  : C.Space Γ Ψ s sv')
      (hsv₀' : C.Space Γ Ψ (Basis.sof b₀') sv₀')
      (hcob  : C.Cob Γ Ψ b₀ env₂ b₀')
      (hembd : C.Term ∅ Γ Ψ (Term.lembd s)
                 (.tprod (.dual (.proj s b₀ b₁)) b₀) env₃ (.space (.tprod sv sv₀)))
      (hproj : C.Term ∅ Γ Ψ (Term.lproj s (Basis.sof b₀'))
                 (.tprod (.dual b₀') (.proj s b₀' b₁)) env₁ (.space (.tprod sv₀' sv'))) :
      C.Cob Γ Ψ (.proj s b₀ b₁)
        (.mtm 0 0 sv₀' sv₀'
          (ValExpr.reshapBase env₁ (.tprod sv₀' sv'))
          (.mtm 0 0 sv₀ sv₀ (ValExpr.reshapBase env₂ (.tprod sv₀ sv₀'))
            (ValExpr.reshapBase env₃ (.tprod sv sv₀))))
        (.proj s b₀' b₁)

  | proj_img_coimg {Γ Ψ s₀ s₁ e s b₀ b₁ b₁' env₁ env₂ env₃ sv₀ sv₁ sv sv' sv₁'}
      (hbS : BasisValid Γ (.proj s b₀ b₁)) (hbT : BasisValid Γ (.proj s b₀ b₁'))
      (hs    : s = Space.img s₀ s₁ e ∨ s = Space.coimg s₀ s₁ e)
      (hsofb₀ : Basis.sof b₀ = s₀) (hsofb₁ : Basis.sof b₁ = s₁)
      (hsv₀  : C.Space Γ Ψ (Basis.sof b₀) sv₀)
      (hsv₁  : C.Space Γ Ψ (Basis.sof b₁) sv₁)
      (hsv   : C.Space Γ Ψ s sv)
      (hsv'  : C.Space Γ Ψ s sv')
      (hsv₁' : C.Space Γ Ψ (Basis.sof b₁') sv₁')
      (hcob  : C.Cob Γ Ψ b₁ env₂ b₁')
      (hembd : C.Term ∅ Γ Ψ (Term.lembd s)
                 (.tprod (.dual (.proj s b₀ b₁)) b₁) env₃ (.space (.tprod sv sv₁)))
      (hproj : C.Term ∅ Γ Ψ (Term.lproj s (Basis.sof b₁'))
                 (.tprod (.dual b₁') (.proj s b₀ b₁')) env₁ (.space (.tprod sv₁' sv'))) :
      C.Cob Γ Ψ (.proj s b₀ b₁)
        (.mtm 0 0 sv₁' sv₁'
          (ValExpr.reshapBase env₁ (.tprod sv₁' sv'))
          (.mtm 0 0 sv₁ sv₁ (ValExpr.reshapBase env₂ (.tprod sv₁ sv₁'))
            (ValExpr.reshapBase env₃ (.tprod sv sv₁))))
        (.proj s b₀ b₁')

  | terms_rref {Γ Ψ b b' e es env₀ env₁ sv τv}
      (hbS : BasisValid Γ b) (hbT : BasisValid Γ (.terms (Basis.sof b') (e :: es) b'))
      (hbb : C.Cob Γ Ψ b env₁ b')
      (hch : C.Term ∅ Γ Ψ (Term.dsumChain e es) (Basis.dsumChain b' es.length) env₀ τv)
      (hsv : C.Space Γ Ψ (Basis.sof b) sv) :
      C.Cob Γ Ψ b
        (ValExpr.reshapBase
          (.rrefRep env₀ (ValExpr.reshapBase env₁ (.tprod sv sv))) (.tprod sv sv))
        (.terms (Basis.sof b') (e :: es) b')

  | refl {Γ Ψ b sv}
      (hb : BasisValid Γ b)
      (htof : Basis.tof b = .space (Basis.sof b))
      (hsv  : C.Space Γ Ψ (Basis.sof b) sv) :
      C.Cob Γ Ψ b
        (.reshap (.idelta sv) (.space (.tprod sv sv)) (.space (.tprod sv sv))) b

  | proj_ker_coker_cod {Γ Ψ s₀ s₁ e s b₀ b₁ b₁' env₁ env₃ sv₀ sv sv'}
      (hbS : BasisValid Γ (.proj s b₀ b₁)) (hbT : BasisValid Γ (.proj s b₀ b₁'))
      (hs : s = Space.ker s₀ s₁ e ∨ s = Space.coker s₀ s₁ e)
      (hsofb₀ : Basis.sof b₀ = s₀) (hsofb₁ : Basis.sof b₁ = s₁) (hsofb₁' : Basis.sof b₁' = s₁)
      (hsv₀ : C.Space Γ Ψ (Basis.sof b₀) sv₀)
      (hsv  : C.Space Γ Ψ s sv)
      (hsv' : C.Space Γ Ψ s sv')
      (hembd : C.Term ∅ Γ Ψ (Term.lembd s)
                 (.tprod (.dual (.proj s b₀ b₁)) b₀) env₃ (.space (.tprod sv sv₀)))
      (hproj : C.Term ∅ Γ Ψ (Term.lproj s (Basis.sof b₀))
                 (.tprod (.dual b₀) (.proj s b₀ b₁')) env₁ (.space (.tprod sv₀ sv'))) :
      C.Cob Γ Ψ (.proj s b₀ b₁)
        (.mtm 0 0 sv₀ sv₀
          (ValExpr.reshapBase env₁ (.tprod sv₀ sv'))
          (ValExpr.reshapBase env₃ (.tprod sv sv₀)))
        (.proj s b₀ b₁')

  | proj_img_coimg_dom {Γ Ψ s₀ s₁ e s b₀ b₁ b₀' env₁ env₃ sv₁ sv sv'}
      (hbS : BasisValid Γ (.proj s b₀ b₁)) (hbT : BasisValid Γ (.proj s b₀' b₁))
      (hs : s = Space.img s₀ s₁ e ∨ s = Space.coimg s₀ s₁ e)
      (hsofb₀ : Basis.sof b₀ = s₀) (hsofb₁ : Basis.sof b₁ = s₁) (hsofb₀' : Basis.sof b₀' = s₀)
      (hsv₁ : C.Space Γ Ψ (Basis.sof b₁) sv₁)
      (hsv  : C.Space Γ Ψ s sv)
      (hsv' : C.Space Γ Ψ s sv')
      (hembd : C.Term ∅ Γ Ψ (Term.lembd s)
                 (.tprod (.dual (.proj s b₀ b₁)) b₁) env₃ (.space (.tprod sv sv₁)))
      (hproj : C.Term ∅ Γ Ψ (Term.lproj s (Basis.sof b₁))
                 (.tprod (.dual b₁) (.proj s b₀' b₁)) env₁ (.space (.tprod sv₁ sv'))) :
      C.Cob Γ Ψ (.proj s b₀ b₁)
        (.mtm 0 0 sv₁ sv₁
          (ValExpr.reshapBase env₁ (.tprod sv₁ sv'))
          (ValExpr.reshapBase env₃ (.tprod sv sv₁)))
        (.proj s b₀' b₁)

inductive C.Term :
    LCtx → NLCtx → EvalCtx → Term → Basis → ValExpr → ValTy → Prop
  /-- Linear variable (`HasType.var_lin` × `OpStep.var`). -/
  | var_lin {Γ Ψ x b v s τv}
      (h : EvalCtx.lookup Ψ (x, b) = some v)
      (htof : Basis.tof b = .space s)
      (hbv : BasisValid Γ b)
      (hτv : C.TyAt Γ Ψ b τv) :
      C.Term (Finmap.singleton x s) Γ Ψ (.var x) b v τv
  /-- Non-linear variable (`HasType.var_nlin` × `OpStep.var`). -/
  | var_nlin {Γ Ψ x b v τv}
      (h : EvalCtx.lookup Ψ (x, b) = some v)
      (hΓ : Γ.lookup x = some (Basis.tof b))
      (hbv : BasisValid Γ b)
      (hτv : C.TyAt Γ Ψ b τv) :
      C.Term ∅ Γ Ψ (.var x) b v τv

  | promote {Δ Γ' Γ'' Ψ e b v τv} (lin : LCtx)
      (hdΔ : Finmap.Disjoint lin Δ)
      (hdΓ : Finmap.Disjoint lin.toNL Γ'')
      (hfr : PromoteFresh lin Δ Γ')
      (hle : NLCtxIncl Γ' Γ'')
      (ht  : Nonempty (HasType Δ (lin.toNL ∪ Γ'') e (Basis.tof b)))
      (hbv : BasisValid (lin.toNL ∪ Γ'') b)
      (hτv : C.TyAt (lin.toNL ∪ Γ'') Ψ b τv)
      (h : C.Term (lin ∪ Δ) Γ' Ψ e b v τv) :
      C.Term Δ (lin.toNL ∪ Γ'') Ψ e b v τv

  | cob {Δ Γ Ψ e b₀ b₁ v env₀ sv τv}
      (htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
      (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
      (ht  : Nonempty (HasType Δ Γ e (Basis.tof b₀)))
      (hbv : BasisValid Γ b₀)
      (hτv : C.TyAt Γ Ψ b₀ (.space sv))
      (he  : C.Term Δ Γ Ψ e b₁ v τv)
      (hbb : C.Cob Γ Ψ b₁ env₀ b₀)
      (hes : C.Space Γ Ψ (Basis.sof b₀) sv) :
      C.Term Δ Γ Ψ e b₀
        (.ttv sv (ValExpr.reshapBase env₀ (.tprod sv sv))
          (ValExpr.reshapBase v sv)) (.space sv)

  | reshape_cob {Δ Γ Ψ e b v τv τv'}
      (ht  : Nonempty (HasType Δ Γ e (Basis.tof b)))
      (hbv : BasisValid Γ b)
      (hτv : C.TyAt Γ Ψ b τv')
      (he  : C.Term Δ Γ Ψ e b v τv) :
      C.Term Δ Γ Ψ e b (.reshap v τv' τv) τv'
  /-- Scalar multiplication (`HasType.smul` × `OpStep.scale`). -/
  | scale {Δ₀ Δ₁ Γ Ψ e₀ e₁ b v₀ v₁ sv}
      (hdisj : Finmap.Disjoint Δ₀ Δ₁)
      (htof : Basis.tof b = .space (Basis.sof b))
      (ht  : Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.smul e₀ e₁) (Basis.tof b)))
      (hbv : BasisValid Γ b)
      (hτv : C.TyAt Γ Ψ b (.space sv))
      (he₀ : C.Term Δ₀ Γ Ψ e₀ .one v₀ (.space .real))
      (he₁ : C.Term Δ₁ Γ Ψ e₁ b v₁ (.space sv)) :
      C.Term (Δ₀ ∪ Δ₁) Γ Ψ (.smul e₀ e₁) b (.scale v₀ v₁) (.space sv)
  /-- Addition (`HasType.add` × `OpStep.add`).  The result carries an explicit realization
      `sv`; the two operands may have independent realizations `sv₀` and `sv₁` of the
      same source type.  The exception-carrying value denotation checks both operand arrays
      against `dof sv`.  Claim (1) for each operand and claim (3) for `hτv` pin all three
      dimensions to the one source-basis length, so adequacy rules out `DimError` without an
      `inferSpace` equality guard or a reshape. -/
  | add {Δ Γ Ψ e₀ e₁ b v₀ v₁ sv sv₀ sv₁}
      (htof : Basis.tof b = .space (Basis.sof b))
      (ht  : Nonempty (HasType Δ Γ (.add e₀ e₁) (Basis.tof b)))
      (hbv : BasisValid Γ b)
      (hτv : C.TyAt Γ Ψ b (.space sv))
      (he₀ : C.Term Δ Γ Ψ e₀ b v₀ (.space sv₀))
      (he₁ : C.Term Δ Γ Ψ e₁ b v₁ (.space sv₁)) :
      C.Term Δ Γ Ψ (.add e₀ e₁) b (.vadd sv v₀ v₁) (.space sv)
  /-- Direct sum of terms (`HasType.dsumE` × `OpStep.dsumE`). -/
  | dsumE {Δ Γ Ψ e₀ e₁ b₀ b₁ v₀ v₁ sv₀ sv₁}
      (htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
      (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
      (ht  : Nonempty (HasType Δ Γ (.dsumE e₀ e₁) (Basis.tof (.dsum b₀ b₁))))
      (hbv : BasisValid Γ (.dsum b₀ b₁))
      (hτv : C.TyAt Γ Ψ (.dsum b₀ b₁) (.space (.dsum sv₀ sv₁)))
      (he₀ : C.Term Δ Γ Ψ e₀ b₀ v₀ (.space sv₀))
      (he₁ : C.Term Δ Γ Ψ e₁ b₁ v₁ (.space sv₁)) :
      C.Term Δ Γ Ψ (.dsumE e₀ e₁) (.dsum b₀ b₁) (.dsumE v₀ v₁) (.space (.dsum sv₀ sv₁))
  /-- Tensor product of terms (`HasType.tprodE` × `OpStep.tprodE`). -/
  | tprodE {Δ₀ Δ₁ Γ Ψ e₀ e₁ b₀ b₁ v₀ v₁ sv₀ sv₁}
      (hdisj : Finmap.Disjoint Δ₀ Δ₁)
      (htof₀ : Basis.tof b₀ = .space (Basis.sof b₀))
      (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
      (ht  : Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.tprodE e₀ e₁) (Basis.tof (.tprod b₀ b₁))))
      (hbv : BasisValid Γ (.tprod b₀ b₁))
      (hτv : C.TyAt Γ Ψ (.tprod b₀ b₁) (.space (.tprod sv₀ sv₁)))
      (he₀ : C.Term Δ₀ Γ Ψ e₀ b₀ v₀ (.space sv₀))
      (he₁ : C.Term Δ₁ Γ Ψ e₁ b₁ v₁ (.space sv₁)) :
      C.Term (Δ₀ ∪ Δ₁) Γ Ψ (.tprodE e₀ e₁) (.tprod b₀ b₁) (.tprodE v₀ v₁)
        (.space (.tprod sv₀ sv₁))

  | pinvT_std {Γ Ψ b₀ b₁ e v sv₀ sv₁}
      (hb₀ : Basis.isStd b₀) (hb₁ : Basis.isStd b₁)
      (ht  : Nonempty (HasType ∅ Γ (.pinvT (Basis.sof b₁) (Basis.sof b₀) e)
               (Basis.tof (.tprod (.dual b₀) b₁))))
      (hbv : BasisValid Γ (.tprod (.dual b₀) b₁))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual b₀) b₁) (.space (.tprod sv₀ sv₁)))
      (he  : C.Term ∅ Γ Ψ e (.tprod (.dual b₁) b₀) v (.space (.tprod sv₁ sv₀))) :
      C.Term ∅ Γ Ψ (.pinvT (Basis.sof b₁) (Basis.sof b₀) e)
        (.tprod (.dual b₀) b₁) (.pinv v) (.space (.tprod sv₀ sv₁))

  | pinvT_gpinv {Γ Ψ b₀ b₁ e v env₀ env₁ sv₀ sv₁}
      (ht  : Nonempty (HasType ∅ Γ (.pinvT (Basis.sof b₁) (Basis.sof b₀) e)
               (Basis.tof (.tprod (.dual b₀) b₁))))
      (hbv : BasisValid Γ (.tprod (.dual b₀) b₁))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual b₀) b₁) (.space (.tprod sv₀ sv₁)))
      (he  : C.Term ∅ Γ Ψ e (.tprod (.dual b₁) b₀) v (.space (.tprod sv₁ sv₀)))
      (hi₀ : C.Term ∅ Γ Ψ (.inner (Basis.sof b₀))
               (.tprod (.dual b₀) (.dual b₀)) env₀ (.space (.tprod sv₀ sv₀)))
      (hi₁ : C.Term ∅ Γ Ψ (.inner (Basis.sof b₁))
               (.tprod (.dual b₁) (.dual b₁)) env₁ (.space (.tprod sv₁ sv₁))) :
      C.Term ∅ Γ Ψ (.pinvT (Basis.sof b₁) (Basis.sof b₀) e)
        (.tprod (.dual b₀) b₁) (.gpinv v env₁ env₀) (.space (.tprod sv₀ sv₁))

  | pinvD_std {Γ Ψ b₀ b₁ e v sv₁}
      (hsofb₀ : Basis.sof b₀ = .real)
      (hb₀ : Basis.isStd b₀) (hb₁ : Basis.isStd b₁)
      (ht  : Nonempty (HasType ∅ Γ (.pinvD (Basis.sof b₁) e) (Basis.tof (.tprod (.dual b₀) b₁))))
      (hbv : BasisValid Γ (.tprod (.dual b₀) b₁))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual b₀) b₁) (.space (.tprod .real sv₁)))
      (he  : C.Term ∅ Γ Ψ e (.dual b₁) v (.space sv₁)) :
      C.Term ∅ Γ Ψ (.pinvD (Basis.sof b₁) e) (.tprod (.dual b₀) b₁)
        (.pinv (.reshap v (.space (.tprod sv₁ .real)) (.space sv₁)))
        (.space (.tprod .real sv₁))

  | pinvD_gpinv {Γ Ψ b₀ b₁ e v env₀ env₁ sv₁}
      (hsofb₀ : Basis.sof b₀ = .real)
      (hb₀ : Basis.isStd b₀)
      (ht  : Nonempty (HasType ∅ Γ (.pinvD (Basis.sof b₁) e) (Basis.tof (.tprod (.dual b₀) b₁))))
      (hbv : BasisValid Γ (.tprod (.dual b₀) b₁))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual b₀) b₁) (.space (.tprod .real sv₁)))
      (he  : C.Term ∅ Γ Ψ e (.dual b₁) v (.space sv₁))
      (hi₀ : C.Term ∅ Γ Ψ (.inner (Basis.sof b₀))
               (.tprod (.dual b₀) (.dual b₀)) env₀ (.space (.tprod .real .real)))
      (hi₁ : C.Term ∅ Γ Ψ (.inner (Basis.sof b₁))
               (.tprod (.dual b₁) (.dual b₁)) env₁ (.space (.tprod sv₁ sv₁))) :
      C.Term ∅ Γ Ψ (.pinvD (Basis.sof b₁) e) (.tprod (.dual b₀) b₁)
        (.gpinv (.reshap v (.space (.tprod sv₁ .real)) (.space sv₁)) env₁ env₀)
        (.space (.tprod .real sv₁))

  | inner_std {Γ Ψ b₀ s sv}
      (hb₀  : Basis.isStd b₀)
      (hsof : Basis.sof b₀ = s)
      (ht  : Nonempty (HasType ∅ Γ (.inner s) (Basis.tof (.tprod (.dual b₀) (.dual b₀)))))
      (hbv : BasisValid Γ (.tprod (.dual b₀) (.dual b₀)))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual b₀) (.dual b₀)) (.space (.tprod sv sv)))
      (hsv : C.Space Γ Ψ s sv) :
      C.Term ∅ Γ Ψ (.inner s) (.tprod (.dual b₀) (.dual b₀)) (.idelta sv)
        (.space (.tprod sv sv))

  | embed_ker {Γ Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ sv₀ sv₁}
      (hs₀ : Basis.sof b₀ = s₀) (hs₁ : Basis.sof b₁ = s₁)
      (ht  : Nonempty (HasType ∅ Γ (.embed (Space.ker s₀ s₁ e))
               (Basis.tof (.tprod (.dual (.proj (.ker s₀ s₁ e) b₀ b₁)) b₀))))
      (hbv : BasisValid Γ (.tprod (.dual (.proj (.ker s₀ s₁ e) b₀ b₁)) b₀))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual (.proj (.ker s₀ s₁ e) b₀ b₁)) b₀)
               (.space (.tprod (.ffs .kernel (.tprod sv₀ sv₁)
                                 (ValExpr.reshapBase v (.tprod sv₀ sv₁)))
                               sv₀)))
      (hi₀ : C.Term ∅ Γ Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀
               (.space (.tprod sv₀ sv₀)))
      (hi₁ : C.Term ∅ Γ Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁
               (.space (.tprod sv₁ sv₁)))
      (he  : C.Term ∅ Γ Ψ e (.tprod (.dual b₀) b₁) v (.space (.tprod sv₀ sv₁))) :
      C.Term ∅ Γ Ψ (.embed (Space.ker s₀ s₁ e))
        (.tprod (.dual (.proj (.ker s₀ s₁ e) b₀ b₁)) b₀)
        (.vtrans (.gsvdUI v env₀ env₁))
        (.space (.tprod (.ffs .kernel (.tprod sv₀ sv₁)
                          (ValExpr.reshapBase v (.tprod sv₀ sv₁))) sv₀))

  | embed_coker {Γ Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ sv₀ sv₁}
      (hs₀ : Basis.sof b₀ = s₀) (hs₁ : Basis.sof b₁ = s₁)
      (ht  : Nonempty (HasType ∅ Γ (.embed (Space.coker s₀ s₁ e))
               (Basis.tof (.tprod (.dual (.proj (.coker s₀ s₁ e) b₀ b₁)) b₀))))
      (hbv : BasisValid Γ (.tprod (.dual (.proj (.coker s₀ s₁ e) b₀ b₁)) b₀))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual (.proj (.coker s₀ s₁ e) b₀ b₁)) b₀)
               (.space (.tprod (.ffs .cokernel (.tprod sv₀ sv₁)
                                 (ValExpr.reshapBase v (.tprod sv₀ sv₁)))
                               sv₀)))
      (hi₀ : C.Term ∅ Γ Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀
               (.space (.tprod sv₀ sv₀)))
      (hi₁ : C.Term ∅ Γ Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁
               (.space (.tprod sv₁ sv₁)))
      (he  : C.Term ∅ Γ Ψ e (.tprod (.dual b₀) b₁) v (.space (.tprod sv₀ sv₁))) :
      C.Term ∅ Γ Ψ (.embed (Space.coker s₀ s₁ e))
        (.tprod (.dual (.proj (.coker s₀ s₁ e) b₀ b₁)) b₀)
        (.vtrans (.gsvdU v env₀ env₁))
        (.space (.tprod (.ffs .cokernel (.tprod sv₀ sv₁)
                          (ValExpr.reshapBase v (.tprod sv₀ sv₁))) sv₀))

  | embed_img {Γ Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ sv₀ sv₁}
      (hs₀ : Basis.sof b₀ = s₀) (hs₁ : Basis.sof b₁ = s₁)
      (ht  : Nonempty (HasType ∅ Γ (.embed (Space.img s₀ s₁ e))
               (Basis.tof (.tprod (.dual (.proj (.img s₀ s₁ e) b₀ b₁)) b₁))))
      (hbv : BasisValid Γ (.tprod (.dual (.proj (.img s₀ s₁ e) b₀ b₁)) b₁))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual (.proj (.img s₀ s₁ e) b₀ b₁)) b₁)
               (.space (.tprod (.ffs .image (.tprod sv₀ sv₁)
                                 (ValExpr.reshapBase v (.tprod sv₀ sv₁)))
                               sv₁)))
      (hi₀ : C.Term ∅ Γ Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀
               (.space (.tprod sv₀ sv₀)))
      (hi₁ : C.Term ∅ Γ Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁
               (.space (.tprod sv₁ sv₁)))
      (he  : C.Term ∅ Γ Ψ e (.tprod (.dual b₀) b₁) v (.space (.tprod sv₀ sv₁))) :
      C.Term ∅ Γ Ψ (.embed (Space.img s₀ s₁ e))
        (.tprod (.dual (.proj (.img s₀ s₁ e) b₀ b₁)) b₁)
        (.vtrans (.gsvdV v env₀ env₁))
        (.space (.tprod (.ffs .image (.tprod sv₀ sv₁)
                          (ValExpr.reshapBase v (.tprod sv₀ sv₁))) sv₁))

  | embed_coimg {Γ Ψ b₀ b₁ e v env₀ env₁ s₀ s₁ sv₀ sv₁}
      (hs₀ : Basis.sof b₀ = s₀) (hs₁ : Basis.sof b₁ = s₁)
      (ht  : Nonempty (HasType ∅ Γ (.embed (Space.coimg s₀ s₁ e))
               (Basis.tof (.tprod (.dual (.proj (.coimg s₀ s₁ e) b₀ b₁)) b₁))))
      (hbv : BasisValid Γ (.tprod (.dual (.proj (.coimg s₀ s₁ e) b₀ b₁)) b₁))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual (.proj (.coimg s₀ s₁ e) b₀ b₁)) b₁)
               (.space (.tprod (.ffs .coimage (.tprod sv₀ sv₁)
                                 (ValExpr.reshapBase v (.tprod sv₀ sv₁)))
                               sv₁)))
      (hi₀ : C.Term ∅ Γ Ψ (.inner s₀) (.tprod (.dual b₀) (.dual b₀)) env₀
               (.space (.tprod sv₀ sv₀)))
      (hi₁ : C.Term ∅ Γ Ψ (.inner s₁) (.tprod (.dual b₁) (.dual b₁)) env₁
               (.space (.tprod sv₁ sv₁)))
      (he  : C.Term ∅ Γ Ψ e (.tprod (.dual b₀) b₁) v (.space (.tprod sv₀ sv₁))) :
      C.Term ∅ Γ Ψ (.embed (Space.coimg s₀ s₁ e))
        (.tprod (.dual (.proj (.coimg s₀ s₁ e) b₀ b₁)) b₁)
        (.vtrans (.gsvdVI v env₀ env₁))
        (.space (.tprod (.ffs .coimage (.tprod sv₀ sv₁)
                          (ValExpr.reshapBase v (.tprod sv₀ sv₁))) sv₁))

  | appL_lin {Δ₀ Δ₁ Γ Ψ b₀ b₁ n₀ n₁ env₀ env₁
              sv svOut svMat₀ svMat₁ svArg}
      (hdisj : Finmap.Disjoint Δ₀ Δ₁)
      (htof₁ : Basis.tof b₁ = .space (Basis.sof b₁))
      (ht  : Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.appL (Basis.sof b₀) (Basis.sof b₁) n₀ n₁)
               (Basis.tof b₁)))
      (hbv : BasisValid Γ b₁)
      (hsv : C.Space Γ Ψ (Basis.sof b₀) sv)
      (hτv : C.TyAt Γ Ψ b₁ (.space svOut))
      (h₀  : C.Term Δ₀ Γ Ψ n₀ (.tprod (.dual b₀) b₁) env₀
               (.space (.tprod svMat₀ svMat₁)))
      (h₁  : C.Term Δ₁ Γ Ψ n₁ b₀ env₁ (.space svArg)) :
      C.Term (Δ₀ ∪ Δ₁) Γ Ψ (.appL (Basis.sof b₀) (Basis.sof b₁) n₀ n₁) b₁
        (ValExpr.reshapBase (.ttv sv env₀ env₁) svOut) (.space svOut)

  | appI_lin {Δ₀ Δ₁ Γ Ψ b₀ n₀ n₁ env₀ env₁ sv svFun svArg}
      (hdisj : Finmap.Disjoint Δ₀ Δ₁)
      (ht  : Nonempty (HasType (Δ₀ ∪ Δ₁) Γ (.appI (Basis.sof b₀) n₀ n₁) (Basis.tof .one)))
      (hsv : C.Space Γ Ψ (Basis.sof b₀) sv)
      (hτv : C.TyAt Γ Ψ .one (.space .real))
      (h₀  : C.Term Δ₀ Γ Ψ n₀ (.dual b₀) env₀ (.space svFun))
      (h₁  : C.Term Δ₁ Γ Ψ n₁ b₀ env₁ (.space svArg)) :
      C.Term (Δ₀ ∪ Δ₁) Γ Ψ (.appI (Basis.sof b₀) n₀ n₁) .one
        (.ttv sv (.reshap env₀ (.space (.tprod sv .real)) (.space sv)) env₁) (.space .real)

  | nllam {Γ Ψ b₀ b₁ τ₀ τ₁ e τv₀ τv₁ env}
      (hb₀ : Basis.tof b₀ = τ₀) (hb₁ : Basis.tof b₁ = τ₁)
      (ht  : Nonempty (HasType ∅ Γ (.nllam τ₀ e) (Basis.tof (.frame b₀ b₁))))
      (hbv : BasisValid Γ (.frame b₀ b₁))
      (hτv : C.TyAt Γ Ψ (.frame b₀ b₁) (.piTy τv₀ τv₁))
      (h₀  : C.TyAt Γ Ψ b₀ τv₀)
      (L : Finset Name)
      (he  : ∀ y, y ∉ L →
               C.Term ∅ (Finmap.insert y τ₀ Γ) (Ψ.extend y b₀ (.var y τv₀))
                 (Term.openVar y e) (Basis.openVar y b₁)
                 (ValExpr.openVar y τv₀ env) (ValTy.openVar y τv₀ τv₁))
      (h₁  : ∀ y, y ∉ L →
               C.TyAt (Finmap.insert y τ₀ Γ) (Ψ.extend y b₀ (.var y τv₀))
                 (Basis.openVar y b₁) (ValTy.openVar y τv₀ τv₁)) :
      C.Term ∅ Γ Ψ (.nllam τ₀ e) (.frame b₀ b₁)
        (.vlam τv₀ τv₁ (.reshap env τv₁ τv₁))
        (.piTy τv₀ τv₁)

  | appN_val {Γ Ψ b₀ b₁ n₀ n₁ env₀ env₁
              τvFun₀ τvFun₁ τvArg τ_out}
      (ht  : Nonempty (HasType ∅ Γ (.appN n₀ n₁) (Basis.tof (Basis.instantiate n₁ b₁))))
      (hbv : BasisValid Γ (Basis.instantiate n₁ b₁))
      (hτv : C.TyAt Γ Ψ (Basis.instantiate n₁ b₁) τ_out)
      (h₀ : C.Term ∅ Γ Ψ n₀ (.frame b₀ b₁) env₀ (.piTy τvFun₀ τvFun₁))
      (h₁ : C.Term ∅ Γ Ψ n₁ b₀ env₁ τvArg) :
      C.Term ∅ Γ Ψ (.appN n₀ n₁) (Basis.instantiate n₁ b₁)
        (.applyAt env₀ env₁ τ_out) τ_out

  | frame_reanchor {Γ Ψ b₀ b₀' b₁ n₀ leev env₁ τv₀ τv₀' τv₁ τv₁'}
      (htof : Basis.tof b₀' = Basis.tof b₀)
      (ht  : Nonempty (HasType ∅ Γ n₀ (Basis.tof (.frame b₀ b₁))))
      (hbv : BasisValid Γ (.frame b₀ b₁))
      (hτv : C.TyAt Γ Ψ (.frame b₀ b₁) (.piTy τv₀ τv₁'))
      (h₀   : C.TyAt Γ Ψ b₀ τv₀)
      (hfn  : C.Term ∅ Γ Ψ n₀ (.frame b₀' b₁) leev (.piTy τv₀' τv₁))
      (hdom : C.TyAt Γ Ψ b₀' τv₀')
      (L : Finset Name)
      (hx   : ∀ y, y ∉ L →
                C.Term ∅ (Finmap.insert y (Basis.tof b₀) Γ)
                  (Ψ.extend y b₀ (.var y τv₀))
                  (.var y) b₀' (ValExpr.openVar y τv₀ env₁) τv₀')
      (hcod : ∀ y, y ∉ L →
                C.TyAt (Finmap.insert y (Basis.tof b₀) Γ)
                  (Ψ.extend y b₀ (.var y τv₀))
                  (Basis.openVar y b₁) (ValTy.openVar y τv₀ τv₁')) :
      C.Term ∅ Γ Ψ n₀ (.frame b₀ b₁)
        (.vlam τv₀ τv₁'
          (.reshap
            (.applyValue leev
              (.reshap env₁ τv₀' τv₀'))
            τv₁' τv₁'))
        (.piTy τv₀ τv₁')

  | frame_eta {Γ Ψ b₀ b₁ n₀ τv₀ τv₁ env}
      (ht  : Nonempty (HasType ∅ Γ n₀ (Basis.tof (.frame b₀ b₁))))
      (hbv : BasisValid Γ (.frame b₀ b₁))
      (hτv : C.TyAt Γ Ψ (.frame b₀ b₁) (.piTy τv₀ τv₁))
      (h₀ : C.TyAt Γ Ψ b₀ τv₀)
      (L : Finset Name)
      (he : ∀ y, y ∉ L →
              C.Term ∅ (Finmap.insert y (Basis.tof b₀) Γ)
                (Ψ.extend y b₀ (.var y τv₀))
                (.appN n₀ (.var y)) (Basis.openVar y b₁)
                (ValExpr.openVar y τv₀ env) (ValTy.openVar y τv₀ τv₁))
      (h₁ : ∀ y, y ∉ L →
              C.TyAt (Finmap.insert y (Basis.tof b₀) Γ)
                (Ψ.extend y b₀ (.var y τv₀))
                (Basis.openVar y b₁) (ValTy.openVar y τv₀ τv₁)) :
      C.Term ∅ Γ Ψ n₀ (.frame b₀ b₁)
        (.vlam τv₀ τv₁ (.reshap env τv₁ τv₁))
        (.piTy τv₀ τv₁)

  | llam_assemble {Δ Γ Ψ b' b e sv' sv}
      {env : Fin (ValSpace.dofUB sv') → ValExpr}
      (htof' : Basis.tof b' = .space (Basis.sof b'))
      (ht  : Nonempty (HasType Δ Γ (.llam (Basis.sof b') (Basis.sof b) e)
               (Basis.tof (.tprod (.dual b') b))))
      (hbv : BasisValid Γ (.tprod (.dual b') b))
      (hτv : C.TyAt Γ Ψ (.tprod (.dual b') b) (.space (.tprod sv' sv)))
      (hsv' : C.Space Γ Ψ (Basis.sof b') sv')
      (hsv  : C.Space Γ Ψ (Basis.sof b) sv)
      (L : Finset Name)
      (hfam : ∀ y, y ∉ L → ∀ i : Fin (ValSpace.dofUB sv'),
                C.Term (Finmap.insert y (Basis.sof b') Δ) Γ
                  (Ψ.extend y b' (.delta i.val sv'))
                  (Term.openVar y e) b (env i) (.space sv)) :
      C.Term Δ Γ Ψ (.llam (Basis.sof b') (Basis.sof b) e)
        (.tprod (.dual b') b)
        (ValExpr.sumAt sv' (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
          .tprodE (.delta i.val sv') (ValExpr.reshapBase (env i) sv))
          (.tprod sv' sv))
        (.space (.tprod sv' sv))

  | llam_assemble_real {Δ Γ Ψ b' e sv'}
      {env : Fin (ValSpace.dofUB sv') → ValExpr}
      (htof' : Basis.tof b' = .space (Basis.sof b'))
      (ht  : Nonempty (HasType Δ Γ (.llam (Basis.sof b') .real e) (Basis.tof (.dual b'))))
      (hbv : BasisValid Γ (.dual b'))
      (hτv : C.TyAt Γ Ψ (.dual b') (.space sv'))
      (hsv' : C.Space Γ Ψ (Basis.sof b') sv')
      (L : Finset Name)
      (hfam : ∀ y, y ∉ L → ∀ i : Fin (ValSpace.dofUB sv'),
                C.Term (Finmap.insert y (Basis.sof b') Δ) Γ
                  (Ψ.extend y b' (.delta i.val sv'))
                  (Term.openVar y e) .one (env i) (.space .real)) :
      C.Term Δ Γ Ψ (.llam (Basis.sof b') .real e)
        (.dual b')
        (ValExpr.sumAt sv' (List.ofFn fun i : Fin (ValSpace.dofUB sv') =>
          .scale (ValExpr.reshapBase (env i) .real) (.delta i.val sv')) sv')
        (.space sv')

  | zero {Δ Γ Ψ b sv}
      (htof : Basis.tof b = .space (Basis.sof b))
      (ht  : Nonempty (HasType Δ Γ (.zero (Basis.sof b)) (Basis.tof b)))
      (hbv : BasisValid Γ b)
      (hτv : C.TyAt Γ Ψ b (.space sv))
      (hsv : C.Space Γ Ψ (Basis.sof b) sv) :
      C.Term Δ Γ Ψ (.zero (Basis.sof b)) b (.zero sv) (.space sv)
  /-- Real literal (`HasType.real_lit` × `OpStep.rlit`). -/
  | rlit {Γ Ψ} (r : ℝ)
      (ht  : Nonempty (HasType ∅ Γ (.real r) (Basis.tof .one)))
      (hτv : C.TyAt Γ Ψ .one (.space .real)) :
      C.Term ∅ Γ Ψ (.real r) .one (.rlit r) (.space .real)

end

end RawCertifiedOperational
end GLang
