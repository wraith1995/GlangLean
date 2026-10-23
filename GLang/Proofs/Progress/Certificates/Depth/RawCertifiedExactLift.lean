import GLang.Proofs.Progress.CheckedErasure

/-!
# Exact lift of certified ordinary evaluation

The certified ordinary judgments and strengthened judgments have the same
constructor tree.  This module performs the structural namespace change and
then packages the term projection as the exact-lift interface used by the raw
adequacy boundary.  Source term, selected basis, produced value, and realized
result type are all preserved literally.
-/

namespace GLang
namespace RawCertifiedOperational

/- All five `.rec` entry points expose the same generated mutual recursor. -/
local macro "solve_exact_lift" "(" rec:term "," h:term ")" : tactic =>
  `(tactic| (
    refine ($rec
      (motive_1 := fun Γ Ψ s sv _ => S.Space Γ Ψ s sv)
      (motive_2 := fun Γ Ψ τ τv _ => S.Ty Γ Ψ τ τv)
      (motive_3 := fun Γ Ψ b τv _ => S.TyAt Γ Ψ b τv)
      (motive_4 := fun Γ Ψ b₀ env b₁ _ => S.Cob Γ Ψ b₀ env b₁)
      (motive_5 := fun Δ Γ Ψ e b v τv _ => S.Term Δ Γ Ψ e b v τv)
      ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
      ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
      ?tySpace ?tyPi
      ?tyAtSpace ?tyAtFrame
      ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
      ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
      ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
      ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
      ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
      ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
      ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
      ?termAppL ?termAppI ?termNllam ?termAppNVal
      ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
      ?termZero ?termRlit $h)
    case termAppNVal =>
      intros
      apply S.Term.appN_val <;> assumption
    case termAppL =>
      intros
      apply S.Term.appL_lin <;> assumption
    case termLlam =>
      intros
      apply S.Term.llam_assemble <;> assumption
    case termLlamReal =>
      intros
      apply S.Term.llam_assemble_real <;> assumption
    all_goals
      intros
      first | assumption | (constructor <;> assumption)))

/-- Exact structural lift of a checked space certificate. -/
theorem C.Space.toS
    (h : C.Space Γ Ψ s sv) : S.Space Γ Ψ s sv := by
  solve_exact_lift(C.Space.rec, h)

/-- Exact structural lift of a checked type certificate. -/
theorem C.Ty.toS
    (h : C.Ty Γ Ψ τ τv) : S.Ty Γ Ψ τ τv := by
  solve_exact_lift(C.Ty.rec, h)

/-- Exact structural lift of a checked basis-indexed type certificate. -/
theorem C.TyAt.toS
    (h : C.TyAt Γ Ψ b τv) : S.TyAt Γ Ψ b τv := by
  solve_exact_lift(C.TyAt.rec, h)

/-- Exact structural lift of a checked change-of-basis certificate. -/
theorem C.Cob.toS
    (h : C.Cob Γ Ψ b₀ env b₁) : S.Cob Γ Ψ b₀ env b₁ := by
  solve_exact_lift(C.Cob.rec, h)

/-- Exact term lift through the generated five-way mutual recursor.  Although
the entry point is a term, the five motives prove the corresponding `S`
judgment for every recursive space, type, exact type, COB, and term node.
Every handler is exactly the matching `S` constructor. -/
theorem C.Term.toS
    (h : C.Term Δ Γ Ψ e b v τv) : S.Term Δ Γ Ψ e b v τv :=
  by
    refine h.rec
      (motive_1 := fun Γ Ψ s sv _ => S.Space Γ Ψ s sv)
      (motive_2 := fun Γ Ψ τ τv _ => S.Ty Γ Ψ τ τv)
      (motive_3 := fun Γ Ψ b τv _ => S.TyAt Γ Ψ b τv)
      (motive_4 := fun Γ Ψ b₀ env b₁ _ => S.Cob Γ Ψ b₀ env b₁)
      (motive_5 := fun Δ Γ Ψ e b v τv _ => S.Term Δ Γ Ψ e b v τv)
      -- C.Space (10)
      ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
      ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
      -- C.Ty (3)
      ?tySpace ?tyPi
      -- C.TyAt (3)
      ?tyAtSpace ?tyAtFrame
      -- C.Cob (14)
      ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
      ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
      ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
      -- C.Term (29)
      ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
      ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
      ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
      ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
      ?termAppL ?termAppI ?termNllam ?termAppNVal
      ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
      ?termZero ?termRlit
    case termAppNVal =>
      intros
      apply S.Term.appN_val <;> assumption
    case termAppL =>
      intros
      apply S.Term.appL_lin <;> assumption
    case termLlam =>
      intros
      apply S.Term.llam_assemble <;> assumption
    case termLlamReal =>
      intros
      apply S.Term.llam_assemble_real <;> assumption
    all_goals
      intros
      first | assumption | (constructor <;> assumption)

end RawCertifiedOperational
end GLang
