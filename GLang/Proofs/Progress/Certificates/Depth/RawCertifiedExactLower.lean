import GLang.Proofs.Progress.CheckedErasure

/-!
# Exact lowering from strengthened evaluation to the checked ordinary semantics

The checked and strengthened judgments have the same constructor tree.  This
module records the reverse structural map to `C.Term.toS`, preserving every
source, basis, value, and realized-type index literally.  Besides making the
two presentations visibly equivalent, the map lets checked-progress work
reuse strengthened structural lemmas and turns exact `S.TyAt` certificates
stored by `RawConsistent` into checked certificates without an axiom.
-/

namespace GLang
namespace RawCertifiedOperational

/- All five `.rec` entry points expose the same generated mutual recursor.
Keeping the handler list in one local tactic avoids four more copies of its
59 constructor cases. -/
local macro "solve_exact_lower" "(" rec:term "," h:term ")" : tactic =>
  `(tactic| (
    refine ($rec
      (motive_1 := fun Γ Ψ s sv _ => C.Space Γ Ψ s sv)
      (motive_2 := fun Γ Ψ τ τv _ => C.Ty Γ Ψ τ τv)
      (motive_3 := fun Γ Ψ b τv _ => C.TyAt Γ Ψ b τv)
      (motive_4 := fun Γ Ψ b₀ env b₁ _ => C.Cob Γ Ψ b₀ env b₁)
      (motive_5 := fun Δ Γ Ψ e b v τv _ => C.Term Δ Γ Ψ e b v τv)
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
      apply C.Term.appN_val <;> assumption
    case termAppL =>
      intros
      apply C.Term.appL_lin <;> assumption
    case termLlam =>
      intros
      apply C.Term.llam_assemble <;> assumption
    case termLlamReal =>
      intros
      apply C.Term.llam_assemble_real <;> assumption
    all_goals
      intros
      first | assumption | (constructor <;> assumption)))

/-- Exact lowering of a strengthened space certificate. -/
theorem S.Space.toC
    (h : S.Space Γ Ψ s sv) : C.Space Γ Ψ s sv := by
  solve_exact_lower(S.Space.rec, h)

/-- Exact lowering of a strengthened type certificate. -/
theorem S.Ty.toC
    (h : S.Ty Γ Ψ τ τv) : C.Ty Γ Ψ τ τv := by
  solve_exact_lower(S.Ty.rec, h)

/-- Exact lowering of a strengthened basis-indexed type certificate. -/
theorem S.TyAt.toC
    (h : S.TyAt Γ Ψ b τv) : C.TyAt Γ Ψ b τv := by
  solve_exact_lower(S.TyAt.rec, h)

/-- Exact lowering of a strengthened change-of-basis certificate. -/
theorem S.Cob.toC
    (h : S.Cob Γ Ψ b₀ env b₁) : C.Cob Γ Ψ b₀ env b₁ := by
  solve_exact_lower(S.Cob.rec, h)

/-- Exact lowering through the generated five-way mutual recursor. -/
theorem S.Term.toC
    (h : S.Term Δ Γ Ψ e b v τv) : C.Term Δ Γ Ψ e b v τv :=
  by
    refine h.rec
      (motive_1 := fun Γ Ψ s sv _ => C.Space Γ Ψ s sv)
      (motive_2 := fun Γ Ψ τ τv _ => C.Ty Γ Ψ τ τv)
      (motive_3 := fun Γ Ψ b τv _ => C.TyAt Γ Ψ b τv)
      (motive_4 := fun Γ Ψ b₀ env b₁ _ => C.Cob Γ Ψ b₀ env b₁)
      (motive_5 := fun Δ Γ Ψ e b v τv _ => C.Term Δ Γ Ψ e b v τv)
      -- S.Space (10)
      ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
      ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
      -- S.Ty (3)
      ?tySpace ?tyPi
      -- S.TyAt (3)
      ?tyAtSpace ?tyAtFrame
      -- S.Cob (14)
      ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
      ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
      ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
      -- S.Term (29)
      ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
      ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
      ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
      ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
      ?termAppL ?termAppI ?termNllam ?termAppNVal
      ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
      ?termZero ?termRlit
    case termAppNVal =>
      intros
      apply C.Term.appN_val <;> assumption
    case termAppL =>
      intros
      apply C.Term.appL_lin <;> assumption
    case termLlam =>
      intros
      apply C.Term.llam_assemble <;> assumption
    case termLlamReal =>
      intros
      apply C.Term.llam_assemble_real <;> assumption
    all_goals
      intros
      first | assumption | (constructor <;> assumption)

end RawCertifiedOperational
end GLang
