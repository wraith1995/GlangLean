import GLang.Annotated.Binding
import GLang.Proofs.Source.FreeVars
import GLang.Annotated.Judgments
import GLang.Proofs.Source.SourceLN

/-! Basis space/type operations and validity, including dependent frames.
Raw projections are total; validity excludes their fallback cases. -/
namespace GLang

/-! Basis substitution uses locally nameless binding. In `frame b₀ b₁`,
`bvar 0` in `b₁` refers to the frame parameter. -/

def Basis.sof : Basis → Space
  | .empty           => .empty
  | .one             => .real
  | .dual b          => .dual (Basis.sof b)
  | .dsum b₀ b₁      => .dsum (Basis.sof b₀) (Basis.sof b₁)
  | .tprod b₀ b₁     => .tprod (Basis.sof b₀) (Basis.sof b₁)
  | .proj s _ _      => s
  | .image b         =>
      match Basis.sof b with
      | .coker s₀ s₁ e => .img s₀ s₁ e
      | _              => .empty
  | .terms _ _ b     => Basis.sof b
  | .frame _ _       => .empty  -- frames have a type, not a space

/-- `Basis.tof` extends `sof` to cover frames: a frame is the basis
    analogue of a dependent function type. Non-frame bases have
    `tof = .space (sof b)`. -/
def Basis.tof : Basis → Ty
  | .frame b₀ b₁     => .piTy (Basis.tof b₀) (Basis.tof b₁)
  | b                => .space (Basis.sof b)

/-- A basis is matrix-compatible for the four-fundamental-space evaluator when
    it is syntactically a tensor of a dual domain basis and a codomain basis.

    This condition is stronger than merely representing the source tensor
    space: the FFS oracle reshapes the witness coordinates as a matrix, so its
    rows and columns must come from separate endpoint bases. -/
def Basis.FFSMatrixCompatible (b : Basis) : Prop :=
  ∃ b₀ b₁, b = .tprod (.dual b₀) b₁

/-- Basis validity, with cofinite opening of frame bodies and explicit
formation and typing premises. -/
inductive Basis.BasisValid : NLCtx → Basis → Prop
  | empty {ε} : Basis.BasisValid ε .empty
  | one   {ε} : Basis.BasisValid ε .one
  | dual  {ε b} : Basis.BasisValid ε b →
      Basis.tof b = .space (Basis.sof b) →
      Basis.BasisValid ε (.dual b)
  | dsum  {ε b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space (Basis.sof b₀) →
      Basis.tof b₁ = .space (Basis.sof b₁) →
      Basis.BasisValid ε (.dsum b₀ b₁)
  | tprod {ε b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space (Basis.sof b₀) →
      Basis.tof b₁ = .space (Basis.sof b₁) →
      Basis.BasisValid ε (.tprod b₀ b₁)

  | proj_ker {ε s₀ s₁ e b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space s₀ → Basis.tof b₁ = .space s₁ →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.proj (.ker s₀ s₁ e) b₀ b₁)
  | proj_coker {ε s₀ s₁ e b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space s₀ → Basis.tof b₁ = .space s₁ →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.proj (.coker s₀ s₁ e) b₀ b₁)
  | proj_img {ε s₀ s₁ e b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space s₀ → Basis.tof b₁ = .space s₁ →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.proj (.img s₀ s₁ e) b₀ b₁)
  | proj_coimg {ε s₀ s₁ e b₀ b₁} : Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space s₀ → Basis.tof b₁ = .space s₁ →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.proj (.coimg s₀ s₁ e) b₀ b₁)

  | image {ε b s₀ s₁ e} : Basis.BasisValid ε b → Basis.sof b = .coker s₀ s₁ e →
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) →
      Basis.BasisValid ε (.image b)

  | terms {ε s es b} : Basis.BasisValid ε b → Basis.tof b = .space s →
      Nonempty (SValid ε s) →
      (∀ e ∈ es, Nonempty (HasType ∅ ε e (.space s))) →
      es ≠ [] →
      Basis.BasisValid ε (.terms s es b)

  | frame {ε b₀ b₁} (L : Finset Name) :
      Basis.BasisValid ε b₀ →
      (∀ y, y ∉ L →
        Basis.BasisValid (Finmap.insert y (Basis.tof b₀) ε) (Basis.openVar y b₁)) →
      Basis.BasisValid ε (.frame b₀ b₁)

end GLang
