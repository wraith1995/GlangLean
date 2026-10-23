/- Value-language syntax for GLang. -/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

namespace GLang

abbrev VName := String

inductive ValFFSProp : Type
  | kernel
  | cokernel
  | image
  | coimage
  deriving Repr, DecidableEq, Inhabited

/-- Ambient side of the selected fundamental subspace. -/
def ValFFSProp.ambient {α : Type} : ValFFSProp → α → α → α
  | .kernel, a, _ | .cokernel, a, _ => a
  | .image, _, b | .coimage, _, b => b

@[simp] theorem ValFFSProp.map_ambient {α β : Type} (which : ValFFSProp)
    (f : α → β) (a b : α) : f (which.ambient a b) = which.ambient (f a) (f b) := by
  cases which <;> rfl

mutual

  inductive ValSpace : Type
    | empty
    | real                                             -- `\lR`
    | dsum  : ValSpace → ValSpace → ValSpace           -- `\lsnv{0} \losum \lsnv{1}`
    | tprod : ValSpace → ValSpace → ValSpace

    | ffs : ValFFSProp → ValSpace → ValExpr → ValSpace

  inductive ValTy : Type
    | space : ValSpace → ValTy                          -- `\lsv` as a type
    | piTy  : ValTy → ValTy → ValTy                    -- `(x:\ltynv{0}) \fnto \ltynv{1}`; LOCALLY-NAMELESS: codomain is a *body* (`bvar 0` = the param)

  inductive ValExpr : Type
    -- Vector-space generic.
    | zero  : ValSpace → ValExpr                        -- `\lvzero_{\lsv}`
    | rlit  : ℝ → ValExpr                               -- `r ∈ ℝ`
    | scale : ValExpr → ValExpr → ValExpr               -- `\lenv{0} \lvscale \lenv{1}`
    | vadd  : ValSpace → ValExpr → ValExpr → ValExpr    -- `\lenv{0} \lvadd \lenv{1}` at result space
    | dsumE : ValExpr → ValExpr → ValExpr               -- `\lenv{0} \losum \lenv{1}`
    | tprodE : ValExpr → ValExpr → ValExpr              -- `\lenv{0} \loprod \lenv{1}`
    -- Basis vector / identity tensor.
    | delta  : Nat → ValSpace → ValExpr                 -- `\ldelta{n}{\lsv}`
    | idelta : ValSpace → ValExpr
    | vsum   : ValSpace → List ValExpr → ValExpr

    | vlam   : ValTy → ValTy → ValExpr → ValExpr

    | bvar   : Nat → ValExpr

    | var    : VName → ValTy → ValExpr

    | ttv    : ValSpace → ValExpr → ValExpr → ValExpr

    | mtm    : Nat → Nat → ValSpace → ValSpace → ValExpr → ValExpr → ValExpr
    -- Application (linear / non-linear share one constructor in the
    -- value layer; typing distinguishes).
    -- Its result type is obtained by substituting the argument into the
    -- function codomain, in both typing and inference.
    | appV   : ValExpr → ValExpr → ValExpr
    -- Kronecker / block products on values.
    | vkrn   : ValExpr → ValExpr → ValExpr              -- `\vkrn(\leev, \leevp)`
    | vblk   : ValExpr → ValExpr → ValExpr              -- `\vblk(\leev, \leevp)`
    -- Reshape between value types.  The target comes first; the source is
    -- stored explicitly for array dimension checks. Function reshaping uses
    -- the operand's inferred type instead (PartialValueEval.reshapeInferred).
    | reshap : ValExpr → ValTy → ValTy → ValExpr    -- `\Reshap(\leev, \ltyv_t, \ltyv_s)`
    -- Transpose of a tensor-shaped value.
    | vtrans : ValExpr → ValExpr                        -- `\Trans(\leev)`
    -- (G)SVD. All five share the (leev, lenv₀, lenv₁) triple.
    | gsvdS  : ValExpr → ValExpr → ValExpr → ValExpr
    | gsvdU  : ValExpr → ValExpr → ValExpr → ValExpr
    | gsvdUI : ValExpr → ValExpr → ValExpr → ValExpr
    | gsvdV  : ValExpr → ValExpr → ValExpr → ValExpr
    | gsvdVI : ValExpr → ValExpr → ValExpr → ValExpr

    | pinv   : ValExpr → ValExpr
    -- Generalized pseudo-inverse with explicit inner-product operands.
    | gpinv  : ValExpr → ValExpr → ValExpr → ValExpr
    -- RREF representation.
    | rrefRep : ValExpr → ValExpr → ValExpr

    | inv    : ValExpr → ValExpr

    | svds   : ValExpr → ValExpr

end

/-- Select a fundamental-subspace block of the canonical paired SVD.
This is a derived expression; the value language has only the SVD selectors. -/
def ValExpr.canonicalFSV (which : ValFFSProp) (e a b : ValExpr) : ValExpr :=
  match which with
  | .kernel => .gsvdUI e a b
  | .cokernel => .gsvdU e a b
  | .image => .gsvdV e a b
  | .coimage => .gsvdVI e a b

/-- Oracle-independent upper bound on the semantic degrees of freedom of a
    value space.  Fundamental-space ranks are bounded by the appropriate
    ambient tensor factor; composite spaces combine those bounds exactly as
    their dimensions combine.  This lives in the value-language layer so
    both the ordinary and strengthened operational semantics can require a
    dimension-complete finite family without depending on an oracle. -/
def ValSpace.dofUB : ValSpace → Nat
  | .empty        => 0
  | .real         => 1
  | .dsum s₀ s₁   => ValSpace.dofUB s₀ + ValSpace.dofUB s₁
  | .tprod s₀ s₁  => ValSpace.dofUB s₀ * ValSpace.dofUB s₁
  | .ffs .kernel   (.tprod s₀ _)  _ => ValSpace.dofUB s₀
  | .ffs .cokernel (.tprod s₀ _)  _ => ValSpace.dofUB s₀
  | .ffs .image    (.tprod _ s₁)  _ => ValSpace.dofUB s₁
  | .ffs .coimage  (.tprod _ s₁)  _ => ValSpace.dofUB s₁
  | .ffs _ s _    => ValSpace.dofUB s

inductive ValKind : Type
  | base
  | arrow : ValKind → ValKind → ValKind
  deriving Repr, DecidableEq, Inhabited

instance : Inhabited ValSpace := ⟨ValSpace.empty⟩
instance : Inhabited ValTy    := ⟨ValTy.space ValSpace.empty⟩
instance : Inhabited ValExpr  := ⟨ValExpr.zero ValSpace.empty⟩

end GLang
