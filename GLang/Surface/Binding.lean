import GLang.Surface.Syntax
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

namespace GLang.Surface

mutual
  def Space.openRec (k : Nat) (u : Term) : Space → Space
    | .empty => .empty
    | .real => .real
    | .dual s => .dual (s.openRec k u)
    | .dsum s t => .dsum (s.openRec k u) (t.openRec k u)
    | .tprod s t => .tprod (s.openRec k u) (t.openRec k u)
    | .ker e => .ker (Term.openRec k u e)
    | .coker e => .coker (Term.openRec k u e)
    | .img e => .img (Term.openRec k u e)
    | .coimg e => .coimg (Term.openRec k u e)
  def Ty.openRec (k : Nat) (u : Term) : Ty → Ty
    | .space s => .space (s.openRec k u)
    | .piTy a b => .piTy (Ty.openRec k u a) (Ty.openRec (k + 1) u b)
  def Term.openRec (k : Nat) (u : Term) : Term → Term
    | .bvar i => if i = k then u else .bvar i
    | .var x => .var x
    | .real r => .real r
    | .zero s => .zero (s.openRec k u)
    | .smul a b => .smul (Term.openRec k u a) (Term.openRec k u b)
    | .add a b => .add (Term.openRec k u a) (Term.openRec k u b)
    | .inner s => .inner (s.openRec k u)
    | .app a b => .app (Term.openRec k u a) (Term.openRec k u b)
    | .llam s e => .llam (s.openRec k u) (Term.openRec (k + 1) u e)
    | .nllam a e => .nllam (Ty.openRec k u a) (Term.openRec (k + 1) u e)
    | .pinv e => .pinv (Term.openRec k u e)
    | .dsumE a b => .dsumE (Term.openRec k u a) (Term.openRec k u b)
    | .tprodE a b => .tprodE (Term.openRec k u a) (Term.openRec k u b)
    | .embed s => .embed (s.openRec k u)
end

mutual
  def Space.subst (x : Name) (u : Term) : Space → Space
    | .empty => .empty
    | .real => .real
    | .dual s => .dual (s.subst x u)
    | .dsum s t => .dsum (s.subst x u) (t.subst x u)
    | .tprod s t => .tprod (s.subst x u) (t.subst x u)
    | .ker e => .ker (Term.subst x u e)
    | .coker e => .coker (Term.subst x u e)
    | .img e => .img (Term.subst x u e)
    | .coimg e => .coimg (Term.subst x u e)
  def Ty.subst (x : Name) (u : Term) : Ty → Ty
    | .space s => .space (s.subst x u)
    | .piTy a b => .piTy (Ty.subst x u a) (Ty.subst x u b)
  def Term.subst (x : Name) (u : Term) : Term → Term
    | .bvar i => .bvar i
    | .var y => if x = y then u else .var y
    | .real r => .real r
    | .zero s => .zero (s.subst x u)
    | .smul a b => .smul (Term.subst x u a) (Term.subst x u b)
    | .add a b => .add (Term.subst x u a) (Term.subst x u b)
    | .inner s => .inner (s.subst x u)
    | .app a b => .app (Term.subst x u a) (Term.subst x u b)
    | .llam s e => .llam (s.subst x u) (Term.subst x u e)
    | .nllam a e => .nllam (Ty.subst x u a) (Term.subst x u e)
    | .pinv e => .pinv (Term.subst x u e)
    | .dsumE a b => .dsumE (Term.subst x u a) (Term.subst x u b)
    | .tprodE a b => .tprodE (Term.subst x u a) (Term.subst x u b)
    | .embed s => .embed (s.subst x u)
end

abbrev Term.openVar (x : Name) := Term.openRec 0 (.var x)
abbrev Ty.openVar (x : Name) := Ty.openRec 0 (.var x)
abbrev Ty.instantiate := Ty.openRec 0

mutual
  def Space.fv : Space → Finset Name
    | .empty | .real => ∅
    | .dual s => s.fv
    | .dsum a b | .tprod a b => a.fv ∪ b.fv
    | .ker e | .coker e | .img e | .coimg e => e.fv
  def Ty.fv : Ty → Finset Name
    | .space s => s.fv
    | .piTy a b => a.fv ∪ b.fv
  def Term.fv : Term → Finset Name
    | .bvar _ | .real _ => ∅
    | .var x => {x}
    | .zero s | .inner s | .embed s => s.fv
    | .smul a b | .add a b | .app a b | .dsumE a b | .tprodE a b => a.fv ∪ b.fv
    | .llam s e => s.fv ∪ e.fv
    | .nllam t e => t.fv ∪ e.fv
    | .pinv e => e.fv
end

def Basis.openRec (k : Nat) (u : Term) : Basis → Basis
  | .empty => .empty
  | .one => .one
  | .dual b => .dual (b.openRec k u)
  | .dsum a b => .dsum (a.openRec k u) (b.openRec k u)
  | .tprod a b => .tprod (a.openRec k u) (b.openRec k u)
  | .proj s a b => .proj (s.openRec k u) (a.openRec k u) (b.openRec k u)
  | .image b => .image (b.openRec k u)
  | .terms es b => .terms (es.map (Term.openRec k u)) (b.openRec k u)
  | .frame a b => .frame (a.openRec k u) (b.openRec (k+1) u)

abbrev Basis.openVar (x : Name) := Basis.openRec 0 (.var x)

def Basis.sof : Basis → Space
  | .empty => .empty
  | .one => .real
  | .dual b => .dual b.sof
  | .dsum a b => .dsum a.sof b.sof
  | .tprod a b => .tprod a.sof b.sof
  | .proj s _ _ => s
  | .image b => match b.sof with | .coker e => .img e | _ => .empty
  | .terms _ b => b.sof
  | .frame _ _ => .empty

def Basis.tof : Basis → Ty
  | .frame a b => .piTy a.tof b.tof
  | b => .space b.sof

end GLang.Surface
