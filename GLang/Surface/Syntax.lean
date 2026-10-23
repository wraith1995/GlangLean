import GLang.Core.NamesKinds
import Mathlib.Data.Real.Basic

namespace GLang.Surface

mutual
  inductive Space : Type
    | empty | real
    | dual : Space → Space
    | dsum : Space → Space → Space
    | tprod : Space → Space → Space
    | ker : Term → Space
    | coker : Term → Space
    | img : Term → Space
    | coimg : Term → Space
  inductive Ty : Type
    | space : Space → Ty
    | piTy : Ty → Ty → Ty
  inductive Term : Type
    | bvar : Nat → Term
    | var : Name → Term
    | real : ℝ → Term
    | zero : Space → Term
    | smul : Term → Term → Term
    | add : Term → Term → Term
    | inner : Space → Term
    | app : Term → Term → Term
    | llam : Space → Term → Term
    | nllam : Ty → Term → Term
    | pinv : Term → Term
    | dsumE : Term → Term → Term
    | tprodE : Term → Term → Term
    | embed : Space → Term
end

inductive Basis : Type
  | empty | one
  | dual : Basis → Basis
  | dsum : Basis → Basis → Basis
  | tprod : Basis → Basis → Basis
  | proj : Space → Basis → Basis → Basis
  | image : Basis → Basis
  | terms : List Term → Basis → Basis
  | frame : Basis → Basis → Basis

end GLang.Surface
