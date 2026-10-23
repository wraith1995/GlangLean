

import GLang.Annotated.Binding
import GLang.Proofs.Source.FreeVars
import GLang.Annotated.Judgments
import GLang.Annotated.Denotation
import GLang.Proofs.Source.FVIrrelevance
import Mathlib.Data.Finmap

namespace GLang

structure CtxWF (Δ : LCtx) (ε : NLCtx) : Prop where
  /-- `ε ∩ Δ = ∅` — linear and non-linear namespaces are disjoint. -/
  disjoint  : ∀ x, x ∈ Δ → x ∉ ε
  /-- Barendregt: linear-binding spaces only mention non-linear names. -/
  lin_fv_in_ε : ∀ x s, Δ.lookup x = some s → ∀ y ∈ Space.fv s, y ∈ ε
  /-- Barendregt: non-linear-binding types only mention non-linear names. -/
  nl_fv_in_ε : ∀ x τ, ε.lookup x = some τ → ∀ y ∈ Ty.fv τ, y ∈ ε

structure EnvWF (σ : DEnv) (Δ : LCtx) (ε : NLCtx) : Prop where
  /-- For each `(x, s) ∈ Δ`: `σ.vars.lookup x = some v` and `v`'s shape
      is exactly `HType.hil (denotSpace σ s)`. -/
  lin_match : ∀ x s, Δ.lookup x = some s →
              ∃ v, σ.vars.lookup x = some v ∧
                   v.matchesShape (HType.hil (denotSpace σ s))
  /-- For each `(x, τ) ∈ ε`: `σ.vars.lookup x = some v` and `v`'s shape
      is exactly `denotTy σ τ`. -/
  nl_match  : ∀ x τ, ε.lookup x = some τ →
              ∃ v, σ.vars.lookup x = some v ∧
                   v.matchesShape (denotTy σ τ)

end GLang
