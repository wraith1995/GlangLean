import GLang.Paper
import GLang.Artifact
import Lean

namespace GLang.FrozenPaperDenotationTests
open PaperDenotationResults

-- The zero space has one vector; its ordered basis has no vectors.
example (σ : DEnv) : Nonempty (denotSpace σ .empty).carrier := ⟨0⟩
example (σ : DEnv) (v : (denotSpace σ .empty).carrier) : v = 0 := by
  exact @Subsingleton.elim PUnit inferInstance v 0
example (σ : DEnv) : denotBasis σ .empty = .vecs HSpace.empty [] := by
  rw [denotBasis]

-- Tensor/linear-map identification preserves evaluation, with linearity
-- deduced from the typing derivation, including promotion.
example (hctx : InductiveCtxWF Δ ε)
    (ht : HasType Δ ε (.llam s₀ s₁ body) (.space (.tprod (.dual s₀) s₁)))
    (hσ : EnvWF σ Δ ε) (a : (denotSpace σ s₀).carrier) :
    (denotTerm σ (.llam s₀ s₁ body)).asLinMap (denotSpace σ s₀) (denotSpace σ s₁) a =
      (denotTermAux σ [.hil ⟨denotSpace σ s₀, a⟩] body).atSpace (denotSpace σ s₁) :=
  linearTensor_apply hctx ht hσ a
example (hctx : InductiveCtxWF Δ ε)
    (ht : HasType Δ ε (.llam s .real body) (.space (.dual s)))
    (hσ : EnvWF σ Δ ε) (a : (denotSpace σ s).carrier) :
    (denotTerm σ (.llam s .real body)).atSpace (HSpace.dual (denotSpace σ s)) a =
      (denotTermAux σ [.hil ⟨denotSpace σ s, a⟩] body).atSpace HSpace.real :=
  linearReal_apply hctx ht hσ a

-- An arbitrary raw lambda need not have the displayed body function.
-- The malformed constant-one linear lambda cannot map zero to one.
example (σ : DEnv) :
    (denotTerm σ (.llam .real .real (.real 1))).atSpace (HSpace.dual HSpace.real) 0 = 0 :=
  map_zero _

-- Named binder semantics also applies to genuinely higher-order domains.
example {σ : DEnv} {d c : Ty} {e : Term} {x : Name}
    (he : Term.lc (Term.openVar x e)) (hx : x ∉ Term.fv e)
    (f : (denotTy σ (.piTy d c)).El) :
    (denotTerm σ (.nllam (.piTy d c) e)).applyEl f =
      denotTerm (σ.bind x ((denotTy σ (.piTy d c)).embed f)) (Term.openVar x e) :=
  nonlinear_apply he hx f
example {σ : DEnv} {d c : Ty} {x : Name}
    (hc : Ty.lc (Ty.openVar x c)) (hx : x ∉ Ty.fv c) :
    denotTy σ (.piTy d c) = HType.sec (denotTy σ d).El
      (fun a => denotTy (σ.bind x ((denotTy σ d).embed a)) (Ty.openVar x c)) :=
  dependentType_named hc hx
example {σ : DEnv} {b₀ b₁ : Basis} (x : Name) (hx : x ∉ Basis.fv b₁)
    (a : (denotTy σ (Basis.tof b₀)).El) :
    (denotBasis σ (.frame b₀ b₁)).applyEl a =
      denotBasis (σ.bind x ((denotTy σ (Basis.tof b₀)).embed a)) (Basis.openVar x b₁) :=
  denotBasis_frame_applyEl_openVar x hx a

-- The denotation's fixed inner products are exactly its `innerOf` choice.
example (hctx : InductiveCtxWF ∅ ε) (hσ : EnvWF σ ∅ ε)
    (hs : SValid ε s) (hfresh : IofFresh ε) :
    (denotTerm σ (.inner s)).asLinMap (denotSpace σ s) (HSpace.dual (denotSpace σ s)) =
      (denotTerm σ (Space.iof s)).asLinMap (denotSpace σ s) (HSpace.dual (denotSpace σ s)) :=
  inner_eq_innerOf hctx hσ hs hfresh

-- A dual basis is dual even when the original basis is not orthonormal.
example {V : HSpace} {vs : List V.carrier} (h : IsListBasis V vs)
    (i j : Fin vs.length) : (V.dualVec vs i) (vs.get j) = if i = j then 1 else 0 :=
  h.dual_delta i j

-- The displayed comprehensions retain order: the first tensor index is outer.
example (V W : HSpace) (xs : List V.carrier) (ys : List W.carrier) :
    HSpace.tprodOfLists V W xs ys = xs.flatMap (fun x => ys.map (fun y => x ⊗ₜ[ℝ] y)) := rfl
example (V W : HSpace) (xs : List V.carrier) (ys : List W.carrier) :
    HSpace.dsumOfLists V W xs ys =
      xs.map (fun x => (x, 0)) ++ ys.map (fun y => (0, y)) := rfl

-- The projected-basis subtype conversion cannot drop an FSV vector in any
-- of the four cases. The existing pointwise theorem also preserves order.
example (V W : HSpace) (f : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier) :
    (HSpace.liftToSubmodule (LinearMap.ker f)
      (BasisFSV.fsvLeft V W f (fun μ => decide (μ = 0)) xs ys)).length =
      (BasisFSV.fsvLeft V W f (fun μ => decide (μ = 0)) xs ys).length :=
  HSpace.liftToSubmodule_length_of_subset _ _ (BasisFSV.fsvLeft_subset_ker V W f xs ys)
example (V W : HSpace) (f : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier) :
    (HSpace.liftToSubmodule (Submodule.orthRel V.innerProduct (LinearMap.ker f))
      (BasisFSV.fsvLeft V W f (fun μ => decide (μ ≠ 0)) xs ys)).length =
      (BasisFSV.fsvLeft V W f (fun μ => decide (μ ≠ 0)) xs ys).length :=
  HSpace.liftToSubmodule_length_of_subset _ _ (BasisFSV.fsvLeft_subset_coker V W f xs ys)
example (V W : HSpace) (f : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier) :
    (HSpace.liftToSubmodule (LinearMap.range f)
      (BasisFSV.fsvRight V W f (fun μ => decide (μ ≠ 0)) xs ys)).length =
      (BasisFSV.fsvRight V W f (fun μ => decide (μ ≠ 0)) xs ys).length :=
  HSpace.liftToSubmodule_length_of_subset _ _ (BasisFSV.fsvRight_subset_range V W f xs ys)
example (V W : HSpace) (f : V.carrier →ₗ[ℝ] W.carrier)
    (xs : List V.carrier) (ys : List W.carrier) :
    (HSpace.liftToSubmodule (Submodule.orthRel W.innerProduct (LinearMap.range f))
      (BasisFSV.fsvRight V W f (fun μ => decide (μ = 0)) xs ys)).length =
      (BasisFSV.fsvRight V W f (fun μ => decide (μ = 0)) xs ys).length :=
  HSpace.liftToSubmodule_length_of_subset _ _ (BasisFSV.fsvRight_subset_coimg V W f xs ys)

open Lean Meta Elab Command in
elab "check_frozen_denotation_catalogue" : command => liftTermElabM do
  for n in #[``linearTensor_apply, ``linearReal_apply, ``nonlinear_apply,
      ``dependentType_named, ``inner_eq_innerOf, ``denotBasis_frame_applyEl_openVar,
      ``IsListBasis.dual_delta, ``HSpace.liftToSubmodule_get_val_of_subset] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected denotation axiom in {n}: {ax}"
  logInfo "Denotation bridges use standard foundations."

check_frozen_denotation_catalogue
end GLang.FrozenPaperDenotationTests
