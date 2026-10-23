/-
Mathematical helpers for source denotation: bundled finite-dimensional real
Hilbert spaces, inner products, tensor products, subspaces, and pseudoinverses.
The mutual interpretation is in `Annotated/Denotation.lean`; bundled values,
dependent fibers, and environments are in `Semantics/SourceValues.lean`.
-/

import GLang.Annotated.Binding
import GLang.Annotated.Judgments
import Mathlib.Data.Finmap
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.InnerProductSpace.TensorProduct

namespace GLang

open scoped TensorProduct

/-! ## Inner-product structure (used by HSpace). -/

/-- A bilinear form on a real vector space is a *valid inner product* iff
    it is symmetric, positive semi-definite, and definite. -/
def IsInnerProduct {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : Prop :=
  (∀ x y, B x y = B y x) ∧
  (∀ x, 0 ≤ B x x) ∧
  (∀ x, B x x = 0 → x = 0)

/-- The standard inner product on ℝ (multiplication) is a valid inner product. -/
lemma isInnerProduct_mul : IsInnerProduct (LinearMap.mul ℝ ℝ) :=
  ⟨fun x y => by simp [mul_comm],
   fun x => by simpa using mul_self_nonneg x,
   fun x hx => by simpa using mul_self_eq_zero.mp hx⟩

/-- Basis-induced standard inner product on a finite-dim ℝ-vector space.
    `B(x, y) := Σ_i (b.repr x i) * (b.repr y i)`. -/
noncomputable def basisStandardIP {V : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V] (b : Module.Basis ι ℝ V) :
    V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun x y => ∑ i, b.repr x i * b.repr y i)
    (by intros; simp; rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intros; ring)
    (by intros; simp; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intros; ring)
    (by intros; simp; rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intros; ring)
    (by intros; simp; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intros; ring)

/-- The basis-induced standard IP is an inner product. -/
lemma basisStandardIP_isInnerProduct {V : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℝ V] (b : Module.Basis ι ℝ V) :
    IsInnerProduct (basisStandardIP b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    show ∑ i, b.repr x i * b.repr y i = ∑ i, b.repr y i * b.repr x i
    apply Finset.sum_congr rfl; intros; ring
  · intro x
    show 0 ≤ ∑ i, b.repr x i * b.repr x i
    apply Finset.sum_nonneg; intros; exact mul_self_nonneg _
  · intro x hx
    show x = 0
    have h_each : ∀ i ∈ Finset.univ, b.repr x i * b.repr x i = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_self_nonneg _)).mp
      exact hx
    have h_coord : ∀ i, b.repr x i = 0 := by
      intro i
      have := h_each i (Finset.mem_univ i)
      exact mul_self_eq_zero.mp this
    have h_repr : b.repr x = (b.repr 0 : _) := by
      ext i; simp; exact h_coord i
    exact b.repr.injective h_repr

/-- Promote a valid inner product to an `InnerProductSpace.Core` over ℝ. -/
@[reducible] noncomputable def IsInnerProduct.toIPSCoreEarly {V : Type}
    [AddCommGroup V] [Module ℝ V]
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (h : IsInnerProduct B) :
    InnerProductSpace.Core ℝ V where
  inner x y := B x y
  conj_inner_symm x y := by simp [h.1 y x]
  re_inner_nonneg x := by simpa using h.2.1 x
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := h.2.2 x hx

/-- **Riesz inverse**: for a PD bilinear form `B` on a finite-dim real vector
    space `V`, the curry `B : V →ₗ V*` is a linear bijection. The Riesz
    inverse `♯ : V* →ₗ V` is its inverse.

    Injective: if `B x = 0` as a functional, then `B x x = 0`, so `x = 0` by
    definiteness. Bijective: `dim V = dim V*` for finite-dim V, and injective
    + same finite dim ⇒ surjective. -/
noncomputable def IsInnerProduct.rieszInv {V : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (h : IsInnerProduct B) :
    (V →ₗ[ℝ] ℝ) →ₗ[ℝ] V :=
  letI h_inj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hx' : B x = 0 := LinearMap.mem_ker.mp hx
    have hxx : B x x = 0 := by rw [hx']; rfl
    exact h.2.2 x hxx
  letI h_dim : Module.finrank ℝ V = Module.finrank ℝ (V →ₗ[ℝ] ℝ) :=
    Subspace.dual_finrank_eq.symm
  (LinearMap.linearEquivOfInjective B h_inj h_dim).symm.toLinearMap

/-- The Riesz inverse is injective (since it's a `LinearEquiv.symm`). -/
lemma IsInnerProduct.rieszInv_injective {V : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (h : IsInnerProduct B) :
    Function.Injective h.rieszInv := by
  unfold IsInnerProduct.rieszInv
  exact (LinearMap.linearEquivOfInjective _ _ _).symm.injective

/-! ## Bundled finite-dimensional real Hilbert spaces. -/

/-- Bundled finite-dimensional real Hilbert space: carrier + algebraic
    structure + an *inner product*. -/
structure HSpace : Type 1 where
  carrier : Type
  [acg : AddCommGroup carrier]
  [mod : Module ℝ carrier]
  [fd  : FiniteDimensional ℝ carrier]
  /-- The inner product (PD bilinear form). -/
  innerProduct : carrier →ₗ[ℝ] carrier →ₗ[ℝ] ℝ
  innerIsIP : IsInnerProduct innerProduct

attribute [instance] HSpace.acg HSpace.mod HSpace.fd

namespace HSpace

@[reducible] noncomputable def empty : HSpace where
  carrier := PUnit
  innerProduct := 0
  innerIsIP := by
    refine ⟨fun _ _ => ?_, fun _ => ?_, fun _ _ => ?_⟩
    · simp
    · simp
    · rfl

@[reducible] noncomputable def real : HSpace where
  carrier := ℝ
  innerProduct := LinearMap.mul ℝ ℝ
  innerIsIP := isInnerProduct_mul

@[reducible] noncomputable def dsum (V W : HSpace) : HSpace where
  carrier := V.carrier × W.carrier
  innerProduct :=
    LinearMap.mk₂ ℝ
      (fun p q => V.innerProduct p.1 q.1 + W.innerProduct p.2 q.2)
      (by intros; simp; ring)
      (by intros; simp; ring)
      (by intros; simp; ring)
      (by intros; simp; ring)
  innerIsIP := by
    refine ⟨?_, ?_, ?_⟩
    · intro p q
      show V.innerProduct p.1 q.1 + W.innerProduct p.2 q.2 =
            V.innerProduct q.1 p.1 + W.innerProduct q.2 p.2
      rw [V.innerIsIP.1, W.innerIsIP.1]
    · intro p
      show 0 ≤ V.innerProduct p.1 p.1 + W.innerProduct p.2 p.2
      exact add_nonneg (V.innerIsIP.2.1 _) (W.innerIsIP.2.1 _)
    · intro p hp
      show p = 0
      have hp' : V.innerProduct p.1 p.1 + W.innerProduct p.2 p.2 = 0 := hp
      have h_nn₀ := V.innerIsIP.2.1 p.1
      have h_nn₁ := W.innerIsIP.2.1 p.2
      have h_eq : V.innerProduct p.1 p.1 = 0 ∧ W.innerProduct p.2 p.2 = 0 := by
        constructor <;> linarith
      exact Prod.ext (V.innerIsIP.2.2 _ h_eq.1) (W.innerIsIP.2.2 _ h_eq.2)

/-- Tensor product HSpace. Inner product is the **canonical tensor IP**:
    `(V.IP ⊗ W.IP)(a⊗b, c⊗d) := V.IP(a,c) · W.IP(b,d)` via
    `LinearMap.BilinForm.tmul`.

    PD-preservation under tensor product is proved via Mathlib's
    `TensorProduct.instInnerProductSpace`: promote V, W to IPSs via
    their PD bilinear forms, then the tensor product is also an IPS,
    yielding the required PD on `V.IP.tmul W.IP`. -/
@[reducible] noncomputable def tprod (V W : HSpace) : HSpace where
  carrier := V.carrier ⊗[ℝ] W.carrier
  innerProduct := LinearMap.BilinForm.tmul V.innerProduct W.innerProduct
  innerIsIP := by
    letI coreV : InnerProductSpace.Core ℝ V.carrier :=
      IsInnerProduct.toIPSCoreEarly V.innerIsIP
    letI coreW : InnerProductSpace.Core ℝ W.carrier :=
      IsInnerProduct.toIPSCoreEarly W.innerIsIP
    letI nagV : NormedAddCommGroup V.carrier :=
      InnerProductSpace.Core.toNormedAddCommGroup (cd := coreV)
    letI nagW : NormedAddCommGroup W.carrier :=
      InnerProductSpace.Core.toNormedAddCommGroup (cd := coreW)
    letI ipsV : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
    letI ipsW : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance
    have h_bridge : ∀ x y : V.carrier ⊗[ℝ] W.carrier,
        LinearMap.BilinForm.tmul V.innerProduct W.innerProduct x y =
          @inner ℝ (V.carrier ⊗[ℝ] W.carrier) _ x y := by
      intro x y
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul c d =>
          show W.innerProduct b d * V.innerProduct a c =
            @inner ℝ V.carrier _ a c * @inner ℝ W.carrier _ b d
          show W.innerProduct b d * V.innerProduct a c =
            V.innerProduct a c * W.innerProduct b d
          ring
        | add y₁ y₂ ih₁ ih₂ =>
          rw [map_add (LinearMap.BilinForm.tmul V.innerProduct W.innerProduct _),
              ih₁, ih₂, inner_add_right]
      | add x₁ x₂ ih₁ ih₂ =>
        rw [show ((LinearMap.BilinForm.tmul V.innerProduct W.innerProduct) (x₁ + x₂)) y
                = ((LinearMap.BilinForm.tmul V.innerProduct W.innerProduct) x₁) y
                  + ((LinearMap.BilinForm.tmul V.innerProduct W.innerProduct) x₂) y from by
              rw [map_add (LinearMap.BilinForm.tmul V.innerProduct W.innerProduct) x₁ x₂,
                  LinearMap.add_apply],
            ih₁, ih₂]
        exact (inner_add_left x₁ x₂ y).symm
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      rw [h_bridge x y, h_bridge y x]
      exact real_inner_comm y x
    · intro x
      rw [h_bridge x x]
      exact @real_inner_self_nonneg _ _ _ x
    · intro x hx
      rw [h_bridge x x] at hx
      exact @inner_self_eq_zero ℝ _ _ _ _ x |>.mp hx

@[reducible] noncomputable def dual (V : HSpace) : HSpace where
  carrier := V.carrier →ₗ[ℝ] ℝ
  innerProduct :=
    V.innerProduct.compl₁₂ V.innerIsIP.rieszInv V.innerIsIP.rieszInv
  innerIsIP := by
    refine ⟨?_, ?_, ?_⟩
    · intro φ ψ
      show V.innerProduct (V.innerIsIP.rieszInv φ) (V.innerIsIP.rieszInv ψ) =
           V.innerProduct (V.innerIsIP.rieszInv ψ) (V.innerIsIP.rieszInv φ)
      exact V.innerIsIP.1 _ _
    · intro φ
      show 0 ≤ V.innerProduct (V.innerIsIP.rieszInv φ) (V.innerIsIP.rieszInv φ)
      exact V.innerIsIP.2.1 _
    · intro φ hφ
      show φ = 0
      have h_sharp_zero : V.innerIsIP.rieszInv φ = 0 :=
        V.innerIsIP.2.2 _ hφ
      have h_inj := V.innerIsIP.rieszInv_injective
      have : V.innerIsIP.rieszInv φ = V.innerIsIP.rieszInv 0 := by
        rw [h_sharp_zero, map_zero]
      exact h_inj this

/-- Wrap a Mathlib submodule of `V`'s carrier as an `HSpace`. The
    submodule inherits its algebraic structure + IP from `V` (restriction). -/
@[reducible] noncomputable def ofSubmodule (V : HSpace)
    (K : Submodule ℝ V.carrier) : HSpace where
  carrier := K
  innerProduct := LinearMap.BilinForm.restrict V.innerProduct K
  innerIsIP := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y; simpa using V.innerIsIP.1 x y
    · intro x; simpa using V.innerIsIP.2.1 x
    · intro x hx
      have : (x : V.carrier) = 0 := V.innerIsIP.2.2 _ (by simpa using hx)
      exact Subtype.ext this

end HSpace

/-- Orthogonal complement of `K` in `V` relative to a bilinear form `B`:
    `K⊥ = { v ∈ V | ∀ k ∈ K, B v k = 0 }`. Realised as the preimage
    under `B : V →ₗ V*` of `K`'s annihilator in `V*`. -/
noncomputable def Submodule.orthRel {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (K : Submodule ℝ V) : Submodule ℝ V :=
  Submodule.comap B K.dualAnnihilator

/-- Promote a valid inner product to an `InnerProductSpace.Core` over ℝ. -/
@[reducible] noncomputable def IsInnerProduct.toIPSCore {V : Type}
    [AddCommGroup V] [Module ℝ V]
    {B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} (h : IsInnerProduct B) :
    InnerProductSpace.Core ℝ V where
  inner x y := B x y
  conj_inner_symm x y := by simp [h.1 y x]
  re_inner_nonneg x := by simpa using h.2.1 x
  add_left x y z := by simp
  smul_left x y r := by simp
  definite x hx := h.2.2 x hx

noncomputable def LinearMap.ofFun {V W : Type*}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (f : V → W) : V →ₗ[ℝ] W :=
  open Classical in
  if h_add : ∀ x y, f (x + y) = f x + f y then
    if h_smul : ∀ (c : ℝ) x, f (c • x) = c • f x then
      { toFun := f, map_add' := h_add, map_smul' := h_smul }
    else 0
  else 0

noncomputable def LinearMap.mooreInv {V₀ V₁ : Type}
    [AddCommGroup V₀] [Module ℝ V₀] [FiniteDimensional ℝ V₀]
    [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
    {B₀ : V₀ →ₗ[ℝ] V₀ →ₗ[ℝ] ℝ} (h₀ : IsInnerProduct B₀)
    {B₁ : V₁ →ₗ[ℝ] V₁ →ₗ[ℝ] ℝ} (h₁ : IsInnerProduct B₁)
    (f : V₀ →ₗ[ℝ] V₁) : V₁ →ₗ[ℝ] V₀ :=
  letI core₀ : InnerProductSpace.Core ℝ V₀ := h₀.toIPSCore
  letI core₁ : InnerProductSpace.Core ℝ V₁ := h₁.toIPSCore
  letI nag₀ : NormedAddCommGroup V₀ :=
    InnerProductSpace.Core.toNormedAddCommGroup (cd := core₀)
  letI nag₁ : NormedAddCommGroup V₁ :=
    InnerProductSpace.Core.toNormedAddCommGroup (cd := core₁)
  letI ips₀ : InnerProductSpace ℝ V₀ := InnerProductSpace.ofCore inferInstance
  letI ips₁ : InnerProductSpace ℝ V₁ := InnerProductSpace.ofCore inferInstance
  -- ker f, its orthogonal complement, range f.
  let R  : Submodule ℝ V₁ := LinearMap.range f
  -- Orthogonal projection onto range f (continuous linear map V₁ →L R).
  let P  : V₁ →L[ℝ] R := Submodule.orthogonalProjection R
  -- Restriction of f to (ker f)ᗮ with codomain restricted to range f.
  let f_restr : ((LinearMap.ker f)ᗮ : Submodule ℝ V₀) →ₗ[ℝ] R :=
    LinearMap.codRestrict R (f ∘ₗ (LinearMap.ker f)ᗮ.subtype)
      (fun ⟨x, _⟩ => ⟨x, rfl⟩)
  -- Injectivity: ker(f) ∩ (ker f)ᗮ = ⊥ in a PD inner product space.
  have inj : Function.Injective f_restr := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ heq
    apply Subtype.ext
    have hfeq : f x = f y := by
      have := congrArg Subtype.val heq
      simpa [f_restr] using this
    have hsub_in_ker : x - y ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker, map_sub, hfeq, sub_self]
    have hsub_in_perp : x - y ∈ (LinearMap.ker f)ᗮ := sub_mem hx hy
    have h_inf : x - y ∈ LinearMap.ker f ⊓ (LinearMap.ker f)ᗮ :=
      ⟨hsub_in_ker, hsub_in_perp⟩
    rw [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at h_inf
    exact sub_eq_zero.mp h_inf
  -- Surjectivity: every y ∈ range f has a preimage in (ker f)ᗮ via decomp.
  have surj : Function.Surjective f_restr := by
    intro ⟨y, hy⟩
    obtain ⟨x, hxy⟩ := hy
    have hsup : LinearMap.ker f ⊔ (LinearMap.ker f)ᗮ = ⊤ :=
      Submodule.sup_orthogonal_of_hasOrthogonalProjection
    have hxmem : x ∈ LinearMap.ker f ⊔ (LinearMap.ker f)ᗮ := by
      rw [hsup]; exact Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxmem
    refine ⟨⟨b, hb⟩, ?_⟩
    apply Subtype.ext
    have hfa : f a = 0 := LinearMap.mem_ker.mp ha
    have hfb : f b = y := by
      have : f a + f b = f x := by
        rw [← LinearMap.map_add, hab]
      rw [hfa, zero_add] at this
      rw [this, hxy]
    simpa [f_restr] using hfb
  -- Bundle as a LinearEquiv and take the inverse.
  let equiv : ((LinearMap.ker f)ᗮ : Submodule ℝ V₀) ≃ₗ[ℝ] R :=
    LinearEquiv.ofBijective f_restr ⟨inj, surj⟩
  -- Compose: V₁ →L P→ R →ₗ (ker f)ᗮ →ₗ V₀.
  (LinearMap.ker f)ᗮ.subtype ∘ₗ equiv.symm.toLinearMap ∘ₗ P.toLinearMap

end GLang
