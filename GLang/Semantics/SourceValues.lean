import GLang.Semantics.VectorSpaces

/-! Bundled semantic values, dependent fibers, environments, and the
carrier conversions used by the raw source interpretation. -/
namespace GLang
open scoped TensorProduct

/-- A `Σ V : HSpace, V.carrier` — a vector tagged with its bundled space. -/
abbrev HElem : Type 1 := Σ V : HSpace, V.carrier

noncomputable def HElem.default : HElem := ⟨HSpace.empty, PUnit.unit⟩

inductive HType : Type 1
  | hil : HSpace → HType
  | sec : (T : Type) → (T → HType) → HType

/-- Underlying Lean type of an `HType`. Computed structurally; `(.sec T f).El`
    is exactly the dependent function space `(y : T) → (f y).El`. -/
def HType.El : HType → Type
  | .hil V   => V.carrier
  | .sec T f => (y : T) → (f y).El

noncomputable def HType.default : HType := .hil HSpace.empty

/-! ## Denotation values — `DVal`. -/

/-- Denotation values, untyped at the constructor level. `DVal.pi`'s base
    is a raw `Type` (paralleling `HType.sec`); the structural shape is
    recoverable via `DVal.shape`. -/
inductive DVal : Type 1

  | hil : HElem → DVal
  /-- A section of a discrete fiber bundle. The base `T : Type` is a
      raw Lean type — soundness pins it to `T_outer.El` of an enclosing
      `HType`. -/
  | pi  : (T : Type) → (T → DVal) → DVal

noncomputable def DVal.default : DVal := .hil HElem.default

/-- Coerce a `DVal` to a vector, falling back to default if it's a section. -/
noncomputable def DVal.asHil : DVal → HElem
  | .hil h => h
  | .pi _ _ => HElem.default

/-- Coerce a `DVal` to a section, falling back to a constant default. -/
noncomputable def DVal.asPi : DVal → (T : Type) ×' (T → DVal)
  | .pi T f => ⟨T, f⟩
  | .hil _  => ⟨PUnit, fun _ => .hil HElem.default⟩

/-- Extract a value at a specific space's carrier; returns 0 on type
    mismatch. The mismatch is a "denotation-time" check standing in for a
    soundness theorem (`HasType e (.space s) → ⟦e⟧.fst = ⟦s⟧`). -/
noncomputable def DVal.atSpace (V : HSpace) (d : DVal) : V.carrier :=
  let h := d.asHil
  haveI := Classical.dec (h.fst.carrier = V.carrier)
  if eq : h.fst.carrier = V.carrier then eq ▸ h.snd else 0

/-! ## Bridges between `HType` and `DVal`.

These provide round-tripping when we need to put an `HType`-typed value
into the environment (`embed`) or pull an `HType`-typed value out of a
`DVal` (`extract`/`shape`). -/

/-- Lift an element of `T.El` into the untyped `DVal` world. Structural
    recursion on `T : HType`. -/
def HType.embed : (T : HType) → T.El → DVal
  | .hil V,   y => DVal.hil ⟨V, y⟩
  | .sec T f, g => DVal.pi T (fun y : T => HType.embed (f y) (g y))

/-- Recover an `HType` shape from a `DVal`. Structural recursion on the
    `DVal` (analogous to W-type recursion through `.pi`'s function
    field). Soundness will eventually align `v.shape` with the
    `denotTy`-given shape. -/
def DVal.shape : DVal → HType
  | .hil ⟨V, _⟩ => HType.hil V
  | .pi T g     => HType.sec T (fun y : T => (g y).shape)

/-- Extract a value at a specific `HType` shape from a `DVal`, with
    Classical fallbacks on shape mismatch. Recurses structurally on
    `T : HType`. -/
noncomputable def HType.extract : (T : HType) → DVal → T.El
  | .hil V, .hil ⟨V', v⟩ =>
      haveI := Classical.dec (V'.carrier = V.carrier)
      show V.carrier from
        if h : V'.carrier = V.carrier then h ▸ v else (0 : V.carrier)
  | .hil V, .pi _ _ => show V.carrier from (0 : V.carrier)
  | .sec T f, .pi T' g =>
      haveI := Classical.dec (T = T')
      show (y : T) → (f y).El from
        if h : T = T' then
          fun y : T => HType.extract (f y) (g (h ▸ y))
        else
          fun y : T => HType.extract (f y) DVal.default
  | .sec T f, .hil _ =>
      show (y : T) → (f y).El from
        fun y : T => HType.extract (f y) DVal.default

def DVal.matchesTopCarrier (v : DVal) : HType → Prop
  | .hil V'   => v.asHil.fst.carrier = V'.carrier
  | .sec T' _ => v.asPi.fst = T'

/-- `v.matchesShape T` — **deep** shape-matching: the value `v`'s full
    `DVal.shape` agrees with the type-denotation `T`. -/
def DVal.matchesShape (v : DVal) (T : HType) : Prop := v.shape = T

/-! ## Denotational environment. -/

structure DEnv : Type 1 where
  vars : @Finmap Name (fun _ => DVal)

/-- Extend `σ` with `x ↦ v`. Linear and non-linear variables share a
    single namespace at the value level — disambiguation is by the
    typing rules, not the environment. -/
def DEnv.bind (σ : DEnv) (x : Name) (v : DVal) : DEnv where
  vars := σ.vars.insert x v

/-! ## Helpers factoring dependent casts out of the mutual recursion.

These wrap the `Classical.dec`-driven carrier-equality casts in
top-level functions of `HSpace` / `DVal` arguments, so downstream proofs
can rewrite at the function-call level without running into "motive is
not type correct" errors on dependent if-then-else expressions. -/

/-- Tensor-shaped DVal → underlying linear map `V₀ → V₁`. Falls back to
    the zero map on shape mismatch. -/
noncomputable def DVal.asLinMap (V₀ V₁ : HSpace) (d : DVal) :
    V₀.carrier →ₗ[ℝ] V₁.carrier :=
  let ⟨V_t, t⟩ := d.asHil
  haveI := Classical.dec (V_t.carrier = (Module.Dual ℝ V₀.carrier ⊗[ℝ] V₁.carrier))
  if h : V_t.carrier = (Module.Dual ℝ V₀.carrier ⊗[ℝ] V₁.carrier) then
    dualTensorHom ℝ V₀.carrier V₁.carrier (h ▸ t)
  else
    0

/-- Dual-shaped DVal → underlying linear functional `V → ℝ`. -/
noncomputable def DVal.asLinFunctional (V : HSpace) (d : DVal) :
    V.carrier →ₗ[ℝ] ℝ :=
  let ⟨V_t, t⟩ := d.asHil
  haveI := Classical.dec (V_t.carrier = (V.carrier →ₗ[ℝ] ℝ))
  if h : V_t.carrier = (V.carrier →ₗ[ℝ] ℝ) then h ▸ t else 0

/-- Real-shaped DVal → underlying scalar. Falls back to 0 on shape mismatch. -/
noncomputable def DVal.asReal (d : DVal) : ℝ :=
  let ⟨V, v⟩ := d.asHil
  haveI := Classical.dec (V.carrier = ℝ)
  if h : V.carrier = ℝ then h ▸ v else 0

/-- Add two DVals when their carriers match; otherwise return the first. -/
noncomputable def DVal.addAt (d₀ d₁ : DVal) : DVal :=
  let ⟨V₀, v₀⟩ := d₀.asHil
  let ⟨V₁, v₁⟩ := d₁.asHil
  haveI := Classical.dec (V₀.carrier = V₁.carrier)
  if h : V₀.carrier = V₁.carrier then
    .hil ⟨V₀, v₀ + h.symm ▸ v₁⟩
  else
    .hil ⟨V₀, v₀⟩

/-- Apply a section-valued DVal to an argument DVal. Casts the argument
    to the section's domain shape; falls back to `DVal.default` on
    shape mismatch. -/
noncomputable def DVal.applyAsPi (d_op d_arg : DVal) : DVal :=
  let ⟨T, f⟩ := d_op.asPi
  let T_arg : HType := d_arg.shape
  let y : T_arg.El := T_arg.extract d_arg
  haveI := Classical.dec (T_arg.El = T)
  if h : T_arg.El = T then f (h ▸ y) else DVal.default

/-- Encode the inner-product bilinear form `B : V →ₗ V* ` as a tensor in
    `V* ⊗ V*`. Wraps `dualTensorHomEquiv` so the dependent typing is
    captured at the function-application level. -/
noncomputable def HSpace.innerTensor (V : HSpace)
    (B : V.carrier →ₗ[ℝ] (V.carrier →ₗ[ℝ] ℝ)) : DVal :=
  let t : Module.Dual ℝ V.carrier ⊗[ℝ] Module.Dual ℝ V.carrier :=
    (dualTensorHomEquiv ℝ V.carrier (Module.Dual ℝ V.carrier)).symm B
  .hil ⟨HSpace.tprod (HSpace.dual V) (HSpace.dual V), t⟩

/-- Pseudo-inverse of a tensor `t : V₀* ⊗ V₁`, viewed as a linear map
    `V₀ → V₁` and Moore–Penrose-inverted using V₀ and V₁'s intrinsic
    inner products. -/
noncomputable def pinvTensorDVal (V₀ V₁ : HSpace) (d : DVal) : DVal :=
  let f : V₀.carrier →ₗ[ℝ] V₁.carrier := d.asLinMap V₀ V₁
  let g : V₁.carrier →ₗ[ℝ] V₀.carrier :=
    LinearMap.mooreInv V₀.innerIsIP V₁.innerIsIP f
  let result : Module.Dual ℝ V₁.carrier ⊗[ℝ] V₀.carrier :=
    (dualTensorHomEquiv ℝ V₁.carrier V₀.carrier).symm g
  .hil ⟨HSpace.tprod (HSpace.dual V₁) V₀, result⟩

/-- Pseudo-inverse of a dual functional `f : V → ℝ` as a tensor in `ℝ* ⊗ V`. -/
noncomputable def pinvDualDVal (V : HSpace) (d : DVal) : DVal :=
  let φ : V.carrier →ₗ[ℝ] ℝ := d.asLinFunctional V
  let g : ℝ →ₗ[ℝ] V.carrier :=
    LinearMap.mooreInv V.innerIsIP HSpace.real.innerIsIP φ
  let result : Module.Dual ℝ ℝ ⊗[ℝ] V.carrier :=
    (dualTensorHomEquiv ℝ ℝ V.carrier).symm g
  .hil ⟨HSpace.tprod (HSpace.dual HSpace.real) V, result⟩

/-- Linear λ to ℝ: bundle a function `DVal → ℝ` as a dual vector in `V₀*`,
    treating each `y : V₀.carrier` as the DVal `.hil ⟨V₀, y⟩`. The DVal-typed
    input is independent of `V₀` so callers can use the same function with
    different `V₀`. -/
noncomputable def llamRealDVal (V₀ : HSpace) (f : DVal → ℝ) : DVal :=
  let g : V₀.carrier → ℝ := fun y => f (.hil ⟨V₀, y⟩)
  .hil ⟨HSpace.dual V₀, LinearMap.ofFun g⟩

/-- Linear λ to a non-ℝ codomain: bundle a function `DVal → DVal` as a
    tensor in `V₀* ⊗ V₁`, treating each `y : V₀.carrier` as the DVal
    `.hil ⟨V₀, y⟩` and extracting the result at `V₁`. -/
noncomputable def llamTensorDVal (V₀ V₁ : HSpace) (f : DVal → DVal) : DVal :=
  let g : V₀.carrier → V₁.carrier := fun y => (f (.hil ⟨V₀, y⟩)).atSpace V₁
  let φ : V₀.carrier →ₗ[ℝ] V₁.carrier := LinearMap.ofFun g
  let tensor : Module.Dual ℝ V₀.carrier ⊗[ℝ] V₁.carrier :=
    (dualTensorHomEquiv ℝ V₀.carrier V₁.carrier).symm φ
  .hil ⟨HSpace.tprod (HSpace.dual V₀) V₁, tensor⟩

/-- The inclusion of a fundamental-subspace `V_sub` of an ambient space
    `V_amb`, packaged as a tensor in `V_sub* ⊗ V_amb`. Used uniformly for
    all four `.embed` cases. -/
noncomputable def embedDVal (V_sub V_amb : HSpace)
    (incl : V_sub.carrier →ₗ[ℝ] V_amb.carrier) : DVal :=
  let tensor := (dualTensorHomEquiv ℝ V_sub.carrier V_amb.carrier).symm incl
  .hil ⟨HSpace.tprod (HSpace.dual V_sub) V_amb, tensor⟩

end GLang
