import GLang.Value.Supporting.TotalDimensions

/-! Syntactic inference and expression-building operations. Binary
application substitutes its argument into the inferred function codomain. -/
namespace GLang

/-! Named variables retain their explicit type annotation. Application
substitutes into the inferred codomain. Inference is total on raw syntax;
RuntimeValueInfer proves its typing properties. Runtime compatibility checks
remain in the value evaluator. -/

def ValExpr.inferType : ValExpr → ValTy
  | .zero s              => .space s
  | .rlit _              => .space .real
  | .scale _ e₁          => ValExpr.inferType e₁
  | .vadd s _ _          => .space s
  | .dsumE e₀ e₁         =>
      .space (.dsum (ValTy.spaceOf (ValExpr.inferType e₀))
                    (ValTy.spaceOf (ValExpr.inferType e₁)))
  | .tprodE e₀ e₁        =>
      .space (.tprod (ValTy.spaceOf (ValExpr.inferType e₀))
                     (ValTy.spaceOf (ValExpr.inferType e₁)))
  | .delta _ s           => .space s
  | .idelta s            => .space (.tprod s s)
  -- vsum re-encoded to a list family. All summands share the result type
  -- `.space s`; recover it from the head. Empty list → `.space .empty`
  -- (consistent with `inferSpace`'s empty default; never arises for a
  -- well-typed `vsum`).
  | .vsum _ es           =>
      match es with
      | e :: _ => ValExpr.inferType e
      | []     => .space .empty
  -- B7 annotation: free `.var` carries its type.
  | .var _ τ             => τ

  | .bvar _              => .space .empty
  -- Binary application substitutes the argument into the inferred codomain.
  | .appV f a =>
      match ValExpr.inferType f with
      | .piTy _ codomain => ValTy.applyCodomain a codomain
      | .space _ => .space .empty
  -- Lambda — annotation-faithful: LN `.vlam τ₀ τ₁ _` has type `.piTy τ₀ τ₁`.
  | .vlam τ₀ τ₁ _        => .piTy τ₀ τ₁
  -- Reshape carries the target type explicitly.
  | .reshap _ τ _        => τ
  | .ttv _ e₀ _          =>
      -- e₀ : s₀' ⊗ s_out → result `.space s_out` (ttv_space);
      -- fall back to `.space .real` (ttv_real) on non-tprod operand.
      match ValExpr.inferType e₀ with
      | .space (.tprod _ s_out) => .space s_out
      | _                       => .space .real
  | .mtm _ _ _ _ e₀ e₁   =>
      -- e₀ : s₁' ⊗ s₀, e₁ : s₂ ⊗ s₁ → result `.space (s₂ ⊗ s₀)`.
      match ValExpr.inferType e₀, ValExpr.inferType e₁ with
      | .space (.tprod _ s_0), .space (.tprod s_2 _) =>
          .space (.tprod s_2 s_0)
      | _, _ => .space .empty
  | .vkrn e e'           =>
      match ValExpr.inferType e, ValExpr.inferType e' with
      | .space (.tprod s0 s2), .space (.tprod s1 s3) =>
          .space (.tprod (.tprod s0 s1) (.tprod s2 s3))
      | _, _ => .space .empty
  | .vblk e e'           =>
      match ValExpr.inferType e, ValExpr.inferType e' with
      | .space (.tprod s0 s2), .space (.tprod s1 s3) =>
          .space (.tprod (.dsum s0 s1) (.dsum s2 s3))
      | _, _ => .space .empty
  | .vtrans e            =>
      match ValExpr.inferType e with
      | .space (.tprod s0 s1) => .space (.tprod s1 s0)
      | _                     => .space .empty
  | .gsvdS e _ _         =>
      match ValExpr.inferType e with
      | .space (.tprod s0 s1) =>
          .space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                         (.ffs .image    (.tprod s0 s1) e))
      | _ => .space .empty
  | .gsvdU e _ _         =>
      match ValExpr.inferType e with
      | .space (.tprod s0 s1) =>
          .space (.tprod s0 (.ffs .cokernel (.tprod s0 s1) e))
      | _ => .space .empty
  | .gsvdUI e _ _        =>
      match ValExpr.inferType e with
      | .space (.tprod s0 s1) =>
          .space (.tprod s0 (.ffs .kernel (.tprod s0 s1) e))
      | _ => .space .empty
  | .gsvdV e _ _         =>

      match ValExpr.inferType e with
      | .space (.tprod s0 s1) =>
          .space (.tprod s1 (.ffs .image (.tprod s0 s1) e))
      | _ => .space .empty
  | .gsvdVI e _ _        =>

      match ValExpr.inferType e with
      | .space (.tprod s0 s1) =>
          .space (.tprod s1 (.ffs .coimage (.tprod s0 s1) e))
      | _ => .space .empty
  | .pinv e              =>
      match ValExpr.inferType e with
      | .space (.tprod s0 s1) => .space (.tprod s1 s0)
      | .space s              => .space (.tprod .real s)
      | _                     => .space .empty
  | .gpinv e _ _         =>
      match ValExpr.inferType e with
      | .space (.tprod s0 s1) => .space (.tprod s1 s0)
      | _                     => .space .empty
  | .rrefRep _ e₁        =>
      match ValExpr.inferType e₁ with
      | .space (.tprod p0 p1) => .space (.tprod p1 p0)
      | _                     => .space .empty
  | .inv e               =>
      match ValExpr.inferType e with
      | .space (.tprod s0 s1) => .space (.tprod s1 s0)
      | .space s              => .space (.tprod .real s)
      | _                     => .space .empty
  | .svds e              =>
      match ValExpr.inferType e with
      | .space (.tprod s0 s1) =>
          .space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                         (.ffs .image    (.tprod s0 s1) e))
      | _ => .space .empty

/-! Type inference under a locally nameless type context. Bound-variable
lookup raises declaration-relative entries to their occurrence depth. -/
def ValExpr.inferTypeCtx (Γ : List ValTy) : ValExpr → ValTy
  | .zero s              => .space s
  | .rlit _              => .space .real
  | .scale _ e₁          => ValExpr.inferTypeCtx Γ e₁
  | .vadd s _ _          => .space s
  | .dsumE e₀ e₁         =>
      .space (.dsum (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e₀))
                    (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e₁)))
  | .tprodE e₀ e₁        =>
      .space (.tprod (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e₀))
                     (ValTy.spaceOf (ValExpr.inferTypeCtx Γ e₁)))
  | .delta _ s           => .space s
  | .idelta s            => .space (.tprod s s)
  | .vsum _ es           =>
      match es with
      | e :: _ => ValExpr.inferTypeCtx Γ e
      | []     => .space .empty
  | .var _ τ             => τ
  -- LN bound variable: realize its declaration-level type at the current use depth.
  | .bvar k              => ValTyCtx.lookupUse Γ k
  | .appV f a =>
      match ValExpr.inferTypeCtx Γ f with
      | .piTy _ codomain => ValTy.applyCodomain a codomain
      | .space _ => .space .empty
  | .vlam τ₀ τ₁ _        => .piTy τ₀ τ₁
  | .reshap _ τ _        => τ
  | .ttv _ e₀ _          =>
      match ValExpr.inferTypeCtx Γ e₀ with
      | .space (.tprod _ s_out) => .space s_out
      | _                       => .space .real
  | .mtm _ _ _ _ e₀ e₁   =>
      match ValExpr.inferTypeCtx Γ e₀, ValExpr.inferTypeCtx Γ e₁ with
      | .space (.tprod _ s_0), .space (.tprod s_2 _) =>
          .space (.tprod s_2 s_0)
      | _, _ => .space .empty
  | .vkrn e e'           =>
      match ValExpr.inferTypeCtx Γ e, ValExpr.inferTypeCtx Γ e' with
      | .space (.tprod s0 s2), .space (.tprod s1 s3) =>
          .space (.tprod (.tprod s0 s1) (.tprod s2 s3))
      | _, _ => .space .empty
  | .vblk e e'           =>
      match ValExpr.inferTypeCtx Γ e, ValExpr.inferTypeCtx Γ e' with
      | .space (.tprod s0 s2), .space (.tprod s1 s3) =>
          .space (.tprod (.dsum s0 s1) (.dsum s2 s3))
      | _, _ => .space .empty
  | .vtrans e            =>
      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) => .space (.tprod s1 s0)
      | _                     => .space .empty
  | .gsvdS e _ _         =>
      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) =>
          .space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                         (.ffs .image    (.tprod s0 s1) e))
      | _ => .space .empty
  | .gsvdU e _ _         =>
      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) =>
          .space (.tprod s0 (.ffs .cokernel (.tprod s0 s1) e))
      | _ => .space .empty
  | .gsvdUI e _ _        =>
      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) =>
          .space (.tprod s0 (.ffs .kernel (.tprod s0 s1) e))
      | _ => .space .empty
  | .gsvdV e _ _         =>

      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) =>
          .space (.tprod s1 (.ffs .image (.tprod s0 s1) e))
      | _ => .space .empty
  | .gsvdVI e _ _        =>

      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) =>
          .space (.tprod s1 (.ffs .coimage (.tprod s0 s1) e))
      | _ => .space .empty
  | .pinv e              =>
      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) => .space (.tprod s1 s0)
      | .space s              => .space (.tprod .real s)
      | _                     => .space .empty
  | .gpinv e _ _         =>
      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) => .space (.tprod s1 s0)
      | _                     => .space .empty
  | .rrefRep _ e₁        =>
      match ValExpr.inferTypeCtx Γ e₁ with
      | .space (.tprod p0 p1) => .space (.tprod p1 p0)
      | _                     => .space .empty
  | .inv e               =>
      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) => .space (.tprod s1 s0)
      | .space s              => .space (.tprod .real s)
      | _                     => .space .empty
  | .svds e              =>
      match ValExpr.inferTypeCtx Γ e with
      | .space (.tprod s0 s1) =>
          .space (.tprod (.ffs .cokernel (.tprod s0 s1) e)
                         (.ffs .image    (.tprod s0 s1) e))
      | _ => .space .empty

/-- Best-effort syntactic value-space of a value expression. Defined by
    structural recursion on `ValExpr`; subterms whose space cannot be
    determined from syntax alone (notably `.var`) default to `.empty`.
    Matches `ValHasType`'s conclusion for every well-typed `ValExpr`. -/
def ValExpr.inferSpace : ValExpr → ValSpace
  | .zero s              => s
  | .rlit _              => .real
  | .scale _ e₁          => ValExpr.inferSpace e₁
  | .vadd s _ _          => s
  | .dsumE e₀ e₁         =>
      .dsum (ValExpr.inferSpace e₀) (ValExpr.inferSpace e₁)
  | .tprodE e₀ e₁        =>
      .tprod (ValExpr.inferSpace e₀) (ValExpr.inferSpace e₁)
  | .delta _ s           => s
  | .idelta s            => .tprod s s
  -- vsum re-encoded to a list family. All summands share the result space
  -- `s`; recover it from the head. Empty list → `.empty` (sensible default:
  -- a `Σ` over no summands is the zero of `.empty`; never arises for a
  -- well-typed `vsum`, whose typing forces a uniform `.space s` per element).
  | .vsum _ es           =>
      match es with
      | e :: _ => ValExpr.inferSpace e
      | []     => .empty
  | .vlam _ _ _          => .empty   -- deferred (function value)
  -- LN bound var: dead arm (inferSpace only runs on locally-closed values).
  | .bvar _              => .empty
  -- `.var x τ` carries its type annotation; recover the space directly.
  -- For arrow types we still return `.empty` (no scalar shape).
  | .var _ τ             => ValTy.spaceOf τ
  | .ttv _ e₀ _          =>
      -- e₀ : s' ⊗ s_out → result lives in s_out (the ttv_space rule);
      -- fall back to .real (the ttv_real rule) if shape is not tprod.
      match ValExpr.inferSpace e₀ with
      | .tprod _ s_out => s_out
      | _              => .real
  | .mtm _ _ _ _ e₀ e₁   =>
      -- e₀ : s_1' ⊗ s_0, e₁ : s_2 ⊗ s_1 → result : s_2 ⊗ s_0.
      match ValExpr.inferSpace e₀, ValExpr.inferSpace e₁ with
      | .tprod _ s_0, .tprod s_2 _ => .tprod s_2 s_0
      | _,            _            => .empty
  -- Recover the space from the substituted dependent result type.
  -- Arrow-typed results yield `.empty` (no scalar shape).
  | .appV f a => (ValExpr.inferType (.appV f a)).spaceOf
  | .vkrn e e'           =>
      match ValExpr.inferSpace e, ValExpr.inferSpace e' with
      | .tprod s0 s2, .tprod s1 s3 =>
          .tprod (.tprod s0 s1) (.tprod s2 s3)
      | _,            _            => .empty
  | .vblk e e'           =>
      match ValExpr.inferSpace e, ValExpr.inferSpace e' with
      | .tprod s0 s2, .tprod s1 s3 =>
          .tprod (.dsum s0 s1) (.dsum s2 s3)
      | _,            _            => .empty
  | .reshap _ τ _        => ValTy.spaceOf τ
  | .vtrans e            =>
      match ValExpr.inferSpace e with
      | .tprod s0 s1 => .tprod s1 s0
      | _            => .empty
  | .gsvdS  e _ _        => .tprod (.ffs .cokernel (ValExpr.inferSpace e) e)
                                    (.ffs .image    (ValExpr.inferSpace e) e)
  | .gsvdU  e _ _        =>
      match ValExpr.inferSpace e with
      | .tprod s0 _ => .tprod s0 (.ffs .cokernel (ValExpr.inferSpace e) e)
      | _           => .empty
  | .gsvdUI e _ _        =>
      match ValExpr.inferSpace e with
      | .tprod s0 _ => .tprod s0 (.ffs .kernel (ValExpr.inferSpace e) e)
      | _           => .empty
  | .gsvdV  e _ _        =>

      match ValExpr.inferSpace e with
      | .tprod _ s1 => .tprod s1 (.ffs .image (ValExpr.inferSpace e) e)
      | _           => .empty
  | .gsvdVI e _ _        =>

      match ValExpr.inferSpace e with
      | .tprod _ s1 => .tprod s1 (.ffs .coimage (ValExpr.inferSpace e) e)
      | _           => .empty
  | .pinv e              =>
      match ValExpr.inferSpace e with
      | .tprod s0 s1 => .tprod s1 s0
      | s            => .tprod .real s
  | .gpinv e _ _         =>
      match ValExpr.inferSpace e with
      | .tprod s0 s1 => .tprod s1 s0
      | _            => .empty
  | .rrefRep _ e₁        =>
      match ValExpr.inferSpace e₁ with
      | .tprod p0 p1 => .tprod p1 p0
      | _            => .empty
  | .inv e               =>
      match ValExpr.inferSpace e with
      | .tprod s0 s1 => .tprod s1 s0
      | s            => .tprod .real s
  | .svds e              => .tprod (.ffs .cokernel (ValExpr.inferSpace e) e)
                                    (.ffs .image    (ValExpr.inferSpace e) e)

/-! Space inference under a locally nameless type context. Bound variables
resolve to their declared spaces, raised to the current occurrence depth. -/
def ValExpr.inferSpaceCtx (Γ : List ValTy) : ValExpr → ValSpace
  | .zero s              => s
  | .rlit _              => .real
  | .scale _ e₁          => ValExpr.inferSpaceCtx Γ e₁
  | .vadd s _ _          => s
  | .dsumE e₀ e₁         =>
      .dsum (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁)
  | .tprodE e₀ e₁        =>
      .tprod (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁)
  | .delta _ s           => s
  | .idelta s            => .tprod s s
  | .vsum _ es           =>
      match es with
      | e :: _ => ValExpr.inferSpaceCtx Γ e
      | []     => .empty
  | .vlam _ _ _          => .empty   -- deferred (function value)
  -- LN bound var: realize its declaration-level type at the current use depth.
  | .bvar k              => ValTy.spaceOf (ValTyCtx.lookupUse Γ k)
  | .var _ τ             => ValTy.spaceOf τ
  | .ttv _ e₀ _          =>
      match ValExpr.inferSpaceCtx Γ e₀ with
      | .tprod _ s_out => s_out
      | _              => .real
  | .mtm _ _ _ _ e₀ e₁   =>
      match ValExpr.inferSpaceCtx Γ e₀, ValExpr.inferSpaceCtx Γ e₁ with
      | .tprod _ s_0, .tprod s_2 _ => .tprod s_2 s_0
      | _,            _            => .empty
  | .appV f a => (ValExpr.inferTypeCtx Γ (.appV f a)).spaceOf
  | .vkrn e e'           =>
      match ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ e' with
      | .tprod s0 s2, .tprod s1 s3 =>
          .tprod (.tprod s0 s1) (.tprod s2 s3)
      | _,            _            => .empty
  | .vblk e e'           =>
      match ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ e' with
      | .tprod s0 s2, .tprod s1 s3 =>
          .tprod (.dsum s0 s1) (.dsum s2 s3)
      | _,            _            => .empty
  | .reshap _ τ _        => ValTy.spaceOf τ
  | .vtrans e            =>
      match ValExpr.inferSpaceCtx Γ e with
      | .tprod s0 s1 => .tprod s1 s0
      | _            => .empty
  | .gsvdS  e _ _        => .tprod (.ffs .cokernel (ValExpr.inferSpaceCtx Γ e) e)
                                    (.ffs .image    (ValExpr.inferSpaceCtx Γ e) e)
  | .gsvdU  e _ _        =>
      match ValExpr.inferSpaceCtx Γ e with
      | .tprod s0 _ => .tprod s0 (.ffs .cokernel (ValExpr.inferSpaceCtx Γ e) e)
      | _           => .empty
  | .gsvdUI e _ _        =>
      match ValExpr.inferSpaceCtx Γ e with
      | .tprod s0 _ => .tprod s0 (.ffs .kernel (ValExpr.inferSpaceCtx Γ e) e)
      | _           => .empty
  | .gsvdV  e _ _        =>

      match ValExpr.inferSpaceCtx Γ e with
      | .tprod _ s1 => .tprod s1 (.ffs .image (ValExpr.inferSpaceCtx Γ e) e)
      | _           => .empty
  | .gsvdVI e _ _        =>

      match ValExpr.inferSpaceCtx Γ e with
      | .tprod _ s1 => .tprod s1 (.ffs .coimage (ValExpr.inferSpaceCtx Γ e) e)
      | _           => .empty
  | .pinv e              =>
      match ValExpr.inferSpaceCtx Γ e with
      | .tprod s0 s1 => .tprod s1 s0
      | s            => .tprod .real s
  | .gpinv e _ _         =>
      match ValExpr.inferSpaceCtx Γ e with
      | .tprod s0 s1 => .tprod s1 s0
      | _            => .empty
  | .rrefRep _ e₁        =>
      match ValExpr.inferSpaceCtx Γ e₁ with
      | .tprod p0 p1 => .tprod p1 p0
      | _            => .empty
  | .inv e               =>
      match ValExpr.inferSpaceCtx Γ e with
      | .tprod s0 s1 => .tprod s1 s0
      | s            => .tprod .real s
  | .svds e              => .tprod (.ffs .cokernel (ValExpr.inferSpaceCtx Γ e) e)
                                    (.ffs .image    (ValExpr.inferSpaceCtx Γ e) e)

@[simp] theorem ValExpr.inferSpace_zero (s : ValSpace) :
    ValExpr.inferSpace (.zero s) = s := rfl

@[simp] theorem ValExpr.inferSpace_rlit (r : ℝ) :
    ValExpr.inferSpace (.rlit r) = .real := rfl

@[simp] theorem ValExpr.inferSpace_tprodE (e₀ e₁ : ValExpr) :
    ValExpr.inferSpace (.tprodE e₀ e₁)
      = .tprod (ValExpr.inferSpace e₀) (ValExpr.inferSpace e₁) := rfl

@[simp] theorem ValExpr.inferSpace_dsumE (e₀ e₁ : ValExpr) :
    ValExpr.inferSpace (.dsumE e₀ e₁)
      = .dsum (ValExpr.inferSpace e₀) (ValExpr.inferSpace e₁) := rfl

@[simp] theorem ValExpr.inferSpace_idelta (s : ValSpace) :
    ValExpr.inferSpace (.idelta s) = .tprod s s := rfl

@[simp] theorem ValExpr.inferSpace_delta (n : Nat) (s : ValSpace) :
    ValExpr.inferSpace (.delta n s) = s := rfl

@[simp] theorem ValExpr.inferSpace_reshap (e : ValExpr) (τ τ₀ : ValTy) :
    ValExpr.inferSpace (.reshap e τ τ₀) = ValTy.spaceOf τ := rfl

@[simp] theorem ValExpr.inferSpace_vsum_cons (s : ValSpace) (e : ValExpr)
    (es : List ValExpr) :
    ValExpr.inferSpace (.vsum s (e :: es)) = ValExpr.inferSpace e := rfl

@[simp] theorem ValExpr.inferSpace_vsum_nil (s : ValSpace) :
    ValExpr.inferSpace (.vsum s []) = .empty := rfl

/-- Construct a base-kind reshape whose source and target annotations agree. -/
def ValExpr.reshapBase (e : ValExpr) (target : ValSpace) : ValExpr :=
  .reshap e (.space target) (.space target)

/-- Assemble a finite sum at a chosen result space. The empty syntactic
family has original type `empty`; record that source before coercing it to
the desired (possibly differently shaped zero-dimensional) result. List
emptiness is stable under opening, closing, renaming, and substitution. -/
def ValExpr.sumAt (index : ValSpace) (es : List ValExpr) (target : ValSpace) : ValExpr :=
  .reshap (.vsum index es) (.space target)
    (.space (if es.isEmpty then .empty else target))

@[simp] theorem ValExpr.inferType_var (x : VName) (τ : ValTy) :
    ValExpr.inferType (.var x τ) = τ := rfl

@[simp] theorem ValExpr.inferType_reshap (e : ValExpr) (τ τ₀ : ValTy) :
    ValExpr.inferType (.reshap e τ τ₀) = τ := rfl

/-- Compile a call with an explicit conversion to the function's domain.
The result type is supplied by dependent substitution, never by this helper. -/
def ValExpr.applyValue (f a : ValExpr) : ValExpr :=
  .appV f (.reshap a (ValExpr.inferType f).domain (ValExpr.inferType a))

/-- Convert a call's native dependent result to the representation selected by
operational type evaluation. Both conversions are ordinary reshape expressions. -/
def ValExpr.applyAt (f a : ValExpr) (target : ValTy) : ValExpr :=
  .reshap (.applyValue f a) target (ValExpr.inferType (.applyValue f a))

@[simp] theorem ValExpr.inferType_applyAt (f a : ValExpr) (target : ValTy) :
    ValExpr.inferType (.applyAt f a target) = target := rfl

@[simp] theorem ValExpr.inferType_appV (f a : ValExpr) :
    ValExpr.inferType (.appV f a) =
      match ValExpr.inferType f with
      | .piTy _ codomain => ValTy.applyCodomain a codomain
      | .space _ => .space .empty := rfl

@[simp] theorem ValExpr.inferType_vlam (τ₀ τ₁ : ValTy) (e : ValExpr) :
    ValExpr.inferType (.vlam τ₀ τ₁ e) = .piTy τ₀ τ₁ := rfl

/-- Construct the syntactic body of the closure produced by the
    higher-kinded `.reshap` arrow case. See banner above. -/
noncomputable def ValExpr.reshapBody : ValTy → ValTy → ValExpr → ValExpr
  | .piTy τ₂ τ₃, .piTy τ₄ τ₅, e =>

      let inner_reshap : ValExpr := .reshap (.bvar 0) τ₄ τ₂
      let τ₅_inst : ValTy        := ValTy.instantiate inner_reshap τ₅
      let app_e   : ValExpr      := .appV e inner_reshap
      .reshap app_e τ₃ τ₅_inst
  | _, _, e => e  -- fallback (not exercised on well-typed input)

/-! ## Denotation skeleton.

The full value denotation `\Sem{\leev}{\rho}{i_{0},…,i_{n}} : ℝ` requires
shape-indexed indices and a value environment. We outline the shape of
the API here; the body is left to the next iteration.

Indices for a value space are tuples of natural numbers respecting the
shape; we expose them as `List Nat` with a runtime-checked length /
bounds. -/

abbrev ValIdx := Nat

/-- Decode a flat tensor index into `(i₀, i₁)` given the dimension of
    the right operand. C-order: `i = d₁ * i₀ + i₁`. -/
def decode_tprod (d₁ : Nat) (i : Nat) : Nat × Nat :=
  (i / d₁, i % d₁)

@[simp] theorem decode_tprod_def (d₁ i : Nat) :
    decode_tprod d₁ i = (i / d₁, i % d₁) := rfl

/-- Decode a flat direct-sum index `i` against the left-summand
    dimension `d₀`: returns `Sum.inl` for the first summand,
    `Sum.inr` for the second (after subtracting `d₀`). -/
def decode_dsum (d₀ : Nat) (i : Nat) : Sum Nat Nat :=
  if i < d₀ then .inl i else .inr (i - d₀)

@[simp] theorem decode_dsum_lt (d₀ i : Nat) (h : i < d₀) :
    decode_dsum d₀ i = .inl i := by simp [decode_dsum, h]

@[simp] theorem decode_dsum_ge (d₀ i : Nat) (h : ¬ i < d₀) :
    decode_dsum d₀ i = .inr (i - d₀) := by simp [decode_dsum, h]

end GLang
