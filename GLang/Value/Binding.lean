import GLang.Value.Syntax

/-! Sizes, free variables, and substitution for the value syntax.
Opening and closing are supplied by ValueLN. -/
namespace GLang

/-! ## Size measures for well-founded recursion. -/

mutual
  /-- Size of a value space — strictly positive, used for termination. -/
  def ValSpace.size : ValSpace → Nat
    | .empty         => 1
    | .real          => 1
    | .dsum s₀ s₁    => 1 + ValSpace.size s₀ + ValSpace.size s₁
    | .tprod s₀ s₁   => 1 + ValSpace.size s₀ + ValSpace.size s₁
    | .ffs _ s e     => 1 + ValSpace.size s + ValExpr.size e

  def ValTy.size : ValTy → Nat
    | .space s        => 1 + ValSpace.size s
    | .piTy τ₀ τ₁     => 1 + ValTy.size τ₀ + ValTy.size τ₁

  def ValExpr.size : ValExpr → Nat
    | .zero s              => 1 + ValSpace.size s
    | .rlit _              => 1
    | .scale e₀ e₁         => 1 + ValExpr.size e₀ + ValExpr.size e₁
    | .vadd s e₀ e₁        => 1 + ValSpace.size s + ValExpr.size e₀ + ValExpr.size e₁
    | .dsumE e₀ e₁         => 1 + ValExpr.size e₀ + ValExpr.size e₁
    | .tprodE e₀ e₁        => 1 + ValExpr.size e₀ + ValExpr.size e₁
    | .delta _ s           => 1 + ValSpace.size s
    | .idelta s            => 1 + ValSpace.size s
    -- The list of summands is folded via the structurally-recursive
    -- companion `ValExpr.sizeList` (a plain `List.foldr` over the nested
    -- `List ValExpr` would force the whole mutual block onto well-founded
    -- recursion, destroying the definitional reduction downstream proofs
    -- rely on — see `sizeList_eq_foldr`).
    | .vsum s es           => 1 + ValSpace.size s + ValExpr.sizeList es
    | .vlam τ₀ τ₁ e        => 1 + ValTy.size τ₀ + ValTy.size τ₁ + ValExpr.size e
    | .bvar _              => 1
    | .var _ τ             => 1 + ValTy.size τ
    | .ttv s e₀ e₁         => 1 + ValSpace.size s + ValExpr.size e₀ + ValExpr.size e₁
    | .mtm _ _ s₀ s₁ e₀ e₁ => 1 + ValSpace.size s₀ + ValSpace.size s₁
                                 + ValExpr.size e₀ + ValExpr.size e₁
    | .appV e₀ e₁          => 1 + ValExpr.size e₀ + ValExpr.size e₁
    | .vkrn e₀ e₁          => 1 + ValExpr.size e₀ + ValExpr.size e₁
    | .vblk e₀ e₁          => 1 + ValExpr.size e₀ + ValExpr.size e₁
    | .reshap e τ τ₀       => 1 + ValExpr.size e + ValTy.size τ + ValTy.size τ₀
    | .vtrans e            => 1 + ValExpr.size e
    | .gsvdS e a b         => 1 + ValExpr.size e + ValExpr.size a + ValExpr.size b
    | .gsvdU e a b         => 1 + ValExpr.size e + ValExpr.size a + ValExpr.size b
    | .gsvdUI e a b        => 1 + ValExpr.size e + ValExpr.size a + ValExpr.size b
    | .gsvdV e a b         => 1 + ValExpr.size e + ValExpr.size a + ValExpr.size b
    | .gsvdVI e a b        => 1 + ValExpr.size e + ValExpr.size a + ValExpr.size b
    | .pinv e              => 1 + ValExpr.size e
    | .gpinv e a b         => 1 + ValExpr.size e + ValExpr.size a + ValExpr.size b
    | .rrefRep e₀ e₁       => 1 + ValExpr.size e₀ + ValExpr.size e₁
    | .inv e               => 1 + ValExpr.size e
    | .svds e              => 1 + ValExpr.size e

  /-- Structural companion summing `ValExpr.size` over a `List ValExpr`
      (the `.vsum` summand family). Recurses on the list spine. -/
  def ValExpr.sizeList : List ValExpr → Nat
    | []      => 0
    | e :: es => ValExpr.size e + ValExpr.sizeList es
end

@[simp] theorem ValExpr.sizeList_eq_foldr (es : List ValExpr) :
    ValExpr.sizeList es = es.foldr (fun e acc => ValExpr.size e + acc) 0 := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ValExpr.sizeList, List.foldr_cons, ih]

/-- Each element's `size` is bounded by `ValExpr.sizeList` of any list
    containing it — the `decreasing_by` lemma for the `.vsum` list family
    (`denotValB_sem` recurses on `e ∈ es`). -/
theorem ValExpr.size_le_sizeList {e : ValExpr} :
    ∀ {es : List ValExpr}, e ∈ es → ValExpr.size e ≤ ValExpr.sizeList es
  | _ :: tl, hmem => by
      simp only [ValExpr.sizeList]
      rcases List.mem_cons.1 hmem with h | h
      · subst h; omega
      · have := ValExpr.size_le_sizeList (es := tl) h; omega

/-! ### Annotation-free constructor count (`csize`).

`ValExpr.size` counts the sizes of `ValTy`/`ValSpace` annotations, so it is NOT
invariant under opening (`openVar x τ₀` replaces a `bvar` — `size 1` — by `var x
τ₀` — `size 1 + ValTy.size τ₀`). `csize` counts only `ValExpr` constructors (every
leaf is `1`, annotations contribute `0`), so it IS opening-invariant
(`csize_openRec`, in `ValueSoundnessSem`). It is the well-founded measure for the
value-soundness recursion, whose `.vlam` case recurses on `openVar x τ₀ body`. -/
mutual
  def ValExpr.csize : ValExpr → Nat
    | .zero _              => 1
    | .rlit _              => 1
    | .scale e₀ e₁         => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .vadd _ e₀ e₁        => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .dsumE e₀ e₁         => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .tprodE e₀ e₁        => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .delta _ _           => 1
    | .idelta _            => 1
    | .vsum _ es           => 1 + ValExpr.csizeList es
    | .vlam _ _ e          => 1 + ValExpr.csize e
    | .bvar _              => 1
    | .var _ _             => 1
    | .ttv _ e₀ e₁         => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .mtm _ _ _ _ e₀ e₁   => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .appV e₀ e₁          => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .vkrn e₀ e₁          => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .vblk e₀ e₁          => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .reshap e _ _        => 1 + ValExpr.csize e
    | .vtrans e            => 1 + ValExpr.csize e
    | .gsvdS e a b         => 1 + ValExpr.csize e + ValExpr.csize a + ValExpr.csize b
    | .gsvdU e a b         => 1 + ValExpr.csize e + ValExpr.csize a + ValExpr.csize b
    | .gsvdUI e a b        => 1 + ValExpr.csize e + ValExpr.csize a + ValExpr.csize b
    | .gsvdV e a b         => 1 + ValExpr.csize e + ValExpr.csize a + ValExpr.csize b
    | .gsvdVI e a b        => 1 + ValExpr.csize e + ValExpr.csize a + ValExpr.csize b
    | .pinv e              => 1 + ValExpr.csize e
    | .gpinv e a b         => 1 + ValExpr.csize e + ValExpr.csize a + ValExpr.csize b
    | .rrefRep e₀ e₁       => 1 + ValExpr.csize e₀ + ValExpr.csize e₁
    | .inv e               => 1 + ValExpr.csize e
    | .svds e              => 1 + ValExpr.csize e

  /-- Structural companion summing `ValExpr.csize` over the `.vsum` family. -/
  def ValExpr.csizeList : List ValExpr → Nat
    | []      => 0
    | e :: es => ValExpr.csize e + ValExpr.csizeList es
end

/-- Each element's `csize` is bounded by `csizeList` of any list containing it. -/
theorem ValExpr.csize_le_csizeList {e : ValExpr} :
    ∀ {es : List ValExpr}, e ∈ es → ValExpr.csize e ≤ ValExpr.csizeList es
  | _ :: tl, hmem => by
      simp only [ValExpr.csizeList]
      rcases List.mem_cons.1 hmem with h | h
      · subst h; omega
      · have := ValExpr.csize_le_csizeList (es := tl) h; omega

def ValTy.kindSize : ValTy → Nat
  | .space _        => 0
  | .piTy τ₀ τ₁     => 1 + ValTy.kindSize τ₀ + ValTy.kindSize τ₁

@[simp] theorem ValTy.kindSize_space (s : ValSpace) :
    ValTy.kindSize (.space s) = 0 := rfl

@[simp] theorem ValTy.kindSize_piTy (τ₀ τ₁ : ValTy) :
    ValTy.kindSize (.piTy τ₀ τ₁)
      = 1 + ValTy.kindSize τ₀ + ValTy.kindSize τ₁ := rfl

/-! ## Free variables. -/

mutual
  def ValSpace.fv : ValSpace → Finset VName
    | .empty         => ∅
    | .real          => ∅
    | .dsum s₀ s₁    => ValSpace.fv s₀ ∪ ValSpace.fv s₁
    | .tprod s₀ s₁   => ValSpace.fv s₀ ∪ ValSpace.fv s₁
    | .ffs _ s e     => ValSpace.fv s ∪ ValExpr.fv e

  def ValTy.fv : ValTy → Finset VName
    | .space s        => ValSpace.fv s
    -- LN: the codomain binds `bvar 0`, not a name, so no `erase`.
    | .piTy τ₀ τ₁     => ValTy.fv τ₀ ∪ ValTy.fv τ₁

  def ValExpr.fv : ValExpr → Finset VName
    | .zero s              => ValSpace.fv s
    | .rlit _              => ∅
    | .scale e₀ e₁         => ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .vadd s e₀ e₁        => ValSpace.fv s ∪ ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .dsumE e₀ e₁         => ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .tprodE e₀ e₁        => ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .delta _ s           => ValSpace.fv s
    | .idelta s            => ValSpace.fv s

    | .vsum s es           => ValSpace.fv s ∪ ValExpr.fvList es
    -- LN: `vlam` binds `bvar 0` in the codomain `τ₁` and body `e`, not a
    -- name, so no `erase`.
    | .vlam τ₀ τ₁ e        => ValTy.fv τ₀ ∪ ValTy.fv τ₁ ∪ ValExpr.fv e
    -- Bound var: no free name, no annotation.
    | .bvar _              => ∅

    | .var x τ             => insert x (ValTy.fv τ)
    | .ttv s e₀ e₁         => ValSpace.fv s ∪ ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .mtm _ _ s₀ s₁ e₀ e₁ =>
        ValSpace.fv s₀ ∪ ValSpace.fv s₁ ∪ ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .appV e₀ e₁          => ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .vkrn e₀ e₁          => ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .vblk e₀ e₁          => ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .reshap e τ τ₀       => ValExpr.fv e ∪ ValTy.fv τ ∪ ValTy.fv τ₀
    | .vtrans e            => ValExpr.fv e
    | .gsvdS e a b         => ValExpr.fv e ∪ ValExpr.fv a ∪ ValExpr.fv b
    | .gsvdU e a b         => ValExpr.fv e ∪ ValExpr.fv a ∪ ValExpr.fv b
    | .gsvdUI e a b        => ValExpr.fv e ∪ ValExpr.fv a ∪ ValExpr.fv b
    | .gsvdV e a b         => ValExpr.fv e ∪ ValExpr.fv a ∪ ValExpr.fv b
    | .gsvdVI e a b        => ValExpr.fv e ∪ ValExpr.fv a ∪ ValExpr.fv b
    | .pinv e              => ValExpr.fv e
    | .gpinv e a b         => ValExpr.fv e ∪ ValExpr.fv a ∪ ValExpr.fv b
    | .rrefRep e₀ e₁       => ValExpr.fv e₀ ∪ ValExpr.fv e₁
    | .inv e               => ValExpr.fv e
    | .svds e              => ValExpr.fv e

  /-- Structural companion unioning `ValExpr.fv` over a `List ValExpr`. -/
  def ValExpr.fvList : List ValExpr → Finset VName
    | []      => ∅
    | e :: es => ValExpr.fv e ∪ ValExpr.fvList es
end

@[simp] theorem ValExpr.fvList_eq_foldr (es : List ValExpr) :
    ValExpr.fvList es = es.foldr (fun e acc => ValExpr.fv e ∪ acc) ∅ := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [ValExpr.fvList, List.foldr_cons, ih]

theorem ValExpr.mem_fvList {w : VName} {es : List ValExpr} :
    w ∈ ValExpr.fvList es ↔ ∃ e ∈ es, w ∈ ValExpr.fv e := by
  induction es with
  | nil => simp [ValExpr.fvList]
  | cons e es ih =>
      simp only [ValExpr.fvList, Finset.mem_union, ih, List.mem_cons,
        exists_eq_or_imp]

end GLang
