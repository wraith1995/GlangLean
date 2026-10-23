import GLang.Annotated.Syntax

/-! Sizes, free variables, and substitution on annotated syntax. -/
namespace GLang

/-! ## Size measures for well-founded recursion. -/

mutual
  def Space.size : Space → Nat
    | .empty       => 1
    | .real        => 1
    | .dual s      => 1 + Space.size s
    | .dsum s₀ s₁  => 1 + Space.size s₀ + Space.size s₁
    | .tprod s₀ s₁ => 1 + Space.size s₀ + Space.size s₁
    | .ker s₀ s₁ e   => 1 + Space.size s₀ + Space.size s₁ + Term.size e
    | .coker s₀ s₁ e => 1 + Space.size s₀ + Space.size s₁ + Term.size e
    | .img s₀ s₁ e   => 1 + Space.size s₀ + Space.size s₁ + Term.size e
    | .coimg s₀ s₁ e => 1 + Space.size s₀ + Space.size s₁ + Term.size e

  def Ty.size : Ty → Nat
    | .space s        => 1 + Space.size s
    | .piTy τ₀ τ₁     => 1 + Ty.size τ₀ + Ty.size τ₁

  def Term.size : Term → Nat
    | .bvar _              => 1
    | .zero s              => 1 + Space.size s
    | .smul e₀ e₁          => 1 + Term.size e₀ + Term.size e₁
    | .real _              => 1
    | .add e₀ e₁           => 1 + Term.size e₀ + Term.size e₁
    | .inner s             => 1 + Space.size s
    | .appL s₀ s₁ e₀ e₁    => 1 + Space.size s₀ + Space.size s₁ + Term.size e₀ + Term.size e₁
    | .appI s e₀ e₁        => 1 + Space.size s + Term.size e₀ + Term.size e₁
    | .appN e₀ e₁          => 1 + Term.size e₀ + Term.size e₁
    | .llam s₀ s e         => 1 + Space.size s₀ + Space.size s + Term.size e
    | .nllam τ e           => 1 + Ty.size τ + Term.size e
    | .var _               => 1
    | .pinvT s₀ s₁ e       => 1 + Space.size s₀ + Space.size s₁ + Term.size e
    | .pinvD s e           => 1 + Space.size s + Term.size e
    | .dsumE e₀ e₁         => 1 + Term.size e₀ + Term.size e₁
    | .tprodE e₀ e₁        => 1 + Term.size e₀ + Term.size e₁
    | .embed s             => 1 + Space.size s
end

/-- Size measure for `Basis`. References `Term.size` and `Space.size` from
    the mutual block above; not itself part of the mutual (Term/Space do
    not reference Basis). -/
def Basis.size : Basis → Nat
  | .empty           => 1
  | .one             => 1
  | .dual b          => 1 + Basis.size b
  | .dsum b₀ b₁      => 1 + Basis.size b₀ + Basis.size b₁
  | .tprod b₀ b₁     => 1 + Basis.size b₀ + Basis.size b₁
  | .proj s b₀ b₁    => 1 + Space.size s + Basis.size b₀ + Basis.size b₁
  | .image b         => 1 + Basis.size b
  | .terms s es b    =>
      1 + Space.size s + Basis.size b + (es.map Term.size).sum
  | .frame b₀ b₁     => 1 + Basis.size b₀ + Basis.size b₁

/-! Substitution for bases. The frame body uses locally nameless binding. -/

mutual
  def Space.subst (x : Name) (e : Term) : Space → Space
    | .empty        => .empty
    | .real         => .real
    | .dual s       => .dual (Space.subst x e s)
    | .dsum s₀ s₁   => .dsum (Space.subst x e s₀) (Space.subst x e s₁)
    | .tprod s₀ s₁  => .tprod (Space.subst x e s₀) (Space.subst x e s₁)
    | .ker s₀ s₁ t   =>
        .ker (Space.subst x e s₀) (Space.subst x e s₁) (Term.subst x e t)
    | .coker s₀ s₁ t =>
        .coker (Space.subst x e s₀) (Space.subst x e s₁) (Term.subst x e t)
    | .img s₀ s₁ t   =>
        .img (Space.subst x e s₀) (Space.subst x e s₁) (Term.subst x e t)
    | .coimg s₀ s₁ t =>
        .coimg (Space.subst x e s₀) (Space.subst x e s₁) (Term.subst x e t)

  def Ty.subst (x : Name) (e : Term) : Ty → Ty
    | .space s        => .space (Space.subst x e s)
    -- LN: `piTy` is nameless (codomain binds `bvar 0`), so `subst` — which only
    -- rewrites the FREE name `x` — recurses uniformly with no shadow guard.
    | .piTy τ₀ τ₁     => .piTy (Ty.subst x e τ₀) (Ty.subst x e τ₁)

  def Term.subst (x : Name) (e : Term) : Term → Term
    | .bvar i            => .bvar i
    | .var y             => if x = y then e else .var y
    | .real r            => .real r
    | .zero s            => .zero (Space.subst x e s)
    | .add e₀ e₁         => .add (Term.subst x e e₀) (Term.subst x e e₁)
    | .smul e₀ e₁        => .smul (Term.subst x e e₀) (Term.subst x e e₁)
    | .dsumE e₀ e₁       => .dsumE (Term.subst x e e₀) (Term.subst x e e₁)
    | .tprodE e₀ e₁      => .tprodE (Term.subst x e e₀) (Term.subst x e e₁)
    | .inner s           => .inner (Space.subst x e s)
    | .embed s           => .embed (Space.subst x e s)
    | .pinvT s₀ s₁ e'    =>
        .pinvT (Space.subst x e s₀) (Space.subst x e s₁) (Term.subst x e e')
    | .pinvD s e'        => .pinvD (Space.subst x e s) (Term.subst x e e')
    -- LN: `llam`/`nllam` are nameless (body binds `bvar 0`); `subst` recurses
    -- uniformly with no shadow guard.
    | .llam s₀ s e'      =>
        .llam (Space.subst x e s₀) (Space.subst x e s) (Term.subst x e e')
    | .nllam τ e'        =>
        .nllam (Ty.subst x e τ) (Term.subst x e e')
    | .appL s₀ s₁ e₀ e₁  =>
        .appL (Space.subst x e s₀) (Space.subst x e s₁)
              (Term.subst x e e₀) (Term.subst x e e₁)
    | .appI s e₀ e₁      =>
        .appI (Space.subst x e s) (Term.subst x e e₀) (Term.subst x e e₁)
    | .appN e₀ e₁        => .appN (Term.subst x e e₀) (Term.subst x e e₁)
end

/-! Substitution for bases. The frame body uses locally nameless binding. -/

def Basis.subst (x : Name) (e : Term) : Basis → Basis
  | .empty           => .empty
  | .one             => .one
  | .dual b          => .dual (Basis.subst x e b)
  | .dsum b₀ b₁      => .dsum (Basis.subst x e b₀) (Basis.subst x e b₁)
  | .tprod b₀ b₁     => .tprod (Basis.subst x e b₀) (Basis.subst x e b₁)
  | .proj s b₀ b₁    =>
      .proj (Space.subst x e s) (Basis.subst x e b₀) (Basis.subst x e b₁)
  | .image b         => .image (Basis.subst x e b)
  | .terms s es b    =>
      .terms (Space.subst x e s) (es.map (Term.subst x e)) (Basis.subst x e b)
  | .frame b₀ b₁     =>
      .frame (Basis.subst x e b₀) (Basis.subst x e b₁)

/-! ## Free variables (locally-nameless).

`fv X` collects the FREE names of `X`. Under LN the four binders
(`Ty.piTy`, `Term.llam`, `Term.nllam`, `Basis.frame`) carry no name and bind
via `bvar`, so there is NO `erase` at any binder — a binder body's free names
are exactly the body's free names. `bvar` contributes nothing. -/

mutual
  def Space.fv : Space → Finset Name
    | .empty         => ∅
    | .real          => ∅
    | .dual s        => Space.fv s
    | .dsum s₀ s₁    => Space.fv s₀ ∪ Space.fv s₁
    | .tprod s₀ s₁   => Space.fv s₀ ∪ Space.fv s₁
    | .ker s₀ s₁ e   => Space.fv s₀ ∪ Space.fv s₁ ∪ Term.fv e
    | .coker s₀ s₁ e => Space.fv s₀ ∪ Space.fv s₁ ∪ Term.fv e
    | .img s₀ s₁ e   => Space.fv s₀ ∪ Space.fv s₁ ∪ Term.fv e
    | .coimg s₀ s₁ e => Space.fv s₀ ∪ Space.fv s₁ ∪ Term.fv e

  def Ty.fv : Ty → Finset Name
    | .space s        => Space.fv s
    -- LN: codomain binds `bvar 0`, not a name, so no `erase`.
    | .piTy τ₀ τ₁     => Ty.fv τ₀ ∪ Ty.fv τ₁

  def Term.fv : Term → Finset Name
    | .bvar _             => ∅
    | .var x              => {x}
    | .real _             => ∅
    | .zero s             => Space.fv s
    | .add e₀ e₁          => Term.fv e₀ ∪ Term.fv e₁
    | .smul e₀ e₁         => Term.fv e₀ ∪ Term.fv e₁
    | .dsumE e₀ e₁        => Term.fv e₀ ∪ Term.fv e₁
    | .tprodE e₀ e₁       => Term.fv e₀ ∪ Term.fv e₁
    | .inner s            => Space.fv s
    | .embed s            => Space.fv s
    | .pinvT s₀ s₁ e      => Space.fv s₀ ∪ Space.fv s₁ ∪ Term.fv e
    | .pinvD s e          => Space.fv s ∪ Term.fv e
    -- LN: `llam`/`nllam` bodies bind `bvar 0`, not a name, so no `erase`.
    | .llam s₀ s e        => Space.fv s₀ ∪ Space.fv s ∪ Term.fv e
    | .nllam τ e          => Ty.fv τ ∪ Term.fv e
    | .appL s₀ s₁ e₀ e₁   => Space.fv s₀ ∪ Space.fv s₁ ∪ Term.fv e₀ ∪ Term.fv e₁
    | .appI s e₀ e₁       => Space.fv s ∪ Term.fv e₀ ∪ Term.fv e₁
    | .appN e₀ e₁         => Term.fv e₀ ∪ Term.fv e₁

  /-- Structural companion unioning `Term.fv` over a `List Term` (used by
      `Basis.terms`). -/
  def Term.fvList : List Term → Finset Name
    | []      => ∅
    | e :: es => Term.fv e ∪ Term.fvList es
end

@[simp] theorem Term.fvList_eq_foldr (es : List Term) :
    Term.fvList es = es.foldr (fun e acc => Term.fv e ∪ acc) ∅ := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Term.fvList, List.foldr_cons, ih]

theorem Term.mem_fvList {w : Name} {es : List Term} :
    w ∈ Term.fvList es ↔ ∃ e ∈ es, w ∈ Term.fv e := by
  induction es with
  | nil => simp [Term.fvList]
  | cons e es ih =>
      simp only [Term.fvList, Finset.mem_union, ih, List.mem_cons, exists_eq_or_imp]

/-- Free variables of a `Basis` (LN: `frame` is nameless ⇒ no `erase`). -/
def Basis.fv : Basis → Finset Name
  | .empty           => ∅
  | .one             => ∅
  | .dual b          => Basis.fv b
  | .dsum b₀ b₁      => Basis.fv b₀ ∪ Basis.fv b₁
  | .tprod b₀ b₁     => Basis.fv b₀ ∪ Basis.fv b₁
  | .proj s b₀ b₁    => Space.fv s ∪ Basis.fv b₀ ∪ Basis.fv b₁
  | .image b         => Basis.fv b
  | .terms s es b    => Space.fv s ∪ Basis.fv b ∪ Term.fvList es
  | .frame b₀ b₁     => Basis.fv b₀ ∪ Basis.fv b₁

/-- Left-folded ⊕-chain `((e ⊕ e₁) ⊕ ⋯) ⊕ eₙ` over a head `e` and tail `es`. -/
def Term.dsumChain (e : Term) (es : List Term) : Term :=
  es.foldl Term.dsumE e

@[simp] theorem Term.dsumChain_nil (e : Term) : Term.dsumChain e [] = e := rfl

theorem Term.dsumChain_cons (e a : Term) (as : List Term) :
    Term.dsumChain e (a :: as) = Term.dsumChain (.dsumE e a) as := rfl

/-- `n` extra `⊕ b` layers onto `b` (so `dsumChain b n` is an n+1-fold chain
    `((b ⊕ b) ⊕ ⋯) ⊕ b`, left-associated to mirror `Term.dsumChain`). -/
def Basis.dsumChain (b : Basis) : Nat → Basis
  | 0     => b
  | n + 1 => .dsum (Basis.dsumChain b n) b

/-- `Term.subst` commutes with the ⊕-chain fold. -/
theorem Term.subst_dsumChain (x : Name) (u : Term) :
    ∀ (es : List Term) (e : Term),
      Term.subst x u (Term.dsumChain e es)
        = Term.dsumChain (Term.subst x u e) (es.map (Term.subst x u))
  | [], _ => rfl
  | a :: as, e => by
      rw [Term.dsumChain_cons, List.map_cons, Term.dsumChain_cons,
        Term.subst_dsumChain x u as (.dsumE e a)]
      rfl

/-- `Basis.subst` commutes with the basis ⊕-chain. -/
theorem Basis.subst_dsumChain (x : Name) (u : Term) (b : Basis) :
    ∀ n, Basis.subst x u (Basis.dsumChain b n)
      = Basis.dsumChain (Basis.subst x u b) n
  | 0 => rfl
  | n + 1 => by
      simp only [Basis.dsumChain, Basis.subst, Basis.subst_dsumChain x u b n]

/-! Inclusion, orthogonal projection, and inclusion application.
`Term.lembd` is `Term.embed`; `Term.lproj` is its pseudoinverse. -/

namespace Term

@[reducible] def lembd (s : Space) : Term := Term.embed s

@[reducible] def lproj (s_sub s_amb : Space) : Term :=
  Term.pinvT s_sub s_amb (Term.embed s_sub)

/-- Apply an inclusion `embed_sub` to a vector `e : sub`, landing in the
    ambient space `s_amb`. The `.appL sub s_amb (.embed sub) ·` idiom. -/
@[reducible] def embedApp (sub s_amb : Space) (e : Term) : Term :=
  Term.appL sub s_amb (Term.embed sub) e

@[simp] theorem lembd_def (s : Space) : Term.lembd s = Term.embed s := rfl

@[simp] theorem lproj_def (s_sub s_amb : Space) :
    Term.lproj s_sub s_amb = Term.pinvT s_sub s_amb (Term.embed s_sub) := rfl

@[simp] theorem embedApp_def (sub s_amb : Space) (e : Term) :
    Term.embedApp sub s_amb e = Term.appL sub s_amb (Term.embed sub) e := rfl

end Term

end GLang
