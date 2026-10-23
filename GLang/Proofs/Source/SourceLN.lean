/- GLang.SourceLN — locally-nameless operations for the SOURCE language. -/
import GLang.Annotated.Binding
import Mathlib.Data.Fintype.EquivFin  -- `Infinite.exists_notMem_finset`, `String.infinite`

namespace GLang

/-! ## `openRec` — instantiate a bound index. -/

mutual
  def Space.openRec (k : Nat) (u : Term) : Space → Space
    | .empty         => .empty
    | .real          => .real
    | .dual s        => .dual (Space.openRec k u s)
    | .dsum s₀ s₁    => .dsum (Space.openRec k u s₀) (Space.openRec k u s₁)
    | .tprod s₀ s₁   => .tprod (Space.openRec k u s₀) (Space.openRec k u s₁)
    | .ker s₀ s₁ e   => .ker (Space.openRec k u s₀) (Space.openRec k u s₁) (Term.openRec k u e)
    | .coker s₀ s₁ e => .coker (Space.openRec k u s₀) (Space.openRec k u s₁) (Term.openRec k u e)
    | .img s₀ s₁ e   => .img (Space.openRec k u s₀) (Space.openRec k u s₁) (Term.openRec k u e)
    | .coimg s₀ s₁ e => .coimg (Space.openRec k u s₀) (Space.openRec k u s₁) (Term.openRec k u e)

  def Ty.openRec (k : Nat) (u : Term) : Ty → Ty
    | .space s    => .space (Space.openRec k u s)
    -- codomain `τ₁` is UNDER the binder ⇒ index `k+1`.
    | .piTy τ₀ τ₁ => .piTy (Ty.openRec k u τ₀) (Ty.openRec (k+1) u τ₁)

  def Term.openRec (k : Nat) (u : Term) : Term → Term
    | .bvar i             => if i = k then u else .bvar i
    | .var x              => .var x
    | .real r             => .real r
    | .zero s             => .zero (Space.openRec k u s)
    | .smul e₀ e₁         => .smul (Term.openRec k u e₀) (Term.openRec k u e₁)
    | .add e₀ e₁          => .add (Term.openRec k u e₀) (Term.openRec k u e₁)
    | .dsumE e₀ e₁        => .dsumE (Term.openRec k u e₀) (Term.openRec k u e₁)
    | .tprodE e₀ e₁       => .tprodE (Term.openRec k u e₀) (Term.openRec k u e₁)
    | .inner s            => .inner (Space.openRec k u s)
    | .embed s            => .embed (Space.openRec k u s)
    | .pinvT s₀ s₁ e      => .pinvT (Space.openRec k u s₀) (Space.openRec k u s₁) (Term.openRec k u e)
    | .pinvD s e          => .pinvD (Space.openRec k u s) (Term.openRec k u e)
    -- `llam` binds in BODY `e` only ⇒ index `k+1`; the domain `s₀` and codomain
    -- space `s` are at level `k` (the linear vector parameter is not in scope
    -- in a `Space`).
    | .llam s₀ s e        => .llam (Space.openRec k u s₀) (Space.openRec k u s) (Term.openRec (k+1) u e)
    -- `nllam` binds in BODY `e` ⇒ index `k+1`; the domain type `τ` is at level `k`.
    | .nllam τ e          => .nllam (Ty.openRec k u τ) (Term.openRec (k+1) u e)
    | .appL s₀ s₁ e₀ e₁   =>
        .appL (Space.openRec k u s₀) (Space.openRec k u s₁)
              (Term.openRec k u e₀) (Term.openRec k u e₁)
    | .appI s e₀ e₁       =>
        .appI (Space.openRec k u s) (Term.openRec k u e₀) (Term.openRec k u e₁)
    | .appN e₀ e₁         => .appN (Term.openRec k u e₀) (Term.openRec k u e₁)
end

/-- Open every `Term` of a list (the `Basis.terms` summand list). -/
def Term.openRecList (k : Nat) (u : Term) (es : List Term) : List Term :=
  es.map (Term.openRec k u)

/-- `Basis.openRec` — standalone (Basis embeds Space/Term; not vice versa). -/
def Basis.openRec (k : Nat) (u : Term) : Basis → Basis
  | .empty        => .empty
  | .one          => .one
  | .dual b       => .dual (Basis.openRec k u b)
  | .dsum b₀ b₁   => .dsum (Basis.openRec k u b₀) (Basis.openRec k u b₁)
  | .tprod b₀ b₁  => .tprod (Basis.openRec k u b₀) (Basis.openRec k u b₁)
  | .proj s b₀ b₁ => .proj (Space.openRec k u s) (Basis.openRec k u b₀) (Basis.openRec k u b₁)
  | .image b      => .image (Basis.openRec k u b)
  | .terms s es b => .terms (Space.openRec k u s) (Term.openRecList k u es) (Basis.openRec k u b)
  -- `frame` binds in BODY `b₁` ⇒ index `k+1`; the input basis `b₀` is at level `k`.
  | .frame b₀ b₁  => .frame (Basis.openRec k u b₀) (Basis.openRec (k+1) u b₁)

/-! ## `closeRec` — abstract a free name to a bound index. -/

mutual
  def Space.closeRec (k : Nat) (x : Name) : Space → Space
    | .empty         => .empty
    | .real          => .real
    | .dual s        => .dual (Space.closeRec k x s)
    | .dsum s₀ s₁    => .dsum (Space.closeRec k x s₀) (Space.closeRec k x s₁)
    | .tprod s₀ s₁   => .tprod (Space.closeRec k x s₀) (Space.closeRec k x s₁)
    | .ker s₀ s₁ e   => .ker (Space.closeRec k x s₀) (Space.closeRec k x s₁) (Term.closeRec k x e)
    | .coker s₀ s₁ e => .coker (Space.closeRec k x s₀) (Space.closeRec k x s₁) (Term.closeRec k x e)
    | .img s₀ s₁ e   => .img (Space.closeRec k x s₀) (Space.closeRec k x s₁) (Term.closeRec k x e)
    | .coimg s₀ s₁ e => .coimg (Space.closeRec k x s₀) (Space.closeRec k x s₁) (Term.closeRec k x e)

  def Ty.closeRec (k : Nat) (x : Name) : Ty → Ty
    | .space s    => .space (Space.closeRec k x s)
    | .piTy τ₀ τ₁ => .piTy (Ty.closeRec k x τ₀) (Ty.closeRec (k+1) x τ₁)

  def Term.closeRec (k : Nat) (x : Name) : Term → Term
    | .bvar i             => .bvar i
    | .var y              => if y = x then .bvar k else .var y
    | .real r             => .real r
    | .zero s             => .zero (Space.closeRec k x s)
    | .smul e₀ e₁         => .smul (Term.closeRec k x e₀) (Term.closeRec k x e₁)
    | .add e₀ e₁          => .add (Term.closeRec k x e₀) (Term.closeRec k x e₁)
    | .dsumE e₀ e₁        => .dsumE (Term.closeRec k x e₀) (Term.closeRec k x e₁)
    | .tprodE e₀ e₁       => .tprodE (Term.closeRec k x e₀) (Term.closeRec k x e₁)
    | .inner s            => .inner (Space.closeRec k x s)
    | .embed s            => .embed (Space.closeRec k x s)
    | .pinvT s₀ s₁ e      => .pinvT (Space.closeRec k x s₀) (Space.closeRec k x s₁) (Term.closeRec k x e)
    | .pinvD s e          => .pinvD (Space.closeRec k x s) (Term.closeRec k x e)
    | .llam s₀ s e        => .llam (Space.closeRec k x s₀) (Space.closeRec k x s) (Term.closeRec (k+1) x e)
    | .nllam τ e          => .nllam (Ty.closeRec k x τ) (Term.closeRec (k+1) x e)
    | .appL s₀ s₁ e₀ e₁   =>
        .appL (Space.closeRec k x s₀) (Space.closeRec k x s₁)
              (Term.closeRec k x e₀) (Term.closeRec k x e₁)
    | .appI s e₀ e₁       =>
        .appI (Space.closeRec k x s) (Term.closeRec k x e₀) (Term.closeRec k x e₁)
    | .appN e₀ e₁         => .appN (Term.closeRec k x e₀) (Term.closeRec k x e₁)
end

/-- Close every `Term` of a list (the `Basis.terms` summand list). -/
def Term.closeRecList (k : Nat) (x : Name) (es : List Term) : List Term :=
  es.map (Term.closeRec k x)

def Basis.closeRec (k : Nat) (x : Name) : Basis → Basis
  | .empty        => .empty
  | .one          => .one
  | .dual b       => .dual (Basis.closeRec k x b)
  | .dsum b₀ b₁   => .dsum (Basis.closeRec k x b₀) (Basis.closeRec k x b₁)
  | .tprod b₀ b₁  => .tprod (Basis.closeRec k x b₀) (Basis.closeRec k x b₁)
  | .proj s b₀ b₁ => .proj (Space.closeRec k x s) (Basis.closeRec k x b₀) (Basis.closeRec k x b₁)
  | .image b      => .image (Basis.closeRec k x b)
  | .terms s es b => .terms (Space.closeRec k x s) (Term.closeRecList k x es) (Basis.closeRec k x b)
  | .frame b₀ b₁  => .frame (Basis.closeRec k x b₀) (Basis.closeRec (k+1) x b₁)

/-! ## Derived openers. -/

/-- The β-substitution: instantiate the top bound index with `u`. -/
@[reducible] def Term.instantiate (u e : Term) : Term := Term.openRec 0 u e
@[reducible] def Ty.instantiate (u : Term) (τ : Ty) : Ty := Ty.openRec 0 u τ
@[reducible] def Basis.instantiate (u : Term) (b : Basis) : Basis := Basis.openRec 0 u b

/-- Open the top binder with a fresh free variable `x`. -/
@[reducible] def Term.openVar (x : Name) (e : Term) : Term := Term.openRec 0 (.var x) e
@[reducible] def Ty.openVar (x : Name) (σ : Ty) : Ty := Ty.openRec 0 (.var x) σ
@[reducible] def Basis.openVar (x : Name) (b : Basis) : Basis := Basis.openRec 0 (.var x) b

/-! ## `lc` — locally closed (no dangling `bvar`).

Cofinitely quantified at the four binders. REPLACES the named `bound`-freshness
discipline. There is deliberately NO `bvar` rule — a lone bound index is not
locally closed; indices only appear under their binder and become `var` once
opened. -/

mutual
  inductive Space.lc : Space → Prop
    | empty : Space.lc .empty
    | real  : Space.lc .real
    | dual  {s} : Space.lc s → Space.lc (.dual s)
    | dsum  {s₀ s₁} : Space.lc s₀ → Space.lc s₁ → Space.lc (.dsum s₀ s₁)
    | tprod {s₀ s₁} : Space.lc s₀ → Space.lc s₁ → Space.lc (.tprod s₀ s₁)
    | ker   {s₀ s₁ e} : Space.lc s₀ → Space.lc s₁ → Term.lc e → Space.lc (.ker s₀ s₁ e)
    | coker {s₀ s₁ e} : Space.lc s₀ → Space.lc s₁ → Term.lc e → Space.lc (.coker s₀ s₁ e)
    | img   {s₀ s₁ e} : Space.lc s₀ → Space.lc s₁ → Term.lc e → Space.lc (.img s₀ s₁ e)
    | coimg {s₀ s₁ e} : Space.lc s₀ → Space.lc s₁ → Term.lc e → Space.lc (.coimg s₀ s₁ e)

  inductive Ty.lc : Ty → Prop
    | space {s} : Space.lc s → Ty.lc (.space s)
    | piTy  {τ₀ τ₁} (L : Finset Name) :
        Ty.lc τ₀ → (∀ x, x ∉ L → Ty.lc (Ty.openVar x τ₁)) → Ty.lc (.piTy τ₀ τ₁)

  inductive Term.lc : Term → Prop
    | var   {x} : Term.lc (.var x)
    | real  {r} : Term.lc (.real r)
    | zero  {s} : Space.lc s → Term.lc (.zero s)
    | smul  {e₀ e₁} : Term.lc e₀ → Term.lc e₁ → Term.lc (.smul e₀ e₁)
    | add   {e₀ e₁} : Term.lc e₀ → Term.lc e₁ → Term.lc (.add e₀ e₁)
    | dsumE {e₀ e₁} : Term.lc e₀ → Term.lc e₁ → Term.lc (.dsumE e₀ e₁)
    | tprodE {e₀ e₁} : Term.lc e₀ → Term.lc e₁ → Term.lc (.tprodE e₀ e₁)
    | inner {s} : Space.lc s → Term.lc (.inner s)
    | embed {s} : Space.lc s → Term.lc (.embed s)
    | pinvT {s₀ s₁ e} : Space.lc s₀ → Space.lc s₁ → Term.lc e → Term.lc (.pinvT s₀ s₁ e)
    | pinvD {s e} : Space.lc s → Term.lc e → Term.lc (.pinvD s e)
    | llam  {s₀ s e} (L : Finset Name) :
        Space.lc s₀ → Space.lc s →
        (∀ x, x ∉ L → Term.lc (Term.openVar x e)) → Term.lc (.llam s₀ s e)
    | nllam {τ e} (L : Finset Name) :
        Ty.lc τ → (∀ x, x ∉ L → Term.lc (Term.openVar x e)) → Term.lc (.nllam τ e)
    | appL  {s₀ s₁ e₀ e₁} : Space.lc s₀ → Space.lc s₁ → Term.lc e₀ → Term.lc e₁ →
        Term.lc (.appL s₀ s₁ e₀ e₁)
    | appI  {s e₀ e₁} : Space.lc s → Term.lc e₀ → Term.lc e₁ → Term.lc (.appI s e₀ e₁)
    | appN  {e₀ e₁} : Term.lc e₀ → Term.lc e₁ → Term.lc (.appN e₀ e₁)
end

/-- `Basis.lc` — standalone inductive (references `Space.lc`/`Term.lc`/itself). -/
inductive Basis.lc : Basis → Prop
  | empty : Basis.lc .empty
  | one   : Basis.lc .one
  | dual  {b} : Basis.lc b → Basis.lc (.dual b)
  | dsum  {b₀ b₁} : Basis.lc b₀ → Basis.lc b₁ → Basis.lc (.dsum b₀ b₁)
  | tprod {b₀ b₁} : Basis.lc b₀ → Basis.lc b₁ → Basis.lc (.tprod b₀ b₁)
  | proj  {s b₀ b₁} : Space.lc s → Basis.lc b₀ → Basis.lc b₁ → Basis.lc (.proj s b₀ b₁)
  | image {b} : Basis.lc b → Basis.lc (.image b)
  | terms {s es b} : Space.lc s → (∀ e ∈ es, Term.lc e) → Basis.lc b → Basis.lc (.terms s es b)
  | frame {b₀ b₁} (L : Finset Name) :
      Basis.lc b₀ → (∀ x, x ∉ L → Basis.lc (Basis.openVar x b₁)) → Basis.lc (.frame b₀ b₁)

/-! ## List-companion `_eq_map` simp lemmas. -/

@[simp] theorem Term.openRecList_eq_map (k : Nat) (u : Term) (es : List Term) :
    Term.openRecList k u es = es.map (Term.openRec k u) := rfl
@[simp] theorem Term.closeRecList_eq_map (k : Nat) (x : Name) (es : List Term) :
    Term.closeRecList k x es = es.map (Term.closeRec k x) := rfl

/-! ## Lemma kit (1): `subst` is identity on a free name not in `fv`.

The LN analogue of the retired `subst_of_not_mem_fv`. No binder shadow-guards
(binders are nameless), so the binder arms recurse uniformly. -/

mutual
theorem Space.subst_fresh (x : Name) (u : Term) :
    ∀ (s : Space), x ∉ Space.fv s → Space.subst x u s = s
  | .empty, _ => rfl
  | .real, _ => rfl
  | .dual s, h => by
      simp only [Space.fv] at h
      simp only [Space.subst, Space.subst_fresh x u s h]
  | .dsum s₀ s₁, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.subst, Space.subst_fresh x u s₀ h.1, Space.subst_fresh x u s₁ h.2]
  | .tprod s₀ s₁, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.subst, Space.subst_fresh x u s₀ h.1, Space.subst_fresh x u s₁ h.2]
  | .ker s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.subst, Space.subst_fresh x u s₀ h.1.1, Space.subst_fresh x u s₁ h.1.2,
        Term.subst_fresh x u e h.2]
  | .coker s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.subst, Space.subst_fresh x u s₀ h.1.1, Space.subst_fresh x u s₁ h.1.2,
        Term.subst_fresh x u e h.2]
  | .img s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.subst, Space.subst_fresh x u s₀ h.1.1, Space.subst_fresh x u s₁ h.1.2,
        Term.subst_fresh x u e h.2]
  | .coimg s₀ s₁ e, h => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.subst, Space.subst_fresh x u s₀ h.1.1, Space.subst_fresh x u s₁ h.1.2,
        Term.subst_fresh x u e h.2]

theorem Ty.subst_fresh (x : Name) (u : Term) :
    ∀ (τ : Ty), x ∉ Ty.fv τ → Ty.subst x u τ = τ
  | .space s, h => by
      simp only [Ty.fv] at h
      simp only [Ty.subst, Space.subst_fresh x u s h]
  | .piTy τ₀ τ₁, h => by
      simp only [Ty.fv, Finset.mem_union, not_or] at h
      simp only [Ty.subst, Ty.subst_fresh x u τ₀ h.1, Ty.subst_fresh x u τ₁ h.2]

theorem Term.subst_fresh (x : Name) (u : Term) :
    ∀ (e : Term), x ∉ Term.fv e → Term.subst x u e = e
  | .bvar _, _ => rfl
  | .var y, h => by
      simp only [Term.fv, Finset.mem_singleton] at h
      simp only [Term.subst, if_neg h]
  | .real _, _ => rfl
  | .zero s, h => by
      simp only [Term.fv] at h; simp only [Term.subst, Space.subst_fresh x u s h]
  | .inner s, h => by
      simp only [Term.fv] at h; simp only [Term.subst, Space.subst_fresh x u s h]
  | .embed s, h => by
      simp only [Term.fv] at h; simp only [Term.subst, Space.subst_fresh x u s h]
  | .smul e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Term.subst_fresh x u e₀ h.1, Term.subst_fresh x u e₁ h.2]
  | .add e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Term.subst_fresh x u e₀ h.1, Term.subst_fresh x u e₁ h.2]
  | .dsumE e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Term.subst_fresh x u e₀ h.1, Term.subst_fresh x u e₁ h.2]
  | .tprodE e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Term.subst_fresh x u e₀ h.1, Term.subst_fresh x u e₁ h.2]
  | .pinvT s₀ s₁ e, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Space.subst_fresh x u s₀ h.1.1, Space.subst_fresh x u s₁ h.1.2,
        Term.subst_fresh x u e h.2]
  | .pinvD s e, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Space.subst_fresh x u s h.1, Term.subst_fresh x u e h.2]
  | .llam s₀ s e, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Space.subst_fresh x u s₀ h.1.1, Space.subst_fresh x u s h.1.2,
        Term.subst_fresh x u e h.2]
  | .nllam τ e, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Ty.subst_fresh x u τ h.1, Term.subst_fresh x u e h.2]
  | .appL s₀ s₁ e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Space.subst_fresh x u s₀ h.1.1.1, Space.subst_fresh x u s₁ h.1.1.2,
        Term.subst_fresh x u e₀ h.1.2, Term.subst_fresh x u e₁ h.2]
  | .appI s e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Space.subst_fresh x u s h.1.1, Term.subst_fresh x u e₀ h.1.2,
        Term.subst_fresh x u e₁ h.2]
  | .appN e₀ e₁, h => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.subst, Term.subst_fresh x u e₀ h.1, Term.subst_fresh x u e₁ h.2]
end

theorem Term.substList_fresh (x : Name) (u : Term) :
    ∀ (es : List Term), x ∉ Term.fvList es → es.map (Term.subst x u) = es
  | [], _ => rfl
  | e :: es, h => by
      simp only [Term.fvList, Finset.mem_union, not_or] at h
      simp only [List.map_cons, Term.subst_fresh x u e h.1, Term.substList_fresh x u es h.2]

theorem Basis.subst_fresh (x : Name) (u : Term) :
    ∀ (b : Basis), x ∉ Basis.fv b → Basis.subst x u b = b
  | .empty, _ => rfl
  | .one, _ => rfl
  | .dual b, h => by
      simp only [Basis.fv] at h; simp only [Basis.subst, Basis.subst_fresh x u b h]
  | .dsum b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.subst, Basis.subst_fresh x u b₀ h.1, Basis.subst_fresh x u b₁ h.2]
  | .tprod b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.subst, Basis.subst_fresh x u b₀ h.1, Basis.subst_fresh x u b₁ h.2]
  | .proj s b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.subst, Space.subst_fresh x u s h.1.1, Basis.subst_fresh x u b₀ h.1.2,
        Basis.subst_fresh x u b₁ h.2]
  | .image b, h => by
      simp only [Basis.fv] at h; simp only [Basis.subst, Basis.subst_fresh x u b h]
  | .terms s es b, h => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.subst, Space.subst_fresh x u s h.1.1, Basis.subst_fresh x u b h.1.2,
        Term.substList_fresh x u es h.2]
  | .frame b₀ b₁, h => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.subst, Basis.subst_fresh x u b₀ h.1, Basis.subst_fresh x u b₁ h.2]

/-! ## Lemma kit (2): `subst_intro` — opening = substituting at a fresh name.

`x ∉ fv e → openRec k u e = subst x u (openRec k (.var x) e)`. The bridge that
turns the cofinite "open at a fresh `x`" reasoning into `subst`. No `lc` needed;
pure structural induction (the inserted `.var x` lands at index `k`, and `subst`
turns exactly that occurrence into `u`). -/

mutual
theorem Space.subst_intro (x : Name) (u : Term) :
    ∀ (s : Space), x ∉ Space.fv s → ∀ (k : Nat),
      Space.openRec k u s = Space.subst x u (Space.openRec k (.var x) s)
  | .empty, _ => fun _ => rfl
  | .real, _ => fun _ => rfl
  | .dual s, h => fun k => by
      simp only [Space.fv] at h
      simp only [Space.openRec, Space.subst, Space.subst_intro x u s h k]
  | .dsum s₀ s₁, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.subst, Space.subst_intro x u s₀ h.1 k,
        Space.subst_intro x u s₁ h.2 k]
  | .tprod s₀ s₁, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.subst, Space.subst_intro x u s₀ h.1 k,
        Space.subst_intro x u s₁ h.2 k]
  | .ker s₀ s₁ e, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.subst, Space.subst_intro x u s₀ h.1.1 k,
        Space.subst_intro x u s₁ h.1.2 k, Term.subst_intro x u e h.2 k]
  | .coker s₀ s₁ e, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.subst, Space.subst_intro x u s₀ h.1.1 k,
        Space.subst_intro x u s₁ h.1.2 k, Term.subst_intro x u e h.2 k]
  | .img s₀ s₁ e, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.subst, Space.subst_intro x u s₀ h.1.1 k,
        Space.subst_intro x u s₁ h.1.2 k, Term.subst_intro x u e h.2 k]
  | .coimg s₀ s₁ e, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.subst, Space.subst_intro x u s₀ h.1.1 k,
        Space.subst_intro x u s₁ h.1.2 k, Term.subst_intro x u e h.2 k]

theorem Ty.subst_intro (x : Name) (u : Term) :
    ∀ (σ : Ty), x ∉ Ty.fv σ → ∀ (k : Nat),
      Ty.openRec k u σ = Ty.subst x u (Ty.openRec k (.var x) σ)
  | .space s, h => fun k => by
      simp only [Ty.fv] at h
      simp only [Ty.openRec, Ty.subst, Space.subst_intro x u s h k]
  | .piTy τ₀ τ₁, h => fun k => by
      simp only [Ty.fv, Finset.mem_union, not_or] at h
      simp only [Ty.openRec, Ty.subst, Ty.subst_intro x u τ₀ h.1 k,
        Ty.subst_intro x u τ₁ h.2 (k+1)]

theorem Term.subst_intro (x : Name) (u : Term) :
    ∀ (e : Term), x ∉ Term.fv e → ∀ (k : Nat),
      Term.openRec k u e = Term.subst x u (Term.openRec k (.var x) e)
  | .bvar i, _ => fun k => by
      by_cases hik : i = k
      · subst hik; simp only [Term.openRec, Term.subst, ↓reduceIte]
      · simp only [Term.openRec, if_neg hik, Term.subst]
  | .var y, h => fun k => by
      simp only [Term.fv, Finset.mem_singleton] at h
      simp only [Term.openRec, Term.subst, if_neg h]
  | .real _, _ => fun _ => rfl
  | .zero s, h => fun k => by
      simp only [Term.fv] at h
      simp only [Term.openRec, Term.subst, Space.subst_intro x u s h k]
  | .inner s, h => fun k => by
      simp only [Term.fv] at h
      simp only [Term.openRec, Term.subst, Space.subst_intro x u s h k]
  | .embed s, h => fun k => by
      simp only [Term.fv] at h
      simp only [Term.openRec, Term.subst, Space.subst_intro x u s h k]
  | .smul e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Term.subst_intro x u e₀ h.1 k,
        Term.subst_intro x u e₁ h.2 k]
  | .add e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Term.subst_intro x u e₀ h.1 k,
        Term.subst_intro x u e₁ h.2 k]
  | .dsumE e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Term.subst_intro x u e₀ h.1 k,
        Term.subst_intro x u e₁ h.2 k]
  | .tprodE e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Term.subst_intro x u e₀ h.1 k,
        Term.subst_intro x u e₁ h.2 k]
  | .pinvT s₀ s₁ e, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Space.subst_intro x u s₀ h.1.1 k,
        Space.subst_intro x u s₁ h.1.2 k, Term.subst_intro x u e h.2 k]
  | .pinvD s e, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Space.subst_intro x u s h.1 k,
        Term.subst_intro x u e h.2 k]
  | .llam s₀ s e, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Space.subst_intro x u s₀ h.1.1 k,
        Space.subst_intro x u s h.1.2 k, Term.subst_intro x u e h.2 (k+1)]
  | .nllam τ e, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Ty.subst_intro x u τ h.1 k,
        Term.subst_intro x u e h.2 (k+1)]
  | .appL s₀ s₁ e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Space.subst_intro x u s₀ h.1.1.1 k,
        Space.subst_intro x u s₁ h.1.1.2 k, Term.subst_intro x u e₀ h.1.2 k,
        Term.subst_intro x u e₁ h.2 k]
  | .appI s e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Space.subst_intro x u s h.1.1 k,
        Term.subst_intro x u e₀ h.1.2 k, Term.subst_intro x u e₁ h.2 k]
  | .appN e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.subst, Term.subst_intro x u e₀ h.1 k,
        Term.subst_intro x u e₁ h.2 k]
end

theorem Term.substList_intro (x : Name) (u : Term) :
    ∀ (es : List Term), x ∉ Term.fvList es → ∀ (k : Nat),
      es.map (Term.openRec k u) = (es.map (Term.openRec k (.var x))).map (Term.subst x u)
  | [], _ => fun _ => rfl
  | e :: es, h => fun k => by
      simp only [Term.fvList, Finset.mem_union, not_or] at h
      simp only [List.map_cons, Term.subst_intro x u e h.1 k, Term.substList_intro x u es h.2 k]

theorem Basis.subst_intro (x : Name) (u : Term) :
    ∀ (b : Basis), x ∉ Basis.fv b → ∀ (k : Nat),
      Basis.openRec k u b = Basis.subst x u (Basis.openRec k (.var x) b)
  | .empty, _ => fun _ => rfl
  | .one, _ => fun _ => rfl
  | .dual b, h => fun k => by
      simp only [Basis.fv] at h
      simp only [Basis.openRec, Basis.subst, Basis.subst_intro x u b h k]
  | .dsum b₀ b₁, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.subst, Basis.subst_intro x u b₀ h.1 k,
        Basis.subst_intro x u b₁ h.2 k]
  | .tprod b₀ b₁, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.subst, Basis.subst_intro x u b₀ h.1 k,
        Basis.subst_intro x u b₁ h.2 k]
  | .proj s b₀ b₁, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.subst, Space.subst_intro x u s h.1.1 k,
        Basis.subst_intro x u b₀ h.1.2 k, Basis.subst_intro x u b₁ h.2 k]
  | .image b, h => fun k => by
      simp only [Basis.fv] at h
      simp only [Basis.openRec, Basis.subst, Basis.subst_intro x u b h k]
  | .terms s es b, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.subst, Term.openRecList_eq_map,
        Space.subst_intro x u s h.1.1 k, Basis.subst_intro x u b h.1.2 k,
        Term.substList_intro x u es h.2 k]
  | .frame b₀ b₁, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.subst, Basis.subst_intro x u b₀ h.1 k,
        Basis.subst_intro x u b₁ h.2 (k+1)]

/-! ## Lemma kit (3): `openRec_lc_core` — index commutation.

Standard `open_rec_lc_core` (Aydemir et al.): a doubly-opened term whose outer
open is a no-op has a no-op single open at the other index. The `i ≠ j` guard
keeps the two opened indices distinct. -/

mutual
theorem Space.openRec_lc_core :
    ∀ (s : Space) (i j : Nat) (u v : Term), i ≠ j →
      Space.openRec i u (Space.openRec j v s) = Space.openRec j v s →
      Space.openRec i u s = s
  | .empty, _, _, _, _, _, _ => rfl
  | .real, _, _, _, _, _, _ => rfl
  | .dual s, i, j, u, v, hij, h => by
      simp only [Space.openRec] at h ⊢
      injection h with h₀
      rw [Space.openRec_lc_core s i j u v hij h₀]
  | .dsum s₀ s₁, i, j, u, v, hij, h => by
      simp only [Space.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Space.openRec_lc_core s₀ i j u v hij h₀, Space.openRec_lc_core s₁ i j u v hij h₁]
  | .tprod s₀ s₁, i, j, u, v, hij, h => by
      simp only [Space.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Space.openRec_lc_core s₀ i j u v hij h₀, Space.openRec_lc_core s₁ i j u v hij h₁]
  | .ker s₀ s₁ e, i, j, u, v, hij, h => by
      simp only [Space.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [Space.openRec_lc_core s₀ i j u v hij h₀, Space.openRec_lc_core s₁ i j u v hij h₁,
        Term.openRec_lc_core e i j u v hij h₂]
  | .coker s₀ s₁ e, i, j, u, v, hij, h => by
      simp only [Space.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [Space.openRec_lc_core s₀ i j u v hij h₀, Space.openRec_lc_core s₁ i j u v hij h₁,
        Term.openRec_lc_core e i j u v hij h₂]
  | .img s₀ s₁ e, i, j, u, v, hij, h => by
      simp only [Space.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [Space.openRec_lc_core s₀ i j u v hij h₀, Space.openRec_lc_core s₁ i j u v hij h₁,
        Term.openRec_lc_core e i j u v hij h₂]
  | .coimg s₀ s₁ e, i, j, u, v, hij, h => by
      simp only [Space.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [Space.openRec_lc_core s₀ i j u v hij h₀, Space.openRec_lc_core s₁ i j u v hij h₁,
        Term.openRec_lc_core e i j u v hij h₂]

theorem Ty.openRec_lc_core :
    ∀ (τ : Ty) (i j : Nat) (u v : Term), i ≠ j →
      Ty.openRec i u (Ty.openRec j v τ) = Ty.openRec j v τ →
      Ty.openRec i u τ = τ
  | .space s, i, j, u, v, hij, h => by
      simp only [Ty.openRec] at h ⊢
      injection h with h₀
      rw [Space.openRec_lc_core s i j u v hij h₀]
  | .piTy τ₀ τ₁, i, j, u, v, hij, h => by
      simp only [Ty.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Ty.openRec_lc_core τ₀ i j u v hij h₀,
        Ty.openRec_lc_core τ₁ (i+1) (j+1) u v (by omega) h₁]

theorem Term.openRec_lc_core :
    ∀ (e : Term) (i j : Nat) (u v : Term), i ≠ j →
      Term.openRec i u (Term.openRec j v e) = Term.openRec j v e →
      Term.openRec i u e = e
  | .bvar n, i, j, _, _, hij, h => by
      by_cases hnj : n = j
      · have hni : ¬ n = i := fun e => hij (e.symm.trans hnj)
        simp only [Term.openRec, if_neg hni]
      · simp only [Term.openRec, if_neg hnj] at h ⊢; exact h
  | .var _, _, _, _, _, _, _ => rfl
  | .real _, _, _, _, _, _, _ => rfl
  | .zero s, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀
      rw [Space.openRec_lc_core s i j u v hij h₀]
  | .inner s, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀
      rw [Space.openRec_lc_core s i j u v hij h₀]
  | .embed s, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀
      rw [Space.openRec_lc_core s i j u v hij h₀]
  | .smul e₀ e₁, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Term.openRec_lc_core e₀ i j u v hij h₀, Term.openRec_lc_core e₁ i j u v hij h₁]
  | .add e₀ e₁, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Term.openRec_lc_core e₀ i j u v hij h₀, Term.openRec_lc_core e₁ i j u v hij h₁]
  | .dsumE e₀ e₁, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Term.openRec_lc_core e₀ i j u v hij h₀, Term.openRec_lc_core e₁ i j u v hij h₁]
  | .tprodE e₀ e₁, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Term.openRec_lc_core e₀ i j u v hij h₀, Term.openRec_lc_core e₁ i j u v hij h₁]
  | .pinvT s₀ s₁ e, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [Space.openRec_lc_core s₀ i j u v hij h₀, Space.openRec_lc_core s₁ i j u v hij h₁,
        Term.openRec_lc_core e i j u v hij h₂]
  | .pinvD s e, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Space.openRec_lc_core s i j u v hij h₀, Term.openRec_lc_core e i j u v hij h₁]
  | .llam s₀ s e, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [Space.openRec_lc_core s₀ i j u v hij h₀, Space.openRec_lc_core s i j u v hij h₁,
        Term.openRec_lc_core e (i+1) (j+1) u v (by omega) h₂]
  | .nllam τ e, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Ty.openRec_lc_core τ i j u v hij h₀,
        Term.openRec_lc_core e (i+1) (j+1) u v (by omega) h₁]
  | .appL s₀ s₁ e₀ e₁, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁ h₂ h₃
      rw [Space.openRec_lc_core s₀ i j u v hij h₀, Space.openRec_lc_core s₁ i j u v hij h₁,
        Term.openRec_lc_core e₀ i j u v hij h₂, Term.openRec_lc_core e₁ i j u v hij h₃]
  | .appI s e₀ e₁, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [Space.openRec_lc_core s i j u v hij h₀, Term.openRec_lc_core e₀ i j u v hij h₁,
        Term.openRec_lc_core e₁ i j u v hij h₂]
  | .appN e₀ e₁, i, j, u, v, hij, h => by
      simp only [Term.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Term.openRec_lc_core e₀ i j u v hij h₀, Term.openRec_lc_core e₁ i j u v hij h₁]
end

theorem Term.openRecList_lc_core (es : List Term) (i j : Nat) (u v : Term) (hij : i ≠ j)
    (h : (es.map (Term.openRec j v)).map (Term.openRec i u) = es.map (Term.openRec j v)) :
    es.map (Term.openRec i u) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨Term.openRec_lc_core e i j u v hij h.1, ih h.2⟩

theorem Basis.openRec_lc_core :
    ∀ (b : Basis) (i j : Nat) (u v : Term), i ≠ j →
      Basis.openRec i u (Basis.openRec j v b) = Basis.openRec j v b →
      Basis.openRec i u b = b
  | .empty, _, _, _, _, _, _ => rfl
  | .one, _, _, _, _, _, _ => rfl
  | .dual b, i, j, u, v, hij, h => by
      simp only [Basis.openRec] at h ⊢
      injection h with h₀
      rw [Basis.openRec_lc_core b i j u v hij h₀]
  | .dsum b₀ b₁, i, j, u, v, hij, h => by
      simp only [Basis.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Basis.openRec_lc_core b₀ i j u v hij h₀, Basis.openRec_lc_core b₁ i j u v hij h₁]
  | .tprod b₀ b₁, i, j, u, v, hij, h => by
      simp only [Basis.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Basis.openRec_lc_core b₀ i j u v hij h₀, Basis.openRec_lc_core b₁ i j u v hij h₁]
  | .proj s b₀ b₁, i, j, u, v, hij, h => by
      simp only [Basis.openRec] at h ⊢
      injection h with h₀ h₁ h₂
      rw [Space.openRec_lc_core s i j u v hij h₀, Basis.openRec_lc_core b₀ i j u v hij h₁,
        Basis.openRec_lc_core b₁ i j u v hij h₂]
  | .image b, i, j, u, v, hij, h => by
      simp only [Basis.openRec] at h ⊢
      injection h with h₀
      rw [Basis.openRec_lc_core b i j u v hij h₀]
  | .terms s es b, i, j, u, v, hij, h => by
      simp only [Basis.openRec, Term.openRecList_eq_map] at h ⊢
      injection h with h₀ h₁ h₂
      rw [Space.openRec_lc_core s i j u v hij h₀, Term.openRecList_lc_core es i j u v hij h₁,
        Basis.openRec_lc_core b i j u v hij h₂]
  | .frame b₀ b₁, i, j, u, v, hij, h => by
      simp only [Basis.openRec] at h ⊢
      injection h with h₀ h₁
      rw [Basis.openRec_lc_core b₀ i j u v hij h₀,
        Basis.openRec_lc_core b₁ (i+1) (j+1) u v (by omega) h₁]

/-! ## Lemma kit (3b): `openRec_lc` — opening a locally-closed term is the identity.

Term-mode recursion on the `lc` proof. Binder cases pick a fresh `x ∉ L` and
transport the opened-body fact to index `k+1` via `openRec_lc_core`. -/
mutual
theorem Space.openRec_lc :
    ∀ {s : Space}, Space.lc s → ∀ (k : Nat) (u : Term), Space.openRec k u s = s
  | _, .empty => fun _ _ => rfl
  | _, .real => fun _ _ => rfl
  | _, .dual hs => fun k u => by simp only [Space.openRec, Space.openRec_lc hs k u]
  | _, .dsum h₀ h₁ => fun k u => by
      simp only [Space.openRec, Space.openRec_lc h₀ k u, Space.openRec_lc h₁ k u]
  | _, .tprod h₀ h₁ => fun k u => by
      simp only [Space.openRec, Space.openRec_lc h₀ k u, Space.openRec_lc h₁ k u]
  | _, .ker hs₀ hs₁ he => fun k u => by
      simp only [Space.openRec, Space.openRec_lc hs₀ k u, Space.openRec_lc hs₁ k u,
        Term.openRec_lc he k u]
  | _, .coker hs₀ hs₁ he => fun k u => by
      simp only [Space.openRec, Space.openRec_lc hs₀ k u, Space.openRec_lc hs₁ k u,
        Term.openRec_lc he k u]
  | _, .img hs₀ hs₁ he => fun k u => by
      simp only [Space.openRec, Space.openRec_lc hs₀ k u, Space.openRec_lc hs₁ k u,
        Term.openRec_lc he k u]
  | _, .coimg hs₀ hs₁ he => fun k u => by
      simp only [Space.openRec, Space.openRec_lc hs₀ k u, Space.openRec_lc hs₁ k u,
        Term.openRec_lc he k u]

theorem Ty.openRec_lc :
    ∀ {τ : Ty}, Ty.lc τ → ∀ (k : Nat) (u : Term), Ty.openRec k u τ = τ
  | _, .space hs => fun k u => by simp only [Ty.openRec, Space.openRec_lc hs k u]
  | .piTy τ₀ τ₁, .piTy L hτ₀ hbody => fun k u => by
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset L
      have hb := Ty.openRec_lc (hbody x hx) (k+1) u
      simp only [Ty.openVar] at hb
      have hc := Ty.openRec_lc_core τ₁ (k+1) 0 u (.var x) (by omega) hb
      simp only [Ty.openRec, Ty.openRec_lc hτ₀ k u, hc]

theorem Term.openRec_lc :
    ∀ {e : Term}, Term.lc e → ∀ (k : Nat) (u : Term), Term.openRec k u e = e
  | _, .var => fun _ _ => rfl
  | _, .real => fun _ _ => rfl
  | _, .zero hs => fun k u => by simp only [Term.openRec, Space.openRec_lc hs k u]
  | _, .inner hs => fun k u => by simp only [Term.openRec, Space.openRec_lc hs k u]
  | _, .embed hs => fun k u => by simp only [Term.openRec, Space.openRec_lc hs k u]
  | _, .smul h₀ h₁ => fun k u => by
      simp only [Term.openRec, Term.openRec_lc h₀ k u, Term.openRec_lc h₁ k u]
  | _, .add h₀ h₁ => fun k u => by
      simp only [Term.openRec, Term.openRec_lc h₀ k u, Term.openRec_lc h₁ k u]
  | _, .dsumE h₀ h₁ => fun k u => by
      simp only [Term.openRec, Term.openRec_lc h₀ k u, Term.openRec_lc h₁ k u]
  | _, .tprodE h₀ h₁ => fun k u => by
      simp only [Term.openRec, Term.openRec_lc h₀ k u, Term.openRec_lc h₁ k u]
  | _, .pinvT hs₀ hs₁ he => fun k u => by
      simp only [Term.openRec, Space.openRec_lc hs₀ k u, Space.openRec_lc hs₁ k u,
        Term.openRec_lc he k u]
  | _, .pinvD hs he => fun k u => by
      simp only [Term.openRec, Space.openRec_lc hs k u, Term.openRec_lc he k u]
  | .llam s₀ s e, .llam L hs₀ hs hbody => fun k u => by
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset L
      have hbe := Term.openRec_lc (hbody x hx) (k+1) u
      simp only [Term.openVar] at hbe
      have hce := Term.openRec_lc_core e (k+1) 0 u (.var x) (by omega) hbe
      simp only [Term.openRec, Space.openRec_lc hs₀ k u, Space.openRec_lc hs k u, hce]
  | .nllam τ e, .nllam L hτ hbody => fun k u => by
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset L
      have hbe := Term.openRec_lc (hbody x hx) (k+1) u
      simp only [Term.openVar] at hbe
      have hce := Term.openRec_lc_core e (k+1) 0 u (.var x) (by omega) hbe
      simp only [Term.openRec, Ty.openRec_lc hτ k u, hce]
  | _, .appL hs₀ hs₁ h₀ h₁ => fun k u => by
      simp only [Term.openRec, Space.openRec_lc hs₀ k u, Space.openRec_lc hs₁ k u,
        Term.openRec_lc h₀ k u, Term.openRec_lc h₁ k u]
  | _, .appI hs h₀ h₁ => fun k u => by
      simp only [Term.openRec, Space.openRec_lc hs k u, Term.openRec_lc h₀ k u,
        Term.openRec_lc h₁ k u]
  | _, .appN h₀ h₁ => fun k u => by
      simp only [Term.openRec, Term.openRec_lc h₀ k u, Term.openRec_lc h₁ k u]
end

theorem Basis.openRec_lc :
    ∀ {b : Basis}, Basis.lc b → ∀ (k : Nat) (u : Term), Basis.openRec k u b = b
  | _, .empty => fun _ _ => rfl
  | _, .one => fun _ _ => rfl
  | _, .dual hb => fun k u => by simp only [Basis.openRec, Basis.openRec_lc hb k u]
  | _, .dsum h₀ h₁ => fun k u => by
      simp only [Basis.openRec, Basis.openRec_lc h₀ k u, Basis.openRec_lc h₁ k u]
  | _, .tprod h₀ h₁ => fun k u => by
      simp only [Basis.openRec, Basis.openRec_lc h₀ k u, Basis.openRec_lc h₁ k u]
  | _, .proj hs hb₀ hb₁ => fun k u => by
      simp only [Basis.openRec, Space.openRec_lc hs k u, Basis.openRec_lc hb₀ k u,
        Basis.openRec_lc hb₁ k u]
  | _, .image hb => fun k u => by simp only [Basis.openRec, Basis.openRec_lc hb k u]
  | _, .terms hs hes hb => fun k u => by
      simp only [Basis.openRec, Term.openRecList_eq_map, Space.openRec_lc hs k u,
        Basis.openRec_lc hb k u]
      rw [List.map_congr_left (g := id) (fun e he => Term.openRec_lc (hes e he) k u), List.map_id]
  | .frame b₀ b₁, .frame L hb₀ hbody => fun k u => by
      obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset L
      have hb := Basis.openRec_lc (hbody x hx) (k+1) u
      simp only [Basis.openVar] at hb
      have hc := Basis.openRec_lc_core b₁ (k+1) 0 u (.var x) (by omega) hb
      simp only [Basis.openRec, Basis.openRec_lc hb₀ k u, hc]

/-! ## Lemma kit (4): `subst_openRec` — substitution commutes with opening.

`lc u → subst x u (openRec k v e) = openRec k (subst x u v) (subst x u e)`. The β
substitution lemma. Only the `var x` leaf uses `lc u` (via `open_lc`, to discharge
`openRec k _ u = u`); everything else is structural. -/

mutual
theorem Space.subst_openRec (x : Name) (u : Term) (hu : Term.lc u) :
    ∀ (s : Space) (k : Nat) (v : Term),
      Space.subst x u (Space.openRec k v s)
        = Space.openRec k (Term.subst x u v) (Space.subst x u s)
  | .empty, _, _ => rfl
  | .real, _, _ => rfl
  | .dual s, k, v => by
      simp only [Space.openRec, Space.subst, Space.subst_openRec x u hu s k v]
  | .dsum s₀ s₁, k, v => by
      simp only [Space.openRec, Space.subst, Space.subst_openRec x u hu s₀ k v,
        Space.subst_openRec x u hu s₁ k v]
  | .tprod s₀ s₁, k, v => by
      simp only [Space.openRec, Space.subst, Space.subst_openRec x u hu s₀ k v,
        Space.subst_openRec x u hu s₁ k v]
  | .ker s₀ s₁ e, k, v => by
      simp only [Space.openRec, Space.subst, Space.subst_openRec x u hu s₀ k v,
        Space.subst_openRec x u hu s₁ k v, Term.subst_openRec x u hu e k v]
  | .coker s₀ s₁ e, k, v => by
      simp only [Space.openRec, Space.subst, Space.subst_openRec x u hu s₀ k v,
        Space.subst_openRec x u hu s₁ k v, Term.subst_openRec x u hu e k v]
  | .img s₀ s₁ e, k, v => by
      simp only [Space.openRec, Space.subst, Space.subst_openRec x u hu s₀ k v,
        Space.subst_openRec x u hu s₁ k v, Term.subst_openRec x u hu e k v]
  | .coimg s₀ s₁ e, k, v => by
      simp only [Space.openRec, Space.subst, Space.subst_openRec x u hu s₀ k v,
        Space.subst_openRec x u hu s₁ k v, Term.subst_openRec x u hu e k v]

theorem Ty.subst_openRec (x : Name) (u : Term) (hu : Term.lc u) :
    ∀ (τ : Ty) (k : Nat) (v : Term),
      Ty.subst x u (Ty.openRec k v τ)
        = Ty.openRec k (Term.subst x u v) (Ty.subst x u τ)
  | .space s, k, v => by
      simp only [Ty.openRec, Ty.subst, Space.subst_openRec x u hu s k v]
  | .piTy τ₀ τ₁, k, v => by
      simp only [Ty.openRec, Ty.subst, Ty.subst_openRec x u hu τ₀ k v,
        Ty.subst_openRec x u hu τ₁ (k+1) v]

theorem Term.subst_openRec (x : Name) (u : Term) (hu : Term.lc u) :
    ∀ (e : Term) (k : Nat) (v : Term),
      Term.subst x u (Term.openRec k v e)
        = Term.openRec k (Term.subst x u v) (Term.subst x u e)
  | .bvar i, k, v => by
      by_cases hik : i = k
      · subst hik; simp only [Term.openRec, Term.subst, ↓reduceIte]
      · simp only [Term.openRec, if_neg hik, Term.subst]
  | .var y, k, v => by
      by_cases hxy : x = y
      · subst hxy
        simp only [Term.openRec, Term.subst, ↓reduceIte, Term.openRec_lc hu k _]
      · simp only [Term.openRec, Term.subst, if_neg hxy]
  | .real _, _, _ => rfl
  | .zero s, k, v => by
      simp only [Term.openRec, Term.subst, Space.subst_openRec x u hu s k v]
  | .inner s, k, v => by
      simp only [Term.openRec, Term.subst, Space.subst_openRec x u hu s k v]
  | .embed s, k, v => by
      simp only [Term.openRec, Term.subst, Space.subst_openRec x u hu s k v]
  | .smul e₀ e₁, k, v => by
      simp only [Term.openRec, Term.subst, Term.subst_openRec x u hu e₀ k v,
        Term.subst_openRec x u hu e₁ k v]
  | .add e₀ e₁, k, v => by
      simp only [Term.openRec, Term.subst, Term.subst_openRec x u hu e₀ k v,
        Term.subst_openRec x u hu e₁ k v]
  | .dsumE e₀ e₁, k, v => by
      simp only [Term.openRec, Term.subst, Term.subst_openRec x u hu e₀ k v,
        Term.subst_openRec x u hu e₁ k v]
  | .tprodE e₀ e₁, k, v => by
      simp only [Term.openRec, Term.subst, Term.subst_openRec x u hu e₀ k v,
        Term.subst_openRec x u hu e₁ k v]
  | .pinvT s₀ s₁ e, k, v => by
      simp only [Term.openRec, Term.subst, Space.subst_openRec x u hu s₀ k v,
        Space.subst_openRec x u hu s₁ k v, Term.subst_openRec x u hu e k v]
  | .pinvD s e, k, v => by
      simp only [Term.openRec, Term.subst, Space.subst_openRec x u hu s k v,
        Term.subst_openRec x u hu e k v]
  | .llam s₀ s e, k, v => by
      simp only [Term.openRec, Term.subst, Space.subst_openRec x u hu s₀ k v,
        Space.subst_openRec x u hu s k v, Term.subst_openRec x u hu e (k+1) v]
  | .nllam τ e, k, v => by
      simp only [Term.openRec, Term.subst, Ty.subst_openRec x u hu τ k v,
        Term.subst_openRec x u hu e (k+1) v]
  | .appL s₀ s₁ e₀ e₁, k, v => by
      simp only [Term.openRec, Term.subst, Space.subst_openRec x u hu s₀ k v,
        Space.subst_openRec x u hu s₁ k v, Term.subst_openRec x u hu e₀ k v,
        Term.subst_openRec x u hu e₁ k v]
  | .appI s e₀ e₁, k, v => by
      simp only [Term.openRec, Term.subst, Space.subst_openRec x u hu s k v,
        Term.subst_openRec x u hu e₀ k v, Term.subst_openRec x u hu e₁ k v]
  | .appN e₀ e₁, k, v => by
      simp only [Term.openRec, Term.subst, Term.subst_openRec x u hu e₀ k v,
        Term.subst_openRec x u hu e₁ k v]
end

theorem Term.substList_openRec (x : Name) (u : Term) (hu : Term.lc u) :
    ∀ (es : List Term) (k : Nat) (v : Term),
      (es.map (Term.openRec k v)).map (Term.subst x u)
        = (es.map (Term.subst x u)).map (Term.openRec k (Term.subst x u v))
  | [], _, _ => rfl
  | e :: es, k, v => by
      simp only [List.map_cons, Term.subst_openRec x u hu e k v,
        Term.substList_openRec x u hu es k v]

theorem Basis.subst_openRec (x : Name) (u : Term) (hu : Term.lc u) :
    ∀ (b : Basis) (k : Nat) (v : Term),
      Basis.subst x u (Basis.openRec k v b)
        = Basis.openRec k (Term.subst x u v) (Basis.subst x u b)
  | .empty, _, _ => rfl
  | .one, _, _ => rfl
  | .dual b, k, v => by
      simp only [Basis.openRec, Basis.subst, Basis.subst_openRec x u hu b k v]
  | .dsum b₀ b₁, k, v => by
      simp only [Basis.openRec, Basis.subst, Basis.subst_openRec x u hu b₀ k v,
        Basis.subst_openRec x u hu b₁ k v]
  | .tprod b₀ b₁, k, v => by
      simp only [Basis.openRec, Basis.subst, Basis.subst_openRec x u hu b₀ k v,
        Basis.subst_openRec x u hu b₁ k v]
  | .proj s b₀ b₁, k, v => by
      simp only [Basis.openRec, Basis.subst, Space.subst_openRec x u hu s k v,
        Basis.subst_openRec x u hu b₀ k v, Basis.subst_openRec x u hu b₁ k v]
  | .image b, k, v => by
      simp only [Basis.openRec, Basis.subst, Basis.subst_openRec x u hu b k v]
  | .terms s es b, k, v => by
      simp only [Basis.openRec, Basis.subst, Term.openRecList_eq_map,
        Space.subst_openRec x u hu s k v, Basis.subst_openRec x u hu b k v,
        Term.substList_openRec x u hu es k v]
  | .frame b₀ b₁, k, v => by
      simp only [Basis.openRec, Basis.subst, Basis.subst_openRec x u hu b₀ k v,
        Basis.subst_openRec x u hu b₁ (k+1) v]

/-! ## Lemma kit (5): `close_openVar` — close after open-with-fresh recovers the body.

`x ∉ fv e → closeRec k x (openRec k (.var x) e) = e`. The introduced `.var x`
abstracts straight back to `bvar k`. Structural induction; `x ∉ fv` ensures the
only `x`-occurrence is the one `openRec` introduced. -/

mutual
theorem Space.close_openVar (x : Name) :
    ∀ (s : Space), x ∉ Space.fv s → ∀ (k : Nat),
      Space.closeRec k x (Space.openRec k (.var x) s) = s
  | .empty, _ => fun _ => rfl
  | .real, _ => fun _ => rfl
  | .dual s, h => fun k => by
      simp only [Space.fv] at h
      simp only [Space.openRec, Space.closeRec, Space.close_openVar x s h k]
  | .dsum s₀ s₁, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.closeRec, Space.close_openVar x s₀ h.1 k,
        Space.close_openVar x s₁ h.2 k]
  | .tprod s₀ s₁, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.closeRec, Space.close_openVar x s₀ h.1 k,
        Space.close_openVar x s₁ h.2 k]
  | .ker s₀ s₁ e, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.closeRec, Space.close_openVar x s₀ h.1.1 k,
        Space.close_openVar x s₁ h.1.2 k, Term.close_openVar x e h.2 k]
  | .coker s₀ s₁ e, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.closeRec, Space.close_openVar x s₀ h.1.1 k,
        Space.close_openVar x s₁ h.1.2 k, Term.close_openVar x e h.2 k]
  | .img s₀ s₁ e, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.closeRec, Space.close_openVar x s₀ h.1.1 k,
        Space.close_openVar x s₁ h.1.2 k, Term.close_openVar x e h.2 k]
  | .coimg s₀ s₁ e, h => fun k => by
      simp only [Space.fv, Finset.mem_union, not_or] at h
      simp only [Space.openRec, Space.closeRec, Space.close_openVar x s₀ h.1.1 k,
        Space.close_openVar x s₁ h.1.2 k, Term.close_openVar x e h.2 k]

theorem Ty.close_openVar (x : Name) :
    ∀ (σ : Ty), x ∉ Ty.fv σ → ∀ (k : Nat),
      Ty.closeRec k x (Ty.openRec k (.var x) σ) = σ
  | .space s, h => fun k => by
      simp only [Ty.fv] at h
      simp only [Ty.openRec, Ty.closeRec, Space.close_openVar x s h k]
  | .piTy τ₀ τ₁, h => fun k => by
      simp only [Ty.fv, Finset.mem_union, not_or] at h
      simp only [Ty.openRec, Ty.closeRec, Ty.close_openVar x τ₀ h.1 k,
        Ty.close_openVar x τ₁ h.2 (k+1)]

theorem Term.close_openVar (x : Name) :
    ∀ (e : Term), x ∉ Term.fv e → ∀ (k : Nat),
      Term.closeRec k x (Term.openRec k (.var x) e) = e
  | .bvar i, _ => fun k => by
      by_cases hik : i = k
      · subst hik; simp only [Term.openRec, Term.closeRec, ↓reduceIte]
      · simp only [Term.openRec, if_neg hik, Term.closeRec]
  | .var y, h => fun k => by
      simp only [Term.fv, Finset.mem_singleton] at h
      simp only [Term.openRec, Term.closeRec, if_neg (Ne.symm h)]
  | .real _, _ => fun _ => rfl
  | .zero s, h => fun k => by
      simp only [Term.fv] at h
      simp only [Term.openRec, Term.closeRec, Space.close_openVar x s h k]
  | .inner s, h => fun k => by
      simp only [Term.fv] at h
      simp only [Term.openRec, Term.closeRec, Space.close_openVar x s h k]
  | .embed s, h => fun k => by
      simp only [Term.fv] at h
      simp only [Term.openRec, Term.closeRec, Space.close_openVar x s h k]
  | .smul e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Term.close_openVar x e₀ h.1 k,
        Term.close_openVar x e₁ h.2 k]
  | .add e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Term.close_openVar x e₀ h.1 k,
        Term.close_openVar x e₁ h.2 k]
  | .dsumE e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Term.close_openVar x e₀ h.1 k,
        Term.close_openVar x e₁ h.2 k]
  | .tprodE e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Term.close_openVar x e₀ h.1 k,
        Term.close_openVar x e₁ h.2 k]
  | .pinvT s₀ s₁ e, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Space.close_openVar x s₀ h.1.1 k,
        Space.close_openVar x s₁ h.1.2 k, Term.close_openVar x e h.2 k]
  | .pinvD s e, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Space.close_openVar x s h.1 k,
        Term.close_openVar x e h.2 k]
  | .llam s₀ s e, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Space.close_openVar x s₀ h.1.1 k,
        Space.close_openVar x s h.1.2 k, Term.close_openVar x e h.2 (k+1)]
  | .nllam τ e, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Ty.close_openVar x τ h.1 k,
        Term.close_openVar x e h.2 (k+1)]
  | .appL s₀ s₁ e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Space.close_openVar x s₀ h.1.1.1 k,
        Space.close_openVar x s₁ h.1.1.2 k, Term.close_openVar x e₀ h.1.2 k,
        Term.close_openVar x e₁ h.2 k]
  | .appI s e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Space.close_openVar x s h.1.1 k,
        Term.close_openVar x e₀ h.1.2 k, Term.close_openVar x e₁ h.2 k]
  | .appN e₀ e₁, h => fun k => by
      simp only [Term.fv, Finset.mem_union, not_or] at h
      simp only [Term.openRec, Term.closeRec, Term.close_openVar x e₀ h.1 k,
        Term.close_openVar x e₁ h.2 k]
end

theorem Term.closeList_openList (x : Name) :
    ∀ (es : List Term), x ∉ Term.fvList es → ∀ (k : Nat),
      (es.map (Term.openRec k (.var x))).map (Term.closeRec k x) = es
  | [], _ => fun _ => rfl
  | e :: es, h => fun k => by
      simp only [Term.fvList, Finset.mem_union, not_or] at h
      simp only [List.map_cons, Term.close_openVar x e h.1 k, Term.closeList_openList x es h.2 k]

theorem Basis.close_openVar (x : Name) :
    ∀ (b : Basis), x ∉ Basis.fv b → ∀ (k : Nat),
      Basis.closeRec k x (Basis.openRec k (.var x) b) = b
  | .empty, _ => fun _ => rfl
  | .one, _ => fun _ => rfl
  | .dual b, h => fun k => by
      simp only [Basis.fv] at h
      simp only [Basis.openRec, Basis.closeRec, Basis.close_openVar x b h k]
  | .dsum b₀ b₁, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.closeRec, Basis.close_openVar x b₀ h.1 k,
        Basis.close_openVar x b₁ h.2 k]
  | .tprod b₀ b₁, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.closeRec, Basis.close_openVar x b₀ h.1 k,
        Basis.close_openVar x b₁ h.2 k]
  | .proj s b₀ b₁, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.closeRec, Space.close_openVar x s h.1.1 k,
        Basis.close_openVar x b₀ h.1.2 k, Basis.close_openVar x b₁ h.2 k]
  | .image b, h => fun k => by
      simp only [Basis.fv] at h
      simp only [Basis.openRec, Basis.closeRec, Basis.close_openVar x b h k]
  | .terms s es b, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.closeRec, Term.openRecList_eq_map,
        Term.closeRecList_eq_map, Space.close_openVar x s h.1.1 k,
        Basis.close_openVar x b h.1.2 k, Term.closeList_openList x es h.2 k]
  | .frame b₀ b₁, h => fun k => by
      simp only [Basis.fv, Finset.mem_union, not_or] at h
      simp only [Basis.openRec, Basis.closeRec, Basis.close_openVar x b₀ h.1 k,
        Basis.close_openVar x b₁ h.2 (k+1)]

/-! ## Lemma kit (6): `fv` under `openRec` / `subst` (scoping subsets).

`fv (openRec k v e) ⊆ fv e ∪ fv v` and `fv (subst x u e) ⊆ fv e ∪ fv u`, plus
the monotonicity reverse `fv e ⊆ fv (openRec k v e)`. Membership form; subset
corollaries below. -/

mutual
theorem Space.fv_openRec_mem {a : Name} {k : Nat} {v : Term} :
    ∀ {s : Space}, a ∈ Space.fv (Space.openRec k v s) → a ∈ Space.fv s ∪ Term.fv v
  | .empty, h => by simp only [Space.openRec, Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .real, h => by simp only [Space.openRec, Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .dual s, h => by
      simp only [Space.openRec, Space.fv] at h ⊢; exact Space.fv_openRec_mem h
  | .dsum s₀ s₁, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprod s₀ s₁, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .ker s₀ s₁ e, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .coker s₀ s₁ e, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .img s₀ s₁ e, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .coimg s₀ s₁ e, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'

theorem Ty.fv_openRec_mem {a : Name} {k : Nat} {v : Term} :
    ∀ {τ : Ty}, a ∈ Ty.fv (Ty.openRec k v τ) → a ∈ Ty.fv τ ∪ Term.fv v
  | .space s, h => by
      simp only [Ty.openRec, Ty.fv] at h ⊢; exact Space.fv_openRec_mem h
  | .piTy τ₀ τ₁, h => by
      simp only [Ty.openRec, Ty.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Ty.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

theorem Term.fv_openRec_mem {a : Name} {k : Nat} {v : Term} :
    ∀ {e : Term}, a ∈ Term.fv (Term.openRec k v e) → a ∈ Term.fv e ∪ Term.fv v
  | .bvar i, h => by
      by_cases hik : i = k
      · subst hik; simp only [Term.openRec, ↓reduceIte] at h
        exact Finset.mem_union_right _ h
      · simp only [Term.openRec, if_neg hik, Term.fv] at h
        exact absurd h (Finset.notMem_empty _)
  | .var y, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_singleton] at h
      subst h
      exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  | .real _, h => by simp only [Term.openRec, Term.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .zero s, h => by
      simp only [Term.openRec, Term.fv] at h ⊢; exact Space.fv_openRec_mem h
  | .inner s, h => by
      simp only [Term.openRec, Term.fv] at h ⊢; exact Space.fv_openRec_mem h
  | .embed s, h => by
      simp only [Term.openRec, Term.fv] at h ⊢; exact Space.fv_openRec_mem h
  | .smul e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .add e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .dsumE e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprodE e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .pinvT s₀ s₁ e, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .pinvD s e, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .llam s₀ s e, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .nllam τ e, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · rcases Finset.mem_union.mp (Ty.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .appL s₀ s₁ e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with ((h | h) | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inl h')))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inr h')))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .appI s e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .appN e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
end

theorem Basis.fv_openRec_mem {a : Name} {k : Nat} {v : Term} :
    ∀ {b : Basis}, a ∈ Basis.fv (Basis.openRec k v b) → a ∈ Basis.fv b ∪ Term.fv v
  | .empty, h => by simp only [Basis.openRec, Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .one, h => by simp only [Basis.openRec, Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .dual b, h => by
      simp only [Basis.openRec, Basis.fv] at h ⊢; exact Basis.fv_openRec_mem h
  | .dsum b₀ b₁, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Basis.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprod b₀ b₁, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Basis.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .proj s b₀ b₁, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Basis.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Basis.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .image b, h => by
      simp only [Basis.openRec, Basis.fv] at h ⊢; exact Basis.fv_openRec_mem h
  | .terms s es b, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union, Term.openRecList_eq_map] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Basis.fv_openRec_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rw [Term.mem_fvList] at h
        obtain ⟨e', hmem, he'⟩ := h
        obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hmem
        rcases Finset.mem_union.mp (Term.fv_openRec_mem he') with h' | h'
        · exact Or.inl (Or.inr (Term.mem_fvList.mpr ⟨e₀, he₀, h'⟩))
        · exact Or.inr h'
  | .frame b₀ b₁, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Basis.fv_openRec_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

theorem Space.fv_openRec_subset (k : Nat) (v : Term) (s : Space) :
    Space.fv (Space.openRec k v s) ⊆ Space.fv s ∪ Term.fv v :=
  fun _ ha => Space.fv_openRec_mem ha
theorem Ty.fv_openRec_subset (k : Nat) (v : Term) (τ : Ty) :
    Ty.fv (Ty.openRec k v τ) ⊆ Ty.fv τ ∪ Term.fv v :=
  fun _ ha => Ty.fv_openRec_mem ha
theorem Term.fv_openRec_subset (k : Nat) (v : Term) (e : Term) :
    Term.fv (Term.openRec k v e) ⊆ Term.fv e ∪ Term.fv v :=
  fun _ ha => Term.fv_openRec_mem ha
theorem Basis.fv_openRec_subset (k : Nat) (v : Term) (b : Basis) :
    Basis.fv (Basis.openRec k v b) ⊆ Basis.fv b ∪ Term.fv v :=
  fun _ ha => Basis.fv_openRec_mem ha

/-! ### `fv` MONOTONICITY under opening (reverse direction).

`openRec k v` only replaces the BOUND index `k`; a FREE name in the body
survives. So `fv X ⊆ fv (openRec k v X)`. -/
mutual
theorem Space.fv_subset_openRec {a : Name} {v : Term} :
    ∀ {k : Nat} {s : Space}, a ∈ Space.fv s → a ∈ Space.fv (Space.openRec k v s)
  | _, .empty, h => by simp only [Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .real, h => by simp only [Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .dual s, h => by
      simp only [Space.openRec, Space.fv] at h ⊢; exact Space.fv_subset_openRec h
  | _, .dsum s₀ s₁, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Space.fv_subset_openRec h)
      · exact Or.inr (Space.fv_subset_openRec h)
  | _, .tprod s₀ s₁, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Space.fv_subset_openRec h)
      · exact Or.inr (Space.fv_subset_openRec h)
  | _, .ker s₀ s₁ e, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.fv_subset_openRec h))
      · exact Or.inl (Or.inr (Space.fv_subset_openRec h))
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .coker s₀ s₁ e, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.fv_subset_openRec h))
      · exact Or.inl (Or.inr (Space.fv_subset_openRec h))
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .img s₀ s₁ e, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.fv_subset_openRec h))
      · exact Or.inl (Or.inr (Space.fv_subset_openRec h))
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .coimg s₀ s₁ e, h => by
      simp only [Space.openRec, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.fv_subset_openRec h))
      · exact Or.inl (Or.inr (Space.fv_subset_openRec h))
      · exact Or.inr (Term.fv_subset_openRec h)

theorem Ty.fv_subset_openRec {a : Name} {v : Term} :
    ∀ {k : Nat} {τ : Ty}, a ∈ Ty.fv τ → a ∈ Ty.fv (Ty.openRec k v τ)
  | _, .space s, h => by
      simp only [Ty.openRec, Ty.fv] at h ⊢; exact Space.fv_subset_openRec h
  | _, .piTy τ₀ τ₁, h => by
      simp only [Ty.openRec, Ty.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Ty.fv_subset_openRec h)
      · exact Or.inr (Ty.fv_subset_openRec h)

theorem Term.fv_subset_openRec {a : Name} {v : Term} :
    ∀ {k : Nat} {e : Term}, a ∈ Term.fv e → a ∈ Term.fv (Term.openRec k v e)
  | _, .bvar _, h => by simp only [Term.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .var y, h => by simp only [Term.openRec, Term.fv] at h ⊢; exact h
  | _, .real _, h => by simp only [Term.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .zero s, h => by
      simp only [Term.openRec, Term.fv] at h ⊢; exact Space.fv_subset_openRec h
  | _, .inner s, h => by
      simp only [Term.openRec, Term.fv] at h ⊢; exact Space.fv_subset_openRec h
  | _, .embed s, h => by
      simp only [Term.openRec, Term.fv] at h ⊢; exact Space.fv_subset_openRec h
  | _, .smul e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Term.fv_subset_openRec h)
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .add e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Term.fv_subset_openRec h)
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .dsumE e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Term.fv_subset_openRec h)
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .tprodE e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Term.fv_subset_openRec h)
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .pinvT s₀ s₁ e, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.fv_subset_openRec h))
      · exact Or.inl (Or.inr (Space.fv_subset_openRec h))
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .pinvD s e, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Space.fv_subset_openRec h)
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .llam s₀ s e, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.fv_subset_openRec h))
      · exact Or.inl (Or.inr (Space.fv_subset_openRec h))
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .nllam τ e, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Ty.fv_subset_openRec h)
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .appL s₀ s₁ e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl (Space.fv_subset_openRec h)))
      · exact Or.inl (Or.inl (Or.inr (Space.fv_subset_openRec h)))
      · exact Or.inl (Or.inr (Term.fv_subset_openRec h))
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .appI s e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.fv_subset_openRec h))
      · exact Or.inl (Or.inr (Term.fv_subset_openRec h))
      · exact Or.inr (Term.fv_subset_openRec h)
  | _, .appN e₀ e₁, h => by
      simp only [Term.openRec, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Term.fv_subset_openRec h)
      · exact Or.inr (Term.fv_subset_openRec h)
end

theorem Basis.fv_subset_openRec {a : Name} {v : Term} :
    ∀ {k : Nat} {b : Basis}, a ∈ Basis.fv b → a ∈ Basis.fv (Basis.openRec k v b)
  | _, .empty, h => by simp only [Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .one, h => by simp only [Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | _, .dual b, h => by
      simp only [Basis.openRec, Basis.fv] at h ⊢; exact Basis.fv_subset_openRec h
  | _, .dsum b₀ b₁, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Basis.fv_subset_openRec h)
      · exact Or.inr (Basis.fv_subset_openRec h)
  | _, .tprod b₀ b₁, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Basis.fv_subset_openRec h)
      · exact Or.inr (Basis.fv_subset_openRec h)
  | _, .proj s b₀ b₁, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.fv_subset_openRec h))
      · exact Or.inl (Or.inr (Basis.fv_subset_openRec h))
      · exact Or.inr (Basis.fv_subset_openRec h)
  | _, .image b, h => by
      simp only [Basis.openRec, Basis.fv] at h ⊢; exact Basis.fv_subset_openRec h
  | _, .terms s es b, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union, Term.openRecList_eq_map] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl (Space.fv_subset_openRec h))
      · exact Or.inl (Or.inr (Basis.fv_subset_openRec h))
      · refine Or.inr ?_
        rw [Term.mem_fvList] at h ⊢
        obtain ⟨e₀, he₀, ha⟩ := h
        exact ⟨Term.openRec _ v e₀, List.mem_map.mpr ⟨e₀, he₀, rfl⟩, Term.fv_subset_openRec ha⟩
  | _, .frame b₀ b₁, h => by
      simp only [Basis.openRec, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · exact Or.inl (Basis.fv_subset_openRec h)
      · exact Or.inr (Basis.fv_subset_openRec h)

/-! ### `fv (subst x u e) ⊆ fv e ∪ fv u`. -/

mutual
theorem Space.fv_subst_mem {a x : Name} {u : Term} :
    ∀ {s : Space}, a ∈ Space.fv (Space.subst x u s) → a ∈ Space.fv s ∪ Term.fv u
  | .empty, h => by simp only [Space.subst, Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .real, h => by simp only [Space.subst, Space.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .dual s, h => by
      simp only [Space.subst, Space.fv] at h ⊢; exact Space.fv_subst_mem h
  | .dsum s₀ s₁, h => by
      simp only [Space.subst, Space.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprod s₀ s₁, h => by
      simp only [Space.subst, Space.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .ker s₀ s₁ e, h => by
      simp only [Space.subst, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .coker s₀ s₁ e, h => by
      simp only [Space.subst, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .img s₀ s₁ e, h => by
      simp only [Space.subst, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .coimg s₀ s₁ e, h => by
      simp only [Space.subst, Space.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'

theorem Ty.fv_subst_mem {a x : Name} {u : Term} :
    ∀ {τ : Ty}, a ∈ Ty.fv (Ty.subst x u τ) → a ∈ Ty.fv τ ∪ Term.fv u
  | .space s, h => by
      simp only [Ty.subst, Ty.fv] at h ⊢; exact Space.fv_subst_mem h
  | .piTy τ₀ τ₁, h => by
      simp only [Ty.subst, Ty.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Ty.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

theorem Term.fv_subst_mem {a x : Name} {u : Term} :
    ∀ {e : Term}, a ∈ Term.fv (Term.subst x u e) → a ∈ Term.fv e ∪ Term.fv u
  | .bvar _, h => by simp only [Term.subst, Term.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .var y, h => by
      by_cases hxy : x = y
      · subst hxy; simp only [Term.subst, ↓reduceIte] at h; exact Finset.mem_union_right _ h
      · simp only [Term.subst, if_neg hxy, Term.fv, Finset.mem_singleton] at h
        subst h
        exact Finset.mem_union_left _ (Finset.mem_singleton_self _)
  | .real _, h => by simp only [Term.subst, Term.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .zero s, h => by
      simp only [Term.subst, Term.fv] at h ⊢; exact Space.fv_subst_mem h
  | .inner s, h => by
      simp only [Term.subst, Term.fv] at h ⊢; exact Space.fv_subst_mem h
  | .embed s, h => by
      simp only [Term.subst, Term.fv] at h ⊢; exact Space.fv_subst_mem h
  | .smul e₀ e₁, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .add e₀ e₁, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .dsumE e₀ e₁, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprodE e₀ e₁, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .pinvT s₀ s₁ e, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .pinvD s e, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .llam s₀ s e, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .nllam τ e, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h
      · rcases Finset.mem_union.mp (Ty.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl h')
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .appL s₀ s₁ e₀ e₁, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with ((h | h) | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inl h')))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inr h')))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .appI s e₀ e₁, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .appN e₀ e₁, h => by
      simp only [Term.subst, Term.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Term.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
end

theorem Basis.fv_subst_mem {a x : Name} {u : Term} :
    ∀ {b : Basis}, a ∈ Basis.fv (Basis.subst x u b) → a ∈ Basis.fv b ∪ Term.fv u
  | .empty, h => by simp only [Basis.subst, Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .one, h => by simp only [Basis.subst, Basis.fv] at h; exact absurd h (Finset.notMem_empty _)
  | .dual b, h => by
      simp only [Basis.subst, Basis.fv] at h ⊢; exact Basis.fv_subst_mem h
  | .dsum b₀ b₁, h => by
      simp only [Basis.subst, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Basis.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .tprod b₀ b₁, h => by
      simp only [Basis.subst, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Basis.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | .proj s b₀ b₁, h => by
      simp only [Basis.subst, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Basis.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Basis.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inr h')
        · exact Or.inr h'
  | .image b, h => by
      simp only [Basis.subst, Basis.fv] at h ⊢; exact Basis.fv_subst_mem h
  | .terms s es b, h => by
      simp only [Basis.subst, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with (h | h) | h
      · rcases Finset.mem_union.mp (Space.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inl h'))
        · exact Or.inr h'
      · rcases Finset.mem_union.mp (Basis.fv_subst_mem h) with h' | h'
        · exact Or.inl (Or.inl (Or.inr h'))
        · exact Or.inr h'
      · rw [Term.mem_fvList] at h
        obtain ⟨e', hmem, he'⟩ := h
        obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.mp hmem
        rcases Finset.mem_union.mp (Term.fv_subst_mem he') with h' | h'
        · exact Or.inl (Or.inr (Term.mem_fvList.mpr ⟨e₀, he₀, h'⟩))
        · exact Or.inr h'
  | .frame b₀ b₁, h => by
      simp only [Basis.subst, Basis.fv, Finset.mem_union] at h ⊢
      rcases h with h | h <;> rcases Finset.mem_union.mp (Basis.fv_subst_mem h) with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'

/-! ## Lemma kit (7): opening with a free VARIABLE preserves `size`.

`size (openRec k (.var y) ·) = size ·`. Opening replaces `bvar i` (size 1) by
`.var y` (size 1), so the structural size is unchanged. This is the termination
key for `denotTy`/`denotTerm`'s open-at-fresh-name binder arms: the recursive
argument `Ty.openVar x τ₁` / `Term.openVar x e` has the same size as the strict
subterm `τ₁` / `e`, hence strictly less than the binder node. -/

mutual
theorem Space.size_openVar (k : Nat) (y : Name) :
    ∀ (s : Space), Space.size (Space.openRec k (.var y) s) = Space.size s
  | .empty => rfl
  | .real => rfl
  | .dual s => by simp only [Space.openRec, Space.size, Space.size_openVar k y s]
  | .dsum s₀ s₁ => by
      simp only [Space.openRec, Space.size, Space.size_openVar k y s₀, Space.size_openVar k y s₁]
  | .tprod s₀ s₁ => by
      simp only [Space.openRec, Space.size, Space.size_openVar k y s₀, Space.size_openVar k y s₁]
  | .ker s₀ s₁ e => by
      simp only [Space.openRec, Space.size, Space.size_openVar k y s₀,
        Space.size_openVar k y s₁, Term.size_openVar k y e]
  | .coker s₀ s₁ e => by
      simp only [Space.openRec, Space.size, Space.size_openVar k y s₀,
        Space.size_openVar k y s₁, Term.size_openVar k y e]
  | .img s₀ s₁ e => by
      simp only [Space.openRec, Space.size, Space.size_openVar k y s₀,
        Space.size_openVar k y s₁, Term.size_openVar k y e]
  | .coimg s₀ s₁ e => by
      simp only [Space.openRec, Space.size, Space.size_openVar k y s₀,
        Space.size_openVar k y s₁, Term.size_openVar k y e]

theorem Ty.size_openVar (k : Nat) (y : Name) :
    ∀ (τ : Ty), Ty.size (Ty.openRec k (.var y) τ) = Ty.size τ
  | .space s => by simp only [Ty.openRec, Ty.size, Space.size_openVar k y s]
  | .piTy τ₀ τ₁ => by
      simp only [Ty.openRec, Ty.size, Ty.size_openVar k y τ₀, Ty.size_openVar (k+1) y τ₁]

theorem Term.size_openVar (k : Nat) (y : Name) :
    ∀ (e : Term), Term.size (Term.openRec k (.var y) e) = Term.size e
  | .bvar i => by
      by_cases hik : i = k
      · subst hik; simp only [Term.openRec, ↓reduceIte, Term.size]
      · simp only [Term.openRec, if_neg hik]
  | .var _ => rfl
  | .real _ => rfl
  | .zero s => by simp only [Term.openRec, Term.size, Space.size_openVar k y s]
  | .inner s => by simp only [Term.openRec, Term.size, Space.size_openVar k y s]
  | .embed s => by simp only [Term.openRec, Term.size, Space.size_openVar k y s]
  | .smul e₀ e₁ => by
      simp only [Term.openRec, Term.size, Term.size_openVar k y e₀, Term.size_openVar k y e₁]
  | .add e₀ e₁ => by
      simp only [Term.openRec, Term.size, Term.size_openVar k y e₀, Term.size_openVar k y e₁]
  | .dsumE e₀ e₁ => by
      simp only [Term.openRec, Term.size, Term.size_openVar k y e₀, Term.size_openVar k y e₁]
  | .tprodE e₀ e₁ => by
      simp only [Term.openRec, Term.size, Term.size_openVar k y e₀, Term.size_openVar k y e₁]
  | .pinvT s₀ s₁ e => by
      simp only [Term.openRec, Term.size, Space.size_openVar k y s₀, Space.size_openVar k y s₁,
        Term.size_openVar k y e]
  | .pinvD s e => by
      simp only [Term.openRec, Term.size, Space.size_openVar k y s, Term.size_openVar k y e]
  | .llam s₀ s e => by
      simp only [Term.openRec, Term.size, Space.size_openVar k y s₀, Space.size_openVar k y s,
        Term.size_openVar (k+1) y e]
  | .nllam τ e => by
      simp only [Term.openRec, Term.size, Ty.size_openVar k y τ, Term.size_openVar (k+1) y e]
  | .appL s₀ s₁ e₀ e₁ => by
      simp only [Term.openRec, Term.size, Space.size_openVar k y s₀, Space.size_openVar k y s₁,
        Term.size_openVar k y e₀, Term.size_openVar k y e₁]
  | .appI s e₀ e₁ => by
      simp only [Term.openRec, Term.size, Space.size_openVar k y s, Term.size_openVar k y e₀,
        Term.size_openVar k y e₁]
  | .appN e₀ e₁ => by
      simp only [Term.openRec, Term.size, Term.size_openVar k y e₀, Term.size_openVar k y e₁]
end

/-! ## Lemma kit (8): `fv (openVar x ·) \ {x} ⊆ fv ·`.

Opening at `x` adds at most the name `x` (plus the body's own free names);
erasing `x` recovers a subset of the body's free names. The agreement-on-FV
bridge for the cofinite binder arms (`σ.bind x v` agrees outside `{x}` iff the
underlying envs agree on the body's fv). -/

theorem Ty.fv_openVar_erase_subset (x : Name) (τ : Ty) :
    (Ty.fv (Ty.openVar x τ)).erase x ⊆ Ty.fv τ := by
  intro a ha
  rw [Finset.mem_erase] at ha
  have hmem := Ty.fv_openRec_subset 0 (.var x) τ ha.2
  rw [Finset.mem_union] at hmem
  rcases hmem with h | h
  · exact h
  · simp only [Term.fv, Finset.mem_singleton] at h; exact absurd h ha.1

theorem Term.fv_openVar_erase_subset (x : Name) (e : Term) :
    (Term.fv (Term.openVar x e)).erase x ⊆ Term.fv e := by
  intro a ha
  rw [Finset.mem_erase] at ha
  have hmem := Term.fv_openRec_subset 0 (.var x) e ha.2
  rw [Finset.mem_union] at hmem
  rcases hmem with h | h
  · exact h
  · simp only [Term.fv, Finset.mem_singleton] at h; exact absurd h ha.1

theorem Basis.fv_openVar_erase_subset (x : Name) (b : Basis) :
    (Basis.fv (Basis.openVar x b)).erase x ⊆ Basis.fv b := by
  intro a ha
  rw [Finset.mem_erase] at ha
  have hmem := Basis.fv_openRec_subset 0 (.var x) b ha.2
  rw [Finset.mem_union] at hmem
  rcases hmem with h | h
  · exact h
  · simp only [Term.fv, Finset.mem_singleton] at h; exact absurd h ha.1

theorem Space.fv_subst_subset (x : Name) (u : Term) (s : Space) :
    Space.fv (Space.subst x u s) ⊆ Space.fv s ∪ Term.fv u :=
  fun _ ha => Space.fv_subst_mem ha
theorem Ty.fv_subst_subset (x : Name) (u : Term) (τ : Ty) :
    Ty.fv (Ty.subst x u τ) ⊆ Ty.fv τ ∪ Term.fv u :=
  fun _ ha => Ty.fv_subst_mem ha
theorem Term.fv_subst_subset (x : Name) (u : Term) (e : Term) :
    Term.fv (Term.subst x u e) ⊆ Term.fv e ∪ Term.fv u :=
  fun _ ha => Term.fv_subst_mem ha
theorem Basis.fv_subst_subset (x : Name) (u : Term) (b : Basis) :
    Basis.fv (Basis.subst x u b) ⊆ Basis.fv b ∪ Term.fv u :=
  fun _ ha => Basis.fv_subst_mem ha

end GLang
