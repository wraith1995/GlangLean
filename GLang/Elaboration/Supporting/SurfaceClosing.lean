import GLang.Elaboration.BasisErasure

/-! Closing laws for reconstructing one binder body from a fresh opened instance. -/
namespace GLang.Surface

mutual
  def Space.closeRec (k : Nat) (x : Name) : Space → Space
    | .empty => .empty
    | .real => .real
    | .dual s => .dual (s.closeRec k x)
    | .dsum s t => .dsum (s.closeRec k x) (t.closeRec k x)
    | .tprod s t => .tprod (s.closeRec k x) (t.closeRec k x)
    | .ker e => .ker (Term.closeRec k x e)
    | .coker e => .coker (Term.closeRec k x e)
    | .img e => .img (Term.closeRec k x e)
    | .coimg e => .coimg (Term.closeRec k x e)
  def Ty.closeRec (k : Nat) (x : Name) : Ty → Ty
    | .space s => .space (s.closeRec k x)
    | .piTy a b => .piTy (Ty.closeRec k x a) (Ty.closeRec (k + 1) x b)
  def Term.closeRec (k : Nat) (x : Name) : Term → Term
    | .bvar i => .bvar i
    | .var y => if y = x then .bvar k else .var y
    | .real r => .real r
    | .zero s => .zero (s.closeRec k x)
    | .smul a b => .smul (Term.closeRec k x a) (Term.closeRec k x b)
    | .add a b => .add (Term.closeRec k x a) (Term.closeRec k x b)
    | .inner s => .inner (s.closeRec k x)
    | .app a b => .app (Term.closeRec k x a) (Term.closeRec k x b)
    | .llam s e => .llam (s.closeRec k x) (Term.closeRec (k + 1) x e)
    | .nllam a e => .nllam (Ty.closeRec k x a) (Term.closeRec (k + 1) x e)
    | .pinv e => .pinv (Term.closeRec k x e)
    | .dsumE a b => .dsumE (Term.closeRec k x a) (Term.closeRec k x b)
    | .tprodE a b => .tprodE (Term.closeRec k x a) (Term.closeRec k x b)
    | .embed s => .embed (s.closeRec k x)
end

def Basis.closeRec (k : Nat) (x : Name) : Basis → Basis
  | .empty => .empty
  | .one => .one
  | .dual b => .dual (b.closeRec k x)
  | .dsum a b => .dsum (a.closeRec k x) (b.closeRec k x)
  | .tprod a b => .tprod (a.closeRec k x) (b.closeRec k x)
  | .proj s a b => .proj (s.closeRec k x) (a.closeRec k x) (b.closeRec k x)
  | .image b => .image (b.closeRec k x)
  | .terms es b => .terms (es.map (Term.closeRec k x)) (b.closeRec k x)
  | .frame a b => .frame (a.closeRec k x) (b.closeRec (k+1) x)

def Basis.fv : Basis → Finset Name
  | .empty | .one => ∅
  | .dual b | .image b => b.fv
  | .dsum a b | .tprod a b | .frame a b => a.fv ∪ b.fv
  | .proj s a b => s.fv ∪ a.fv ∪ b.fv
  | .terms es b => b.fv ∪ (es.map Term.fv).foldr (· ∪ ·) ∅

mutual
  theorem Space.close_openVar (x : Name) :
      ∀ (a : Space), x ∉ a.fv → ∀ k,
        Space.closeRec k x (Space.openRec k (.var x) a) = a
    | .empty, hx, k => by
        rfl
    | .real, hx, k => by
        rfl
    | .dual s, hx, k => by
        simp only [Space.fv] at hx
        simp only [Space.openRec, Space.closeRec, Space.close_openVar x s hx k]
    | .dsum a b, hx, k => by
        simp only [Space.fv, Finset.mem_union, not_or] at hx
        simp only [Space.openRec, Space.closeRec, Space.close_openVar x a hx.1 k, Space.close_openVar x b hx.2 k]
    | .tprod a b, hx, k => by
        simp only [Space.fv, Finset.mem_union, not_or] at hx
        simp only [Space.openRec, Space.closeRec, Space.close_openVar x a hx.1 k, Space.close_openVar x b hx.2 k]
    | .ker e, hx, k => by
        simp only [Space.fv] at hx
        simp only [Space.openRec, Space.closeRec, Term.close_openVar x e hx k]
    | .coker e, hx, k => by
        simp only [Space.fv] at hx
        simp only [Space.openRec, Space.closeRec, Term.close_openVar x e hx k]
    | .img e, hx, k => by
        simp only [Space.fv] at hx
        simp only [Space.openRec, Space.closeRec, Term.close_openVar x e hx k]
    | .coimg e, hx, k => by
        simp only [Space.fv] at hx
        simp only [Space.openRec, Space.closeRec, Term.close_openVar x e hx k]
  theorem Ty.close_openVar (x : Name) :
      ∀ (a : Ty), x ∉ a.fv → ∀ k,
        Ty.closeRec k x (Ty.openRec k (.var x) a) = a
    | .space s, hx, k => by
        simp only [Ty.fv] at hx
        simp only [Ty.openRec, Ty.closeRec, Space.close_openVar x s hx k]
    | .piTy a b, hx, k => by
        simp only [Ty.fv, Finset.mem_union, not_or] at hx
        simp only [Ty.openRec, Ty.closeRec, Ty.close_openVar x a hx.1 k, Ty.close_openVar x b hx.2 (k+1)]
  theorem Term.close_openVar (x : Name) :
      ∀ (a : Term), x ∉ a.fv → ∀ k,
        Term.closeRec k x (Term.openRec k (.var x) a) = a
    | .bvar i, hx, k => by
        by_cases h : i = k <;> simp [Term.openRec, Term.closeRec, h]
    | .var y, hx, k => by
        simp only [Term.fv, Finset.mem_singleton] at hx
        simp [Term.openRec, Term.closeRec, Ne.symm hx]
    | .real r, hx, k => by
        rfl
    | .zero s, hx, k => by
        simp only [Term.fv] at hx
        simp only [Term.openRec, Term.closeRec, Space.close_openVar x s hx k]
    | .inner s, hx, k => by
        simp only [Term.fv] at hx
        simp only [Term.openRec, Term.closeRec, Space.close_openVar x s hx k]
    | .embed s, hx, k => by
        simp only [Term.fv] at hx
        simp only [Term.openRec, Term.closeRec, Space.close_openVar x s hx k]
    | .smul a b, hx, k => by
        simp only [Term.fv, Finset.mem_union, not_or] at hx
        simp only [Term.openRec, Term.closeRec, Term.close_openVar x a hx.1 k, Term.close_openVar x b hx.2 k]
    | .add a b, hx, k => by
        simp only [Term.fv, Finset.mem_union, not_or] at hx
        simp only [Term.openRec, Term.closeRec, Term.close_openVar x a hx.1 k, Term.close_openVar x b hx.2 k]
    | .app a b, hx, k => by
        simp only [Term.fv, Finset.mem_union, not_or] at hx
        simp only [Term.openRec, Term.closeRec, Term.close_openVar x a hx.1 k, Term.close_openVar x b hx.2 k]
    | .dsumE a b, hx, k => by
        simp only [Term.fv, Finset.mem_union, not_or] at hx
        simp only [Term.openRec, Term.closeRec, Term.close_openVar x a hx.1 k, Term.close_openVar x b hx.2 k]
    | .tprodE a b, hx, k => by
        simp only [Term.fv, Finset.mem_union, not_or] at hx
        simp only [Term.openRec, Term.closeRec, Term.close_openVar x a hx.1 k, Term.close_openVar x b hx.2 k]
    | .llam s e, hx, k => by
        simp only [Term.fv, Finset.mem_union, not_or] at hx
        simp only [Term.openRec, Term.closeRec, Space.close_openVar x s hx.1 k, Term.close_openVar x e hx.2 (k+1)]
    | .nllam t e, hx, k => by
        simp only [Term.fv, Finset.mem_union, not_or] at hx
        simp only [Term.openRec, Term.closeRec, Ty.close_openVar x t hx.1 k, Term.close_openVar x e hx.2 (k+1)]
    | .pinv e, hx, k => by
        simp only [Term.fv] at hx
        simp only [Term.openRec, Term.closeRec, Term.close_openVar x e hx k]
end

/-- Closing reverses a fresh opening, including frame binders and term lists. -/
theorem Basis.close_openVar (x : Name) (b : Basis) (hx : x ∉ b.fv) (k : Nat) :
    Basis.closeRec k x (Basis.openRec k (.var x) b) = b := by
  induction b generalizing k with
  | terms es b ih =>
    simp only [Basis.fv, Finset.mem_union, not_or] at hx
    have hlist : (es.map (Term.openRec k (.var x))).map (Term.closeRec k x) = es := by
      induction es with
      | nil => rfl
      | cons e es ihes =>
        simp only [List.map_cons, List.foldr_cons, Finset.mem_union, not_or] at hx
        simp only [List.map_cons, Term.close_openVar x e hx.2.1 k,
          ihes ⟨hx.1, hx.2.2⟩]
    simp only [Basis.openRec, Basis.closeRec, ih hx.1 k, hlist]
  | empty => rfl
  | one => rfl
  | dual b ihb =>
    simp only [Basis.fv] at hx
    simp only [Basis.openRec, Basis.closeRec, ihb hx k]
  | dsum a b iha ihb =>
    simp only [Basis.fv, Finset.mem_union, not_or] at hx
    simp only [Basis.openRec, Basis.closeRec, iha hx.1 k, ihb hx.2 k]
  | tprod a b iha ihb =>
    simp only [Basis.fv, Finset.mem_union, not_or] at hx
    simp only [Basis.openRec, Basis.closeRec, iha hx.1 k, ihb hx.2 k]
  | proj s a b iha ihb =>
    simp only [Basis.fv, Finset.mem_union, not_or] at hx
    simp only [Basis.openRec, Basis.closeRec, Space.close_openVar x s hx.1.1 k, iha hx.1.2 k, ihb hx.2 k]
  | image b ihb =>
    simp only [Basis.fv] at hx
    simp only [Basis.openRec, Basis.closeRec, ihb hx k]
  | frame a b iha ihb =>
    simp only [Basis.fv, Finset.mem_union, not_or] at hx
    simp only [Basis.openRec, Basis.closeRec, iha hx.1 k, ihb hx.2 (k+1)]

end GLang.Surface

namespace GLang

mutual
  theorem Space.erase_closeRec (a : Space) (k : Nat) (x : Name) :
      (Space.closeRec k x a).erase = a.erase.closeRec k x := by
    cases a <;> simp only [Space.closeRec, Space.erase, Surface.Space.closeRec,
      Space.erase_closeRec, Term.erase_closeRec]
  theorem Ty.erase_closeRec (a : Ty) (k : Nat) (x : Name) :
      (Ty.closeRec k x a).erase = a.erase.closeRec k x := by
    cases a <;> simp only [Ty.closeRec, Ty.erase, Surface.Ty.closeRec,
      Space.erase_closeRec, Ty.erase_closeRec]
  theorem Term.erase_closeRec (a : Term) (k : Nat) (x : Name) :
      (Term.closeRec k x a).erase = a.erase.closeRec k x := by
    cases a <;> simp only [Term.closeRec, Term.erase, Surface.Term.closeRec,
      Space.erase_closeRec, Ty.erase_closeRec, Term.erase_closeRec]
    split <;> rfl
end

theorem Basis.erase_closeRec (b : Basis) (k : Nat) (x : Name) :
    (b.closeRec k x).erase = b.erase.closeRec k x := by
  induction b generalizing k with
  | terms s es b ih =>
    simp [Basis.closeRec, Basis.erase, Surface.Basis.closeRec, Space.erase_closeRec,
      Term.closeRecList_eq_map, List.map_map, Term.erase_closeRec, ih]
  | _ => simp_all [Basis.closeRec, Basis.erase, Surface.Basis.closeRec, Space.erase_closeRec]

theorem Term.erase_close_of_open {e : Surface.Term} {a : Term} {x : Name}
    (hx : x ∉ e.fv) (ha : a.erase = e.openVar x) :
    (Term.closeRec 0 x a).erase = e := by
  rw [Term.erase_closeRec, ha]
  exact Surface.Term.close_openVar x e hx 0

/-- The same reconstruction law for dependent type bodies. -/
theorem Ty.erase_close_of_open {t : Surface.Ty} {a : Ty} {x : Name}
    (hx : x ∉ t.fv) (ha : a.erase = t.openVar x) :
    (Ty.closeRec 0 x a).erase = t := by
  rw [Ty.erase_closeRec, ha]
  exact Surface.Ty.close_openVar x t hx 0

/-- The same reconstruction law for basis/frame bodies. -/
theorem Basis.erase_close_of_open {b : Surface.Basis} {a : Basis} {x : Name}
    (hx : x ∉ b.fv) (ha : a.erase = b.openVar x) :
    (Basis.closeRec 0 x a).erase = b := by
  rw [Basis.erase_closeRec, ha]
  exact Surface.Basis.close_openVar x b hx 0

end GLang
