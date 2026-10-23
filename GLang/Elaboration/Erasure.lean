import GLang.Proofs.Source.SourceLN
import GLang.Surface.Binding

/-! Erasure of implementation annotations and its binding laws. -/
namespace GLang

mutual
  def Space.erase : Space → Surface.Space
    | .empty => .empty
    | .real => .real
    | .dual s => .dual s.erase
    | .dsum s t => .dsum s.erase t.erase
    | .tprod s t => .tprod s.erase t.erase
    | .ker _ _ e => .ker e.erase
    | .coker _ _ e => .coker e.erase
    | .img _ _ e => .img e.erase
    | .coimg _ _ e => .coimg e.erase
  def Ty.erase : Ty → Surface.Ty
    | .space s => .space s.erase
    | .piTy a b => .piTy a.erase b.erase
  def Term.erase : Term → Surface.Term
    | .bvar i => .bvar i
    | .var x => .var x
    | .real r => .real r
    | .zero s => .zero s.erase
    | .smul a b => .smul a.erase b.erase
    | .add a b => .add a.erase b.erase
    | .inner s => .inner s.erase
    | .appL _ _ a b => .app a.erase b.erase
    | .appI _ a b => .app a.erase b.erase
    | .appN a b => .app a.erase b.erase
    | .llam s _ e => .llam s.erase e.erase
    | .nllam a e => .nllam a.erase e.erase
    | .pinvT _ _ e => .pinv e.erase
    | .pinvD _ e => .pinv e.erase
    | .dsumE a b => .dsumE a.erase b.erase
    | .tprodE a b => .tprodE a.erase b.erase
    | .embed s => .embed s.erase
end

mutual
  theorem Space.erase_openRec (s : Space) (k : Nat) (u : Term) :
      (Space.openRec k u s).erase = Surface.Space.openRec k u.erase s.erase := by
    cases s <;> simp only [Space.openRec, Space.erase, Surface.Space.openRec,
      Space.erase_openRec, Term.erase_openRec]
  theorem Ty.erase_openRec (a : Ty) (k : Nat) (u : Term) :
      (Ty.openRec k u a).erase = Surface.Ty.openRec k u.erase a.erase := by
    cases a <;> simp only [Ty.openRec, Ty.erase, Surface.Ty.openRec,
      Space.erase_openRec, Ty.erase_openRec]
  theorem Term.erase_openRec (e : Term) (k : Nat) (u : Term) :
      (Term.openRec k u e).erase = Surface.Term.openRec k u.erase e.erase := by
    cases e <;> simp only [Term.openRec, Term.erase, Surface.Term.openRec,
      Space.erase_openRec, Ty.erase_openRec, Term.erase_openRec]
    split <;> rfl
end

mutual
  theorem Space.erase_subst (s : Space) (x : Name) (u : Term) :
      (Space.subst x u s).erase = Surface.Space.subst x u.erase s.erase := by
    cases s <;> simp only [Space.subst, Space.erase, Surface.Space.subst,
      Space.erase_subst, Term.erase_subst]
  theorem Ty.erase_subst (a : Ty) (x : Name) (u : Term) :
      (Ty.subst x u a).erase = Surface.Ty.subst x u.erase a.erase := by
    cases a <;> simp only [Ty.subst, Ty.erase, Surface.Ty.subst,
      Space.erase_subst, Ty.erase_subst]
  theorem Term.erase_subst (e : Term) (x : Name) (u : Term) :
      (Term.subst x u e).erase = Surface.Term.subst x u.erase e.erase := by
    cases e <;> simp only [Term.subst, Term.erase, Surface.Term.subst,
      Space.erase_subst, Ty.erase_subst, Term.erase_subst]
    split <;> rfl
end

/-- Equality of erased terms is preserved by opening with the same name. -/
theorem Term.erase_openVar_congr {e e' : Term} (he : e.erase = e'.erase) (x : Name) :
    (Term.openVar x e).erase = (Term.openVar x e').erase := by
  simp only [Term.openVar, Term.erase_openRec, Term.erase, he]

/-- Equality of erased types is preserved by opening with the same name. -/
theorem Ty.erase_openVar_congr {τ τ' : Ty} (he : τ.erase = τ'.erase) (x : Name) :
    (Ty.openVar x τ).erase = (Ty.openVar x τ').erase := by
  simp only [Ty.openVar, Ty.erase_openRec, Term.erase, he]

/-- Opening at a name fresh for both terms reflects equality of the bodies. -/
theorem Term.eq_of_openVar_eq {e e' : Term} (x : Name)
    (hx : x ∉ Term.fv e) (hx' : x ∉ Term.fv e')
    (he : Term.openVar x e = Term.openVar x e') : e = e' := by
  have h := congrArg (Term.closeRec 0 x) he
  simpa only [Term.openVar, Term.close_openVar x e hx,
    Term.close_openVar x e' hx'] using h

/-- Opening at a name fresh for both types reflects equality of the bodies. -/
theorem Ty.eq_of_openVar_eq {τ τ' : Ty} (x : Name)
    (hx : x ∉ Ty.fv τ) (hx' : x ∉ Ty.fv τ')
    (he : Ty.openVar x τ = Ty.openVar x τ') : τ = τ' := by
  have h := congrArg (Ty.closeRec 0 x) he
  simpa only [Ty.openVar, Ty.close_openVar x τ hx,
    Ty.close_openVar x τ' hx'] using h

end GLang
