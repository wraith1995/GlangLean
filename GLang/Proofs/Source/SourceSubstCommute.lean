/- Substitution-commutation for the SOURCE language (the classic substitution
lemma), **re-built under locally-nameless (LN)**. -/
import GLang.Annotated.Binding
import GLang.Proofs.Source.FreeVars
import GLang.Proofs.Source.SourceLN
import GLang.Proofs.Basis.Binding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

namespace GLang

/-! ## Substitution commutation (LN).

`subst z u (subst x e ·) = subst x (subst z u e) (subst z u ·)` for `x ≠ z` and
`x ∉ fv u`. Mirrors `ValueSubstCommute.lean`. The only nontrivial arm is
`Term.var`; everything else (binders included) is uniform recursion. -/

mutual
theorem Space.subst_comm (z x : Name) (u e : Term)
    (hxz : x ≠ z) (hxu : x ∉ Term.fv u) :
    ∀ (s : Space),
      Space.subst z u (Space.subst x e s)
        = Space.subst x (Term.subst z u e) (Space.subst z u s)
  | .empty => rfl
  | .real => rfl
  | .dual s => by
      simp only [Space.subst, Space.subst_comm z x u e hxz hxu s]
  | .dsum s₀ s₁ => by
      simp only [Space.subst,
        Space.subst_comm z x u e hxz hxu s₀,
        Space.subst_comm z x u e hxz hxu s₁]
  | .tprod s₀ s₁ => by
      simp only [Space.subst,
        Space.subst_comm z x u e hxz hxu s₀,
        Space.subst_comm z x u e hxz hxu s₁]
  | .ker s₀ s₁ t => by
      simp only [Space.subst,
        Space.subst_comm z x u e hxz hxu s₀,
        Space.subst_comm z x u e hxz hxu s₁,
        Term.subst_comm z x u e hxz hxu t]
  | .coker s₀ s₁ t => by
      simp only [Space.subst,
        Space.subst_comm z x u e hxz hxu s₀,
        Space.subst_comm z x u e hxz hxu s₁,
        Term.subst_comm z x u e hxz hxu t]
  | .img s₀ s₁ t => by
      simp only [Space.subst,
        Space.subst_comm z x u e hxz hxu s₀,
        Space.subst_comm z x u e hxz hxu s₁,
        Term.subst_comm z x u e hxz hxu t]
  | .coimg s₀ s₁ t => by
      simp only [Space.subst,
        Space.subst_comm z x u e hxz hxu s₀,
        Space.subst_comm z x u e hxz hxu s₁,
        Term.subst_comm z x u e hxz hxu t]

theorem Ty.subst_comm (z x : Name) (u e : Term)
    (hxz : x ≠ z) (hxu : x ∉ Term.fv u) :
    ∀ (τ : Ty),
      Ty.subst z u (Ty.subst x e τ)
        = Ty.subst x (Term.subst z u e) (Ty.subst z u τ)
  | .space s => by
      simp only [Ty.subst, Space.subst_comm z x u e hxz hxu s]
  | .piTy τ₀ τ₁ => by
      -- LN: `piTy` is nameless — no binder name to split on; uniform recursion.
      simp only [Ty.subst,
        Ty.subst_comm z x u e hxz hxu τ₀,
        Ty.subst_comm z x u e hxz hxu τ₁]

theorem Term.subst_comm (z x : Name) (u e : Term)
    (hxz : x ≠ z) (hxu : x ∉ Term.fv u) :
    ∀ (M : Term),
      Term.subst z u (Term.subst x e M)
        = Term.subst x (Term.subst z u e) (Term.subst z u M)
  | .bvar _ => rfl
  | .var y => by
      by_cases hxy : x = y
      · subst hxy
        -- inner `subst x e (.var x)` = `e`; outer `subst z u e`.
        -- RHS: `subst z u (.var x)` = `.var x` (z ≠ x), then `subst x · (.var x)` = `subst z u e`.
        have hzx : z ≠ x := fun h => hxz h.symm
        simp only [Term.subst, if_true, if_neg hzx]
      · by_cases hzy : z = y
        · -- `z = y`, `x ≠ y`. Inner keeps the var; outer `subst z u` returns `u`;
          -- the outer `subst x _ u` is a no-op by `hxu`.
          subst hzy
          simp only [Term.subst, if_neg hxy, if_true,
            Term.subst_fresh x (Term.subst z u e) u hxu]
        · simp only [Term.subst, if_neg hxy, if_neg hzy]
  | .real _ => rfl
  | .zero s => by
      simp only [Term.subst, Space.subst_comm z x u e hxz hxu s]
  | .inner s => by
      simp only [Term.subst, Space.subst_comm z x u e hxz hxu s]
  | .embed s => by
      simp only [Term.subst, Space.subst_comm z x u e hxz hxu s]
  | .add e₀ e₁ => by
      simp only [Term.subst,
        Term.subst_comm z x u e hxz hxu e₀,
        Term.subst_comm z x u e hxz hxu e₁]
  | .smul e₀ e₁ => by
      simp only [Term.subst,
        Term.subst_comm z x u e hxz hxu e₀,
        Term.subst_comm z x u e hxz hxu e₁]
  | .dsumE e₀ e₁ => by
      simp only [Term.subst,
        Term.subst_comm z x u e hxz hxu e₀,
        Term.subst_comm z x u e hxz hxu e₁]
  | .tprodE e₀ e₁ => by
      simp only [Term.subst,
        Term.subst_comm z x u e hxz hxu e₀,
        Term.subst_comm z x u e hxz hxu e₁]
  | .appN e₀ e₁ => by
      simp only [Term.subst,
        Term.subst_comm z x u e hxz hxu e₀,
        Term.subst_comm z x u e hxz hxu e₁]
  | .pinvD s e' => by
      simp only [Term.subst,
        Space.subst_comm z x u e hxz hxu s,
        Term.subst_comm z x u e hxz hxu e']
  | .pinvT s₀ s₁ e' => by
      simp only [Term.subst,
        Space.subst_comm z x u e hxz hxu s₀,
        Space.subst_comm z x u e hxz hxu s₁,
        Term.subst_comm z x u e hxz hxu e']
  | .appI s e₀ e₁ => by
      simp only [Term.subst,
        Space.subst_comm z x u e hxz hxu s,
        Term.subst_comm z x u e hxz hxu e₀,
        Term.subst_comm z x u e hxz hxu e₁]
  | .appL s₀ s₁ e₀ e₁ => by
      simp only [Term.subst,
        Space.subst_comm z x u e hxz hxu s₀,
        Space.subst_comm z x u e hxz hxu s₁,
        Term.subst_comm z x u e hxz hxu e₀,
        Term.subst_comm z x u e hxz hxu e₁]
  | .nllam τ M => by
      -- LN: `nllam` is nameless — uniform recursion (domain `τ`, body `M`).
      simp only [Term.subst,
        Ty.subst_comm z x u e hxz hxu τ,
        Term.subst_comm z x u e hxz hxu M]
  | .llam s₀ s M => by
      -- LN: `llam` is nameless — uniform recursion (spaces `s₀`/`s`, body `M`).
      simp only [Term.subst,
        Space.subst_comm z x u e hxz hxu s₀,
        Space.subst_comm z x u e hxz hxu s,
        Term.subst_comm z x u e hxz hxu M]
end

/-- **Source basis substitution commutes** (mirror of `Ty.subst_comm`): for
    `x ≠ z` and `x ∉ fv u`,
    `subst z u (subst x e b) = subst x (subst z u e) (subst z u b)`. The only
    binder `frame` is nameless (handled by uniform recursion); the `terms` arm
    threads the list elementwise. -/
theorem Basis.subst_comm (z x : Name) (u e : Term)
    (hxz : x ≠ z) (hxu : x ∉ Term.fv u) :
    ∀ (b : Basis),
      Basis.subst z u (Basis.subst x e b)
        = Basis.subst x (Term.subst z u e) (Basis.subst z u b)
  | .empty => rfl
  | .one => rfl
  | .dual b => by
      simp only [Basis.subst, Basis.subst_comm z x u e hxz hxu b]
  | .dsum b₀ b₁ => by
      simp only [Basis.subst, Basis.subst_comm z x u e hxz hxu b₀,
        Basis.subst_comm z x u e hxz hxu b₁]
  | .tprod b₀ b₁ => by
      simp only [Basis.subst, Basis.subst_comm z x u e hxz hxu b₀,
        Basis.subst_comm z x u e hxz hxu b₁]
  | .proj s b₀ b₁ => by
      simp only [Basis.subst, Space.subst_comm z x u e hxz hxu s,
        Basis.subst_comm z x u e hxz hxu b₀,
        Basis.subst_comm z x u e hxz hxu b₁]
  | .image b => by
      simp only [Basis.subst, Basis.subst_comm z x u e hxz hxu b]
  | .terms s es b => by
      simp only [Basis.subst, Space.subst_comm z x u e hxz hxu s,
        Basis.subst_comm z x u e hxz hxu b, List.map_map]
      congr 1
      apply List.map_congr_left
      intro t _ht
      exact Term.subst_comm z x u e hxz hxu t
  | .frame b₀ b₁ => by
      -- LN: `frame` is nameless — uniform recursion.
      simp only [Basis.subst, Basis.subst_comm z x u e hxz hxu b₀,
        Basis.subst_comm z x u e hxz hxu b₁]

end GLang
