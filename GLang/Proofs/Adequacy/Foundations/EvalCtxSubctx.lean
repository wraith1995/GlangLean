import GLang.Operational.Ordinary

/-!
# Lookup-preserving operational evaluation-context extension

This module contains the small context-order API used by operational and
strengthened-semantics monotonicity.  It lives below those semantics and has
no dependency on adequacy, progress, or consistency.
-/

namespace GLang

/-- Lookup-preserving extension order on operational evaluation contexts. -/
def EvalCtx.Subctx (Psi Psi' : EvalCtx) : Prop :=
  forall key v,
    EvalCtx.lookup Psi key = some v -> EvalCtx.lookup Psi' key = some v

theorem EvalCtx.Subctx.refl (Psi : EvalCtx) : Psi.Subctx Psi := by
  intro key v hlookup
  exact hlookup

theorem EvalCtx.Subctx.trans {Psi0 Psi1 Psi2 : EvalCtx}
    (h01 : Psi0.Subctx Psi1) (h12 : Psi1.Subctx Psi2) :
    Psi0.Subctx Psi2 := by
  intro key v hlookup
  exact h12 key v (h01 key v hlookup)

theorem EvalCtx.Subctx.extend {Psi Psi' : EvalCtx}
    (h : Psi.Subctx Psi') (x : VName) (b : Basis) (v : ValExpr) :
    (Psi.extend x b v).Subctx (Psi'.extend x b v) := by
  intro key w hlookup
  classical
  by_cases hkey : key = (x, b)
  · subst key
    rw [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert] at hlookup ⊢
    exact hlookup
  · rw [EvalCtx.lookup, EvalCtx.extend,
      Finmap.lookup_insert_of_ne _ hkey] at hlookup ⊢
    exact h key w hlookup

/-- Names occurring as the first component of an operational-store key. -/
noncomputable def EvalCtx.names (Psi : EvalCtx) : Finset VName :=
  Psi.keys.image Prod.fst

/-- A successful pair-key lookup witnesses that its source name is already
represented in the operational store. -/
theorem EvalCtx.mem_names_of_lookup {Psi : EvalCtx} {x : VName} {b : Basis}
    {v : ValExpr} (h : EvalCtx.lookup Psi (x, b) = some v) : x ∈ Psi.names := by
  classical
  exact Finset.mem_image.mpr ⟨(x, b),
    Finmap.mem_keys.mpr (Finmap.mem_of_lookup_eq_some h), rfl⟩

/-- Installing a pair-key never removes represented source names, even when
the exact pair key is overwritten. -/
theorem EvalCtx.names_subset_extend (Psi : EvalCtx) (y : VName)
    (b : Basis) (v : ValExpr) :
    Psi.names ⊆ (Psi.extend y b v).names := by
  classical
  intro x hx
  obtain ⟨⟨x', b'⟩, hkey, rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨(x', b'), ?_, rfl⟩
  rw [Finmap.mem_keys] at hkey ⊢
  simp only [EvalCtx.extend, Finmap.mem_insert]
  exact Or.inr hkey

theorem EvalCtx.Subctx.extend_right_of_key_fresh {Psi : EvalCtx}
    {y : VName} {b : Basis} (hy : (y, b) ∉ Psi) (vnew : ValExpr) :
    Psi.Subctx (Psi.extend y b vnew) := by
  intro key v hlookup
  classical
  by_cases hkey : key = (y, b)
  · subst key
    exact absurd (Finmap.mem_of_lookup_eq_some hlookup) hy
  · rw [EvalCtx.lookup, EvalCtx.extend,
      Finmap.lookup_insert_of_ne _ hkey]
    exact hlookup

/-- The name-fresh form used for genuinely fresh binders.  It is a wrapper
around exact-key extension; representation-only history growth should use
`extend_right_of_key_fresh` directly. -/
theorem EvalCtx.Subctx.extend_right_of_name_fresh {Psi : EvalCtx}
    {y : VName} (hy : y ∉ Psi.names) (b : Basis) (vnew : ValExpr) :
    Psi.Subctx (Psi.extend y b vnew) := by
  apply EvalCtx.Subctx.extend_right_of_key_fresh (b := b) _ vnew
  intro hmem
  exact hy (Finset.mem_image.mpr
    ⟨(y, b), Finmap.mem_keys.mpr hmem, rfl⟩)

end GLang
