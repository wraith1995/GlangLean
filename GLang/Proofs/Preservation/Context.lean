import GLang.Operational.Context

/-! Context erasure, lookup typing, and formation properties. -/
namespace GLang.Operational

/-- Forgetting value typing recovers the operational context used by progress. -/
theorem TypedContext.erase (h : TypedContext Δ Γ Γv Ψ) : V2.CtxTele Δ Γ Ψ := by
  induction h with
  | empty => exact .empty
  | extend_nlin _ hf he hb _ _ ih => exact .extend_nlin ih hf he hb
  | extend_lin _ hf he hb hs _ _ ih => exact .extend_lin ih hf he hb hs
  | extend_rep _ hl hk he hb _ ih => exact .extend_rep ih hl hk he hb

/-- The value context declares exactly the names declared by the source contexts. -/
theorem TypedContext.mem_iff (h : TypedContext Δ Γ Γv Ψ) (y : VName) :
    y ∈ Γv ↔ y ∈ Δ ∨ y ∈ Γ := by
  induction h with
  | empty => exact iff_of_false Finmap.notMem_empty (not_or.mpr ⟨Finmap.notMem_empty, Finmap.notMem_empty⟩)
  | extend_nlin _ _ _ _ _ _ ih => simp only [Finmap.mem_insert, ih]; tauto
  | extend_lin _ _ _ _ _ _ _ ih => simp only [Finmap.mem_insert, ih]; tauto
  | extend_rep _ _ _ _ _ _ ih => exact ih

/-- Lookup supplies a value-typing derivation, not merely an inferred annotation. -/
theorem TypedContext.lookup_typed (h : TypedContext Δ Γ Γv Ψ)
    (hl : EvalCtx.lookup Ψ (y, b') = some v') :
    Nonempty (RuntimeValue.ValHasType Γv v' (ValExpr.inferType v')) := by
  induction h with
  | empty => simp [EvalCtx.lookup] at hl
  | @extend_nlin Δ Γ Γv Ψ x b v k hp hf he hb hk hv ih =>
      have hx : x ∉ Γv := fun h => (hp.mem_iff x).mp h |>.elim hf.freshLinear hf.freshNonlinear
      by_cases hkey : (y, b') = (x, b)
      · have heq : v = v' := by
          change Finmap.lookup (y, b') (Finmap.insert (x, b) v Ψ) = some v' at hl
          rw [hkey, Finmap.lookup_insert] at hl
          exact Option.some.inj hl
        subst v'
        exact hv
      · have hold : EvalCtx.lookup Ψ (y, b') = some v' := by
          simpa [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert_of_ne _ hkey] using hl
        obtain ⟨ht⟩ := ih hold
        exact ⟨ht.weaken hx⟩
  | @extend_lin Δ Γ Γv Ψ x b v s k hp hf he hb hs hk hv ih =>
      have hx : x ∉ Γv := fun h => (hp.mem_iff x).mp h |>.elim hf.freshLinear hf.freshNonlinear
      by_cases hkey : (y, b') = (x, b)
      · have heq : v = v' := by
          change Finmap.lookup (y, b') (Finmap.insert (x, b) v Ψ) = some v' at hl
          rw [hkey, Finmap.lookup_insert] at hl
          exact Option.some.inj hl
        subst v'
        exact hv
      · have hold : EvalCtx.lookup Ψ (y, b') = some v' := by
          simpa [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert_of_ne _ hkey] using hl
        obtain ⟨ht⟩ := ih hold
        exact ⟨ht.weaken hx⟩
  | @extend_rep Δ Γ Γv Ψ x b v hp hs hk he hb hv ih =>
      by_cases hkey : (y, b') = (x, b)
      · have heq : v = v' := by
          change Finmap.lookup (y, b') (Finmap.insert (x, b) v Ψ) = some v' at hl
          rw [hkey, Finmap.lookup_insert] at hl
          exact Option.some.inj hl
        subst v'
        exact hv
      · apply ih
        simpa [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert_of_ne _ hkey] using hl

/-- Every declared value type is well formed in the resulting value context. -/
theorem TypedContext.valueContextValid (h : TypedContext Δ Γ Γv Ψ) :
    Nonempty (RuntimeValue.ValCtxValid Γv) := by
  have insert_valid {Γv : ValCtx} {x : VName} {τ : ValTy} {k : ValKind}
      (hc : Nonempty (RuntimeValue.ValCtxValid Γv)) (hx : x ∉ Γv)
      (ht : Nonempty (RuntimeValue.ValTValid Γv τ k)) :
      Nonempty (RuntimeValue.ValCtxValid (Finmap.insert x τ Γv)) := by
    obtain ⟨hc⟩ := hc
    obtain ⟨ht⟩ := ht
    refine ⟨fun y u hu => ?_⟩
    by_cases hy : y = x
    · subst y
      have heq : τ = u := Option.some.inj (by simpa using hu)
      subst u
      exact ⟨k, ht.weaken hx⟩
    · have hold : Γv.lookup y = some u := by
        simpa [Finmap.lookup_insert_of_ne _ hy] using hu
      obtain ⟨ku, hv⟩ := hc y u hold
      exact ⟨ku, hv.weaken hx⟩
  induction h with
  | empty => exact ⟨fun _ _ h => by simp at h⟩
  | extend_nlin hp hf _ _ hk _ ih =>
      exact insert_valid ih
        (fun hm => ((hp.mem_iff _).mp hm).elim hf.freshLinear hf.freshNonlinear) hk
  | extend_lin hp hf _ _ _ hk _ ih =>
      exact insert_valid ih
        (fun hm => ((hp.mem_iff _).mp hm).elim hf.freshLinear hf.freshNonlinear) hk
  | extend_rep _ _ _ _ _ _ ih => exact ih

/-- Indexed context formation supplies exactly the premises threaded by preservation. -/
theorem TypedContext.evalContext (h : TypedContext Δ Γ Γv Ψ) :
    RuntimeValue.EvalContext Ψ Γv :=
  ⟨h.erase.evalCtxValidPlus, h.valueContextValid, fun _ _ _ hl => h.lookup_typed hl⟩

end GLang.Operational
