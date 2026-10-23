import GLang.Proofs.Value.Runtime.RuntimeValueRegular
import GLang.Proofs.Preservation.ValuePreservationV2

namespace GLang.RuntimeValue

mutual
noncomputable def ValSValid.erase : ValSValid Γv s → ValSValidC s
  | .real => .real
  | .empty => .empty
  | .dsum h0 h1 => .dsum h0.erase h1.erase
  | .tprod h0 h1 => .tprod h0.erase h1.erase
  | .ffs h0 h1 he => .ffs h0.erase h1.erase he.inferType_eq_of_typed

noncomputable def ValTValid.erase : ValTValid Γv t k → ValTValidC t k
  | .space hs => .space hs.erase
  | .piTy L hd hc => .piTy L hd.erase (fun x hx => (hc x hx).erase)
end

theorem ValTValid.kind_eq_structural (h : ValTValid Γv t k) : k = t.structuralKind :=
  h.erase.kind_eq_structural

noncomputable def ValCtxValid.insert {Γv : ValCtx} {x : VName} {τ : ValTy} {k : ValKind}
    (hc : ValCtxValid Γv) (hx : x ∉ Γv) (ht : ValTValid Γv τ k) :
    ValCtxValid (Finmap.insert x τ Γv) := by
  intro y u hu
  by_cases hy : y = x
  · subst y
    have heq : τ = u := Option.some.inj (by simpa using hu)
    subst u
    exact ⟨k, ht.weaken hx⟩
  · have hold : Γv.lookup y = some u := by
      simpa [Finmap.lookup_insert_of_ne _ hy] using hu
    obtain ⟨ku, hv⟩ := hc y u hold
    exact ⟨ku, hv.weaken hx⟩

/-- The threadable premises for indexed preservation. -/
structure EvalContext (Ψ : EvalCtx) (Γv : ValCtx) : Prop where
  regular : V2.EvalCtxValidPlus Ψ
  valid : Nonempty (ValCtxValid Γv)
  typed : ∀ x b v, EvalCtx.lookup Ψ (x,b) = some v →
    Nonempty (ValHasType Γv v (ValExpr.inferType v))

/-- A nonlinear source binder introduces the same annotated value variable. -/
theorem EvalContext.extend_var {Ψ : EvalCtx} {Γv : ValCtx} {x : VName} {b : Basis} {τ : ValTy}
    (hc : EvalContext Ψ Γv) (hx : x ∉ Γv) (hkey : (x,b) ∉ Ψ)
    (he : ValTy.EvalT Ψ (Basis.tof b) τ) (ht : ValTValid Γv τ k) :
    EvalContext (Ψ.extend x b (.var x τ)) (Finmap.insert x τ Γv) := by
  refine ⟨V2.evalCtxValidPlus_extend hc.regular hkey (V2.evalT_fv he hc.regular) he,
    ⟨hc.valid.some.insert hx ht⟩, ?_⟩
  intro y b' v hl
  by_cases hp : (y,b') = (x,b)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
    have hv : v = .var y τ := by
      simpa [EvalCtx.lookup,EvalCtx.extend] using hl.symm
    subst v
    exact ⟨.var (by simp)⟩
  · have hold : EvalCtx.lookup Ψ (y,b') = some v := by
      simpa [EvalCtx.lookup,EvalCtx.extend,Finmap.lookup_insert_of_ne _ hp] using hl
    exact ⟨(hc.typed y b' v hold).some.weaken hx⟩

/-- A linear column substitutes a basis vector, so it introduces no value variable. -/
theorem EvalContext.extend_delta {Ψ : EvalCtx} {Γv : ValCtx} {x : VName} {b : Basis}
    {s : ValSpace} (hc : EvalContext Ψ Γv) (hkey : (x,b) ∉ Ψ)
    (he : ValTy.EvalT Ψ (Basis.tof b) (.space s)) (hs : ValSValid Γv s) (i : Nat) :
    EvalContext (Ψ.extend x b (.delta i s)) Γv := by
  have hf := V2.evalT_fv he hc.regular
  have hl := evalT_lc he hc.regular.toEvalCtxLc
  refine ⟨V2.evalCtxValidPlus_extend_delta hc.regular hkey hf (by cases hl; assumption) he,
    hc.valid, ?_⟩
  intro y b' v hv
  by_cases hp : (y,b') = (x,b)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hp
    have hv' : v = .delta i s := by simpa [EvalCtx.lookup,EvalCtx.extend] using hv.symm
    subst v
    exact ⟨.delta hs⟩
  · exact hc.typed y b' v (by
      simpa [EvalCtx.lookup,EvalCtx.extend,Finmap.lookup_insert_of_ne _ hp] using hv)

abbrev ExprTyped (Γv : ValCtx) (v : ValExpr) : Prop :=
  Nonempty (ValHasType Γv v (ValExpr.inferType v))

theorem ExprTyped.of_type (h : ValHasType Γv v t) : ExprTyped Γv v := by
  change Nonempty (ValHasType Γv v (ValExpr.inferType v))
  rw [h.inferType_eq_of_typed]
  exact ⟨h⟩

noncomputable def ExprTyped.at (h : ExprTyped Γv v) (ht : ValExpr.inferType v = t) :
    ValHasType Γv v t := ht ▸ h.some

noncomputable def ExprTyped.reshap (h : ExprTyped Γv v)
    (hs : ValTValid Γv source k) (ht : ValTValid Γv target k) :
    ValHasType Γv (.reshap v target source) target := .reshap h.some hs ht

noncomputable def ExprTyped.base (h : ExprTyped Γv v) (hs : ValSValid Γv s) :
    ValHasType Γv (.reshapBase v s) (.space s) := h.reshap (.space hs) (.space hs)

end GLang.RuntimeValue
