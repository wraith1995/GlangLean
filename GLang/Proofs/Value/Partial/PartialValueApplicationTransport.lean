import GLang.Proofs.Value.Partial.PartialValueReshape
import GLang.Proofs.Value.Partial.PartialValueApplicationRuntime

/-! Runtime application between independently realized value types. Conversion
uses the actual argument type and the function's actual dependent codomain;
checking only the requested result type cannot justify higher-order transport. -/
namespace GLang.PartialValueDomains
open PaperValueDomains

/-- Independent argument/output annotations are sound when runtime application
transports both the argument and the actual dependent result. In particular,
this preserves the recursive function relation, not just array lengths. -/
theorem partial_applyBetween_family (orc : PartialFFSOracleSem)
    (domain codomain argumentType output : ValTy) {I : Type 1} (w : I → World)
    (hfType : ∀ i j, PartialRawTypeCoherent orc (.piTy domain codomain) (w i) (w j))
    (haType : ∀ i j, PartialRawTypeCoherent orc argumentType (w i) (w j))
    (hoType : ∀ i j, PartialRawTypeCoherent orc output (w i) (w j))
    (i j : I) (f g v v' : ValValSem)
    (hf : WorldRuntimeRelated orc (.piTy domain codomain) (w i) (w j) f g)
    (ha : WorldRuntimeRelated orc argumentType (w i) (w j) v v') :
    PartialRel (WorldRuntimeRelated orc output (w i) (w j))
      (PartialValueEval.applyBetween orc (w i).env (w i).types (w i).values domain codomain argumentType output (.ok f) (.ok v))
      (PartialValueEval.applyBetween orc (w j).env (w j).types (w j).values domain codomain argumentType output (.ok g) (.ok v')) := by
  have harg := partial_reshape_family domain argumentType orc w w haType
    (fun i j => (hfType i j).1) i j i j rfl rfl v v' ha
  simp only [PartialValueEval.applyBetween]
  cases hl : PartialValueEval.reshapeBetween orc (w i).env (w i).types (w i).values
      (w i).types (w i).values v domain argumentType <;>
    cases hr : PartialValueEval.reshapeBetween orc (w j).env (w j).types (w j).values
      (w j).types (w j).values v' domain argumentType <;>
    simp only [hl,hr,PartialRel] at harg ⊢
  rename_i a b
  obtain ⟨x,y,hx,hy,hxy⟩ := partial_extract_related domain _ _ a b harg
  rw [hx,hy]
  have happ := partial_apply_runtime_related orc domain codomain (w i) (w j) f g hf x y hxy
  cases hfl : f.applyTyped x <;> cases hgr : g.applyTyped y <;>
    simp only [hfl,hgr,PartialRel] at happ ⊢
  rename_i r s
  have hxx := (partialFamily_laws domain (fun k => PartialWorldType orc (w k) domain)
    (fun k l => (hfType k l).1.toCoherent _ _ _ _)).trans i j i x y x hxy
      (partialRelated_symm domain _ _ _ _ hxy)
  let ax := domain.carrierToVal x
  let ay := domain.carrierToVal y
  let p : PartialRawArgumentClass orc domain w i ax :=
    ⟨⟨i,ax⟩, partial_reify_related domain _ _ x x hxx⟩
  let q : PartialRawArgumentClass orc domain w i ax :=
    ⟨⟨j,ay⟩, partial_reify_related domain _ _ x y hxy⟩
  let sw := partialRawArgumentWorld orc domain w i ax
  simpa only [PartialRel, sw, p, q, ax, ay, partialRawArgumentWorld] using
    (partial_reshape_family output codomain orc sw w
      (partialRawArgument_coherent orc domain codomain w hfType i ax)
      hoType p q i j rfl rfl r s happ)

end GLang.PartialValueDomains
