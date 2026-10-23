import GLang.Proofs.Value.Partial.PartialValuePrimitiveLocality
import GLang.Proofs.Value.Presentation.PaperValuePrimitiveSized

/-! Successful partial numerical evaluation allocates exactly its successfully
interpreted result dimension. Failure is retained, including dimension failure. -/
namespace GLang.PartialValueDomains
open PaperValueDomains

def PartialSizedResult (D : Except DimError Nat) : Except DimError ValValSem → Prop
  | .error _ => True
  | .ok (.array a) => D = .ok a.length
  | .ok (.fn _ _) => False

private theorem sized_arrayOf (D : Except DimError Nat) (n : Nat) (f : Nat → ℝ)
    (hn : D = .ok n) : PartialSizedResult D (.ok (.arrayOf n f)) := by
  simpa [PartialSizedResult, ValValSem.arrayOf, FlatArray.ofFn] using hn

private theorem sized_bindArray (D : Except DimError Nat) (r : Except DimError ValValSem)
    (k : FlatArray → Except DimError ValValSem)
    (h : ∀ a, PartialSizedResult D (k a)) :
    PartialSizedResult D (ValValSem.bindArray r k) := by
  cases r with
  | error e => trivial
  | ok v => cases v <;> simp_all [ValValSem.bindArray, PartialSizedResult]

private theorem sized_bindArrays (D : Except DimError Nat) (r r' : Except DimError ValValSem)
    (k : FlatArray → FlatArray → Except DimError ValValSem)
    (h : ∀ a b, PartialSizedResult D (k a b)) :
    PartialSizedResult D (ValValSem.bindArrays r r' k) :=
  sized_bindArray _ _ _ fun a => sized_bindArray _ _ _ (h a)

private theorem sized_bindArrays3 (D : Except DimError Nat) (r r' r'' : Except DimError ValValSem)
    (k : FlatArray → FlatArray → FlatArray → Except DimError ValValSem)
    (h : ∀ a b c, PartialSizedResult D (k a b c)) :
    PartialSizedResult D (ValValSem.bindArrays3 r r' r'' k) :=
  sized_bindArray _ _ _ fun a => sized_bindArray _ _ _ fun b =>
    sized_bindArray _ _ _ (h a b)

private theorem guard_sized (q : PartialFFSOracle) (ss : List ValSpace) (s : ValSpace)
    (f : FFSOracle → Except DimError ValValSem)
    (hout : (∀ t ∈ ss, ∃ n, t.dofPartial q = .ok n) → ∃ n, s.dofPartial q = .ok n)
    (hf : PartialSizedResult (.ok (s.dof (PartialValueEval.numbers q)))
      (f (PartialValueEval.numbers q))) :
    PartialSizedResult (s.dofPartial q) (PartialValueEval.withDimensions q ss f) := by
  cases hg : PartialValueEval.dimensions q ss with
  | error e => simp [PartialValueEval.withDimensions, hg, PartialSizedResult]
  | ok u =>
    cases u
    obtain ⟨n,hn⟩ := hout ((PartialValueEval.dimensions_ok_iff q ss).mp hg)
    have hd := PartialValueEval.dof_numbers q s n hn
    simpa only [PartialValueEval.withDimensions,hg,hn,hd] using hf

set_option maxHeartbeats 1600000 in
theorem partial_arrayPrimitive_sized (orc : PartialFFSOracleSem) (w : World) (e : ValExpr)
    (hp : ArrayPrimitive e) :
    PartialSizedResult ((ValExpr.inferSpaceCtx w.types e).dofPartial
      (orc w.env w.types w.values))
      (denotValB_partial orc w.env w.types w.values e) := by
  cases e <;> simp only [ArrayPrimitive] at hp
  all_goals try contradiction
  all_goals rw [denotValB_partial]; apply guard_sized
  case dsumE.hout a b =>
    intro h
    obtain ⟨m, hm⟩ := h _ (List.mem_cons_self ..)
    obtain ⟨n, hn⟩ := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    refine ⟨m+n, ?_⟩
    simp only [ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial,
      hm, hn, bind, pure, Except.bind, Except.pure, List.foldr, Nat.mul_one]
  case tprodE.hout a b =>
    intro h
    obtain ⟨m, hm⟩ := h _ (List.mem_cons_self ..)
    obtain ⟨n, hn⟩ := h _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    refine ⟨m*n, ?_⟩
    simp only [ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial,
      hm, hn, bind, pure, Except.bind, Except.pure, List.foldr, Nat.mul_one]
  case idelta.hout s =>
    intro h
    obtain ⟨n, hn⟩ := h _ (List.mem_cons_self ..)
    refine ⟨n*n, ?_⟩
    simp only [ValExpr.inferSpaceCtx, ValSpace.dofPartial, ValSpace.shpOfPartial,
      hn, bind, pure, Except.bind, Except.pure, List.foldr, Nat.mul_one]
  all_goals try { intro h; apply h; simp [ValExpr.inferSpaceCtx] }
  all_goals first
    | apply sized_bindArrays3; intro a b c
    | apply sized_bindArrays; intro a b
    | apply sized_bindArray; intro a
    | skip
  all_goals repeat' first
    | exact sized_arrayOf _ _ _ rfl
    | exact True.intro
    | split
    | dsimp only
  all_goals simp_all [PartialSizedResult, ValueCanonicalFSV.ResultMatrix.flatten,
    ValExpr.inferSpaceCtx]

/-- Equal numerical results, with their actual partial dimensions, are related
at the base result type. No successful dimension is assumed by the caller. -/
theorem partial_arrayPrimitive_related_of_eval_eq (orc : PartialFFSOracleSem)
    (w w' : World) (e : ValExpr) (s : ValSpace) (hp : ArrayPrimitive e)
    (hs : (ValExpr.inferSpaceCtx w.types e).dofPartial (orc w.env w.types w.values) =
      s.dofPartial (orc w.env w.types w.values))
    (hs' : (ValExpr.inferSpaceCtx w'.types e).dofPartial (orc w'.env w'.types w'.values) =
      s.dofPartial (orc w'.env w'.types w'.values))
    (heq : denotValB_partial orc w.env w.types w.values e =
      denotValB_partial orc w'.env w'.types w'.values e) :
    PartialRel (PartialRuntimeRelated (.space s)
      (denotValTyPartial orc w.env w.types w.values (.space s))
      (denotValTyPartial orc w'.env w'.types w'.values (.space s)))
      (denotValB_partial orc w.env w.types w.values e)
      (denotValB_partial orc w'.env w'.types w'.values e) := by
  have h := partial_arrayPrimitive_sized orc w e hp
  have h' := partial_arrayPrimitive_sized orc w' e hp
  rw [hs] at h
  rw [hs'] at h'
  rw [← heq] at h' ⊢
  cases he : denotValB_partial orc w.env w.types w.values e <;>
    simp only [he, PartialSizedResult] at h h' ⊢
  case error err => rfl
  case ok v =>
    cases v with
    | fn A f => exact False.elim h
    | array a =>
      simp only [PartialRel, PartialRuntimeRelated, denotValTyPartial, h, h', PartialRelated]
      simp [PartialValType.space]

end GLang.PartialValueDomains
