import GLang.Proofs.Value.Queries.ValueQueryOpening
import GLang.Proofs.Value.Runtime.RuntimeValueFormation
import GLang.Proofs.Value.Runtime.RuntimeValueResultAnnotations

set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace GLang.RuntimeValue
open ValueDependency ValueQueryDependencies

private abbrev SpaceFinite (s : ValSpace) := ValueQueryDependencies.Finite (.space [] s)
private abbrev TypeFinite (t : ValTy) := ValueQueryDependencies.Finite (.type [] t)
private abbrev ExprFinite (e : ValExpr) := ValueQueryDependencies.Finite (.expr [] e)

/-- Only matching variable annotations are dependency obligations. -/
def MatchedAnnotationsFinite (ε : ValCtx) (xs : List (VName × ValTy)) : Prop :=
  ∀ x t, (x,t) ∈ xs → ε.lookup x = some t → TypeFinite t

theorem MatchedAnnotationsFinite.mono {ε : ValCtx} {xs ys : List (VName × ValTy)}
    (h : MatchedAnnotationsFinite ε ys) (hs : xs ⊆ ys) : MatchedAnnotationsFinite ε xs :=
  fun x t hx hl => h x t (hs hx) hl

private theorem matched_open (ε : ValCtx) (xs ys : List (VName × ValTy))
    (x : VName) (d : ValTy)
    (hinverse : ∀ y a, (y,a) ∈ ys →
      (∃ b j, (y,b) ∈ xs ∧ a = ValTy.openRec j (.var x d) b) ∨
        (y,a) ∈ exprAnnotations (.var x d))
    (hbody : MatchedAnnotationsFinite ε xs)
    (hdom : MatchedAnnotationsFinite ε (typeAnnotations d)) (hd : TypeFinite d)
    (hname : ∀ y a, (y,a) ∈ xs → y ≠ x)
    (hann : x ∉ annotationSupport xs) (hdfresh : x ∉ d.fv)
    (hstored : ∀ y a, ε.lookup y = some a → x ∉ a.fv) :
    MatchedAnnotationsFinite (Finmap.insert x d ε) ys := by
  intro y a hya hlookup
  rcases hinverse y a hya with ⟨b,j,hb,hab⟩ | hu
  · have hyx := hname y b hb
    rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
    have hba := opened_annotation_eq x d b a j
      (annotationSupport_fresh hann hb) (hstored _ _ hlookup) hab.symm
    subst b
    exact hbody y a hb hlookup
  · simp only [exprAnnotations, List.mem_cons, Prod.mk.injEq] at hu
    rcases hu with ⟨rfl,rfl⟩ | hu
    · exact hd
    · have hy : y ∈ d.fv := by
        rw [typeAnnotations_fv]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(y,a),hu,rfl⟩)
      have hyx : y ≠ x := by intro heq; subst y; exact hdfresh hy
      rw [Finmap.lookup_insert_of_ne _ hyx] at hlookup
      exact hdom y a hu hlookup

private theorem typed_expr {ε : ValCtx} {e : ValExpr} {t : ValTy}
    (h : ValHasType ε e t) (ht : TypeFinite t)
    (hc : ∀ child ∈ exprChildren [] e, ValueQueryDependencies.Finite child) : ExprFinite e := by
  apply ValueQueryDependencies.Finite.intro
  simpa only [children, List.mem_cons, forall_eq_or_imp,
    ValExpr.inferTypeCtx_eq_of_typed h, ValExpr.inferSpaceCtx_eq_spaceOf h] using
      And.intro ht (And.intro ht.spaceOf hc)

private theorem typed_pair {ε : ValCtx} {e : ValExpr} {t : ValTy}
    (h : ValHasType ε e t) (ht : TypeFinite t)
    (hc : ∀ child ∈ exprChildren [] e, ValueQueryDependencies.Finite child) :
    ExprFinite e ∧ TypeFinite t := ⟨typed_expr h ht hc, ht⟩

mutual
 theorem matchedSpace_finite {ε : ValCtx} {s : ValSpace} (h : ValSValid ε s)
    (hv : ValCtxValid ε) (hc : MatchedAnnotationsFinite ε (spaceAnnotations s)) : SpaceFinite s :=
  match h with
  | .real => .real
  | .empty => .empty
  | .dsum h0 h1 => .dsum (matchedSpace_finite h0 hv (by apply hc.mono; simp [spaceAnnotations]))
      (matchedSpace_finite h1 hv (by apply hc.mono; simp [spaceAnnotations]))
  | .tprod h0 h1 => .tprod (matchedSpace_finite h0 hv (by apply hc.mono; simp [spaceAnnotations]))
      (matchedSpace_finite h1 hv (by apply hc.mono; simp [spaceAnnotations]))
  | .ffs h0 h1 he => by
    exact .ffs (.tprod (matchedSpace_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, List.mem_append] at *; tauto))
      (matchedSpace_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, List.mem_append] at *; tauto)))
      (matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, List.mem_append] at *; tauto)).1
 termination_by structural h

 theorem matchedType_finite {ε : ValCtx} {t : ValTy} {k : ValKind} (h : ValTValid ε t k)
    (hv : ValCtxValid ε) (hc : MatchedAnnotationsFinite ε (typeAnnotations t)) : TypeFinite t :=
  match h with
  | .space hs => .space (matchedSpace_finite hs hv hc)
  | @ValTValid.piTy ε d c kd kc L hd hb => by
    have hdm : MatchedAnnotationsFinite ε (typeAnnotations d) := hc.mono (by simp [typeAnnotations])
    have hcm : MatchedAnnotationsFinite ε (typeAnnotations c) := hc.mono (by simp [typeAnnotations])
    have hdf := matchedType_finite hd hv hdm
    have hdl := validType_lc hv hd
    obtain ⟨x,hx⟩ := Infinite.exists_notMem_finset (L ∪ c.fv ∪ annotationSupport (typeAnnotations c) ∪ d.fv ∪ ε.fvSupport ∪ ε.keys)
    simp only [Finset.mem_union, not_or] at hx
    obtain ⟨⟨⟨⟨⟨hxL,hxc⟩,hxann⟩,hxd⟩,hxctx⟩,hxkeys⟩ := hx
    have hmatch := matched_open ε (typeAnnotations c) _ x d
      (fun y a h => typeAnnotations_open_inverse c y a 0 (.var x d) h)
      hcm hdm hdf (by
        intro y a ha heq; subst y; apply hxc; rw [typeAnnotations_fv]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(x,a),ha,rfl⟩))
      hxann hxd (fun y a hl => ValCtx.not_mem_fv_of_not_mem_support hxctx hl)
    have hcf := matchedType_finite (hb x hxL) (hv.insert (by simpa only [Finmap.mem_keys] using hxkeys) hd) hmatch
    exact .piTy hdf (hcf.of_openLast hdl x (.type [] c))
 termination_by structural h

 theorem matchedExpr_finite {ε : ValCtx} {e : ValExpr} {t : ValTy} (h : ValHasType ε e t)
    (hv : ValCtxValid ε) (hc : MatchedAnnotationsFinite ε (exprAnnotations e)) :
    ExprFinite e ∧ TypeFinite t :=
  match h with
  | .var hl => by
    refine typed_pair (.var hl) (hc _ _ List.mem_cons_self hl) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using True.intro
  | .zero hs => by
    have a := matchedSpace_finite hs hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.zero hs) (.space a) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using a
  | @ValHasType.rlit ε r => by
    refine typed_pair (ε := ε) (.rlit r) (.space .real) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using True.intro
  | .scale h0 h1 => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.scale h0 h1) (b.2) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 b.1
  | .vadd h0 h1 hs => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedSpace_finite hs hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.vadd h0 h1 hs) (.space c) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro c (And.intro a.1 b.1)
  | .dsumE h0 h1 => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.dsumE h0 h1) (.space (.dsum a.2.space_inv b.2.space_inv)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 b.1
  | .tprodE h0 h1 => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.tprodE h0 h1) (.space (.tprod a.2.space_inv b.2.space_inv)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 b.1
  | .delta hs => by
    have a := matchedSpace_finite hs hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.delta hs) (.space a) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using a
  | .idelta hs => by
    have a := matchedSpace_finite hs hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.idelta hs) (.space (.tprod a a)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using a
  | .ttv_space hs h0 h1 => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedSpace_finite hs hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.ttv_space hs h0 h1) (.space a.2.tensor_inv.2) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro c (And.intro a.1 b.1)
  | .ttv_real hs h0 h1 hnot => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedSpace_finite hs hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.ttv_real hs h0 h1 hnot) (.space .real) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro c (And.intro a.1 b.1)
  | .mtm hs ht h0 h1 => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedSpace_finite hs hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have d := matchedSpace_finite ht hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.mtm hs ht h0 h1) (.space (.tprod b.2.tensor_inv.1 a.2.tensor_inv.2)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro c (And.intro d (And.intro a.1 b.1))
  | @ValHasType.vsum ε s0 s es hs hb ht hdet => by
    have hi := matchedSpace_finite hs hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have hh : ∀ e ∈ es, ExprFinite e ∧ TypeFinite (.space s) := by
      intro e he
      exact matchedExpr_finite (hb e he) hv (by
        apply hc.mono; intro q hq
        exact List.mem_append_right _ (listAnnotations_mem he hq))
    have hr : TypeFinite (.space s) := .space (matchedSpace_finite ht hv
      (hc.mono (ValHasType.resultAnnotations hv (.vsum hs hb ht hdet))))
    refine ⟨typed_expr (.vsum hs hb ht hdet) hr ?_, hr⟩
    simp only [exprChildren, List.mem_cons, forall_eq_or_imp]
    refine ⟨hi, ?_⟩
    intro child hm
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hm
    exact (hh e he).1
  | @ValHasType.vlam ε d c kd kc body L ht hb => by
    have hpi := matchedType_finite ht hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have hd : TypeFinite d := hpi.child (by simp [children])
    have hcod : ValueQueryDependencies.Finite (.type [d] c) := hpi.child (by simp [children])
    have hdv : ValTValid ε d kd := by cases ht; assumption
    have hdl := validType_lc hv hdv
    obtain ⟨x,hx⟩ := Infinite.exists_notMem_finset (L ∪ body.fv ∪ annotationSupport (exprAnnotations body) ∪ d.fv ∪ ε.fvSupport ∪ ε.keys)
    simp only [Finset.mem_union, not_or] at hx
    obtain ⟨⟨⟨⟨⟨hxL,hxb⟩,hxann⟩,hxd⟩,hxctx⟩,hxkeys⟩ := hx
    have hmatch := matched_open ε (exprAnnotations body) _ x d
      (fun y a h => exprAnnotations_open_inverse body y a 0 (.var x d) h)
      (hc.mono (by intro q hq; simp only [exprAnnotations, List.mem_append] at hq ⊢; tauto)) (hc.mono (by intro q hq; simp only [exprAnnotations, List.mem_append] at hq ⊢; tauto)) hd (by
        intro y a ha heq; subst y; apply hxb; rw [exprAnnotations_fv]
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(x,a),ha,rfl⟩))
      hxann hxd (fun y a hl => ValCtx.not_mem_fv_of_not_mem_support hxctx hl)
    have hbody := (matchedExpr_finite (hb x hxL) (hv.insert (by simpa only [Finmap.mem_keys] using hxkeys) hdv) hmatch).1
    have hf := hbody.of_openLast hdl x (.expr [] body)
    refine ⟨typed_expr (.vlam L ht hb) hpi ?_, hpi⟩
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] using And.intro hd (And.intro hcod hf)
  | .appV h0 h1 heq ht => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.appV h0 h1 heq ht) (matchedType_finite ht hv (hc.mono (ValHasType.resultAnnotations hv (.appV h0 h1 heq ht)))) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 b.1
  | .vkrn h0 h1 => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.vkrn h0 h1) (.space (.tprod (.tprod a.2.tensor_inv.1 b.2.tensor_inv.1) (.tprod a.2.tensor_inv.2 b.2.tensor_inv.2))) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 b.1
  | .vblk h0 h1 => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.vblk h0 h1) (.space (.tprod (.dsum a.2.tensor_inv.1 b.2.tensor_inv.1) (.dsum a.2.tensor_inv.2 b.2.tensor_inv.2))) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 b.1
  | .reshap he hs ht => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedType_finite ht hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedType_finite hs hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.reshap he hs ht) (b) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 (And.intro b c)
  | .vtrans he => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.vtrans he) (.space (.tprod a.2.tensor_inv.2 a.2.tensor_inv.1)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using a.1
  | .gsvdS he ha hb => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite ha hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedExpr_finite hb hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have f : ∀ p, SpaceFinite (.ffs p _ _) := fun _ => .ffs a.2.space_inv a.1
    refine typed_pair (.gsvdS he ha hb) (.space (.tprod (f .cokernel) (f .image))) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 (And.intro b.1 c.1)
  | .gsvdU he ha hb => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite ha hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedExpr_finite hb hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have f : ∀ p, SpaceFinite (.ffs p _ _) := fun _ => .ffs a.2.space_inv a.1
    refine typed_pair (.gsvdU he ha hb) (.space (.tprod a.2.tensor_inv.1 (f _))) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 (And.intro b.1 c.1)
  | .gsvdUI he ha hb => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite ha hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedExpr_finite hb hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have f : ∀ p, SpaceFinite (.ffs p _ _) := fun _ => .ffs a.2.space_inv a.1
    refine typed_pair (.gsvdUI he ha hb) (.space (.tprod a.2.tensor_inv.1 (f _))) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 (And.intro b.1 c.1)
  | .gsvdV he ha hb => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite ha hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedExpr_finite hb hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have f : ∀ p, SpaceFinite (.ffs p _ _) := fun _ => .ffs a.2.space_inv a.1
    refine typed_pair (.gsvdV he ha hb) (.space (.tprod a.2.tensor_inv.2 (f _))) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 (And.intro b.1 c.1)
  | .gsvdVI he ha hb => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite ha hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedExpr_finite hb hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have f : ∀ p, SpaceFinite (.ffs p _ _) := fun _ => .ffs a.2.space_inv a.1
    refine typed_pair (.gsvdVI he ha hb) (.space (.tprod a.2.tensor_inv.2 (f _))) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 (And.intro b.1 c.1)
  | .pinv_tensor he => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.pinv_tensor he) (.space (.tprod a.2.tensor_inv.2 a.2.tensor_inv.1)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using a.1
  | .pinv_raw he hnot => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.pinv_raw he hnot) (.space (.tprod .real a.2.space_inv)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using a.1
  | .inv_tensor he => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.inv_tensor he) (.space (.tprod a.2.tensor_inv.2 a.2.tensor_inv.1)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using a.1
  | .inv_raw he hnot => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.inv_raw he hnot) (.space (.tprod .real a.2.space_inv)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using a.1
  | .gpinv he ha hb => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite ha hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedExpr_finite hb hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.gpinv he ha hb) (.space (.tprod a.2.tensor_inv.2 a.2.tensor_inv.1)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 (And.intro b.1 c.1)
  | .rrefRep h0 h1 => by
    have a := matchedExpr_finite h0 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have b := matchedExpr_finite h1 hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.rrefRep h0 h1) (.space (.tprod b.2.tensor_inv.2 b.2.tensor_inv.1)) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using And.intro a.1 b.1
  | .svds he => by
    have a := matchedExpr_finite he hv (by apply hc.mono; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    refine typed_pair (.svds he) (.space (.tprod (.ffs a.2.space_inv a.1) (.ffs a.2.space_inv a.1))) ?_
    simpa only [exprChildren, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true] using a.1
 termination_by structural h
end

/-- Valid contexts and typing imply finite dimension-query dependencies.
The auxiliary matching-annotation obligations are discharged by size induction. -/
theorem validType_queryFinite {ε : ValCtx} (hv : ValCtxValid ε)
    {t : ValTy} {k : ValKind} (h : ValTValid ε t k) : TypeFinite t := by
  generalize hn : t.size = n
  induction n using Nat.strong_induction_on generalizing t k with
  | h n ih =>
    apply matchedType_finite h hv
    intro x a ha hl
    obtain ⟨ka,hat⟩ := hv x a hl
    exact ih a.size (by simpa only [hn] using typeAnnotations_rank t x a ha) hat rfl

theorem validExpr_queryFinite {ε : ValCtx} (hv : ValCtxValid ε)
    {e : ValExpr} {t : ValTy} (h : ValHasType ε e t) : ExprFinite e ∧ TypeFinite t :=
  matchedExpr_finite h hv (fun x a _ hl => validType_queryFinite hv (hv x a hl).2)

theorem validSpace_queryFinite {ε : ValCtx} (hv : ValCtxValid ε)
    {s : ValSpace} (h : ValSValid ε s) : SpaceFinite s :=
  matchedSpace_finite h hv (fun x a _ hl => validType_queryFinite hv (hv x a hl).2)

end GLang.RuntimeValue
