import GLang.Proofs.Value.Binding.ValueBeta
import GLang.Proofs.Value.Binding.ValueMatchedOpening
import GLang.Proofs.Value.Presentation.PaperValueLocalClosure
import GLang.Proofs.Value.Soundness.ValueSoundVals
import GLang.Proofs.Value.Typing.ValueContextSupport
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace GLang.PaperValueDomains
open GLang.ValueDependency

private theorem space_lc_inv {s : ValSpace} (h : ValTy.lc (.space s)) : ValSpace.lc s :=
  by cases h; assumption
private theorem tensor_lc_inv {s t : ValSpace} (h : ValTy.lc (.space (.tprod s t))) :
    ValSpace.lc s ∧ ValSpace.lc t := by
  cases h with
  | space h => cases h with | tprod hs ht => exact ⟨hs, ht⟩

mutual
 theorem matchedSpace_lc {ε : ValCtx} {s : ValSpace}
    (h : ValSValid ε s) (hc : MatchedAnnotationsClosed ε (spaceAnnotations s)) : ValSpace.lc s :=
  match h with
  | .real => by exact .real
  | .empty => by exact .empty
  | .dsum h0 h1 => by exact .dsum (matchedSpace_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) (matchedSpace_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto))
  | .tprod h0 h1 => by exact .tprod (matchedSpace_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) (matchedSpace_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto))
  | .ffs h0 h1 he => by
    exact .ffs (.tprod (matchedSpace_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) (matchedSpace_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)))
      (matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)).1

 termination_by structural h

 theorem matchedType_lc {ε : ValCtx} {τ : ValTy} {k : ValKind}
    (h : ValTValid ε τ k) (hc : MatchedAnnotationsClosed ε (typeAnnotations τ)) : ValTy.lc τ :=
  match h with
  | .space hs => by exact .space (matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto))
  | @ValTValid.piTy ε d c k0 k1 L hd hb => by
    have hdm : MatchedAnnotationsClosed ε (typeAnnotations d) := (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have hcm : MatchedAnnotationsClosed ε (typeAnnotations c) := (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have hdl := matchedType_lc hd hdm
    refine .piTy (L ∪ c.fv ∪ annotationSupport (typeAnnotations c) ∪ d.fv ∪ ε.fvSupport) hdl ?_
    intro x hx
    simp only [Finset.mem_union, not_or] at hx
    obtain ⟨⟨⟨⟨hxL, hxc⟩, hxann⟩, hxd⟩, hxctx⟩ := hx
    exact matchedType_lc (hb x hxL)
      (matched_type_open ε c d x 0 hcm hdm hdl hxc hxann hxd
        (fun y a hl => ValCtx.not_mem_fv_of_not_mem_support hxctx hl))

 termination_by structural h

 theorem matchedExpr_lc {ε : ValCtx} {e : ValExpr} {τ : ValTy}
    (h : ValHasType ε e τ) (hc : MatchedAnnotationsClosed ε (exprAnnotations e)) : ValExpr.lc e ∧ ValTy.lc τ :=
  match h with
  | .var hx => by exact ⟨.var (hc _ _ (List.mem_cons_self) hx), hc _ _ (List.mem_cons_self) hx⟩
  | .zero hs => by exact ⟨.zero (matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)), .space (matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto))⟩
  | .rlit r => by exact ⟨.rlit, .space .real⟩
  | .scale h0 h1 => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.scale a.1 b.1, b.2⟩
  | .vadd h0 h1 hs => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have c := matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.vadd c a.1 b.1, .space c⟩
  | .dsumE h0 h1 => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.dsumE a.1 b.1, .space (.dsum (space_lc_inv a.2) (space_lc_inv b.2))⟩
  | .tprodE h0 h1 => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.tprodE a.1 b.1, .space (.tprod (space_lc_inv a.2) (space_lc_inv b.2))⟩
  | .delta hs => by exact ⟨.delta (matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)), .space (matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto))⟩
  | .idelta hs => by
    have a := matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.idelta a, .space (.tprod a a)⟩
  | .ttv_space hs h0 h1 => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.ttv (matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) a.1 b.1, .space (tensor_lc_inv a.2).2⟩
  | .ttv_real hs h0 h1 _ => by
    exact ⟨.ttv (matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) (matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)).1
      (matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)).1, .space .real⟩
  | .mtm hs ht h0 h1 => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.mtm (matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) (matchedSpace_lc ht (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)) a.1 b.1,
      .space (.tprod (tensor_lc_inv b.2).1 (tensor_lc_inv a.2).2)⟩
  | @ValHasType.vsum ε s0 s es hs hb ht hdet => by
    have hi := matchedSpace_lc hs (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have hh : ∀ e ∈ es, ValExpr.lc e ∧ ValTy.lc (.space s) := by
      intro e he
      exact matchedExpr_lc (hb e he) (by
        apply MatchedAnnotationsClosed.mono hc
        intro q hq
        exact List.mem_append_right _ (listAnnotations_mem he hq))
    refine ⟨.vsum hi (fun e he => (hh e he).1), ?_⟩
    cases es with
    | nil => have hz := hdet rfl; subst s; exact .space .empty
    | cons e es => exact (hh e (List.mem_cons_self)).2
  | @ValHasType.vlam ε d c k0 k1 body L ht hb => by
    have hdm : MatchedAnnotationsClosed ε (typeAnnotations d) := (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have hbm : MatchedAnnotationsClosed ε (exprAnnotations body) := (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have hpi := matchedType_lc ht (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    cases hpi with
    | piTy L' hd hcod =>
      refine ⟨.vlam (L ∪ L' ∪ body.fv ∪ annotationSupport (exprAnnotations body) ∪ d.fv ∪ ε.fvSupport) hd ?_ ?_, .piTy L' hd hcod⟩
      · intro x hx
        simp only [Finset.mem_union, not_or] at hx
        exact hcod x hx.1.1.1.1.2
      · intro x hx
        simp only [Finset.mem_union, not_or] at hx
        obtain ⟨⟨⟨⟨⟨hxL, _⟩, hxb⟩, hxann⟩, hxd⟩, hxctx⟩ := hx
        exact (matchedExpr_lc (hb x hxL)
          (matched_expr_open ε body d x 0 hbm hdm hd hxb hxann hxd
            (fun y a hl => ValCtx.not_mem_fv_of_not_mem_support hxctx hl))).1
  | .appV h0 h1 heq ht => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.appV a.1 b.1, heq ▸ ValTy.applyCodomain_lc a.2 b.1⟩
  | .vkrn h0 h1 => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have p := tensor_lc_inv a.2; have q := tensor_lc_inv b.2
    exact ⟨.vkrn a.1 b.1, .space (.tprod (.tprod p.1 q.1) (.tprod p.2 q.2))⟩
  | .vblk h0 h1 => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have p := tensor_lc_inv a.2; have q := tensor_lc_inv b.2
    exact ⟨.vblk a.1 b.1, .space (.tprod (.dsum p.1 q.1) (.dsum p.2 q.2))⟩
  | .reshap he h0 h1 => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have t := matchedType_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.reshap a.1 t (matchedType_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)), t⟩
  | .vtrans he => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have p := tensor_lc_inv a.2
    exact ⟨.vtrans a.1, .space (.tprod p.2 p.1)⟩
  | .gsvdS he ha hb => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc ha (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have c := matchedExpr_lc hb (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdS a.1 b.1 c.1, .space (.tprod (f .cokernel) (f .image))⟩
  | .gsvdU he ha hb => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc ha (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have c := matchedExpr_lc hb (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdU a.1 b.1 c.1, .space (.tprod p.1 (f _))⟩
  | .gsvdUI he ha hb => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc ha (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have c := matchedExpr_lc hb (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdUI a.1 b.1 c.1, .space (.tprod p.1 (f _))⟩
  | .gsvdV he ha hb => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc ha (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have c := matchedExpr_lc hb (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdV a.1 b.1 c.1, .space (.tprod p.2 (f _))⟩
  | .gsvdVI he ha hb => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc ha (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have c := matchedExpr_lc hb (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have p := tensor_lc_inv a.2
    have f : ∀ q, ValSpace.lc (.ffs q _ _) := fun _ => .ffs (space_lc_inv a.2) a.1
    exact ⟨.gsvdVI a.1 b.1 c.1, .space (.tprod p.2 (f _))⟩
  | .pinv_tensor he => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have p := tensor_lc_inv a.2
    exact ⟨.pinv a.1, .space (.tprod p.2 p.1)⟩
  | .pinv_raw he _ => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.pinv a.1, .space (.tprod .real (space_lc_inv a.2))⟩
  | .inv_tensor he => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have p := tensor_lc_inv a.2
    exact ⟨.inv a.1, .space (.tprod p.2 p.1)⟩
  | .inv_raw he _ => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.inv a.1, .space (.tprod .real (space_lc_inv a.2))⟩
  | .gpinv he ha hb => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc ha (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have c := matchedExpr_lc hb (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have p := tensor_lc_inv a.2
    exact ⟨.gpinv a.1 b.1 c.1, .space (.tprod p.2 p.1)⟩
  | .rrefRep h0 h1 => by
    have a := matchedExpr_lc h0 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto); have b := matchedExpr_lc h1 (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    have p := tensor_lc_inv b.2
    exact ⟨.rrefRep a.1 b.1, .space (.tprod p.2 p.1)⟩
  | .svds he => by
    have a := matchedExpr_lc he (by apply MatchedAnnotationsClosed.mono hc; intro q hq; simp only [spaceAnnotations, typeAnnotations, exprAnnotations, List.mem_append] at hq ⊢; tauto)
    exact ⟨.svds a.1, .space (.tprod (.ffs (space_lc_inv a.2) a.1) (.ffs (space_lc_inv a.2) a.1))⟩
 termination_by structural h
end

/-- Context validity alone forces every valid type locally closed.
The strong induction visits only matching declaration annotations, each strictly
smaller than its enclosing type. Cofinite opening was handled structurally
above and does not enter this size measure. -/
theorem validType_lc {ε : ValCtx} (hc : ValCtxValid ε)
    {τ : ValTy} {k : ValKind} (h : ValTValid ε τ k) : ValTy.lc τ := by
  generalize hn : τ.size = n
  induction n using Nat.strong_induction_on generalizing τ k with
  | h n ih =>
    apply matchedType_lc h
    intro x a ha hl
    obtain ⟨ka, hat⟩ := hc x a hl
    exact ih a.size (by simpa only [hn] using typeAnnotations_rank τ x a ha) hat rfl

/-- The local-closure input contract is derived, never an extra public premise. -/
theorem validContext_lc {ε : ValCtx} (hc : ValCtxValid ε) : ContextLocallyClosed ε := by
  intro x τ hl
  exact validType_lc hc (hc x τ hl).2

theorem validSpace_lc {ε : ValCtx} (hc : ValCtxValid ε)
    {s : ValSpace} (h : ValSValid ε s) : ValSpace.lc s :=
  originalSpace_lc h (validContext_lc hc)

theorem validExpr_lc {ε : ValCtx} (hc : ValCtxValid ε)
    {e : ValExpr} {τ : ValTy} (h : ValHasType ε e τ) : ValExpr.lc e ∧ ValTy.lc τ :=
  originalExpr_lc h (validContext_lc hc)

end GLang.PaperValueDomains
