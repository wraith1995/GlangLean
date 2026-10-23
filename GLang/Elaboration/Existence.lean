import GLang.Elaboration.ContextReconstruction
import GLang.Elaboration.Supporting.SourceBinderReconstruction

/-! Existence of internal annotations, by induction on independent surface
judgments. Extra internal nonlinear bindings absorb surface promotion. -/
namespace GLang
namespace SurfaceElaboration
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

mutual
 theorem elaborateSpace {g s} (h : Surface.SValid g s)
     {E : NLCtx} (hw : Metatheory.SourceContextWF ∅ E)
     (hc : ContextEmbedding ∅ g ∅ E) : ∃ S, SpaceLift E s S :=
   match h with
   | .empty => ⟨.empty, rfl, ⟨.empty⟩⟩
   | .real => ⟨.real, rfl, ⟨.real⟩⟩
   | .dual ha => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     exact ⟨.dual A, congrArg Surface.Space.dual hA, ⟨.dual hvA⟩⟩
   | .dsum ha hb => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     exact ⟨.dsum A B, congrArg₂ Surface.Space.dsum hA hB, ⟨.dsum hvA hvB⟩⟩
   | .tprod ha hb => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     exact ⟨.tprod A B, congrArg₂ Surface.Space.tprod hA hB, ⟨.tprod hvA hvB⟩⟩
   | .ker ha hb he => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have heT : T.erase = (Ty.space (.tprod (.dual A) B)).erase := by
       simpa only [Ty.erase,Space.erase,hA,hB] using hT
     have ht := alignResult hw hve (.space (.tprod (.dual hvA) hvB)) heT
     exact ⟨.ker A B e, congrArg Surface.Space.ker he', ⟨.ker hvA hvB ht⟩⟩
   | .coker ha hb he => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have heT : T.erase = (Ty.space (.tprod (.dual A) B)).erase := by
       simpa only [Ty.erase,Space.erase,hA,hB] using hT
     have ht := alignResult hw hve (.space (.tprod (.dual hvA) hvB)) heT
     exact ⟨.coker A B e, congrArg Surface.Space.coker he', ⟨.coker hvA hvB ht⟩⟩
   | .img ha hb he => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have heT : T.erase = (Ty.space (.tprod (.dual A) B)).erase := by
       simpa only [Ty.erase,Space.erase,hA,hB] using hT
     have ht := alignResult hw hve (.space (.tprod (.dual hvA) hvB)) heT
     exact ⟨.img A B e, congrArg Surface.Space.img he', ⟨.img hvA hvB ht⟩⟩
   | .coimg ha hb he => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have heT : T.erase = (Ty.space (.tprod (.dual A) B)).erase := by
       simpa only [Ty.erase,Space.erase,hA,hB] using hT
     have ht := alignResult hw hve (.space (.tprod (.dual hvA) hvB)) heT
     exact ⟨.coimg A B e, congrArg Surface.Space.coimg he', ⟨.coimg hvA hvB ht⟩⟩
 termination_by structural h

 theorem elaborateType {g t k} (h : Surface.TValid g t k)
     {E : NLCtx} (hw : Metatheory.SourceContextWF ∅ E)
     (hc : ContextEmbedding ∅ g ∅ E) : ∃ T, TypeLift E t k T :=
   match h with
   | .space hs => by
     obtain ⟨S,hS,⟨hvS⟩⟩ := elaborateSpace hs hw hc
     exact ⟨.space S, congrArg Surface.Ty.space hS, ⟨.space hvS⟩⟩
   | @Surface.TValid.piTy _ a b ka kb L ha hb => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateType ha hw hc
     obtain ⟨x,hx⟩ := Infinite.exists_notMem_finset (L ∪ E.keys ∪ b.fv)
     simp only [Finset.mem_union,not_or] at hx
     have hxE : x ∉ E := fun h => hx.1.2 (Finmap.mem_keys.mpr h)
     have hw' := wf_insert_nonlinear hw Finmap.notMem_empty hxE hvA
     have hc' := hc.insert_nonlinear (x := x) Finmap.notMem_empty hA
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateType (hb x hx.1.1) hw' hc'
     refine ⟨.piTy A (Ty.closeRec 0 x B), ?_, ⟨TValid.close_pi hw.scoping hvA hxE hvB⟩⟩
     exact congrArg₂ Surface.Ty.piTy hA (Ty.erase_close_of_open hx.2 hB)
 termination_by structural h

 theorem elaborateSubspace {g s t} (h : Surface.SubType g s t)
     {E : NLCtx} (hw : Metatheory.SourceContextWF ∅ E)
     (hc : ContextEmbedding ∅ g ∅ E) : ∃ p, SubspaceLift E s t p :=
   match h with
   | .sub_ker ha hb he => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have heT : T.erase = (Ty.space (.tprod (.dual A) B)).erase := by
       simpa only [Ty.erase,Space.erase,hA,hB] using hT
     have ht := alignResult hw hve (.space (.tprod (.dual hvA) hvB)) heT
     exact ⟨(.ker A B e,A), congrArg Surface.Space.ker he', hA,
       ⟨.sub_ker hvA hvB ht⟩⟩
   | .sub_coker ha hb he => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have heT : T.erase = (Ty.space (.tprod (.dual A) B)).erase := by
       simpa only [Ty.erase,Space.erase,hA,hB] using hT
     have ht := alignResult hw hve (.space (.tprod (.dual hvA) hvB)) heT
     exact ⟨(.coker A B e,A), congrArg Surface.Space.coker he', hA,
       ⟨.sub_coker hvA hvB ht⟩⟩
   | .sub_img ha hb he => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have heT : T.erase = (Ty.space (.tprod (.dual A) B)).erase := by
       simpa only [Ty.erase,Space.erase,hA,hB] using hT
     have ht := alignResult hw hve (.space (.tprod (.dual hvA) hvB)) heT
     exact ⟨(.img A B e,B), congrArg Surface.Space.img he', hB,
       ⟨.sub_img hvA hvB ht⟩⟩
   | .sub_coimg ha hb he => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have heT : T.erase = (Ty.space (.tprod (.dual A) B)).erase := by
       simpa only [Ty.erase,Space.erase,hA,hB] using hT
     have ht := alignResult hw hve (.space (.tprod (.dual hvA) hvB)) heT
     exact ⟨(.coimg A B e,B), congrArg Surface.Space.coimg he', hB,
       ⟨.sub_coimg hvA hvB ht⟩⟩
 termination_by structural h

 theorem elaborateTerm {d g e t} (h : Surface.HasType d g e t)
     {D : LCtx} {E : NLCtx} (hw : Metatheory.SourceContextWF D E)
     (hc : ContextEmbedding d g D E) : ∃ p, TermLift D E e t p :=
   match h with
   | .zero hs => by
     obtain ⟨S,hS,⟨hvS⟩⟩ := elaborateSpace hs (wf_empty_linear hw) hc.with_empty_linear
     exact ⟨(.zero S,.space S), congrArg Surface.Term.zero hS,
       congrArg Surface.Ty.space hS, ⟨.zero hvS⟩⟩
   | .inner hs => by
     have hD := hc.empty_linear
     subst D
     obtain ⟨S,hS,⟨hvS⟩⟩ := elaborateSpace hs hw hc
     refine ⟨(.inner S,.space (.tprod (.dual S) (.dual S))),
       congrArg Surface.Term.inner hS, ?_, ⟨.inner hvS⟩⟩
     simp only [Ty.erase,Space.erase,hS]
   | .real_lit r => by
     have hD := hc.empty_linear
     subst D
     exact ⟨(.real r,.space .real),rfl,rfl,⟨.real_lit r⟩⟩
   | @Surface.HasType.var_nlin _ x τ hl => by
     have hD := hc.empty_linear
     subst D
     obtain ⟨T,hT,heT⟩ := hc.nonlinear x τ hl
     exact ⟨(.var x,T),rfl,heT,⟨.var_nlin hT⟩⟩
   | @Surface.HasType.var_lin _ x s => by
     rcases hc.linear x s (by simp) with ⟨S,hS,heS⟩ | ⟨S,hS,heS⟩
     · have hD := hc.singleton_linear hS
       subst D
       exact ⟨(.var x,.space S),rfl,congrArg Surface.Ty.space heS,⟨.var_lin⟩⟩
     · have hD := hc.singleton_nonlinear hw hS
       subst D
       exact ⟨(.var x,.space S),rfl,congrArg Surface.Ty.space heS,⟨.var_nlin hS⟩⟩
   | .promote lin hd hg hf he =>
     elaborateTerm he hw (hc.promote hd hg)
   | .add hs h₀ h₁ => by
     obtain ⟨S,hS,⟨hvS⟩⟩ := elaborateSpace hs (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨⟨e₀,T₀⟩,he₀,hT₀,⟨hv₀⟩⟩ := elaborateTerm h₀ hw hc
     obtain ⟨⟨e₁,T₁⟩,he₁,hT₁,⟨hv₁⟩⟩ := elaborateTerm h₁ hw hc
     have ht₀ := alignResult hw hv₀ (.space hvS) (by simpa only [Ty.erase,hS] using hT₀)
     have ht₁ := alignResult hw hv₁ (.space hvS) (by simpa only [Ty.erase,hS] using hT₁)
     exact ⟨(.add e₀ e₁,.space S),congrArg₂ Surface.Term.add he₀ he₁,
       congrArg Surface.Ty.space hS,⟨.add hvS ht₀ ht₁⟩⟩
   | .dsumE ha hb h₀ h₁ => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨⟨e₀,T₀⟩,he₀,hT₀,⟨hv₀⟩⟩ := elaborateTerm h₀ hw hc
     obtain ⟨⟨e₁,T₁⟩,he₁,hT₁,⟨hv₁⟩⟩ := elaborateTerm h₁ hw hc
     have ht₀ := alignResult hw hv₀ (.space hvA) (by simpa only [Ty.erase,hA] using hT₀)
     have ht₁ := alignResult hw hv₁ (.space hvB) (by simpa only [Ty.erase,hB] using hT₁)
     refine ⟨(.dsumE e₀ e₁,.space (.dsum A B)),congrArg₂ Surface.Term.dsumE he₀ he₁,
       ?_,⟨.dsumE hvA hvB ht₀ ht₁⟩⟩
     simp only [Ty.erase,Space.erase,hA,hB]
   | @Surface.HasType.smul d₀ d₁ g e₀ e₁ s hs hd h₀ h₁ => by
     obtain ⟨S,hS,⟨hvS⟩⟩ := elaborateSpace hs (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨hD,hdis,hc₀,hc₁⟩ := hc.split hd
     have hw₀ := restrictSource_wf hw d₀.keys
     have hw₁ := restrictSource_wf hw d₁.keys
     obtain ⟨⟨e₀,T₀⟩,he₀,hT₀,⟨hv₀⟩⟩ := elaborateTerm h₀ hw₀ hc₀
     obtain ⟨⟨e₁,T₁⟩,he₁,hT₁,⟨hv₁⟩⟩ := elaborateTerm h₁ hw₁ hc₁
     have ht₀ := alignResult hw₀ hv₀ (.space .real) (by simpa only [Ty.erase,Space.erase,hS] using hT₀)
     have ht₁ := alignResult hw₁ hv₁ (.space hvS) (by simpa only [Ty.erase,Space.erase,hS] using hT₁)
     refine ⟨(.smul e₀ e₁,.space S),congrArg₂ Surface.Term.smul he₀ he₁, ?_, ⟨?_⟩⟩
     · simp only [Ty.erase,hS]
     · simpa only [← hD] using HasType.smul hvS hdis ht₀ ht₁
   | @Surface.HasType.tprodE d₀ d₁ g e₀ e₁ a b ha hb hd h₀ h₁ => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨hD,hdis,hc₀,hc₁⟩ := hc.split hd
     have hw₀ := restrictSource_wf hw d₀.keys
     have hw₁ := restrictSource_wf hw d₁.keys
     obtain ⟨⟨e₀,T₀⟩,he₀,hT₀,⟨hv₀⟩⟩ := elaborateTerm h₀ hw₀ hc₀
     obtain ⟨⟨e₁,T₁⟩,he₁,hT₁,⟨hv₁⟩⟩ := elaborateTerm h₁ hw₁ hc₁
     have ht₀ := alignResult hw₀ hv₀ (.space hvA) (by simpa only [Ty.erase,Space.erase,hA,hB] using hT₀)
     have ht₁ := alignResult hw₁ hv₁ (.space hvB) (by simpa only [Ty.erase,Space.erase,hA,hB] using hT₁)
     refine ⟨(.tprodE e₀ e₁,.space (.tprod A B)),congrArg₂ Surface.Term.tprodE he₀ he₁, ?_, ⟨?_⟩⟩
     · simp only [Ty.erase,Space.erase,hA,hB]
     · simpa only [← hD] using HasType.tprodE hvA hvB hdis ht₀ ht₁
   | @Surface.HasType.app_linear d₀ d₁ g e₀ e₁ a b ha hb hd h₀ h₁ => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨hD,hdis,hc₀,hc₁⟩ := hc.split hd
     have hw₀ := restrictSource_wf hw d₀.keys
     have hw₁ := restrictSource_wf hw d₁.keys
     obtain ⟨⟨e₀,T₀⟩,he₀,hT₀,⟨hv₀⟩⟩ := elaborateTerm h₀ hw₀ hc₀
     obtain ⟨⟨e₁,T₁⟩,he₁,hT₁,⟨hv₁⟩⟩ := elaborateTerm h₁ hw₁ hc₁
     have ht₀ := alignResult hw₀ hv₀ (.space (.tprod (.dual hvA) hvB)) (by simpa only [Ty.erase,Space.erase,hA,hB] using hT₀)
     have ht₁ := alignResult hw₁ hv₁ (.space hvA) (by simpa only [Ty.erase,Space.erase,hA,hB] using hT₁)
     refine ⟨(.appL A B e₀ e₁,.space B),congrArg₂ Surface.Term.app he₀ he₁, ?_, ⟨?_⟩⟩
     · simp only [Ty.erase,hB]
     · simpa only [← hD] using HasType.app_linear hvA hvB hdis ht₀ ht₁
   | @Surface.HasType.app_inner d₀ d₁ g e₀ e₁ s hs hd h₀ h₁ => by
     obtain ⟨S,hS,⟨hvS⟩⟩ := elaborateSpace hs (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨hD,hdis,hc₀,hc₁⟩ := hc.split hd
     have hw₀ := restrictSource_wf hw d₀.keys
     have hw₁ := restrictSource_wf hw d₁.keys
     obtain ⟨⟨e₀,T₀⟩,he₀,hT₀,⟨hv₀⟩⟩ := elaborateTerm h₀ hw₀ hc₀
     obtain ⟨⟨e₁,T₁⟩,he₁,hT₁,⟨hv₁⟩⟩ := elaborateTerm h₁ hw₁ hc₁
     have ht₀ := alignResult hw₀ hv₀ (.space (.dual hvS)) (by simpa only [Ty.erase,Space.erase,hS] using hT₀)
     have ht₁ := alignResult hw₁ hv₁ (.space hvS) (by simpa only [Ty.erase,Space.erase,hS] using hT₁)
     refine ⟨(.appI S e₀ e₁,.space .real),congrArg₂ Surface.Term.app he₀ he₁, ?_, ⟨?_⟩⟩
     · rfl
     · simpa only [← hD] using HasType.app_inner hvS hdis ht₀ ht₁
   | .pinv_tensor ha hb he => by
     have hD := hc.empty_linear
     subst D
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha hw hc
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have ht := alignResult hw hve (.space (.tprod (.dual hvA) hvB)) (by simpa only [Ty.erase,Space.erase,hA,hB] using hT)
     refine ⟨(.pinvT A B e,.space (.tprod (.dual B) A)),congrArg Surface.Term.pinv he',?_,
       ⟨.pinv_tensor hvA hvB ht⟩⟩
     simp only [Ty.erase,Space.erase,hA,hB]
   | .pinv_dual hs he => by
     have hD := hc.empty_linear
     subst D
     obtain ⟨S,hS,⟨hvS⟩⟩ := elaborateSpace hs hw hc
     obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he hw hc
     have ht := alignResult hw hve (.space (.dual hvS)) (by simpa only [Ty.erase,Space.erase,hS] using hT)
     refine ⟨(.pinvD S e,.space (.tprod (.dual .real) S)),congrArg Surface.Term.pinv he',?_,
       ⟨.pinv_dual hvS ht⟩⟩
     simp only [Ty.erase,Space.erase,hS]
   | .embed hs => by
     have hD := hc.empty_linear
     subst D
     obtain ⟨⟨A,B⟩,hA,hB,⟨hsub⟩⟩ := elaborateSubspace hs hw hc
     refine ⟨(.embed A,.space (.tprod (.dual A) B)),congrArg Surface.Term.embed hA,?_,⟨.embed hsub⟩⟩
     simp only [Ty.erase,Space.erase,hA,hB]
   | .app_nonlinear h₀ h₁ => by
     have hD := hc.empty_linear
     subst D
     obtain ⟨⟨e₀,T₀⟩,he₀,hT₀,⟨hv₀⟩⟩ := elaborateTerm h₀ hw hc
     obtain ⟨⟨e₁,T₁⟩,he₁,hT₁,⟨hv₁⟩⟩ := elaborateTerm h₁ hw hc
     cases T₀ with
     | space s => simp [Ty.erase] at hT₀
     | piTy A B =>
       obtain ⟨hA,hB⟩ := Surface.Ty.piTy.inj hT₀
       obtain ⟨k,hvalid⟩ := resultValid hw hv₀
       cases hvalid with
       | piTy L hvA hvB =>
         have ht₁ := alignResult hw hv₁ hvA (hT₁.trans hA.symm)
         refine ⟨(.appN e₀ e₁,Ty.instantiate e₁ B),congrArg₂ Surface.Term.app he₀ he₁,
           ?_,⟨.app_nonlinear hv₀ ht₁⟩⟩
         simp only [Ty.instantiate,Ty.erase_openRec,he₁,hB,Surface.Ty.instantiate]
   | @Surface.HasType.llam_real d g s e L hs hb => by
     obtain ⟨S,hS,⟨hvS⟩⟩ := elaborateSpace hs (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨x,hx⟩ := Infinite.exists_notMem_finset (L ∪ D.keys ∪ E.keys ∪ e.fv)
     simp only [Finset.mem_union,not_or] at hx
     have hxD : x ∉ D := fun h => hx.1.1.2 (Finmap.mem_keys.mpr h)
     have hxE : x ∉ E := fun h => hx.1.2 (Finmap.mem_keys.mpr h)
     have hw' := wf_insert_linear hw hxE hvS
     obtain ⟨⟨eb,Tb⟩,heb,hTb,⟨hvb⟩⟩ := elaborateTerm (hb x hx.1.1.1) hw'
       (hc.insert_linear hS)
     have htb := alignResult hw' hvb (.space .real) hTb
     exact ⟨(.llam S .real (Term.closeRec 0 x eb),.space (.dual S)),
       congrArg₂ Surface.Term.llam hS (Term.erase_close_of_open hx.2 heb),
       congrArg Surface.Ty.space (congrArg Surface.Space.dual hS),
       ⟨HasType.close_llam_real hw.scoping hvS hxD hxE htb⟩⟩
   | @Surface.HasType.llam_tensor d g a b e L hne ha hb he => by
     obtain ⟨A,hA,⟨hvA⟩⟩ := elaborateSpace ha (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨B,hB,⟨hvB⟩⟩ := elaborateSpace hb (wf_empty_linear hw) hc.with_empty_linear
     obtain ⟨x,hx⟩ := Infinite.exists_notMem_finset (L ∪ D.keys ∪ E.keys ∪ e.fv)
     simp only [Finset.mem_union,not_or] at hx
     have hxD : x ∉ D := fun h => hx.1.1.2 (Finmap.mem_keys.mpr h)
     have hxE : x ∉ E := fun h => hx.1.2 (Finmap.mem_keys.mpr h)
     have hw' := wf_insert_linear hw hxE hvA
     obtain ⟨⟨eb,Tb⟩,heb,hTb,⟨hvb⟩⟩ := elaborateTerm (he x hx.1.1.1) hw'
       (hc.insert_linear hA)
     have htb := alignResult hw' hvb (.space hvB) (by simpa only [Ty.erase,hB] using hTb)
     have hneB : B ≠ .real := fun h => hne (hB.symm.trans (congrArg Space.erase h))
     refine ⟨(.llam A B (Term.closeRec 0 x eb),.space (.tprod (.dual A) B)),
       congrArg₂ Surface.Term.llam hA (Term.erase_close_of_open hx.2 heb),?_,
       ⟨HasType.close_llam_tensor hw.scoping hvA hvB hneB hxD hxE htb⟩⟩
     simp only [Ty.erase,Space.erase,hA,hB]
   | @Surface.HasType.nllam g a b ka kb e L ht he => by
     have hD := hc.empty_linear
     subst D
     obtain ⟨T,hT,⟨hvT⟩⟩ := elaborateType ht hw hc
     cases T with
     | space s => simp [Ty.erase] at hT
     | piTy A B =>
       obtain ⟨hA,hB⟩ := Surface.Ty.piTy.inj hT
       cases hvT with
       | piTy K hvA hvB =>
         obtain ⟨x,hx⟩ := Infinite.exists_notMem_finset (L ∪ K ∪ E.keys ∪ e.fv ∪ B.fv)
         simp only [Finset.mem_union,not_or] at hx
         have hxE : x ∉ E := fun h => hx.1.1.2 (Finmap.mem_keys.mpr h)
         have hw' := wf_insert_nonlinear hw Finmap.notMem_empty hxE hvA
         obtain ⟨⟨eb,Tb⟩,heb,hTb,⟨hvb⟩⟩ := elaborateTerm (he x hx.1.1.1.1) hw'
           (hc.insert_nonlinear (x := x) Finmap.notMem_empty hA)
         have htype := hvB x hx.1.1.1.2
         have htb := alignResult hw' hvb htype
           (by simpa only [Ty.openVar,Ty.erase_openRec,Term.erase,hB] using hTb)
         have hclosed := HasType.close_nllam hw.scoping hvA hxE htype htb
         rw [Ty.openVar,Ty.close_openVar x B hx.2] at hclosed
         exact ⟨(.nllam A (Term.closeRec 0 x eb),.piTy A B),
           congrArg₂ Surface.Term.nllam hA (Term.erase_close_of_open hx.1.2 heb),hT,
           ⟨hclosed⟩⟩
 termination_by structural h
end

/-- Every independently surface-typed term has an internal typed elaboration
in the given well-formed internal context. -/
theorem termExists : TermExists := by
  intro Δ ε hw e t h
  exact elaborateTerm h hw.toSourceContextWF (ContextEmbedding.refl Δ ε)

theorem spaceExists : SpaceExists := by
  intro Δ ε hw s h
  exact elaborateSpace h (wf_empty_linear hw.toSourceContextWF)
    (ContextEmbedding.refl Δ ε).with_empty_linear

theorem typeExists : TypeExists := by
  intro Δ ε hw t k h
  exact elaborateType h (wf_empty_linear hw.toSourceContextWF)
    (ContextEmbedding.refl Δ ε).with_empty_linear

theorem subspaceExists : SubspaceExists := by
  intro Δ ε hw s t h
  exact elaborateSubspace h (wf_empty_linear hw.toSourceContextWF)
    (ContextEmbedding.refl Δ ε).with_empty_linear

/-- Well-formed surface contexts admit well-formed internal reconstructions. -/
theorem contextExists : ContextExists := context_of_formation spaceExists typeExists

/-- Entirely surface-facing typing elaboration: reconstruct both the context
and the typed term. The premises contain no internal typing derivation. -/
theorem typing {d g e t} (hw : Surface.InductiveCtxWF d g)
    (h : Surface.HasType d g e t) :
    ∃ (D : LCtx) (E : NLCtx) (a : Term) (T : Ty),
      D.erase = d ∧ E.erase = g ∧ InductiveCtxWF D E ∧
      a.erase = e ∧ T.erase = t ∧ Nonempty (HasType D E a T) := by
  obtain ⟨⟨D,E⟩,hD,hE,hw'⟩ := contextExists hw
  obtain ⟨⟨a,T⟩,ha,hT,ht⟩ := termExists hw' (by simpa only [hD,hE] using h)
  exact ⟨D,E,a,T,hD,hE,hw',ha,hT,ht⟩

end SurfaceElaboration
end GLang
