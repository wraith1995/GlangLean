import GLang.Elaboration.Bases

namespace GLang.SurfacePaper
open Surface
open SurfaceElaboration

/-- Regularity also holds for a linear subcontext of a well-formed context. -/
theorem regular_subcontext {d d' g e t}
    (hw : Surface.InductiveCtxWF d g)
    (hsub : ∀ x s, d'.lookup x = some s → d.lookup x = some s)
    (h : Surface.HasType d' g e t) :
    ∃ k, Nonempty (Surface.TValid g t k) := by
  obtain ⟨⟨D,E⟩,hD,hE,hw'⟩ := contextExists hw
  have hc : ContextEmbedding d g D E := by
    simpa only [hD,hE] using ContextEmbedding.refl D E
  have hwR := restrictSource_wf hw'.toSourceContextWF d'.keys
  obtain ⟨⟨a,T⟩,_,hT,ht⟩ := elaborateTerm h hwR (hc.restrict d' hsub)
  obtain ⟨k,hk⟩ := resultValid hwR ht.some
  exact ⟨k, ⟨by simpa only [hE,hT] using hk.toSurface⟩⟩

theorem regular {d g e t} (hw : Surface.InductiveCtxWF d g)
    (h : Surface.HasType d g e t) :
    ∃ k, Nonempty (Surface.TValid g t k) :=
  regular_subcontext hw (fun _ _ hs => hs) h

noncomputable def spaceValid_subcontext {d d' g e s}
    (hw : Surface.InductiveCtxWF d g)
    (hsub : ∀ x s, d'.lookup x = some s → d.lookup x = some s)
    (h : Surface.HasType d' g e (.space s)) : Surface.SValid g s := by
  have hv := regular_subcontext hw hsub h
  generalize hk : Classical.choose hv = k at *
  have ht : Surface.TValid g (.space s) k :=
    (hk ▸ Classical.choose_spec hv).some
  cases ht with | space hs => exact hs

noncomputable def spaceValid {d g e s}
    (hw : Surface.InductiveCtxWF d g)
    (h : Surface.HasType d g e (.space s)) : Surface.SValid g s :=
  spaceValid_subcontext hw (fun _ _ hs => hs) h

noncomputable def spaceValid_left {d₀ d₁ g e s}
    (hw : Surface.InductiveCtxWF (d₀ ∪ d₁) g)
    (h : Surface.HasType d₀ g e (.space s)) : Surface.SValid g s :=
  spaceValid_subcontext hw (fun _ _ hs => by
    rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some hs)]; exact hs) h

noncomputable def spaceValid_right {d₀ d₁ g e s}
    (hw : Surface.InductiveCtxWF (d₀ ∪ d₁) g)
    (hd : Finmap.Disjoint d₀ d₁)
    (h : Surface.HasType d₁ g e (.space s)) : Surface.SValid g s :=
  spaceValid_subcontext hw (fun x _ hs => by
    rw [Finmap.lookup_union_right
      (fun hx => hd x hx (Finmap.mem_of_lookup_eq_some hs))]; exact hs) h

def dualValid {g s} (h : Surface.SValid g (.dual s)) : Surface.SValid g s := by
  cases h with | dual hs => exact hs

def tensorValid {g s t} (h : Surface.SValid g (.tprod s t)) :
    Surface.SValid g s × Surface.SValid g t := by
  cases h with | tprod hs ht => exact ⟨hs,ht⟩

noncomputable def mapValid {d g e s t} (hw : Surface.InductiveCtxWF d g)
    (h : Surface.HasType d g e (.space (.tprod (.dual s) t))) :
    Surface.SValid g s × Surface.SValid g t :=
  let hv := tensorValid (spaceValid hw h)
  ⟨dualValid hv.1,hv.2⟩

noncomputable def ker {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Surface.SValid g (.ker e) :=
  let hv := mapValid hw h
  .ker hv.1 hv.2 h

noncomputable def sub_ker {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Surface.SubType g (.ker e) s :=
  let hv := mapValid hw h
  .sub_ker hv.1 hv.2 h

noncomputable def coker {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Surface.SValid g (.coker e) :=
  let hv := mapValid hw h
  .coker hv.1 hv.2 h

noncomputable def sub_coker {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Surface.SubType g (.coker e) s :=
  let hv := mapValid hw h
  .sub_coker hv.1 hv.2 h

noncomputable def img {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Surface.SValid g (.img e) :=
  let hv := mapValid hw h
  .img hv.1 hv.2 h

noncomputable def sub_img {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Surface.SubType g (.img e) t :=
  let hv := mapValid hw h
  .sub_img hv.1 hv.2 h

noncomputable def coimg {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Surface.SValid g (.coimg e) :=
  let hv := mapValid hw h
  .coimg hv.1 hv.2 h

noncomputable def sub_coimg {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Surface.SubType g (.coimg e) t :=
  let hv := mapValid hw h
  .sub_coimg hv.1 hv.2 h

noncomputable def add {d g a b s} (hw : Surface.InductiveCtxWF d g)
    (ha : Surface.HasType d g a (.space s))
    (hb : Surface.HasType d g b (.space s)) :
    Surface.HasType d g (.add a b) (.space s) :=
  .add (spaceValid hw ha) ha hb

noncomputable def smul {d₀ d₁ g a b s}
    (hw : Surface.InductiveCtxWF (d₀ ∪ d₁) g) (hd : Finmap.Disjoint d₀ d₁)
    (ha : Surface.HasType d₀ g a (.space .real))
    (hb : Surface.HasType d₁ g b (.space s)) :
    Surface.HasType (d₀ ∪ d₁) g (.smul a b) (.space s) :=
  .smul (spaceValid_right hw hd hb) hd ha hb

noncomputable def app_linear {d₀ d₁ g a b s t}
    (hw : Surface.InductiveCtxWF (d₀ ∪ d₁) g) (hd : Finmap.Disjoint d₀ d₁)
    (ha : Surface.HasType d₀ g a (.space (.tprod (.dual s) t)))
    (hb : Surface.HasType d₁ g b (.space s)) :
    Surface.HasType (d₀ ∪ d₁) g (.app a b) (.space t) :=
  let hv := tensorValid (spaceValid_left hw ha)
  .app_linear (dualValid hv.1) hv.2 hd ha hb

noncomputable def app_inner {d₀ d₁ g a b s}
    (hw : Surface.InductiveCtxWF (d₀ ∪ d₁) g) (hd : Finmap.Disjoint d₀ d₁)
    (ha : Surface.HasType d₀ g a (.space (.dual s)))
    (hb : Surface.HasType d₁ g b (.space s)) :
    Surface.HasType (d₀ ∪ d₁) g (.app a b) (.space .real) :=
  .app_inner (dualValid (spaceValid_left hw ha)) hd ha hb

noncomputable def pinv_tensor {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Surface.HasType ∅ g (.pinv e) (.space (.tprod (.dual t) s)) :=
  let hv := mapValid hw h
  .pinv_tensor hv.1 hv.2 h

noncomputable def pinv_dual {g e s} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.dual s))) :
    Surface.HasType ∅ g (.pinv e) (.space (.tprod (.dual .real) s)) :=
  .pinv_dual (dualValid (spaceValid hw h)) h

noncomputable def dsumE {d g a b s t} (hw : Surface.InductiveCtxWF d g)
    (ha : Surface.HasType d g a (.space s))
    (hb : Surface.HasType d g b (.space t)) :
    Surface.HasType d g (.dsumE a b) (.space (.dsum s t)) :=
  .dsumE (spaceValid hw ha) (spaceValid hw hb) ha hb

noncomputable def tprodE {d₀ d₁ g a b s t}
    (hw : Surface.InductiveCtxWF (d₀ ∪ d₁) g) (hd : Finmap.Disjoint d₀ d₁)
    (ha : Surface.HasType d₀ g a (.space s))
    (hb : Surface.HasType d₁ g b (.space t)) :
    Surface.HasType (d₀ ∪ d₁) g (.tprodE a b) (.space (.tprod s t)) :=
  .tprodE (spaceValid_left hw ha) (spaceValid_right hw hd hb) hd ha hb

theorem elaborate_unique {Δ ε e t} (hw : GLang.InductiveCtxWF Δ ε)
    (h : Surface.HasType Δ.erase ε.erase e t) :
    ∃! p, TermLift Δ ε e t p := by
  obtain ⟨p,hp⟩ := termExists hw h
  exact ⟨p,hp,fun _ hq => termLift_unique hw hq hp⟩

theorem typing_unique {d g e t} (hw : Surface.InductiveCtxWF d g)
    (h : Surface.HasType d g e t) :
    ∃ (D : GLang.LCtx) (E : GLang.NLCtx),
      D.erase = d ∧ E.erase = g ∧ GLang.InductiveCtxWF D E ∧
      ∃! p, TermLift D E e t p := by
  obtain ⟨⟨D,E⟩,hD,hE,hw'⟩ := contextExists hw
  exact ⟨D,E,hD,hE,hw',elaborate_unique hw' (by simpa only [hD,hE] using h)⟩

end GLang.SurfacePaper
