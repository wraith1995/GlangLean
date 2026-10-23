import GLang.Proofs.Value.Partial.PartialValueFamilyBinders
import GLang.Proofs.Value.Partial.PartialValueCheckedRelation

namespace GLang.PartialValueDomains
open PaperValueDomains

/-- Raw arguments in one supported class across a coherent family. -/
def PartialRawArgumentClass (orc : PartialFFSOracleSem) (d : ValTy) {I : Type 1}
    (w : I → World) (i : I) (v : ValValSem) :=
  {p : I × ValValSem // WorldRuntimeRelated orc d (w i) (w p.1) v p.2}

def partialRawArgumentWorld (orc : PartialFFSOracleSem) (d : ValTy) {I : Type 1}
    (w : I → World) (i : I) (v : ValValSem)
    (p : PartialRawArgumentClass orc d w i v) : World :=
  ⟨(w p.val.1).env,d::(w p.val.1).types,p.val.2::(w p.val.1).values⟩

theorem partialRawArgument_coherent (orc : PartialFFSOracleSem) (d c : ValTy) {I : Type 1}
    (w : I → World) (hc : ∀ i j, PartialRawTypeCoherent orc (.piTy d c) (w i) (w j))
    (i : I) (v : ValValSem) :
    ∀ p q : PartialRawArgumentClass orc d w i v,
      PartialRawTypeCoherent orc c (partialRawArgumentWorld orc d w i v p)
        (partialRawArgumentWorld orc d w i v q) := by
  intro p q
  exact (hc p.val.1 q.val.1).2 _ _
    (partialRuntime_family_trans d (fun j => PartialWorldType orc (w j) d)
      (fun i j => (hc i j).1.toCoherent _ _ _ _) _ _ _ _ _ _
      (partialRuntimeRelated_symm d _ _ _ _ p.property) q.property)

/-- Related runtime functions map related structural arguments to related dependent results. -/
theorem partial_apply_runtime_related (orc : PartialFFSOracleSem) (d c : ValTy)
    (w w' : World) (v v' : ValValSem)
    (hv : WorldRuntimeRelated orc (.piTy d c) w w' v v')
    (a b : d.carrierEl)
    (hab : PartialRelated d (PartialWorldType orc w d) (PartialWorldType orc w' d) a b) :
    PartialRel (WorldRuntimeRelated orc c
      ⟨w.env,d::w.types,d.carrierToVal a::w.values⟩
      ⟨w'.env,d::w'.types,d.carrierToVal b::w'.values⟩)
      (v.applyTyped a) (v'.applyTyped b) := by
  cases hD : denotValTyPartial orc w.env w.types w.values d <;>
    cases hE : denotValTyPartial orc w'.env w'.types w'.values d <;>
    cases v <;> cases v' <;>
    simp only [WorldRuntimeRelated,PartialWorldType,denotValTyPartial,hD,hE,PartialRuntimeRelated] at hv
  all_goals try contradiction
  obtain ⟨hA,hB,hfg⟩ := hv
  subst_vars
  simpa only [ValValSem.applyTyped_fn] using (hfg a b (by
    simpa only [PartialWorldType,hD,hE] using hab))

/-- Paired partial reshape preserves recursive raw functions and latent errors;
all fibre transport follows from ordinary recursive formation coherence. -/
theorem partial_reshape_family (target source : ValTy) (orc : PartialFFSOracleSem)
    {I J : Type 1} (sw : I → World) (tw : J → World)
    (hs : ∀ i j, PartialRawTypeCoherent orc source (sw i) (sw j))
    (ht : ∀ i j, PartialRawTypeCoherent orc target (tw i) (tw j))
    (i j : I) (k l : J) (he : (tw k).env = (sw i).env) (he' : (tw l).env = (sw j).env)
    (v v' : ValValSem) (hv : WorldRuntimeRelated orc source (sw i) (sw j) v v') :
    PartialRel (WorldRuntimeRelated orc target (tw k) (tw l))
      (PartialValueEval.reshapeBetween orc (sw i).env (tw k).types (tw k).values
        (sw i).types (sw i).values v target source)
      (PartialValueEval.reshapeBetween orc (sw j).env (tw l).types (tw l).values
        (sw j).types (sw j).values v' target source) := by
  cases target with
  | space st =>
    cases source with
    | space ss =>
      cases v <;> cases v' <;> try exact False.elim hv
      rename_i a b
      have htarget := (PartialSpaceAgreement.observations _ _ st (ht k l)).2
      cases hns : ss.dofPartial (orc (sw i).env (sw i).types (sw i).values) <;>
        cases hns' : ss.dofPartial (orc (sw j).env (sw j).types (sw j).values) <;>
        simp only [WorldRuntimeRelated,PartialWorldType,denotValTyPartial,PartialRuntimeRelated,hns,hns',PartialRelated] at hv
      all_goals try contradiction
      rename_i ns ns'
      obtain ⟨rfl,ha,hb⟩ := hv
      have hn := ha.symm.trans hb
      change ns = ns' at hn
      change a.length = ns at ha
      subst ns'
      rw [←he] at hns
      rw [←he'] at hns'
      simp only [PartialValueEval.reshapeBetween,PartialValueEval.reshapeArray,←he,←he',hns,hns',htarget]
      cases hnt : st.dofPartial (orc (tw l).env (tw l).types (tw l).values) with
      | error e => trivial
      | ok nt =>
        simp only [ha,true_and]
        split
        · rename_i hn
          simp only [PartialRel,WorldRuntimeRelated,PartialWorldType,denotValTyPartial,
            PartialRuntimeRelated,htarget,hnt,PartialRelated]
          exact ⟨trivial,ha.trans hn,ha.trans hn⟩
        · trivial
    | piTy sd sc =>
      cases v <;> cases v' <;> simp only [PartialValueEval.reshapeBetween,PartialRel]
  | piTy td tc =>
    cases source with
    | space ss => simp only [PartialValueEval.reshapeBetween,PartialRel]
    | piTy sd sc =>
      have hv0 := hv
      have htd := (ht k l).1.toCoherent orc td _ _
      have hsd := (hs i j).1.toCoherent orc sd _ _
      cases hDS : denotValTyPartial orc (sw i).env (sw i).types (sw i).values sd <;>
        cases hES : denotValTyPartial orc (sw j).env (sw j).types (sw j).values sd <;>
        simp only [WorldRuntimeRelated,PartialWorldType,denotValTyPartial,hDS,hES] at hv
      all_goals try (cases v <;> cases v' <;> exact False.elim hv)
      rename_i DS ES
      have hDS' := hDS
      have hES' := hES
      rw [←he] at hDS'
      rw [←he'] at hES'
      simp only [PartialValueEval.reshapeBetween,←he,←he',hDS',hES']
      cases hDT : denotValTyPartial orc (tw k).env (tw k).types (tw k).values td <;>
        cases hET : denotValTyPartial orc (tw l).env (tw l).types (tw l).values td
      · trivial
      · cases td <;> simp only [PartialWorldType,hDT,hET,PartialCoherent] at htd
      · cases td <;> simp only [PartialWorldType,hDT,hET,PartialCoherent] at htd
      rename_i DT ET
      simp only [PartialRel,WorldRuntimeRelated,PartialWorldType,denotValTyPartial,hDT,hET,PartialRuntimeRelated]
      refine ⟨rfl,rfl,?_⟩
      intro a b hab
      have hcheck := validate_related td (.ok DT) (.ok ET) (by simpa only [PartialWorldType,hDT,hET] using htd)
        (.ok a) (.ok b) hab
      have hmix := validate_related_right td (.ok DT) (.ok ET) (by simpa only [PartialWorldType,hDT,hET] using htd)
        (.ok a) (.ok b) hab
      simp only [validate,Except.bind] at hcheck hmix
      cases hca : DT.check a <;> cases hcb : ET.check b <;> simp only [hca,hcb,PartialRel] at hcheck hmix ⊢
      rename_i a' b'
      have harg : WorldRuntimeRelated orc td (tw k) (tw l) (td.carrierToVal a') (td.carrierToVal b') :=
        partial_reify_related td _ _ a' b' (by simpa only [PartialWorldType,hDT,hET] using hcheck)
      have hdom := partial_reshape_family sd td orc tw sw (fun i j => (ht i j).1) (fun i j => (hs i j).1)
        k l i j he.symm he'.symm _ _ harg
      cases hsa : PartialValueEval.reshapeBetween orc (sw i).env (sw i).types (sw i).values
          (tw k).types (tw k).values (td.carrierToVal a') sd td <;>
        cases hsb : PartialValueEval.reshapeBetween orc (sw j).env (sw j).types (sw j).values
          (tw l).types (tw l).values (td.carrierToVal b') sd td
      all_goals simp only [he,he',hsa,hsb,PartialRel] at hdom ⊢
      rename_i argS argS'
      obtain ⟨x,y,hx,hy,hxy⟩ := partial_extract_related sd _ _ _ _ hdom
      rw [hx,hy]
      have happ := partial_apply_runtime_related orc sd sc (sw i) (sw j) v v' hv0 x y hxy
      cases hpa : v.applyTyped x <;> cases hpb : v'.applyTyped y <;>
        simp only [hpa,hpb,PartialRel] at happ ⊢
      rename_i res res'
      have hss := partialRuntime_family_trans sd (fun i => PartialWorldType orc (sw i) sd)
        (fun i j => (hs i j).1.toCoherent _ _ _ _) i j i argS argS' argS hdom
        (partialRuntimeRelated_symm sd _ _ _ _ hdom)
      let s0 : PartialRawArgumentClass orc sd sw i argS := ⟨⟨i,argS⟩,hss⟩
      let s1 : PartialRawArgumentClass orc sd sw i argS := ⟨⟨j,argS'⟩,hdom⟩
      let s2 : PartialRawArgumentClass orc sd sw i argS := ⟨⟨i,sd.carrierToVal x⟩,
        partialRuntime_normalize_right sd _ _ _ _ hss x hx⟩
      let s3 : PartialRawArgumentClass orc sd sw i argS := ⟨⟨j,sd.carrierToVal y⟩,
        partialRuntime_normalize_right sd _ _ _ _ hdom y hy⟩
      let SC := partialRawArgumentWorld orc sd sw i argS
      have hsc := partialRawArgument_coherent orc sd sc sw hs i argS
      have hres := partialRuntime_family_transport sc (fun p => PartialWorldType orc (SC p) sc)
        (fun p q => (hsc p q).toCoherent _ _ _ _) s2 s3 s0 s1 res res' happ
      have hab' : PartialRelated td (PartialWorldType orc (tw k) td) (PartialWorldType orc (tw l) td) a b :=
        by simpa only [PartialWorldType,hDT,hET] using hab
      have haa := (partialFamily_laws td (fun k => PartialWorldType orc (tw k) td)
        (fun k l => (ht k l).1.toCoherent _ _ _ _)).trans k l k a b a hab'
        (partialRelated_symm td _ _ _ _ hab')
      have hca' := validate_related_right td _ _ ((ht k k).1.toCoherent _ _ _ _) (.ok a) (.ok a) haa
      simp only [PartialWorldType,hDT,validate,Except.bind,hca,PartialRel] at hca'
      let t0 : PartialRawArgumentClass orc td tw k (td.carrierToVal a) := ⟨⟨k,td.carrierToVal a'⟩,
        partial_reify_related td _ _ a a' (by simpa only [PartialWorldType,hDT] using hca')⟩
      let t1 : PartialRawArgumentClass orc td tw k (td.carrierToVal a) := ⟨⟨l,td.carrierToVal b'⟩,
        partial_reify_related td _ _ a b' (by simpa only [PartialWorldType,hDT,hET] using hmix)⟩
      let t2 : PartialRawArgumentClass orc td tw k (td.carrierToVal a) := ⟨⟨k,td.carrierToVal a⟩,
        partial_reify_related td _ _ a a haa⟩
      let t3 : PartialRawArgumentClass orc td tw k (td.carrierToVal a) := ⟨⟨l,td.carrierToVal b⟩,
        partial_reify_related td _ _ a b hab'⟩
      let TC := partialRawArgumentWorld orc td tw k (td.carrierToVal a)
      have htc := partialRawArgument_coherent orc td tc tw ht k (td.carrierToVal a)
      have hout := partial_reshape_family tc sc orc SC TC hsc htc s0 s1 t0 t1 he he' res res' hres
      have hm := PartialRel.map (fun v => v) (fun v => v)
        (fun r r' hr => partialRuntime_family_transport tc (fun p => PartialWorldType orc (TC p) tc)
          (fun p q => (htc p q).toCoherent _ _ _ _) t0 t1 t2 t3 r r' hr) hout
      simp only [SC,TC,s0,s1,t0,t1,t2,t3,partialRawArgumentWorld,←he,←he'] at hm
      cases hlo : PartialValueEval.reshapeBetween orc (tw k).env (td::(tw k).types)
          (td.carrierToVal a'::(tw k).values) (sd::(sw i).types) (argS::(sw i).values) res tc sc <;>
        cases hro : PartialValueEval.reshapeBetween orc (tw l).env (td::(tw l).types)
          (td.carrierToVal b'::(tw l).values) (sd::(sw j).types) (argS'::(sw j).values) res' tc sc <;>
        simpa only [←he,←he',hlo,hro,Except.map,PartialRel] using hm
termination_by sizeOf target + sizeOf source

/-- The live reshape constructor, with formation coherence obtained from the
original source and target type induction hypotheses. -/
theorem partial_eval_reshape_related_of_rawFamily (target source : ValTy) (orc : PartialFFSOracleSem)
    {I : Type} (w : I → World)
    (hs : ∀ i j, PartialRawTypeCoherent orc source (w i) (w j))
    (ht : ∀ i j, PartialRawTypeCoherent orc target (w i) (w j))
    (i j : I) (e e' : ValExpr)
    (hei : ValExpr.inferTypeCtx (w i).types e = source)
    (hej : ValExpr.inferTypeCtx (w j).types e' = source)
    (hr : PartialRel (WorldRuntimeRelated orc source (w i) (w j))
      (denotValB_partial orc (w i).env (w i).types (w i).values e)
      (denotValB_partial orc (w j).env (w j).types (w j).values e')) :
    PartialRel (WorldRuntimeRelated orc target (w i) (w j))
      (denotValB_partial orc (w i).env (w i).types (w i).values (.reshap e target source))
      (denotValB_partial orc (w j).env (w j).types (w j).values (.reshap e' target source)) := by
  simp only [denotValB_partial, hei, hej, PartialValueEval.reshapeInferred_self]
  cases hl : denotValB_partial orc (w i).env (w i).types (w i).values e <;>
    cases he : denotValB_partial orc (w j).env (w j).types (w j).values e' <;>
    simp only [hl,he,PartialRel] at hr ⊢
  simpa only [PartialRel] using (partial_reshape_family target source orc (fun p : ULift.{1} I => w p.down)
    (fun p : ULift.{1} I => w p.down) (fun p q => hs p.down q.down) (fun p q => ht p.down q.down)
    ⟨i⟩ ⟨j⟩ ⟨i⟩ ⟨j⟩ rfl rfl _ _ hr)

end GLang.PartialValueDomains
