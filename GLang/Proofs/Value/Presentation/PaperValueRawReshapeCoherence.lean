import GLang.Proofs.Value.Presentation.PaperValueRawCoherence
import GLang.Proofs.Value.Presentation.PaperValueMixedCodecs
import GLang.Proofs.Value.Presentation.PaperValueDependentReshape

namespace GLang.PaperValueDomains

/-- A supported class of raw binders, across a coherent family of worlds. -/
def RawArgumentClass (orc : FFSOracleSem) (d : ValTy) {I : Type 1}
    (w : I → World) (i : I) (v : ValValSem) :=
  {p : I × ValValSem // RuntimeRelated orc d (w i) (w p.1) v p.2}

def rawArgumentWorld (orc : FFSOracleSem) (d : ValTy) {I : Type 1}
    (w : I → World) (i : I) (v : ValValSem)
    (p : RawArgumentClass orc d w i v) : World :=
  (w p.val.1).rawPush d p.val.2

/-- Raw codomain formation supplies a coherent family for every supported
argument class, including checked and ordinary reifications. -/
theorem rawArgument_coherent (orc : FFSOracleSem) (d c : ValTy) {I : Type 1}
    (w : I → World) (hc : ∀ i j, RawTypeCoherent orc (.piTy d c) (w i) (w j))
    (i : I) (v : ValValSem) :
    ∀ p q : RawArgumentClass orc d w i v,
      RawTypeCoherent orc c (rawArgumentWorld orc d w i v p)
        (rawArgumentWorld orc d w i v q) := by
  intro p q
  exact (hc p.val.1 q.val.1).2 _ _
    (coherentFamily_runtime_trans orc d w
      (fun i j => (hc i j).1.toCoherent orc d _ _) _ _ _ _ _ _
      (runtime_related_symm orc d _ _ _ _ p.property) q.property)

/-- Pairwise raw formation of target and source types discharges every local
fibre condition of checked higher-order reshape. -/
theorem reshapeCoherent_of_rawFamilies (target source : ValTy) (orc : FFSOracleSem)
    {I J : Type 1} (sw : I → World) (tw : J → World)
    (hs : ∀ i j, RawTypeCoherent orc source (sw i) (sw j))
    (ht : ∀ i j, RawTypeCoherent orc target (tw i) (tw j))
    (i j : I) (k l : J) (he : (tw k).env = (sw i).env)
    (he' : (tw l).env = (sw j).env) :
    ReshapeCoherent orc target source (sw i) (sw j)
      (tw k).types (tw l).types (tw k).values (tw l).values := by
  have hw : (sw i).restack (tw k).types (tw k).values = tw k := by
    cases h : sw i; cases h' : tw k; simp_all [World.restack]
  have hw' : (sw j).restack (tw l).types (tw l).values = tw l := by
    cases h : sw j; cases h' : tw l; simp_all [World.restack]
  cases target with
  | space st =>
    cases source with
    | space ss =>
      simp only [ReshapeCoherent]
      change SpaceOracleAgreement _ _ st
      simpa only [← he, ← he'] using ht k l
    | piTy sd sc => simp only [ReshapeCoherent]
  | piTy td tc =>
    cases source with
    | space ss => simp only [ReshapeCoherent]
    | piTy sd sc =>
      simp only [ReshapeCoherent]
      rw [hw, hw']
      refine ⟨?_, ?_⟩
      · exact reshapeCoherent_of_rawFamilies sd td orc tw sw
          (fun i j => (ht i j).1) (fun i j => (hs i j).1) k l i j he.symm he'.symm
      intro a b hab argT argT' hargT hargT' hTT argS argS' _ _ hSS x y hx hy hxy
      have hsd := fun i j => (hs i j).1.toCoherent orc sd _ _
      have htd := fun i j => (ht i j).1.toCoherent orc td _ _
      have hSself := coherentFamily_runtime_trans orc sd sw hsd i j i argS argS' argS
        hSS (runtime_related_symm orc sd _ _ _ _ hSS)
      have hTself := coherentFamily_runtime_trans orc td tw htd k l k argT argT' argT
        hTT (runtime_related_symm orc td _ _ _ _ hTT)
      let s0 : RawArgumentClass orc sd sw i argS := ⟨⟨i,argS⟩,hSself⟩
      let s1 : RawArgumentClass orc sd sw i argS := ⟨⟨j,argS'⟩,hSS⟩
      let s2 : RawArgumentClass orc sd sw i argS :=
        ⟨⟨i,ValValSem.fromEl ((sw i).denot orc sd) x⟩,
          runtime_normalize_right orc sd _ _ _ _ hSself x hx⟩
      let s3 : RawArgumentClass orc sd sw i argS :=
        ⟨⟨j,ValValSem.fromEl ((sw j).denot orc sd) y⟩,
          runtime_normalize_right orc sd _ _ _ _ hSS y hy⟩
      have hamix := reify_mixed_related orc td (tw l) (tw k) b a
        (related_symm orc td _ _ _ _ hab)
      rw [hargT] at hamix
      have hamix' := runtime_related_symm orc td _ _ _ _ hamix
      have hamix0 := reify_mixed_related orc td (tw k) (tw k) a a
        ((coherentFamily_laws orc td tw htd).trans k l k a b a hab
          (related_symm orc td _ _ _ _ hab))
      rw [hargT] at hamix0
      let t0 : RawArgumentClass orc td tw k argT := ⟨⟨k,argT⟩,hTself⟩
      let t1 : RawArgumentClass orc td tw k argT := ⟨⟨l,argT'⟩,hTT⟩
      let t2 : RawArgumentClass orc td tw k argT :=
        ⟨⟨k,ValValSem.fromEl ((tw k).denot orc td) a⟩,
          runtime_related_symm orc td _ _ _ _ hamix0⟩
      let t3 : RawArgumentClass orc td tw k argT :=
        ⟨⟨l,ValValSem.fromEl ((tw l).denot orc td) b⟩,hamix'⟩
      have hsc := rawArgument_coherent orc sd sc sw hs i argS
      have htc := rawArgument_coherent orc td tc tw ht k argT
      refine ⟨?_, ?_, ?_⟩
      · exact coherentFamily_fiber orc sc (rawArgumentWorld orc sd sw i argS)
          (fun p q => (hsc p q).toCoherent orc sc _ _) s2 s3 s0 s1
      · have hf := coherentFamily_fiber orc tc (rawArgumentWorld orc td tw k argT)
          (fun p q => (htc p q).toCoherent orc tc _ _) t0 t1 t2 t3
        simpa only [rawArgumentWorld, t0, t1, t2, t3, World.rawPush, World.restack,
          World.push, ← he, ← he'] using hf
      · exact reshapeCoherent_of_rawFamilies tc sc orc
          (rawArgumentWorld orc sd sw i argS) (rawArgumentWorld orc td tw k argT)
          hsc htc s0 s1 t0 t1 he he'
termination_by sizeOf target + sizeOf source

/-- Same-world-family form used by the original typing induction. -/
theorem reshapeCoherent_of_rawFamily (target source : ValTy) (orc : FFSOracleSem)
    {I : Type} (w : I → World)
    (hs : ∀ i j, RawTypeCoherent orc source (w i) (w j))
    (ht : ∀ i j, RawTypeCoherent orc target (w i) (w j)) (i j : I) :
    ReshapeCoherent orc target source (w i) (w j)
      (w i).types (w j).types (w i).values (w j).values :=
  reshapeCoherent_of_rawFamilies target source orc
    (fun p : ULift.{1} I => w p.down) (fun p : ULift.{1} I => w p.down)
    (fun p q => hs p.down q.down) (fun p q => ht p.down q.down)
    ⟨i⟩ ⟨j⟩ ⟨i⟩ ⟨j⟩ rfl rfl

/-- Original evaluator reshape preserves related results from raw formation
coherence alone; all local representation obligations are derived. -/
theorem eval_reshape_related_of_rawFamily (target source : ValTy) (orc : FFSOracleSem)
    {I : Type} (w : I → World)
    (hs : ∀ i j, RawTypeCoherent orc source (w i) (w j))
    (ht : ∀ i j, RawTypeCoherent orc target (w i) (w j)) (i j : I)
    (e e' : ValExpr)
    (he : PartialRel (RuntimeRelated orc source (w i) (w j))
      (denotValB_semS orc (w i).env (w i).types (w i).values e)
      (denotValB_semS orc (w j).env (w j).types (w j).values e')) :
    PartialRel (RuntimeRelated orc target (w i) (w j))
      (denotValB_semS orc (w i).env (w i).types (w i).values (.reshap e target source))
      (denotValB_semS orc (w j).env (w j).types (w j).values (.reshap e' target source)) :=
  eval_reshape_dependent_related target source orc (w i) (w j) e e' he
    (reshapeCoherent_of_rawFamily target source orc w hs ht i j)

end GLang.PaperValueDomains
