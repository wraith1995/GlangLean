import GLang.Proofs.Progress.CheckedErasure
import GLang.Graded.SourceSubst
import GLang.Graded.SourceWeaken
import GLang.Proofs.Preservation.ValuePreservationV2
import GLang.Proofs.Source.Soundness

/-!
# Source substitution for checked operational certificates

The checked operational substitution proof needs to rewrite the source typing
evidence stored in every certificate node.  The source contexts below keep the
original, fresh nonlinear context fixed as the ambient context of the existing
axiom-free graded substitution theorem.  Dependent binders may then be added to
the source and target contexts in lockstep.
-/

namespace GLang
namespace RawCertifiedSourceSubst

open GLang.Graded

/-! ## Substitution on finite source contexts -/

/-- Apply source substitution to every space stored in a linear context. -/
def LCtx.substMap (x : Name) (n : Term) (Delta : LCtx) : LCtx where
  entries := Delta.entries.map
    (fun p : Sigma (fun _ : Name => Space) =>
      (Sigma.mk p.1 (Space.subst x n p.2) : Sigma (fun _ : Name => Space)))
  nodupKeys := by
    have h :
        (Delta.entries.map
          (fun p : Sigma (fun _ : Name => Space) =>
            (Sigma.mk p.1 (Space.subst x n p.2) : Sigma (fun _ : Name => Space)))).keys
          = Delta.entries.keys := by
      show (Delta.entries.map _).map Sigma.fst = Delta.entries.map Sigma.fst
      rw [Multiset.map_map]
      rfl
    rw [<- Multiset.nodup_keys, h]
    exact Multiset.nodup_keys.mpr Delta.nodupKeys

@[simp] theorem LCtx.substMap_keys (x : Name) (n : Term) (Delta : LCtx) :
    (LCtx.substMap x n Delta).keys = Delta.keys := by
  unfold Finmap.keys LCtx.substMap
  congr 1
  show (Delta.entries.map _).map Sigma.fst = Delta.entries.map Sigma.fst
  rw [Multiset.map_map]
  rfl

theorem LCtx.mem_substMap_iff (x : Name) (n : Term) (Delta : LCtx) (z : Name) :
    z ∈ LCtx.substMap x n Delta <-> z ∈ Delta := by
  rw [<- Finmap.mem_keys, <- Finmap.mem_keys, LCtx.substMap_keys]

theorem LCtx.substMap_lookup (x : Name) (n : Term) (Delta : LCtx)
    (z : Name) (s : Space) (h : Delta.lookup z = some s) :
    (LCtx.substMap x n Delta).lookup z = some (Space.subst x n s) := by
  rw [Finmap.lookup_eq_some_iff] at h ⊢
  show (Sigma.mk z (Space.subst x n s) : Sigma (fun _ : Name => Space)) ∈
    Delta.entries.map
      (fun p : Sigma (fun _ : Name => Space) =>
        (Sigma.mk p.1 (Space.subst x n p.2) : Sigma (fun _ : Name => Space)))
  rw [Multiset.mem_map]
  exact ⟨Sigma.mk z s, h, rfl⟩

theorem LCtx.substMap_lookup_none (x : Name) (n : Term) (Delta : LCtx)
    (z : Name) (h : Delta.lookup z = none) :
    (LCtx.substMap x n Delta).lookup z = none := by
  rw [Finmap.lookup_eq_none, LCtx.mem_substMap_iff, <- Finmap.lookup_eq_none]
  exact h

@[simp] theorem LCtx.substMap_empty (x : Name) (n : Term) :
    LCtx.substMap x n (∅ : LCtx) = ∅ := by
  apply Finmap.ext_lookup
  intro z
  exact LCtx.substMap_lookup_none x n ∅ z (Finmap.lookup_empty z)

theorem LCtx.substMap_insert (x : Name) (n : Term) (Delta : LCtx)
    (z : Name) (s : Space) :
    LCtx.substMap x n (Finmap.insert z s Delta) =
      Finmap.insert z (Space.subst x n s) (LCtx.substMap x n Delta) := by
  apply Finmap.ext_lookup
  intro w
  by_cases hwz : w = z
  · subst w
    rw [LCtx.substMap_lookup x n _ z s (by rw [Finmap.lookup_insert]),
      Finmap.lookup_insert]
  · rw [Finmap.lookup_insert_of_ne _ hwz]
    cases hlook : Delta.lookup w with
    | none =>
        rw [LCtx.substMap_lookup_none x n _ w (by
          rw [Finmap.lookup_insert_of_ne _ hwz]
          exact hlook)]
        exact (LCtx.substMap_lookup_none x n Delta w hlook).symm
    | some sw =>
        rw [LCtx.substMap_lookup x n _ w sw (by
          rw [Finmap.lookup_insert_of_ne _ hwz]
          exact hlook)]
        exact (LCtx.substMap_lookup x n Delta w sw hlook).symm

theorem LCtx.substMap_singleton (x : Name) (n : Term) (z : Name) (s : Space) :
    LCtx.substMap x n (Finmap.singleton z s) =
      Finmap.singleton z (Space.subst x n s) := by
  rw [show (Finmap.singleton z s : LCtx) = Finmap.insert z s ∅ by rfl,
    LCtx.substMap_insert, LCtx.substMap_empty]
  rfl

theorem LCtx.substMap_union (x : Name) (n : Term) (Delta0 Delta1 : LCtx) :
    LCtx.substMap x n (Delta0 ∪ Delta1) =
      LCtx.substMap x n Delta0 ∪ LCtx.substMap x n Delta1 := by
  apply Finmap.ext_lookup
  intro z
  by_cases hz0 : z ∈ Delta0
  · obtain ⟨s, hs⟩ := Finmap.mem_iff.mp hz0
    rw [Finmap.lookup_union_left ((LCtx.mem_substMap_iff x n Delta0 z).mpr hz0),
      LCtx.substMap_lookup x n Delta0 z s hs,
      LCtx.substMap_lookup x n (Delta0 ∪ Delta1) z s
        (by rw [Finmap.lookup_union_left hz0]; exact hs)]
  · rw [Finmap.lookup_union_right ((LCtx.mem_substMap_iff x n Delta0 z).not.mpr hz0)]
    cases hlook : Delta1.lookup z with
    | none =>
        have hu : (Delta0 ∪ Delta1).lookup z = none := by
          rw [Finmap.lookup_union_right hz0]
          exact hlook
        rw [LCtx.substMap_lookup_none x n (Delta0 ∪ Delta1) z hu,
          LCtx.substMap_lookup_none x n Delta1 z hlook]
    | some s =>
        rw [LCtx.substMap_lookup x n Delta1 z s hlook,
          LCtx.substMap_lookup x n (Delta0 ∪ Delta1) z s
            (by rw [Finmap.lookup_union_right hz0]; exact hlook)]

theorem LCtx.substMap_disjoint (x : Name) (n : Term) {Delta0 Delta1 : LCtx}
    (h : Finmap.Disjoint Delta0 Delta1) :
    Finmap.Disjoint (LCtx.substMap x n Delta0) (LCtx.substMap x n Delta1) := by
  intro z hz0 hz1
  exact h z ((LCtx.mem_substMap_iff x n Delta0 z).mp hz0)
    ((LCtx.mem_substMap_iff x n Delta1 z).mp hz1)

/-! ## A dependent nonlinear cut world -/

/--
`SourceCutCtx x n tauX Gamma0 GammaS GammaT` says that `GammaS` is a source
context containing the distinguished nonlinear variable `x : tauX`, while
`GammaT` is the context obtained after cutting `x` out with `n`.  `Gamma0` is
the fixed fresh ambient context in which `n` is typed.  Keeping `Gamma0` fixed
is essential: dependent binder entries in `GammaS` are rewritten on the target
side and therefore need not literally agree with their source versions.
-/
structure SourceCutCtx (x : Name) (n : Term) (tauX : Ty)
    (Gamma0 GammaS GammaT : NLCtx) : Type where
  data : GSubstData x n Gamma0 tauX
  tinv : TInv x tauX Gamma0 (asTypeCtx GammaS)
  /-- The computed type context may be smaller than the selected checked target.
  This slack is what makes the relation stable under non-linear weakening
  (`C.*.weaken`) and under the extended conclusion context of `C.Term.promote`. -/
  target : SubMap (tsubstCtx x n Gamma0 (asTypeCtx GammaS)) (asTypeCtx GammaT)

private theorem asTypeCtx_lookup {Gamma : NLCtx} {z : Name} {tau : Ty}
    (h : Gamma.lookup z = some tau) : asTypeCtx Gamma z = some tau := h

/-- Build the root cut world from exactly the application-cut hypotheses. -/
noncomputable def SourceCutCtx.root {x : Name} {n : Term} {tauX : Ty}
    {Gamma : NLCtx} (hwf : V2.CtxWF' ∅ Gamma) (hxGamma : x ∉ Gamma)
    (harg : HasType ∅ Gamma n tauX) :
    SourceCutCtx x n tauX Gamma (Finmap.insert x tauX Gamma) Gamma := by
  have hxlook : Gamma.lookup x = none := Finmap.lookup_eq_none.mpr hxGamma
  have hcd : CtxDisj (∅ : LCtx) Gamma := CtxDisj.empty Gamma
  have hctx : CtxValid (tr (∅ : LCtx) Gamma) :=
    ctxValid_tr hcd
      (fun z s h => Classical.choice (hwf.lin_valid z s h))
      (fun z tau h => by
        let hex := hwf.nl_valid z tau h
        exact ⟨Classical.choose hex, Classical.choice (Classical.choose_spec hex)⟩)
  obtain ⟨k, htauX⟩ := hasType_regular hcd hctx harg
  have hxfv : x ∉ Ty.fv tauX := by
    intro hx
    exact hxGamma (Finmap.mem_keys.mp (TValid.fv_closure htauX hx))
  have hGammaFresh : ∀ z tau, Gamma.lookup z = some tau -> x ∉ Ty.fv tau := by
    intro z tau hz hxfvTau
    exact hxGamma (Finmap.mem_keys.mp (hwf.nl_fv z tau hz hxfvTau))
  have htinv : TInv x tauX Gamma
      (asTypeCtx (Finmap.insert x tauX Gamma)) := by
    rw [asTypeCtx_insert]
    refine ⟨?_, ?_⟩
    · intro z tau hz tau' hu
      by_cases hzx : z = x
      · subst z
        rw [hxlook] at hz
        contradiction
      · rw [Function.update_of_ne hzx] at hu
        exact Option.some.inj (hz.symm.trans hu)
    · intro tau hu
      rw [Function.update_self] at hu
      exact (Option.some.inj hu).symm
  exact
    { data :=
        { lc := harg.lc
          argTyped := hasTypeBridge hcd harg
          yfvτ0 := hxfv
          ynε := hxlook
          εfresh := hGammaFresh }
      tinv := htinv
      target := by
        rw [asTypeCtx_insert]
        rw [tsubstCtx_update_asTypeCtx hxlook hGammaFresh]
        exact fun _ _ h => h }

/-- Extend a cut world under a fresh dependent nonlinear binder. -/
def SourceCutCtx.extendNL
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 GammaS GammaT : NLCtx}
    (w : SourceCutCtx x n tauX Gamma0 GammaS GammaT)
    (z : Name) (tau : Ty) (hzx : z ≠ x) (hz0 : Gamma0.lookup z = none) :
    SourceCutCtx x n tauX Gamma0
      (Finmap.insert z tau GammaS)
      (Finmap.insert z (Ty.subst x n tau) GammaT) := by
  refine
    { data := w.data
      tinv := ?_
      target := ?_ }
  · rw [asTypeCtx_insert]
    exact w.tinv.update hzx hz0
  · rw [asTypeCtx_insert, asTypeCtx_insert, tsubstCtx_update hzx]
    exact submap_update w.target z (some (Ty.subst x n tau))

private theorem tsubstCtx_submap_of_tinv
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 : NLCtx}
    {f f' : Name -> Option Ty}
    (hsub : SubMap f f') (hinv : TInv x tauX Gamma0 f') :
    SubMap (tsubstCtx x n Gamma0 f) (tsubstCtx x n Gamma0 f') := by
  intro z tau hlook
  by_cases hzx : z = x
  · subst z
    simp only [tsubstCtx] at hlook
    contradiction
  · simp only [tsubstCtx, if_neg hzx] at hlook ⊢
    cases hf : f z with
    | some tauF =>
        have hf' : f' z = some tauF := hsub z tauF hf
        rw [hf] at hlook
        rw [hf']
        exact hlook
    | none =>
        rw [hf] at hlook
        cases h0 : Gamma0.lookup z with
        | none =>
            rw [h0] at hlook
            contradiction
        | some tau0 =>
            rw [h0] at hlook
            cases hf' : f' z with
            | none =>
                simpa only [Option.orElse_none, Option.map_some] using hlook
            | some tau' =>
                have heq : tau0 = tau' := hinv.1 z tau0 h0 tau' hf'
                subst tau'
                simpa only [Option.orElse_some, Option.map_some] using hlook

/-- Restrict the source side along nonlinear inclusion while retaining the
same (possibly larger) target.  This is the context operation needed wherever
a checked node's conclusion context strictly extends its premise context: the
generalized `C.Term.promote` rule and the admissible weakening `C.*.weaken`. -/
def SourceCutCtx.pullSource
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 GammaS GammaT GammaSmall : NLCtx}
    (w : SourceCutCtx x n tauX Gamma0 GammaS GammaT)
    (hle : NLCtxIncl GammaSmall GammaS) :
    SourceCutCtx x n tauX Gamma0 GammaSmall GammaT := by
  have hsub : SubMap (asTypeCtx GammaSmall) (asTypeCtx GammaS) := hle
  have hinv : TInv x tauX Gamma0 (asTypeCtx GammaSmall) := by
    refine ⟨?_, ?_⟩
    · intro z tau hz tau' hs
      exact w.tinv.1 z tau hz tau' (hsub z tau' hs)
    · intro tau hs
      exact w.tinv.2 tau (hsub x tau hs)
  exact
    { data := w.data
      tinv := hinv
      target := fun z tau hz =>
        w.target z tau (tsubstCtx_submap_of_tinv hsub w.tinv z tau hz) }

/-- Every ambient binding used to type the cut argument remains available in
the selected target nonlinear context.  This is the checked-term weakening
fact needed at a distinguished-variable leaf. -/
def SourceCutCtx.ambientIncl
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 GammaS GammaT : NLCtx}
    (w : SourceCutCtx x n tauX Gamma0 GammaS GammaT) :
    NLCtxIncl Gamma0 GammaT := by
  intro z tau h0
  apply w.target z tau
  have hzx : z ≠ x := by
    rintro rfl
    rw [w.data.ynε] at h0
    contradiction
  simp only [tsubstCtx, if_neg hzx, asTypeCtx]
  cases hs : GammaS.lookup z with
  | none =>
      rw [h0]
      simp only [Option.orElse_none, Option.map_some]
      exact congrArg some (Ty.subst_fresh x n tau (w.data.εfresh z tau h0))
  | some tauS =>
      have heq : tau = tauS := w.tinv.1 z tau h0 tauS hs
      subst tauS
      simp only [Option.orElse_some, Option.map_some]
      exact congrArg some (Ty.subst_fresh x n tau (w.data.εfresh z tau h0))

/-- Source-space validity transported through a nonlinear cut world. -/
noncomputable def SourceCutCtx.svalid
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 GammaS GammaT : NLCtx}
    (w : SourceCutCtx x n tauX Gamma0 GammaS GammaT)
    {s : Space} (h : SValid GammaS s) :
    SValid GammaT (Space.subst x n s) := by
  have hg := gsvalid_subst w.data w.tinv (svalidBridge h)
  exact svalidBwd hg w.target

/-- Source-type validity transported through a nonlinear cut world. -/
noncomputable def SourceCutCtx.tvalid
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 GammaS GammaT : NLCtx}
    (w : SourceCutCtx x n tauX Gamma0 GammaS GammaT)
    {tau : Ty} {k : Kind} (h : TValid GammaS tau k) :
    TValid GammaT (Ty.subst x n tau) k := by
  have hg := gtvalid_subst w.data w.tinv (tvalidBridge h)
  exact tvalidBwd hg w.target

/-- Term typing at an empty linear context transported through a type cut
world.  This is the form used by FFS witnesses inside `BasisValid`. -/
noncomputable def SourceCutCtx.hasTypeEmpty
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 GammaS GammaT : NLCtx}
    (w : SourceCutCtx x n tauX Gamma0 GammaS GammaT)
    {e : Term} {tau : Ty} (h : HasType ∅ GammaS e tau) :
    HasType ∅ GammaT (Term.subst x n e) (Ty.subst x n tau) := by
  have hsrc : GInv x tauX Gamma0 (tr (∅ : LCtx) GammaS) := by
    rw [tr_empty_resurrect]
    exact w.tinv.toResurrect
  have hg := ghastype_subst w.data hsrc
    (hasTypeBridge (CtxDisj.empty GammaS) h)
  have htarget : TrGe
      (gsubstCtx x n Gamma0 (tr (∅ : LCtx) GammaS))
      (∅ : LCtx) GammaT := by
    rw [tr_empty_resurrect, gsubstCtx_resurrect]
    exact TrGe.resurrect_of_submap w.target
  exact hasTypeBwd hg htarget (CtxDisj.empty GammaT)

/-! ## Basis validity -/

private theorem subst_sof_eq {x : Name} {n : Term} {b : Basis} {s : Space}
    (h : Basis.sof b = s) :
    Basis.sof (Basis.subst x n b) = Space.subst x n s := by
  simpa only [Basis.sof_subst] using congrArg (Space.subst x n) h

private theorem subst_tof_eq_space {x : Name} {n : Term} {b : Basis} {s : Space}
    (h : Basis.tof b = .space s) :
    Basis.tof (Basis.subst x n b) = .space (Space.subst x n s) := by
  simp only [Basis.tof_subst, h, Ty.subst]

/-- Basis validity is stable under a source cut, including the embedded FFS
typing premises and cofinite dependent-frame body. -/
noncomputable def SourceCutCtx.basisValid
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 GammaS GammaT : NLCtx}
    (w : SourceCutCtx x n tauX Gamma0 GammaS GammaT) :
    {b : Basis} -> Basis.BasisValid GammaS b ->
      Basis.BasisValid GammaT (Basis.subst x n b)
  | .empty, .empty => .empty
  | .one, .one => .one
  | .dual b, .dual hb htof =>
      .dual (w.basisValid hb) (by
        simpa only [Basis.sof_subst] using subst_tof_eq_space htof)
  | .dsum b0 b1, .dsum hb0 hb1 htof0 htof1 =>
      .dsum (w.basisValid hb0) (w.basisValid hb1)
        (by simpa only [Basis.sof_subst] using subst_tof_eq_space htof0)
        (by simpa only [Basis.sof_subst] using subst_tof_eq_space htof1)
  | .tprod b0 b1, .tprod hb0 hb1 htof0 htof1 =>
      .tprod (w.basisValid hb0) (w.basisValid hb1)
        (by simpa only [Basis.sof_subst] using subst_tof_eq_space htof0)
        (by simpa only [Basis.sof_subst] using subst_tof_eq_space htof1)
  | .proj (.ker s0 s1 e) b0 b1, .proj_ker hb0 hb1 htof0 htof1 he => by
      refine .proj_ker (w.basisValid hb0) (w.basisValid hb1)
        (subst_tof_eq_space htof0) (subst_tof_eq_space htof1) ?_
      exact ⟨w.hasTypeEmpty he.some⟩
  | .proj (.coker s0 s1 e) b0 b1, .proj_coker hb0 hb1 htof0 htof1 he => by
      refine .proj_coker (w.basisValid hb0) (w.basisValid hb1)
        (subst_tof_eq_space htof0) (subst_tof_eq_space htof1) ?_
      exact ⟨w.hasTypeEmpty he.some⟩
  | .proj (.img s0 s1 e) b0 b1, .proj_img hb0 hb1 htof0 htof1 he => by
      refine .proj_img (w.basisValid hb0) (w.basisValid hb1)
        (subst_tof_eq_space htof0) (subst_tof_eq_space htof1) ?_
      exact ⟨w.hasTypeEmpty he.some⟩
  | .proj (.coimg s0 s1 e) b0 b1, .proj_coimg hb0 hb1 htof0 htof1 he => by
      refine .proj_coimg (w.basisValid hb0) (w.basisValid hb1)
        (subst_tof_eq_space htof0) (subst_tof_eq_space htof1) ?_
      exact ⟨w.hasTypeEmpty he.some⟩
  | .image b, @Basis.BasisValid.image _ _ s0 s1 e hb hsof he => by
      have hout : Basis.BasisValid GammaT (.image (Basis.subst x n b)) := by
        refine @Basis.BasisValid.image GammaT (Basis.subst x n b)
          (Space.subst x n s0) (Space.subst x n s1) (Term.subst x n e)
          (w.basisValid hb) ?_ ?_
        · simpa only [Basis.sof_subst, Space.subst] using
            congrArg (Space.subst x n) hsof
        · exact ⟨w.hasTypeEmpty he.some⟩
      simpa only [Basis.subst] using hout

  | .terms s es b, .terms hb htof hs hes hne => by
      refine .terms (w.basisValid hb) (subst_tof_eq_space htof)
        ⟨w.svalid hs.some⟩ ?_ ?_
      intro e he
      rw [List.mem_map] at he
      obtain ⟨e0, he0, rfl⟩ := he
      exact ⟨w.hasTypeEmpty (hes e0 he0).some⟩
      exact fun hempty => hne (List.map_eq_nil_iff.mp hempty)
  | .frame b0 b1, @Basis.BasisValid.frame _ _ _ L hb0 hbody => by
      have hout : Basis.BasisValid GammaT
          (.frame (Basis.subst x n b0) (Basis.subst x n b1)) := by
        refine @Basis.BasisValid.frame GammaT (Basis.subst x n b0)
          (Basis.subst x n b1) (L ∪ {x} ∪ Gamma0.keys)
          (w.basisValid hb0) ?_
        · intro z hz
          simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hz
          obtain ⟨⟨hzL, hzx⟩, hz0keys⟩ := hz
          have hz0 : Gamma0.lookup z = none :=
            Finmap.lookup_eq_none.mpr (fun hm => hz0keys (Finmap.mem_keys.mpr hm))
          have w' := w.extendNL z (Basis.tof b0) hzx hz0
          have hrec := w'.basisValid (hbody z hzL)
          have hopen : Basis.subst x n (Basis.openVar z b1) =
              Basis.openVar z (Basis.subst x n b1) := by
            simp only [Basis.openVar, Basis.subst_openRec x n w.data.lc b1 0 (.var z),
              Term.subst, if_neg (Ne.symm hzx)]
          rw [hopen] at hrec
          simpa only [Basis.tof_subst] using hrec
      simpa only [Basis.subst] using hout

/-! ## Term-side cut worlds -/

/-- The term-side relation keeps the exact graded substitution invariant and
the conservative-backward-bridge witness for a selected target pair.  Unlike
the type-only relation, this also covers the case where `x` has moved into a
linear context below a `promote` rule. -/
structure SourceTermCutCtx (x : Name) (n : Term) (tauX : Ty) (Gamma0 : NLCtx)
    (DeltaS : LCtx) (GammaS : NLCtx) (DeltaT : LCtx) (GammaT : NLCtx) : Type where
  data : GSubstData x n Gamma0 tauX
  sourceDisj : CtxDisj DeltaS GammaS
  targetDisj : CtxDisj DeltaT GammaT
  inv : GInv x tauX Gamma0 (tr DeltaS GammaS)
  target : TrGe (gsubstCtx x n Gamma0 (tr DeltaS GammaS)) DeltaT GammaT

/-- Turn a type cut world into its empty-linear term world. -/
def SourceCutCtx.termEmpty
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 GammaS GammaT : NLCtx}
    (w : SourceCutCtx x n tauX Gamma0 GammaS GammaT) :
    SourceTermCutCtx x n tauX Gamma0 ∅ GammaS ∅ GammaT := by
  refine
    { data := w.data
      sourceDisj := CtxDisj.empty GammaS
      targetDisj := CtxDisj.empty GammaT
      inv := ?_
      target := ?_ }
  · rw [tr_empty_resurrect]
    exact w.tinv.toResurrect
  · rw [tr_empty_resurrect, gsubstCtx_resurrect]
    exact TrGe.resurrect_of_submap w.target

/-- Recover the type-only cut world carried by any term cut world.  This
continues to work when the distinguished variable has moved into the linear
source context: `TInv` only constrains its type when it occurs in the
nonlinear/type view. -/
def SourceTermCutCtx.typeCtx
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 : NLCtx}
    {DeltaS DeltaT : LCtx} {GammaS GammaT : NLCtx}
    (w : SourceTermCutCtx x n tauX Gamma0 DeltaS GammaS DeltaT GammaT) :
    SourceCutCtx x n tauX Gamma0 GammaS GammaT := by
  have hinv : TInv x tauX Gamma0 (asTypeCtx GammaS) := by
    have h := w.inv.toTInv
    rw [typeCtxOmega_tr w.sourceDisj] at h
    exact h
  have htarget :
      SubMap (tsubstCtx x n Gamma0 (asTypeCtx GammaS))
        (asTypeCtx GammaT) := by
    have h := typeCtxOmega_submap w.target
    rw [← tsubstCtx_typeCtxOmega w.inv.1,
      typeCtxOmega_tr w.sourceDisj] at h
    exact h
  exact
    { data := w.data
      tinv := hinv
      target := htarget }

/-- Extend both sides by a fresh linear binder, rewriting its space on the
target side. -/
def SourceTermCutCtx.extendLin
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 : NLCtx}
    {DeltaS DeltaT : LCtx} {GammaS GammaT : NLCtx}
    (w : SourceTermCutCtx x n tauX Gamma0 DeltaS GammaS DeltaT GammaT)
    (z : Name) (s : Space) (hzx : z ≠ x) (hz0 : Gamma0.lookup z = none)
    (hzS : z ∉ GammaS) (hzT : z ∉ GammaT) :
    SourceTermCutCtx x n tauX Gamma0
      (Finmap.insert z s DeltaS) GammaS
      (Finmap.insert z (Space.subst x n s) DeltaT) GammaT := by
  refine
    { data := w.data
      sourceDisj := CtxDisj.insert' w.sourceDisj hzS
      targetDisj := CtxDisj.insert' w.targetDisj hzT
      inv := ?_
      target := ?_ }
  · rw [tr_insert]
    exact w.inv.update hzx hz0
  · rw [tr_insert, gsubstCtx_update hzx hz0]
    simpa only [mapSubstTy, Ty.subst, Option.map_some] using
      w.target.insert_lin z (Space.subst x n s)

/-- Extend both sides by a fresh dependent nonlinear binder, keeping the
linear contexts fixed. -/
def SourceTermCutCtx.extendNL
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 : NLCtx}
    {DeltaS DeltaT : LCtx} {GammaS GammaT : NLCtx}
    (w : SourceTermCutCtx x n tauX Gamma0 DeltaS GammaS DeltaT GammaT)
    (z : Name) (tau : Ty) (hzx : z ≠ x) (hz0 : Gamma0.lookup z = none)
    (hzDeltaS : z ∉ DeltaS) (hzDeltaT : z ∉ DeltaT) :
    SourceTermCutCtx x n tauX Gamma0 DeltaS
      (Finmap.insert z tau GammaS) DeltaT
      (Finmap.insert z (Ty.subst x n tau) GammaT) := by
  have hsource : CtxDisj DeltaS (Finmap.insert z tau GammaS) := by
    intro q hqDelta hqGamma
    rcases Finmap.mem_insert.mp hqGamma with rfl | hqGammaS
    · exact hzDeltaS hqDelta
    · exact w.sourceDisj q hqDelta hqGammaS
  have htargetDisj :
      CtxDisj DeltaT (Finmap.insert z (Ty.subst x n tau) GammaT) := by
    intro q hqDelta hqGamma
    rcases Finmap.mem_insert.mp hqGamma with rfl | hqGammaT
    · exact hzDeltaT hqDelta
    · exact w.targetDisj q hqDelta hqGammaT
  refine
    { data := w.data
      sourceDisj := hsource
      targetDisj := htargetDisj
      inv := ?_
      target := ?_ }
  · rw [tr_insert_nl_gen hzDeltaS]
    exact w.inv.update hzx hz0
  · rw [tr_insert_nl_gen hzDeltaS, gsubstCtx_update hzx hz0]
    intro q
    rw [tr_insert_nl_gen (τ := Ty.subst x n tau) hzDeltaT]
    by_cases hqz : q = z
    · subst q
      simp only [Function.update_self, mapSubstTy, Option.map_some, WkPt0]
      exact ⟨trivial, GGrade.Wk.refl _⟩
    · simpa only [Function.update_of_ne hqz] using w.target q

/-- Transport a source term-typing derivation through a term cut world. -/
noncomputable def SourceTermCutCtx.hasType
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 : NLCtx}
    {DeltaS DeltaT : LCtx} {GammaS GammaT : NLCtx}
    (w : SourceTermCutCtx x n tauX Gamma0 DeltaS GammaS DeltaT GammaT)
    {e : Term} {tau : Ty} (h : HasType DeltaS GammaS e tau) :
    HasType DeltaT GammaT (Term.subst x n e) (Ty.subst x n tau) := by
  have hg := ghastype_subst w.data w.inv (hasTypeBridge w.sourceDisj h)
  exact hasTypeBwd hg w.target w.targetDisj

/-- Target split data induced by a source linear split. -/
structure SourceTermCutSplit
    (x : Name) (n : Term) (tauX : Ty) (Gamma0 : NLCtx)
    (DeltaS0 DeltaS1 : LCtx) (GammaS : NLCtx)
    (DeltaT : LCtx) (GammaT : NLCtx) : Type where
  DeltaT0 : LCtx
  DeltaT1 : LCtx
  union_eq : DeltaT0 ∪ DeltaT1 = DeltaT
  disjoint : Finmap.Disjoint DeltaT0 DeltaT1
  left : SourceTermCutCtx x n tauX Gamma0 DeltaS0 GammaS DeltaT0 GammaT
  right : SourceTermCutCtx x n tauX Gamma0 DeltaS1 GammaS DeltaT1 GammaT

/-- Split a term cut world along a source linear partition.  The target
partition is recovered constructively by the graded backward bridge, so this
also routes the distinguished variable correctly if it occurs in one branch. -/
noncomputable def SourceTermCutCtx.split
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 : NLCtx}
    {DeltaS0 DeltaS1 DeltaT : LCtx} {GammaS GammaT : NLCtx}
    (w : SourceTermCutCtx x n tauX Gamma0
      (DeltaS0 ∪ DeltaS1) GammaS DeltaT GammaT)
    (hdis : Finmap.Disjoint DeltaS0 DeltaS1) :
    SourceTermCutSplit x n tauX Gamma0 DeltaS0 DeltaS1 GammaS DeltaT GammaT := by
  have hcd0 : CtxDisj DeltaS0 GammaS :=
    fun z hz => w.sourceDisj z (Finmap.mem_union.mpr (Or.inl hz))
  have hcd1 : CtxDisj DeltaS1 GammaS :=
    fun z hz => w.sourceDisj z (Finmap.mem_union.mpr (Or.inr hz))
  have hsplit : ∀ z, tr (DeltaS0 ∪ DeltaS1) GammaS z =
      gadd (tr DeltaS0 GammaS z) (tr DeltaS1 GammaS z) :=
    tr_add hdis hcd0 hcd1
  have hagree : TypeAgree (tr DeltaS0 GammaS) (tr DeltaS1 GammaS) :=
    tr_typeagree hdis hcd0 hcd1
  obtain ⟨hinv0, hinv1⟩ := w.inv.split hsplit hagree
  have houtSplit : ∀ z,
      gsubstCtx x n Gamma0 (tr (DeltaS0 ∪ DeltaS1) GammaS) z =
        gadd (gsubstCtx x n Gamma0 (tr DeltaS0 GammaS) z)
          (gsubstCtx x n Gamma0 (tr DeltaS1 GammaS) z) :=
    gsubstCtx_gadd hsplit hinv1.1
  have houtAgree : TypeAgree
      (gsubstCtx x n Gamma0 (tr DeltaS0 GammaS))
      (gsubstCtx x n Gamma0 (tr DeltaS1 GammaS)) :=
    gsubstCtx_typeagree hagree hinv0.1 hinv1.1
  let splitData := splitBackData houtSplit w.target houtAgree w.targetDisj
  exact
    { DeltaT0 := splitData.Δ₀
      DeltaT1 := splitData.Δ₁
      union_eq := splitData.hun
      disjoint := splitData.hdis
      left :=
        { data := w.data
          sourceDisj := hcd0
          targetDisj := splitData.hcd0
          inv := hinv0
          target := splitData.htr0 }
      right :=
        { data := w.data
          sourceDisj := hcd1
          targetDisj := splitData.hcd1
          inv := hinv1
          target := splitData.htr1 } }

private theorem tr_lookup_of_nlIncl
    {Delta : LCtx} {GammaSmall GammaBig : NLCtx}
    (hle : NLCtxIncl GammaSmall GammaBig) {z : Name}
    {g : GGrade} {tau : Ty} (h : tr Delta GammaSmall z = some (g, tau)) :
    tr Delta GammaBig z = some (g, tau) := by
  cases hD : Delta.lookup z with
  | some s =>
      simpa only [tr, hD] using h
  | none =>
      cases hS : GammaSmall.lookup z with
      | none => simp [tr, hD, hS] at h
      | some tauS =>
          have hB := hle z tauS hS
          simpa only [tr, hD, hS, hB] using h

/-- Restrict the source nonlinear context of a term world along an inclusion,
while retaining the same target.  Extra source nonlinear bindings only have
grade `omega`, so omitting them remains admissible for `TrGe`; linear target
entries are unchanged. -/
def SourceTermCutCtx.pullSource
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 : NLCtx}
    {DeltaS DeltaT : LCtx} {GammaS GammaT GammaSmall : NLCtx}
    (w : SourceTermCutCtx x n tauX Gamma0 DeltaS GammaS DeltaT GammaT)
    (hle : NLCtxIncl GammaSmall GammaS) :
    SourceTermCutCtx x n tauX Gamma0 DeltaS GammaSmall DeltaT GammaT := by
  have hcdSmall : CtxDisj DeltaS GammaSmall := by
    intro z hzD hzS
    obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp hzS
    exact w.sourceDisj z hzD
      (Finmap.mem_of_lookup_eq_some (hle z tau htau))
  have hinv : GInv x tauX Gamma0 (tr DeltaS GammaSmall) := by
    refine ⟨?_, ?_⟩
    · intro z tau hz0 g tau' hz
      exact w.inv.1 z tau hz0 g tau' (tr_lookup_of_nlIncl hle hz)
    · intro g tau hz
      exact w.inv.2 g tau (tr_lookup_of_nlIncl hle hz)
  refine
    { data := w.data
      sourceDisj := hcdSmall
      targetDisj := w.targetDisj
      inv := hinv
      target := ?_ }
  intro z
  have hbig := w.target z
  by_cases hzx : z = x
  · subst z
    simpa only [gsubstCtx, if_pos rfl] using hbig
  · cases hD : DeltaS.lookup z with
    | some s =>
        have hsame : tr DeltaS GammaSmall z = tr DeltaS GammaS z := by
          simp only [tr, hD]
        rw [gsubstCtx, if_neg hzx, hsame]
        simpa only [gsubstCtx, if_neg hzx] using hbig
    | none =>
        cases hS : GammaSmall.lookup z with
        | some tau =>
            have hB := hle z tau hS
            have hsame : tr DeltaS GammaSmall z = tr DeltaS GammaS z := by
              simp only [tr, hD, hS, hB]
            rw [gsubstCtx, if_neg hzx, hsame]
            simpa only [gsubstCtx, if_neg hzx] using hbig
        | none =>
            cases hB : GammaS.lookup z with
            | none =>
                have hsame : tr DeltaS GammaSmall z = tr DeltaS GammaS z := by
                  simp only [tr, hD, hS, hB]
                rw [gsubstCtx, if_neg hzx, hsame]
                simpa only [gsubstCtx, if_neg hzx] using hbig
            | some tau =>
                cases h0 : Gamma0.lookup z with
                | some tau0 =>
                    have heq : tau0 = tau :=
                      w.inv.1 z tau0 h0 GGrade.omega tau (by
                        simp only [tr, hD, hB])
                    subst tau0
                    have hsame :
                        gsubstCtx x n Gamma0 (tr DeltaS GammaSmall) z =
                          gsubstCtx x n Gamma0 (tr DeltaS GammaS) z := by
                      simp only [gsubstCtx, if_neg hzx, tr, hD, hS, hB,
                        Finmap.lookup_empty, h0, gadd, mapSubstTy, Option.map_some,
                        GGrade.add_omega]
                    rw [hsame]
                    exact hbig
                | none =>
                    have hsmall :
                        gsubstCtx x n Gamma0 (tr DeltaS GammaSmall) z = none := by
                      simp only [gsubstCtx, if_neg hzx, tr, hD, hS,
                        Finmap.lookup_empty, h0, gadd, mapSubstTy, Option.map_none]
                    have hbig' :
                        gsubstCtx x n Gamma0 (tr DeltaS GammaS) z =
                          some (GGrade.omega, Ty.subst x n tau) := by
                      simp only [gsubstCtx, if_neg hzx, tr, hD, hB,
                        Finmap.lookup_empty, h0, gadd, mapSubstTy, Option.map_some]
                    rw [hsmall]
                    rw [hbig'] at hbig
                    cases ht : tr DeltaT GammaT z with
                    | none => trivial
                    | some p =>
                        obtain ⟨gt, taut⟩ := p
                        rw [ht] at hbig
                        cases gt <;> simp_all [WkPt0, GGrade.Wk]

private theorem ginv_of_wk_left
    {x : Name} {tauX : Ty} {Gamma0 : NLCtx} {f f' : GCtx}
    (hw : GCtx.Wk f f') (hinv : GInv x tauX Gamma0 f') :
    GInv x tauX Gamma0 f := by
  refine ⟨?_, ?_⟩
  · intro z tau0 hz0 g tau hz
    have hwz := hw z
    rw [hz] at hwz
    cases hf' : f' z with
    | none => rw [hf'] at hwz; contradiction
    | some p =>
        obtain ⟨g', tau'⟩ := p
        rw [hf'] at hwz
        have htau : tau = tau' := hwz.1
        subst tau'
        exact hinv.1 z tau0 hz0 g' tau hf'
  · intro g tau hx
    have hwx := hw x
    rw [hx] at hwx
    cases hf' : f' x with
    | none => rw [hf'] at hwx; contradiction
    | some p =>
        obtain ⟨g', tau'⟩ := p
        rw [hf'] at hwx
        have htau : tau = tau' := hwx.1
        subst tau'
        exact hinv.2 g' tau hf'

private theorem gsubstCtx_wk_of_wk
    {x : Name} {n : Term} {Gamma0 : NLCtx} {f f' : GCtx}
    (hw : GCtx.Wk f f') :
    GCtx.Wk (gsubstCtx x n Gamma0 f) (gsubstCtx x n Gamma0 f') := by
  intro z
  by_cases hzx : z = x
  · subst z
    simp [gsubstCtx]
  · have hwz := hw z
    cases hf : f z with
    | none =>
        cases hf' : f' z with
        | none =>
            cases h0 : Gamma0.lookup z with
            | none =>
                simp [gsubstCtx, hzx, hf, hf', tr, h0, mapSubstTy, gadd]
            | some tau0 =>
                simp [gsubstCtx, hzx, hf, hf', tr, h0, mapSubstTy, gadd,
                  GGrade.Wk]
        | some p => rw [hf, hf'] at hwz; contradiction
    | some p =>
        obtain ⟨g, tau⟩ := p
        cases hf' : f' z with
        | none => rw [hf, hf'] at hwz; contradiction
        | some p' =>
            obtain ⟨g', tau'⟩ := p'
            rw [hf, hf'] at hwz
            obtain ⟨htau, hgrade⟩ := hwz
            subst tau'
            cases h0 : Gamma0.lookup z with
            | none =>
                simpa [gsubstCtx, hzx, hf, hf', tr, h0, mapSubstTy, gadd]
                  using hgrade
            | some tau0 =>
                simp [gsubstCtx, hzx, hf, hf', tr, h0, mapSubstTy, gadd,
                  GGrade.Wk]

private theorem trGe_of_wk_left
    {f f' : GCtx} {Delta : LCtx} {Gamma : NLCtx}
    (hw : GCtx.Wk f f') (htr : TrGe f' Delta Gamma) :
    TrGe f Delta Gamma := by
  intro z
  have hwz := hw z
  have htz := htr z
  cases hf : f z with
  | none =>
      cases hf' : f' z with
      | none =>
          rw [hf, hf'] at hwz
          rw [hf'] at htz
          exact htz
      | some p => rw [hf, hf'] at hwz; contradiction
  | some p =>
      obtain ⟨g, tau⟩ := p
      cases hf' : f' z with
      | none => rw [hf, hf'] at hwz; contradiction
      | some p' =>
          obtain ⟨g', tau'⟩ := p'
          rw [hf, hf'] at hwz
          obtain ⟨htau, hgg'⟩ := hwz
          subst tau'
          cases ht : tr Delta Gamma z with
          | none =>
              rw [hf', ht] at htz
              cases g' <;> simp_all [WkPt0, GGrade.Wk]
          | some q =>
              obtain ⟨gt, taut⟩ := q
              rw [hf', ht] at htz
              rcases hgg' with rfl | ⟨rfl, rfl⟩
              · exact htz
              · simp only [WkPt0] at htz ⊢
                exact ⟨htz.1,
                  GGrade.Wk.trans (Or.inr ⟨rfl, rfl⟩) htz.2⟩

/-- Enter the premise of a source `promote` node while retaining the outer
target pair.  The moved source variables change grade `omega` to grade `one`;
the same target remains valid by transitivity of graded weakening.  In
particular, this routes the distinguished cut variable into an empty target
linear context when it was among the promoted bindings. -/
def SourceTermCutCtx.enterPromote
    {x : Name} {n : Term} {tauX : Ty} {Gamma0 : NLCtx}
    {DeltaS DeltaT lin : LCtx} {GammaS GammaT : NLCtx}
    (w : SourceTermCutCtx x n tauX Gamma0 DeltaS
      (lin.toNL ∪ GammaS) DeltaT GammaT)
    (hdDelta : Finmap.Disjoint lin DeltaS)
    (hdGamma : Finmap.Disjoint lin.toNL GammaS) :
    SourceTermCutCtx x n tauX Gamma0
      (lin ∪ DeltaS) GammaS DeltaT GammaT := by
  have hsource : CtxDisj (lin ∪ DeltaS) GammaS := by
    intro z hzUnion hzGamma
    rw [Finmap.mem_union] at hzUnion
    cases hzUnion with
    | inl hzLin =>
        exact hdGamma z ((LCtx.mem_toNL_iff lin z).mpr hzLin) hzGamma
    | inr hzDelta =>
        exact w.sourceDisj z hzDelta
          (Finmap.mem_union.mpr (Or.inr hzGamma))
  have hwk := tr_promote_wk lin DeltaS GammaS hdDelta
  have hinv := ginv_of_wk_left hwk w.inv
  exact
    { data := w.data
      sourceDisj := hsource
      targetDisj := w.targetDisj
      inv := hinv
      target := trGe_of_wk_left (gsubstCtx_wk_of_wk hwk) w.target }

end RawCertifiedSourceSubst
end GLang
