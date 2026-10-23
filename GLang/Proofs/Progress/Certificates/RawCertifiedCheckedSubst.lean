import GLang.Proofs.Progress.Certificates.RawCertifiedSourceSubst
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLift
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLower
import GLang.Proofs.Adequacy.Foundations.Consistent
import GLang.Proofs.Adequacy.Foundations.EvalCtxSubctx
import GLang.Proofs.Adequacy.Foundations.StrengthenedMono
import GLang.Proofs.Progress.DependentApplication
import GLang.Proofs.Progress.Certificates.RawCertifiedRename
import GLang.Proofs.Progress.Certificates.RawCertifiedRenameProof
import GLang.Proofs.Progress.Certificates.RawCertifiedPiBasisTransport
import GLang.Proofs.Progress.ContextExtension
import GLang.Proofs.Adequacy.Raw.RawLocalCtxWFPromotion

/-!
# Constructive substitution for checked operational certificates

This module transports the full five-way checked evaluator through one
nonlinear source/value substitution.  The source-side obligations are
discharged by the axiom-free graded substitution bridge in
`RawCertifiedSourceSubst`; the runtime indices use the existing `ESubst`
transport.
-/

namespace GLang
namespace RawCertifiedOperational

open Basis (BasisValid)
open RawCertifiedSourceSubst
open GLang.Graded

/-! ## Checked cut worlds

The source and evaluator substitutions have to move in lockstep.  The final
field is the checked version of `ESubst.hcut`; keeping it in the world makes
the distinguished-variable leaves constructive, including leaves reached
under binders. -/

structure CheckedCutCtx (x : VName) (bX : Basis) (tauVX : ValTy)
    (n : Term) (arg : ValExpr) (Gamma0 : NLCtx)
    (GammaS : NLCtx) (PsiS : EvalCtx)
    (GammaT : NLCtx) (PsiT : EvalCtx) : Type where
  source : SourceCutCtx x n (Basis.tof bX) Gamma0 GammaS GammaT
  eval : ESubst x bX tauVX n arg PsiS PsiT
  cut : C.Term ∅ GammaT PsiT n (Basis.subst x n bX) arg
    (ValTy.subst x arg tauVX)

structure CheckedTermCutCtx (x : VName) (bX : Basis) (tauVX : ValTy)
    (n : Term) (arg : ValExpr) (Gamma0 : NLCtx)
    (DeltaS : LCtx) (GammaS : NLCtx) (PsiS : EvalCtx)
    (DeltaT : LCtx) (GammaT : NLCtx) (PsiT : EvalCtx) : Type where
  source : SourceTermCutCtx x n (Basis.tof bX) Gamma0
    DeltaS GammaS DeltaT GammaT
  eval : ESubst x bX tauVX n arg PsiS PsiT
  cut : C.Term ∅ GammaT PsiT n (Basis.subst x n bX) arg
    (ValTy.subst x arg tauVX)

theorem C.Term.extendEval
    (h : C.Term Delta Gamma Psi e b v tauV)
    (hz : ∀ b', (z, b') ∉ Psi) :
    C.Term Delta Gamma (Psi.extend z bz vz) e b v tauV := by
  have hznames : z ∉ Psi.names := by
    intro hm
    obtain ⟨⟨q, bq⟩, hkey, hq⟩ := Finset.mem_image.mp hm
    simp only at hq
    subst q
    exact hz bq (Finmap.mem_keys.mp hkey)
  exact S.Term.toC
    (h.toS.mono (EvalCtx.Subctx.extend_right_of_name_fresh hznames bz vz))

def CheckedCutCtx.termEmpty
    (w : CheckedCutCtx x bX tauVX n arg Gamma0 GammaS PsiS GammaT PsiT) :
    CheckedTermCutCtx x bX tauVX n arg Gamma0
      ∅ GammaS PsiS ∅ GammaT PsiT :=
  ⟨w.source.termEmpty, w.eval, w.cut⟩

def CheckedTermCutCtx.pullSource
    (w : CheckedTermCutCtx x bX tauVX n arg Gamma0
      DeltaS GammaS PsiS DeltaT GammaT PsiT)
    (hle : NLCtxIncl GammaSmall GammaS) :
    CheckedTermCutCtx x bX tauVX n arg Gamma0
      DeltaS GammaSmall PsiS DeltaT GammaT PsiT :=
  ⟨w.source.pullSource hle, w.eval, w.cut⟩

def CheckedTermCutCtx.typeCtx
    (w : CheckedTermCutCtx x bX tauVX n arg Gamma0
      DeltaS GammaS PsiS DeltaT GammaT PsiT) :
    CheckedCutCtx x bX tauVX n arg Gamma0 GammaS PsiS GammaT PsiT :=
  ⟨w.source.typeCtx, w.eval, w.cut⟩

structure CheckedTermCutSplit
    (x : VName) (bX : Basis) (tauVX : ValTy)
    (n : Term) (arg : ValExpr) (Gamma0 : NLCtx)
    (DeltaS0 DeltaS1 : LCtx) (GammaS : NLCtx) (PsiS : EvalCtx)
    (DeltaT : LCtx) (GammaT : NLCtx) (PsiT : EvalCtx) : Type where
  DeltaT0 : LCtx
  DeltaT1 : LCtx
  union_eq : DeltaT0 ∪ DeltaT1 = DeltaT
  disjoint : Finmap.Disjoint DeltaT0 DeltaT1
  left : CheckedTermCutCtx x bX tauVX n arg Gamma0
    DeltaS0 GammaS PsiS DeltaT0 GammaT PsiT
  right : CheckedTermCutCtx x bX tauVX n arg Gamma0
    DeltaS1 GammaS PsiS DeltaT1 GammaT PsiT

noncomputable def CheckedTermCutCtx.split
    (w : CheckedTermCutCtx x bX tauVX n arg Gamma0
      (DeltaS0 ∪ DeltaS1) GammaS PsiS DeltaT GammaT PsiT)
    (hdis : Finmap.Disjoint DeltaS0 DeltaS1) :
    CheckedTermCutSplit x bX tauVX n arg Gamma0
      DeltaS0 DeltaS1 GammaS PsiS DeltaT GammaT PsiT := by
  let ws := w.source.split hdis
  exact
    ⟨ws.DeltaT0, ws.DeltaT1, ws.union_eq, ws.disjoint,
      ⟨ws.left, w.eval, w.cut⟩, ⟨ws.right, w.eval, w.cut⟩⟩

noncomputable def CheckedTermCutCtx.extendLin
    (w : CheckedTermCutCtx x bX tauVX n arg Gamma0
      DeltaS GammaS PsiS DeltaT GammaT PsiT)
    (z : VName) (s : Space) (bz : Basis) (vz : ValExpr)
    (hzx : z ≠ x) (hz0 : Gamma0.lookup z = none)
    (hzS : z ∉ GammaS) (hzT : z ∉ GammaT)
    (hzPsiS : ∀ b, (z, b) ∉ PsiS)
    (hzPsiT : ∀ b, (z, b) ∉ PsiT)
    (hvinfer : ValExpr.inferSpace (ValExpr.subst x arg vz) =
      ValSpace.subst x arg (ValExpr.inferSpace vz))
    (hvtype : InferTypeSubstAt x arg vz) :
    CheckedTermCutCtx x bX tauVX n arg Gamma0
      (Finmap.insert z s DeltaS) GammaS (PsiS.extend z bz vz)
      (Finmap.insert z (Space.subst x n s) DeltaT) GammaT
      (PsiT.extend z (Basis.subst x n bz) (ValExpr.subst x arg vz)) :=
  ⟨w.source.extendLin z s hzx hz0 hzS hzT,
    w.eval.extend_val hzx hzPsiS (hzPsiT _) hvinfer hvtype,
    w.cut.extendEval hzPsiT⟩

noncomputable def CheckedCutCtx.extendNL
    (w : CheckedCutCtx x bX tauVX n arg Gamma0 GammaS PsiS GammaT PsiT)
    (z : VName) (bz : Basis) (tvz : ValTy)
    (hzx : z ≠ x) (hz0 : Gamma0.lookup z = none)
    (hzT : z ∉ GammaT)
    (hzPsiS : ∀ b, (z, b) ∉ PsiS)
    (hzPsiT : ∀ b, (z, b) ∉ PsiT)
    (hzCut : z ∉ Basis.fv (Basis.subst x n bX)) :
    CheckedCutCtx x bX tauVX n arg Gamma0
      (Finmap.insert z (Basis.tof bz) GammaS)
      (PsiS.extend z bz (.var z tvz))
      (Finmap.insert z (Ty.subst x n (Basis.tof bz)) GammaT)
      (PsiT.extend z (Basis.subst x n bz)
        (.var z (ValTy.subst x arg tvz))) := by
  have hle : NLCtxIncl GammaT
      (Finmap.insert z (Ty.subst x n (Basis.tof bz)) GammaT) :=
    (NLCtxIncl.refl GammaT).insert_right hzT _
  have hcutEval : C.Term ∅ GammaT
      (PsiT.extend z (Basis.subst x n bz)
        (.var z (ValTy.subst x arg tvz)))
      n (Basis.subst x n bX) arg (ValTy.subst x arg tauVX) :=
    w.cut.extendEval hzPsiT
  exact
    ⟨w.source.extendNL z (Basis.tof bz) hzx hz0,
      w.eval.extend hzx hzPsiS (hzPsiT _),
      C.Term.weaken hcutEval hle (Graded.CtxDisj.empty _)⟩

/-! ## Locally-nameless commutation at fresh inner binders -/

theorem Basis.subst_openVar_ne_checked {x z : Name} {n : Term} {b : Basis}
    (hn : Term.lc n) (hzx : z ≠ x) :
    Basis.subst x n (Basis.openVar z b) =
      Basis.openVar z (Basis.subst x n b) := by
  simp only [Basis.openVar,
    Basis.subst_openRec x n hn b 0 (.var z), Term.subst,
    if_neg (Ne.symm hzx)]

theorem ValTy.subst_openVar_ne_checked {x z : VName} {arg : ValExpr}
    {tauz tauv : ValTy} (harg : ValExpr.lc arg) (hzx : z ≠ x) :
    ValTy.subst x arg (ValTy.openVar z tauz tauv) =
      ValTy.openVar z (ValTy.subst x arg tauz)
        (ValTy.subst x arg tauv) := by
  simp only [ValTy.openVar,
    ValTy.subst_openRec x arg harg tauv 0 (.var z tauz),
    ValExpr.subst, if_neg hzx]

theorem ValExpr.subst_openVar_ne_checked {x z : VName} {arg : ValExpr}
    {tauz : ValTy} {v : ValExpr} (harg : ValExpr.lc arg) (hzx : z ≠ x) :
    ValExpr.subst x arg (ValExpr.openVar z tauz v) =
      ValExpr.openVar z (ValTy.subst x arg tauz)
        (ValExpr.subst x arg v) := by
  simp only [ValExpr.openVar,
    ValExpr.subst_openRec x arg harg v 0 (.var z tauz),
    ValExpr.subst, if_neg hzx]

theorem Basis.tof_space_subst_checked {x : Name} {n : Term} {b : Basis}
    (h : Basis.tof b = .space (Basis.sof b)) :
    Basis.tof (Basis.subst x n b) =
      .space (Basis.sof (Basis.subst x n b)) := by
  simp only [Basis.tof_subst, h, Ty.subst, Basis.sof_subst]

theorem Basis.isSpaceBasis_subst_checked (x : VName) (u : Term) (b : Basis) :
    Basis.IsSpaceBasis (Basis.subst x u b) ↔ Basis.IsSpaceBasis b := by
  induction b with
  | empty => rfl
  | one => rfl
  | dual b ih => simpa only [Basis.subst, Basis.IsSpaceBasis, ih]
  | dsum b0 b1 ih0 ih1 =>
      simpa only [Basis.subst, Basis.IsSpaceBasis, ih0, ih1]
  | tprod b0 b1 ih0 ih1 =>
      simpa only [Basis.subst, Basis.IsSpaceBasis, ih0, ih1]
  | proj s b0 b1 ih0 ih1 =>
      simpa only [Basis.subst, Basis.IsSpaceBasis, ih0, ih1]
  | image b ih => simpa only [Basis.subst, Basis.IsSpaceBasis, ih]
  | terms s es b ih =>
      simp only [Basis.subst, Basis.IsSpaceBasis, ih]
      constructor
      · rintro ⟨hm, hb⟩
        exact ⟨fun he => hm (List.map_eq_nil_iff.mpr he), hb⟩
      · rintro ⟨he, hb⟩
        exact ⟨fun hm => he (List.map_eq_nil_iff.mp hm), hb⟩
  | frame => rfl

theorem Basis.IsTyBasis.subst_checked {x : VName} {u : Term} {b : Basis}
    (h : Basis.IsTyBasis b) : Basis.IsTyBasis (Basis.subst x u b) := by
  induction b with
  | empty => exact h
  | one => exact h
  | dual b ih => exact (Basis.isSpaceBasis_subst_checked x u (.dual b)).2 h
  | dsum b0 b1 ih0 ih1 => exact (Basis.isSpaceBasis_subst_checked x u (.dsum b0 b1)).2 h
  | tprod b0 b1 ih0 ih1 => exact (Basis.isSpaceBasis_subst_checked x u (.tprod b0 b1)).2 h
  | proj s b0 b1 ih0 ih1 => exact (Basis.isSpaceBasis_subst_checked x u (.proj s b0 b1)).2 h
  | image b ih => exact (Basis.isSpaceBasis_subst_checked x u (.image b)).2 h
  | terms s es b ih => exact (Basis.isSpaceBasis_subst_checked x u (.terms s es b)).2 h
  | frame b0 b1 ih0 ih1 =>
      simpa only [Basis.subst, Basis.IsTyBasis] using And.intro (ih0 h.1) (ih1 h.2)

/-! ## Existential cut worlds

Exact substitution of every runtime annotation is stronger than checked
evaluation supports: a stored variable can be checked at any realization of
its selected source basis.  The application rule only needs existence of a
checked result realization.  The following relation therefore preserves the
source key exactly while allowing the target stored value to be chosen by a
binder reconstruction. -/

structure LooseEvalCut (x : VName) (bX : Basis) (n : Term)
    (PsiS PsiT : EvalCtx) : Prop where
  xonly : forall b v, EvalCtx.lookup PsiS (x, b) = some v -> b = bX
  fwd : forall z b v, z ≠ x -> EvalCtx.lookup PsiS (z, b) = some v ->
    exists vT, EvalCtx.lookup PsiT (z, Basis.subst x n b) = some vT

def LooseEvalCut.ofESubst
    (h : ESubst x bX tauVX n arg PsiS PsiT) :
    LooseEvalCut x bX n PsiS PsiT where
  xonly := h.xonly
  fwd z b v hzx hl := ⟨ValExpr.subst x arg v, h.fwd z b v hzx hl⟩

def LooseEvalCut.extend
    (h : LooseEvalCut x bX n PsiS PsiT)
    (hyx : y ≠ x)
    (hyS : forall b, (y, b) ∉ PsiS)
    (hyT : forall b, (y, b) ∉ PsiT) :
    LooseEvalCut x bX n
      (PsiS.extend y bY vS)
      (PsiT.extend y (Basis.subst x n bY) vT) := by
  refine ⟨?_, ?_⟩
  · intro b v hl
    have hkey : (x, b) ≠ (y, bY) :=
      fun he => hyx (congrArg Prod.fst he).symm
    rw [EvalCtx.lookup, EvalCtx.extend,
      Finmap.lookup_insert_of_ne _ hkey] at hl
    exact h.xonly b v hl
  · intro z b v hzx hl
    by_cases hk : (z, b) = (y, bY)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      exact ⟨vT, by simp [EvalCtx.lookup, EvalCtx.extend]⟩
    · rw [EvalCtx.lookup, EvalCtx.extend,
        Finmap.lookup_insert_of_ne _ hk] at hl
      obtain ⟨v', hv'⟩ := h.fwd z b v hzx hl
      have hzy : z ≠ y := by
        intro hzy
        subst z
        exact hyS b (Finmap.mem_of_lookup_eq_some hl)
      have hkT : (z, Basis.subst x n b) ≠
          (y, Basis.subst x n bY) := fun he => hzy (congrArg Prod.fst he)
      exact ⟨v', by
        rw [EvalCtx.lookup, EvalCtx.extend,
          Finmap.lookup_insert_of_ne _ hkT]
        exact hv'⟩

structure SomeCutCtx (x : VName) (bX : Basis) (tauVX : ValTy)
    (n : Term) (arg : ValExpr) (Gamma0 : NLCtx)
    (GammaS : NLCtx) (PsiS : EvalCtx)
    (GammaT : NLCtx) (PsiT : EvalCtx) : Type where
  source : SourceCutCtx x n (Basis.tof bX) Gamma0 GammaS GammaT
  eval : LooseEvalCut x bX n PsiS PsiT
  cut : C.Term ∅ GammaT PsiT n (Basis.subst x n bX) arg
    (ValTy.subst x arg tauVX)
  wf : V2.CtxWF' ∅ GammaT
  lc : EvalCtxLc PsiT

structure SomeTermCutCtx (x : VName) (bX : Basis) (tauVX : ValTy)
    (n : Term) (arg : ValExpr) (Gamma0 : NLCtx)
    (DeltaS : LCtx) (GammaS : NLCtx) (PsiS : EvalCtx)
    (DeltaT : LCtx) (GammaT : NLCtx) (PsiT : EvalCtx) : Type where
  source : SourceTermCutCtx x n (Basis.tof bX) Gamma0
    DeltaS GammaS DeltaT GammaT
  eval : LooseEvalCut x bX n PsiS PsiT
  cut : C.Term ∅ GammaT PsiT n (Basis.subst x n bX) arg
    (ValTy.subst x arg tauVX)
  wf : V2.CtxWF' DeltaT GammaT
  lc : EvalCtxLc PsiT

private theorem ctxWF_dropLin_checked
    (h : V2.CtxWF' Delta Gamma) : V2.CtxWF' ∅ Gamma where
  disjoint := fun _ hm => absurd hm Finmap.notMem_empty
  lin_fv := fun _ _ hm => absurd
    (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
  nl_fv := h.nl_fv
  lin_valid := fun _ _ hm => absurd
    (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
  nl_valid := h.nl_valid

private theorem ctxWF_lctx_mono
    (h : V2.CtxWF' Delta Gamma)
    (hle : forall z s, DeltaSmall.lookup z = some s ->
      Delta.lookup z = some s) :
    V2.CtxWF' DeltaSmall Gamma where
  disjoint := by
    intro z hzD hzG
    obtain ⟨s, hs⟩ := Finmap.mem_iff.mp hzD
    exact h.disjoint z (Finmap.mem_of_lookup_eq_some (hle z s hs)) hzG
  lin_fv := fun z s hz => h.lin_fv z s (hle z s hz)
  nl_fv := h.nl_fv
  lin_valid := fun z s hz => h.lin_valid z s (hle z s hz)
  nl_valid := h.nl_valid

def SomeCutCtx.termEmpty
    (w : SomeCutCtx x bX tauVX n arg Gamma0 GammaS PsiS GammaT PsiT) :
    SomeTermCutCtx x bX tauVX n arg Gamma0
      ∅ GammaS PsiS ∅ GammaT PsiT :=
  ⟨w.source.termEmpty, w.eval, w.cut, w.wf, w.lc⟩

def SomeTermCutCtx.typeCtx
    (w : SomeTermCutCtx x bX tauVX n arg Gamma0
      DeltaS GammaS PsiS DeltaT GammaT PsiT) :
    SomeCutCtx x bX tauVX n arg Gamma0 GammaS PsiS GammaT PsiT :=
  ⟨w.source.typeCtx, w.eval, w.cut, ctxWF_dropLin_checked w.wf, w.lc⟩

def SomeCutCtx.pullSource
    (w : SomeCutCtx x bX tauVX n arg Gamma0
      GammaS PsiS GammaT PsiT)
    (hle : NLCtxIncl GammaSmall GammaS) :
    SomeCutCtx x bX tauVX n arg Gamma0
      GammaSmall PsiS GammaT PsiT :=
  ⟨w.source.pullSource hle, w.eval, w.cut, w.wf, w.lc⟩

def SomeTermCutCtx.pullSource
    (w : SomeTermCutCtx x bX tauVX n arg Gamma0
      DeltaS GammaS PsiS DeltaT GammaT PsiT)
    (hle : NLCtxIncl GammaSmall GammaS) :
    SomeTermCutCtx x bX tauVX n arg Gamma0
      DeltaS GammaSmall PsiS DeltaT GammaT PsiT :=
  ⟨w.source.pullSource hle, w.eval, w.cut, w.wf, w.lc⟩

structure SomeTermCutSplit
    (x : VName) (bX : Basis) (tauVX : ValTy)
    (n : Term) (arg : ValExpr) (Gamma0 : NLCtx)
    (DeltaS0 DeltaS1 : LCtx) (GammaS : NLCtx) (PsiS : EvalCtx)
    (DeltaT : LCtx) (GammaT : NLCtx) (PsiT : EvalCtx) : Type where
  DeltaT0 : LCtx
  DeltaT1 : LCtx
  union_eq : DeltaT0 ∪ DeltaT1 = DeltaT
  disjoint : Finmap.Disjoint DeltaT0 DeltaT1
  left : SomeTermCutCtx x bX tauVX n arg Gamma0
    DeltaS0 GammaS PsiS DeltaT0 GammaT PsiT
  right : SomeTermCutCtx x bX tauVX n arg Gamma0
    DeltaS1 GammaS PsiS DeltaT1 GammaT PsiT

noncomputable def SomeTermCutCtx.split
    (w : SomeTermCutCtx x bX tauVX n arg Gamma0
      (DeltaS0 ∪ DeltaS1) GammaS PsiS DeltaT GammaT PsiT)
    (hdis : Finmap.Disjoint DeltaS0 DeltaS1) :
    SomeTermCutSplit x bX tauVX n arg Gamma0
      DeltaS0 DeltaS1 GammaS PsiS DeltaT GammaT PsiT := by
  let ws := w.source.split hdis
  have hleft : forall z s, ws.DeltaT0.lookup z = some s ->
      DeltaT.lookup z = some s := by
    intro z s hz
    rw [<- ws.union_eq, Finmap.lookup_union_left
      (Finmap.mem_of_lookup_eq_some hz)]
    exact hz
  have hright : forall z s, ws.DeltaT1.lookup z = some s ->
      DeltaT.lookup z = some s := by
    intro z s hz
    have hzR := Finmap.mem_of_lookup_eq_some hz
    have hzL : z ∉ ws.DeltaT0 := fun hm => ws.disjoint z hm hzR
    rw [<- ws.union_eq, Finmap.lookup_union_right hzL]
    exact hz
  exact
    ⟨ws.DeltaT0, ws.DeltaT1, ws.union_eq, ws.disjoint,
      ⟨ws.left, w.eval, w.cut, ctxWF_lctx_mono w.wf hleft, w.lc⟩,
      ⟨ws.right, w.eval, w.cut, ctxWF_lctx_mono w.wf hright, w.lc⟩⟩

private noncomputable def cut_extendNL
    (hcut : C.Term ∅ Gamma Psi n b arg tauV)
    (hzGamma : z ∉ Gamma)
    (hzPsi : forall b', (z, b') ∉ Psi)
    (hzBasis : z ∉ Basis.fv b)
    (hbz : Basis.BasisValid Gamma bz) :
    C.Term ∅ (Finmap.insert z (Basis.tof bz) Gamma)
      (Psi.extend z bz vz) n b arg tauV := by
  have hle : NLCtxIncl Gamma (Finmap.insert z (Basis.tof bz) Gamma) :=
    (NLCtxIncl.refl Gamma).insert_right hzGamma _
  have heval := hcut.extendEval (bz := bz) (vz := vz) hzPsi
  exact C.Term.weaken heval hle (Graded.CtxDisj.empty _)

noncomputable def SomeCutCtx.extendNL
    (w : SomeCutCtx x bX tauVX n arg Gamma0 GammaS PsiS GammaT PsiT)
    (z : VName) (bz : Basis) (tauS tauT : ValTy)
    (hbzS : Basis.BasisValid GammaS bz)
    (hzx : z ≠ x) (hz0 : Gamma0.lookup z = none)
    (hzT : z ∉ GammaT)
    (hzPsiS : forall b, (z, b) ∉ PsiS)
    (hzPsiT : forall b, (z, b) ∉ PsiT)
    (hzCut : z ∉ Basis.fv (Basis.subst x n bX))
    (hlcTauT : ValTy.lc tauT) :
    SomeCutCtx x bX tauVX n arg Gamma0
      (Finmap.insert z (Basis.tof bz) GammaS)
      (PsiS.extend z bz (.var z tauS))
      (Finmap.insert z (Ty.subst x n (Basis.tof bz)) GammaT)
      (PsiT.extend z (Basis.subst x n bz) (.var z tauT)) := by
  have hbzT := w.source.basisValid hbzS
  have hwfT := RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
    (b := Basis.subst x n bz) w.wf Finmap.notMem_empty hzT hbzT
  exact
    ⟨w.source.extendNL z (Basis.tof bz) hzx hz0,
      w.eval.extend hzx hzPsiS hzPsiT,
      by simpa only [Basis.tof_subst] using
        cut_extendNL w.cut hzT hzPsiT hzCut hbzT,
      by simpa only [Basis.tof_subst] using hwfT,
      w.lc.extend (.var hlcTauT)⟩

noncomputable def SomeTermCutCtx.extendNL
    (w : SomeTermCutCtx x bX tauVX n arg Gamma0
      DeltaS GammaS PsiS DeltaT GammaT PsiT)
    (z : VName) (bz : Basis) (tauS tauT : ValTy)
    (hbzS : Basis.BasisValid GammaS bz)
    (hzx : z ≠ x) (hz0 : Gamma0.lookup z = none)
    (hzDeltaS : z ∉ DeltaS) (hzDeltaT : z ∉ DeltaT)
    (hzGammaT : z ∉ GammaT)
    (hzPsiS : forall b, (z, b) ∉ PsiS)
    (hzPsiT : forall b, (z, b) ∉ PsiT)
    (hzCut : z ∉ Basis.fv (Basis.subst x n bX))
    (hlcTauT : ValTy.lc tauT) :
    SomeTermCutCtx x bX tauVX n arg Gamma0 DeltaS
      (Finmap.insert z (Basis.tof bz) GammaS)
      (PsiS.extend z bz (.var z tauS)) DeltaT
      (Finmap.insert z (Ty.subst x n (Basis.tof bz)) GammaT)
      (PsiT.extend z (Basis.subst x n bz) (.var z tauT)) := by
  have hbzT := w.source.typeCtx.basisValid hbzS
  have hwfT := RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
    (b := Basis.subst x n bz) w.wf hzDeltaT hzGammaT hbzT
  exact
    ⟨w.source.extendNL z (Basis.tof bz) hzx hz0 hzDeltaS hzDeltaT,
      w.eval.extend hzx hzPsiS hzPsiT,
      by simpa only [Basis.tof_subst] using
        cut_extendNL w.cut hzGammaT hzPsiT hzCut hbzT,
      by simpa only [Basis.tof_subst] using hwfT,
      w.lc.extend (.var hlcTauT)⟩

noncomputable def SomeTermCutCtx.extendLin
    (w : SomeTermCutCtx x bX tauVX n arg Gamma0
      DeltaS GammaS PsiS DeltaT GammaT PsiT)
    (z : VName) (bz : Basis) (vS vT : ValExpr)
    (hbzS : Basis.BasisValid GammaS bz)
    (hzx : z ≠ x) (hz0 : Gamma0.lookup z = none)
    (hzGammaS : z ∉ GammaS) (hzGammaT : z ∉ GammaT)
    (hzDeltaT : z ∉ DeltaT)
    (hzPsiS : forall b, (z, b) ∉ PsiS)
    (hzPsiT : forall b, (z, b) ∉ PsiT)
    (hlcVT : ValExpr.lc vT) :
    SomeTermCutCtx x bX tauVX n arg Gamma0
      (Finmap.insert z (Basis.sof bz) DeltaS) GammaS
      (PsiS.extend z bz vS)
      (Finmap.insert z (Space.subst x n (Basis.sof bz)) DeltaT) GammaT
      (PsiT.extend z (Basis.subst x n bz) vT) := by
  have hbzT := w.source.typeCtx.basisValid hbzS
  have hwfT := RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
    (b := Basis.subst x n bz) w.wf hzDeltaT hzGammaT hbzT
  exact
    ⟨w.source.extendLin z (Basis.sof bz) hzx hz0 hzGammaS hzGammaT,
      w.eval.extend hzx hzPsiS hzPsiT,
      w.cut.extendEval hzPsiT,
      by simpa only [Basis.sof_subst] using hwfT,
      w.lc.extend hlcVT⟩

def SomeTermCutCtx.enterPromote
    (w : SomeTermCutCtx x bX tauVX n arg Gamma0 DeltaS
      (GLang.LCtx.toNL lin ∪ GammaS) PsiS DeltaT GammaT PsiT)
    (hdDelta : Finmap.Disjoint lin DeltaS)
    (hdGamma : Finmap.Disjoint (GLang.LCtx.toNL lin) GammaS) :
    SomeTermCutCtx x bX tauVX n arg Gamma0
      (lin ∪ DeltaS) GammaS PsiS DeltaT GammaT PsiT :=
  ⟨w.source.enterPromote hdDelta hdGamma, w.eval, w.cut, w.wf, w.lc⟩

/-- Cutting an empty-linear source context cannot create a target linear
resource. -/
private theorem SomeTermCutCtx.targetLinear_empty
    (w : SomeTermCutCtx x bX tauVX n arg Gamma0
      (∅ : LCtx) GammaS PsiS DeltaT GammaT PsiT) :
    DeltaT = ∅ := by
  have hnlS : NoLin (tr (∅ : LCtx) GammaS) := tr_emptyΔ_no_lin GammaS
  have hnlT : NoLin (gsubstCtx x n Gamma0 (tr (∅ : LCtx) GammaS)) :=
    NoLin.gsubst hnlS
  exact noLin_trge_empty hnlT w.source.target

/-- Runtime spaces rebuilt by the existential cut need only preserve the
numeric facts used by a surrounding linear-lambda assembler.  The second
field makes that equality stable when either realization is wrapped in an
arbitrary FFS node. -/
structure CutSpaceRel (target source : ValSpace) : Prop where
  dofUB_eq : ValSpace.dofUB target = ValSpace.dofUB source
  ffs_dofUB_eq : forall p valueT valueS,
    ValSpace.dofUB (.ffs p target valueT) =
      ValSpace.dofUB (.ffs p source valueS)

def CutSpaceRel.empty : CutSpaceRel .empty .empty where
  dofUB_eq := rfl
  ffs_dofUB_eq := by intro p _ _; cases p <;> rfl

def CutSpaceRel.real : CutSpaceRel .real .real where
  dofUB_eq := rfl
  ffs_dofUB_eq := by intro p _ _; cases p <;> rfl

def CutSpaceRel.dsum (h0 : CutSpaceRel aT aS)
    (h1 : CutSpaceRel bT bS) :
    CutSpaceRel (.dsum aT bT) (.dsum aS bS) where
  dofUB_eq := by
    simp only [ValSpace.dofUB, h0.dofUB_eq, h1.dofUB_eq]
  ffs_dofUB_eq := by
    intro p _ _
    cases p <;> simp only [ValSpace.dofUB] <;>
      rw [h0.dofUB_eq, h1.dofUB_eq]

def CutSpaceRel.tprod (h0 : CutSpaceRel aT aS)
    (h1 : CutSpaceRel bT bS) :
    CutSpaceRel (.tprod aT bT) (.tprod aS bS) where
  dofUB_eq := by
    simp only [ValSpace.dofUB, h0.dofUB_eq, h1.dofUB_eq]
  ffs_dofUB_eq := by
    intro p _ _
    cases p
    · exact h0.dofUB_eq
    · exact h0.dofUB_eq
    · exact h1.dofUB_eq
    · exact h1.dofUB_eq

def CutSpaceRel.ffs (h : CutSpaceRel parentT parentS) :
    CutSpaceRel (.ffs p parentT valueT) (.ffs p parentS valueS) where
  dofUB_eq := h.ffs_dofUB_eq p valueT valueS
  ffs_dofUB_eq := by
    intro q _ _
    cases q <;> exact h.ffs_dofUB_eq p valueT valueS

theorem CutSpaceRel.tprod_left_dof
    (h : CutSpaceRel (.tprod aT bT) (.tprod aS bS)) :
    ValSpace.dofUB aT = ValSpace.dofUB aS := by
  simpa only [ValSpace.dofUB] using
    h.ffs_dofUB_eq .kernel (.zero .empty) (.zero .empty)

theorem CutSpaceRel.tprod_right_dof
    (h : CutSpaceRel (.tprod aT bT) (.tprod aS bS)) :
    ValSpace.dofUB bT = ValSpace.dofUB bS := by
  simpa only [ValSpace.dofUB] using
    h.ffs_dofUB_eq .image (.zero .empty) (.zero .empty)

def CutSpaceRel.tprodOfDof
    (h0 : ValSpace.dofUB aT = ValSpace.dofUB aS)
    (h1 : ValSpace.dofUB bT = ValSpace.dofUB bS) :
    CutSpaceRel (.tprod aT bT) (.tprod aS bS) where
  dofUB_eq := by simp only [ValSpace.dofUB, h0, h1]
  ffs_dofUB_eq := by
    intro p _ _
    cases p <;> simp only [ValSpace.dofUB] <;> assumption

def CutSpaceRel.ffsTail
    (hParent : CutSpaceRel parentT parentS)
    (hTail : ValSpace.dofUB tailT = ValSpace.dofUB tailS) :
    CutSpaceRel
      (.tprod (.ffs p parentT valueT) tailT)
      (.tprod (.ffs p parentS valueS) tailS) where
  dofUB_eq := by
    simp only [ValSpace.dofUB, hParent.ffs_dofUB_eq p valueT valueS, hTail]
  ffs_dofUB_eq := by
    intro q _ _
    cases q <;> simp only [ValSpace.dofUB]
    · exact hParent.ffs_dofUB_eq p valueT valueS
    · exact hParent.ffs_dofUB_eq p valueT valueS
    · exact hTail
    · exact hTail

/-- The existential cut preserves the outer value-type shape.  At a space
leaf it retains the stronger FFS-aware relation above; dependent codomains
need only retain their `piTy` head because they are closed from one chosen
fresh realization. -/
inductive CutTyRel : ValTy -> ValTy -> Prop
  | space : CutSpaceRel target source ->
      CutTyRel (.space target) (.space source)
  | piTy : CutTyRel (.piTy domT codT) (.piTy domS codS)

private theorem CutTyRel.space_inv
    (h : CutTyRel tauT (.space svS)) :
    exists svT, tauT = .space svT /\ CutSpaceRel svT svS := by
  cases h with
  | space hrel => exact ⟨_, rfl, hrel⟩

private theorem checkedTyAt_tprod_dual
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis} {sv0 sv1 : ValSpace}
    (hb : BasisValid Gamma (.tprod (.dual b0) b1))
    (his : Basis.IsTyBasis (.tprod (.dual b0) b1))
    (h0 : C.Space Gamma Psi (Basis.sof b0) sv0)
    (h1 : C.Space Gamma Psi (Basis.sof b1) sv1) :
    C.TyAt Gamma Psi (.tprod (.dual b0) b1) (.space (.tprod sv0 sv1)) := by
  obtain ⟨hv⟩ := hb.sof_valid
  change SValid Gamma (.tprod (.dual (Basis.sof b0)) (Basis.sof b1)) at hv
  cases hv with
  | tprod hv0 hv1 =>
      exact .space rfl hb
        (.tprod ⟨.tprod hv0 hv1⟩ (.dual ⟨hv0⟩ h0) h1)

private theorem checkedSpace_tprod_value_inv
    (h : C.Space Gamma Psi (.tprod s0 s1) sv) :
    exists sv0 sv1, sv = .tprod sv0 sv1 :=
  h.toS.tprod_value_inv

private def CheckedSpaceParts (Gamma : NLCtx) (Psi : EvalCtx)
    (s : Space) (sv : ValSpace) : Prop :=
  match s with
  | .dual s0 => C.Space Gamma Psi s0 sv
  | .tprod s0 s1 => exists sv0 sv1, sv = .tprod sv0 sv1 /\
      C.Space Gamma Psi s0 sv0 /\ C.Space Gamma Psi s1 sv1
  | _ => True

private theorem checkedSpace_parts :
    forall {Gamma : NLCtx} {Psi : EvalCtx} {s : Space} {sv : ValSpace},
      C.Space Gamma Psi s sv -> CheckedSpaceParts Gamma Psi s sv := by
  intro Gamma Psi s sv h
  refine C.Space.rec
    (motive_1 := fun Gamma Psi s sv _ => CheckedSpaceParts Gamma Psi s sv)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ _ _ _ => True)
    ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
    ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
    ?tySpace ?tyPi
    ?tyAtSpace ?tyAtFrame
    ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
    ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
    ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
    ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
    ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
    ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
    ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
    ?termAppL ?termAppI ?termNllam ?termAppNVal
    ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
    ?termZero ?termRlit h
  case spaceDual =>
    intros
    simpa only [CheckedSpaceParts] using
      (by assumption : C.Space _ _ _ _)
  case spaceTprod =>
    intros
    simp only [CheckedSpaceParts]
    exact ⟨_, _, rfl, by assumption, by assumption⟩
  all_goals intros <;> trivial

/-- Full tensor-space inversion, exposing the two component certificates. -/
theorem checkedSpace_tprod_inv_full
    (h : C.Space Gamma Psi (.tprod s0 s1) sv) :
    exists sv0 sv1, sv = .tprod sv0 sv1 /\
      C.Space Gamma Psi s0 sv0 /\ C.Space Gamma Psi s1 sv1 :=
  checkedSpace_parts h

/-- Full dual-space inversion, exposing the underlying space certificate. -/
theorem checkedSpace_dual_inv_full
    (h : C.Space Gamma Psi (.dual s) sv) : C.Space Gamma Psi s sv :=
  checkedSpace_parts h

private theorem checkedSpace_real_eq
    (h : C.Space Gamma Psi .real sv) : sv = .real :=
  evalS_real_eq h.erase

private theorem checkedTyAt_space_tof_eq
    (h : C.TyAt Gamma Psi b (.space sv)) :
    Basis.tof b = .space (Basis.sof b) := by
  obtain ⟨s, hs, _⟩ := ValTy.EvalT.space_inv h.erase
  exact Basis.tof_eq_space_sof_of_tof_space hs

/-- Checked counterpart of the graded backward variable-shape lemma.  A
nonzero affine variable can land either in the target linear singleton or in
the target nonlinear context; the store and `TyAt` data are shared by both
branches. -/
private noncomputable def checked_gvar_shape
    {F : GCtx} {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {z : VName} {g : GGrade} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (htr : TrGe F Delta Gamma)
    (hz : F z = some (g, Basis.tof b)) (hg : g ≠ GGrade.zero)
    (haff : forall y, y ≠ z -> forall tau,
      F y ≠ some (GGrade.one, tau))
    (hlook : EvalCtx.lookup Psi (z, b) = some v)
    (hbv : BasisValid Gamma b) (hTy : C.TyAt Gamma Psi b tauV) :
    C.Term Delta Gamma Psi (.var z) b v tauV := by
  have hsub : forall y, y ≠ z -> Delta.lookup y = none := by
    intro y hyz
    rcases hDelta : Delta.lookup y with _ | sy
    · rfl
    · exfalso
      have htry : tr Delta Gamma y = some (GGrade.one, .space sy) := by
        simp only [tr, hDelta]
      have hw := htr y
      rw [htry] at hw
      have : F y = some (GGrade.one, .space sy) := by
        rcases hfy : F y with _ | ⟨gy, tauy⟩
        · rw [hfy] at hw
          exact absurd rfl hw
        · rw [hfy] at hw
          cases gy <;> simp_all [WkPt0, GGrade.Wk]
      exact haff y hyz (.space sy) this
  rcases hDeltaZ : Delta.lookup z with _ | sz
  · have hDeltaEmpty : Delta = ∅ := by
      apply Finmap.ext_lookup
      intro y
      rw [Finmap.lookup_empty]
      rcases eq_or_ne y z with rfl | hyz
      · exact hDeltaZ
      · exact hsub y hyz
    subst hDeltaEmpty
    have hw := htr z
    rw [hz] at hw
    have hGamma : Gamma.lookup z = some (Basis.tof b) := by
      rcases hG : Gamma.lookup z with _ | tauG
      · exfalso
        have ht : tr (∅ : LCtx) Gamma z = none := by
          simp only [tr, Finmap.lookup_empty, hG]
        rw [ht] at hw
        cases g <;> simp_all [WkPt0]
      · have ht : tr (∅ : LCtx) Gamma z =
            some (GGrade.omega, tauG) := by
          simp only [tr, Finmap.lookup_empty, hG]
        rw [ht] at hw
        have heq : Basis.tof b = tauG := by
          cases g <;> simp_all [WkPt0, GGrade.Wk]
        simpa only [hG, heq]
    exact .var_nlin hlook hGamma hbv hTy
  · have hDeltaSingle : Delta = Finmap.singleton z sz := by
      apply Finmap.ext_lookup
      intro y
      rcases eq_or_ne y z with rfl | hyz
      · rw [hDeltaZ, Finmap.lookup_singleton_eq]
      · rw [hsub y hyz, Finmap.lookup_eq_none.mpr (by
          rw [Finmap.mem_singleton]
          exact hyz)]
    have hw := htr z
    rw [hz] at hw
    have htrz : tr Delta Gamma z = some (GGrade.one, .space sz) := by
      simp only [tr, hDeltaZ]
    rw [htrz] at hw
    have htof : Basis.tof b = .space sz := by
      cases g <;> simp_all [WkPt0, GGrade.Wk]
    rw [hDeltaSingle]
    exact .var_lin hlook htof hbv hTy

private theorem SomeTermCutCtx.targetLinear_singleton_self
    (w : SomeTermCutCtx x bX tauVX n arg Gamma0
      (Finmap.singleton x s) GammaS PsiS DeltaT GammaT PsiT) :
    DeltaT = ∅ := by
  have hnl : NoLin
      (gsubstCtx x n Gamma0 (tr (Finmap.singleton x s : LCtx) GammaS)) := by
    intro z tau hz
    rcases eq_or_ne z x with rfl | hzx
    · simp [gsubstCtx] at hz
    · rw [gsubstCtx, if_neg hzx, mapSubstTy] at hz
      rcases hh : gadd (tr (Finmap.singleton x s : LCtx) GammaS z)
          (tr (∅ : LCtx) Gamma0 z) with _ | ⟨g, tau'⟩
      · rw [hh] at hz
        contradiction
      · rw [hh] at hz
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hz
        exact gadd_noLin_grade
          (fun g' tau'' hs hg' =>
            tr_singleton_no_lin x s GammaS z hzx tau'' (hg' ▸ hs))
          (trEmpty_hn Gamma0 z) (by rw [hh, hz.1])
  exact noLin_trge_empty hnl w.source.target

namespace CheckedSubstBinder

open RenameProof
open RawCertifiedPiBasisTransport

theorem termNllam_arbitrary_cofinite_of_fresh
    {Gamma : NLCtx} {Psi : EvalCtx} {z : VName}
    {b0 b1 : Basis} {tauV0 tauBody : ValTy}
    {e : Term} {vBody : ValExpr}
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hb0 : Basis.BasisValid Gamma b0)
    (hzGamma : z ∉ Gamma)
    (hbody : C.Term (∅ : LCtx)
      (Finmap.insert z (Basis.tof b0) Gamma)
      (Psi.extend z b0 (.var z tauV0))
      (Term.openVar z e) (Basis.openVar z b1) vBody tauBody)
    (hzPsi : z ∉ EvalCtx.avoidB Psi)
    (hzb0 : z ∉ Basis.fv b0)
    (hztauV0 : z ∉ ValTy.fv tauV0)
    (hze : z ∉ Term.fv e)
    (hzb1 : z ∉ Basis.fv b1)
    (hlctauV0 : ValTy.lc tauV0)
    (hlcvBody : ValExpr.lc vBody)
    (hlctauBody : ValTy.lc tauBody) :
    exists L : Finset VName, forall y, y ∉ L ->
      C.Term (∅ : LCtx) (Finmap.insert y (Basis.tof b0) Gamma)
        (Psi.extend y b0 (.var y tauV0))
        (Term.openVar y e) (Basis.openVar y b1)
        (ValExpr.openVar y tauV0 (ValExpr.closeRec 0 z vBody))
        (ValTy.openVar y tauV0 (ValTy.closeRec 0 z tauBody)) := by
  refine ⟨EvalCtx.avoidB Psi ∪ Gamma.keys ∪ {z}, ?_⟩
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨hyPsi, hyGammaKeys⟩, hyz⟩ := hy
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  have ht0 : exists k, Nonempty (TValid Gamma (Basis.tof b0) k) :=
    hb0.tof_tvalid
  have ready : TermReady y (∅ : LCtx)
      (Finmap.insert z (Basis.tof b0) Gamma) :=
    TermReady.empty <| (NLReady.ofWF hwf hyGamma).insert
      hyz (freshTy_of_valid hyGamma (Classical.choice
        (Classical.choose_spec ht0)))
  have hes := ESubst.rename hzPsi hyPsi hzb0 hztauV0 hlctauV0
  have hr := checkedRenameTermCore (Ne.symm hyz) hbody ready
    (Or.inl ⟨y, tauV0, rfl⟩) hes
  have hsrcT : Term.subst z (.var y) (Term.openVar z e) =
      Term.openVar y e := (Term.subst_intro z (.var y) e hze 0).symm
  have hsrcB : Basis.subst z (.var y) (Basis.openVar z b1) =
      Basis.openVar y b1 := (Basis.subst_intro z (.var y) b1 hzb1 0).symm
  rw [renameLCtx_empty, renameNLCtx_insert, Equiv.swap_apply_left,
    Ty.subst_fresh z (.var y) (Basis.tof b0)
      (freshTy_of_valid hzGamma (Classical.choice
        (Classical.choose_spec ht0))),
    renameNLCtx_eq_self hzGamma hyGamma
      (nlctxFresh_of_ctxWF hwf hzGamma),
    hsrcT, hsrcB] at hr
  rw [ValExpr.openVar_closeRec_of_lc z y tauV0 hlcvBody,
    ValTy.openVar_closeRec_of_lc z y tauV0 hlctauBody]
  exact hr

/-- The nonlinear-lambda binder itself closes once its domain and a single
fresh transformed body have been chosen. -/
theorem termNllam_of_one_fresh
    (laws : CheckedRenameLaws)
    {Gamma : NLCtx} {Psi : EvalCtx} {z : VName}
    {b0 b1 : Basis} {tauV0 tauBody : ValTy}
    {e : Term} {vBody : ValExpr}
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hbv : Basis.BasisValid Gamma (.frame b0 b1))
    (hisTy : Basis.IsTyBasis (.frame b0 b1))
    (ht : Nonempty (HasType (∅ : LCtx) Gamma (.nllam (Basis.tof b0) e)
      (Basis.tof (.frame b0 b1))))
    (hdom : C.TyAt Gamma Psi b0 tauV0)
    (hbody : C.Term (∅ : LCtx)
      (Finmap.insert z (Basis.tof b0) Gamma)
      (Psi.extend z b0 (.var z tauV0))
      (Term.openVar z e) (Basis.openVar z b1) vBody tauBody)
    (hbodyTy : C.TyAt (Finmap.insert z (Basis.tof b0) Gamma)
      (Psi.extend z b0 (.var z tauV0))
      (Basis.openVar z b1) tauBody)
    (hzGamma : z ∉ Gamma)
    (hzPsi : z ∉ EvalCtx.avoidB Psi)
    (hzb0 : z ∉ Basis.fv b0)
    (hztauV0 : z ∉ ValTy.fv tauV0)
    (hze : z ∉ Term.fv e)
    (hzb1 : z ∉ Basis.fv b1)
    (hlctauV0 : ValTy.lc tauV0)
    (hlcvBody : ValExpr.lc vBody)
    (hlctauBody : ValTy.lc tauBody) :
    exists vOut tauOut,
      C.Term (∅ : LCtx) Gamma Psi (.nllam (Basis.tof b0) e)
        (.frame b0 b1) vOut tauOut := by
  have hb0 : Basis.BasisValid Gamma b0 := hbv.frame_inv.1
  obtain ⟨LT, hterms⟩ := termNllam_arbitrary_cofinite_of_fresh
    hwf hb0 hzGamma hbody hzPsi hzb0 hztauV0 hze hzb1
    hlctauV0 hlcvBody hlctauBody
  obtain ⟨LY, htypes⟩ := checkedTyAt_arbitrary_cofinite_of_fresh
    laws hwf (hb0.tof_tvalid) rfl hb0 hzGamma
    hbodyTy hzPsi hzb0 hztauV0 hzb1 hlctauV0 hlctauBody
  let env := ValExpr.closeRec 0 z vBody
  let tauV1 := ValTy.closeRec 0 z tauBody
  have hframe : C.TyAt Gamma Psi (.frame b0 b1) (.piTy tauV0 tauV1) :=
    .frame hbv hdom LY (by simpa only [tauV1] using htypes)
  have hout := C.Term.nllam (b₀ := b0) (b₁ := b1) (env := env)
    rfl rfl ht hbv hframe hdom (LT ∪ LY)
    (fun y hy => by
      have hyT : y ∉ LT := fun hm => hy (Finset.mem_union_left _ hm)
      simpa only [env, tauV1] using hterms y hyT)
    (fun y hy => by
      have hyY : y ∉ LY := fun hm => hy (Finset.mem_union_right _ hm)
      simpa only [tauV1] using htypes y hyY)
  exact ⟨_, _, hout⟩

/-- Frame-eta has the same one-fresh reconstruction shape. -/
theorem termFrameEta_of_one_fresh
    (laws : CheckedRenameLaws)
    {Gamma : NLCtx} {Psi : EvalCtx} {z : VName}
    {b0 b1 : Basis} {tauV0 tauBody : ValTy}
    {n0 : Term} {vBody : ValExpr}
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hbv : Basis.BasisValid Gamma (.frame b0 b1))
    (hisTy : Basis.IsTyBasis (.frame b0 b1))
    (ht : Nonempty (HasType (∅ : LCtx) Gamma n0
      (Basis.tof (.frame b0 b1))))
    (hdom : C.TyAt Gamma Psi b0 tauV0)
    (hbody : C.Term (∅ : LCtx)
      (Finmap.insert z (Basis.tof b0) Gamma)
      (Psi.extend z b0 (.var z tauV0))
      (.appN n0 (.var z)) (Basis.openVar z b1) vBody tauBody)
    (hbodyTy : C.TyAt (Finmap.insert z (Basis.tof b0) Gamma)
      (Psi.extend z b0 (.var z tauV0))
      (Basis.openVar z b1) tauBody)
    (hzGamma : z ∉ Gamma)
    (hzPsi : z ∉ EvalCtx.avoidB Psi)
    (hzb0 : z ∉ Basis.fv b0)
    (hztauV0 : z ∉ ValTy.fv tauV0)
    (hzn0 : z ∉ Term.fv n0)
    (hzb1 : z ∉ Basis.fv b1)
    (hlctauV0 : ValTy.lc tauV0)
    (hlcvBody : ValExpr.lc vBody)
    (hlctauBody : ValTy.lc tauBody) :
    exists vOut tauOut,
      C.Term (∅ : LCtx) Gamma Psi n0 (.frame b0 b1) vOut tauOut := by
  have hb0 : Basis.BasisValid Gamma b0 := hbv.frame_inv.1
  obtain ⟨LT, hterms⟩ := checkedTerm_arbitrary_frameEta_cofinite_of_fresh
    laws hwf (hb0.tof_tvalid) rfl hb0 hzGamma
    hbody hzPsi hzb0 hztauV0 hzn0 hzb1 hlctauV0 hlcvBody hlctauBody
  obtain ⟨LY, htypes⟩ := checkedTyAt_arbitrary_cofinite_of_fresh
    laws hwf (hb0.tof_tvalid) rfl hb0 hzGamma
    hbodyTy hzPsi hzb0 hztauV0 hzb1 hlctauV0 hlctauBody
  let env := ValExpr.closeRec 0 z vBody
  let tauV1 := ValTy.closeRec 0 z tauBody
  have hframe : C.TyAt Gamma Psi (.frame b0 b1) (.piTy tauV0 tauV1) :=
    .frame hbv hdom LY (by simpa only [tauV1] using htypes)
  have hout := C.Term.frame_eta (env := env) ht hbv hframe hdom
    (LT ∪ LY)
    (fun y hy => by
      have hyT : y ∉ LT := fun hm => hy (Finset.mem_union_left _ hm)
      simpa only [env, tauV1] using hterms y hyT)
    (fun y hy => by
      have hyY : y ∉ LY := fun hm => hy (Finset.mem_union_right _ hm)
      simpa only [tauV1] using htypes y hyY)
  exact ⟨_, _, hout⟩

/-- Arbitrary-basis linear cofinite packaging. -/
theorem termLlam_arbitrary_cofinite_of_placeholder
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {x : VName}
    {s : Space} {sv : ValSpace} {tauV : ValTy}
    {bIn bOut : Basis} {e : Term} {v : ValExpr}
    (hwf : V2.CtxWF' Delta Gamma)
    (hs : Nonempty (SValid Gamma s))
    (hxDelta : x ∉ Delta) (hxGamma : x ∉ Gamma)
    (h : C.Term (Finmap.insert x s Delta) Gamma
      (Psi.extend x bIn (.var x (.space sv)))
      (Term.openVar x e) bOut v tauV)
    (hxPsi : x ∉ EvalCtx.avoidB Psi)
    (hxbIn : x ∉ Basis.fv bIn)
    (hxsv : x ∉ ValSpace.fv sv)
    (hxe : x ∉ Term.fv e)
    (hxbOut : x ∉ Basis.fv bOut)
    (hxtauV : x ∉ ValTy.fv tauV)
    (hlcsv : ValSpace.lc sv) :
    exists L : Finset VName, forall y, y ∉ L -> forall i : Nat,
      C.Term (Finmap.insert y s Delta) Gamma
        (Psi.extend y bIn (.delta i sv))
        (Term.openVar y e) bOut
        (ValExpr.subst x (.delta i sv) v) tauV := by
  refine ⟨EvalCtx.avoidB Psi ∪ Delta.keys ∪ Gamma.keys ∪ {x}, ?_⟩
  intro y hy i
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨⟨hyPsi, hyDeltaKeys⟩, hyGammaKeys⟩, hyx⟩ := hy
  have hyDelta : y ∉ Delta := by
    intro hm
    exact hyDeltaKeys (Finmap.mem_keys.mpr hm)
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  obtain ⟨hsv⟩ := hs
  have ready : TermReady y (Finmap.insert x s Delta) Gamma :=
    (TermReady.ofWF hwf hyDelta hyGamma).insertL hyx
      (freshSpace_of_valid hyGamma hsv) hxGamma
  have hes := ESubst.delta (i := i) hxPsi hyPsi hxbIn hxsv hlcsv
  have hr := checkedRenameTermCore (Ne.symm hyx) h ready
    (Or.inr ⟨i, sv, rfl⟩) hes
  have hDelta : renameLCtx x y Delta = Delta :=
    renameLCtx_eq_self hxDelta hyDelta
      (lctxFresh_of_ctxWF hwf hxGamma)
  have hGamma : renameNLCtx x y Gamma = Gamma :=
    renameNLCtx_eq_self hxGamma hyGamma
      (nlctxFresh_of_ctxWF hwf hxGamma)
  have hxS : x ∉ Space.fv s := freshSpace_of_valid hxGamma hsv
  have hsrcT : Term.subst x (.var y) (Term.openVar x e) =
      Term.openVar y e := (Term.subst_intro x (.var y) e hxe 0).symm
  rw [renameLCtx_insert, Equiv.swap_apply_left,
    Space.subst_fresh x (.var y) s hxS, hDelta, hGamma,
    hsrcT, Basis.subst_fresh x (.var y) bOut hxbOut,
    ValTy.subst_fresh x (.delta i sv) tauV hxtauV] at hr
  exact hr

/-- Finite-family form used by the actual `llam_assemble` arm.  One common
freshness set works for every column because its contents depend only on the
outer contexts and the symbolic binder data, not on `i`. -/
theorem termLlam_arbitrary_family_cofinite_of_placeholder
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {x : VName}
    {s : Space} {sv : ValSpace} {tauV : ValTy} {ncol : Nat}
    {bIn bOut : Basis} {e : Term} {v : Fin ncol -> ValExpr}
    (hwf : V2.CtxWF' Delta Gamma)
    (hs : Nonempty (SValid Gamma s))
    (hxDelta : x ∉ Delta) (hxGamma : x ∉ Gamma)
    (h : forall i : Fin ncol,
      C.Term (Finmap.insert x s Delta) Gamma
        (Psi.extend x bIn (.var x (.space sv)))
        (Term.openVar x e) bOut (v i) tauV)
    (hxPsi : x ∉ EvalCtx.avoidB Psi)
    (hxbIn : x ∉ Basis.fv bIn)
    (hxsv : x ∉ ValSpace.fv sv)
    (hxe : x ∉ Term.fv e)
    (hxbOut : x ∉ Basis.fv bOut)
    (hxtauV : x ∉ ValTy.fv tauV)
    (hlcsv : ValSpace.lc sv) :
    exists L : Finset VName, forall y, y ∉ L -> forall i : Fin ncol,
      C.Term (Finmap.insert y s Delta) Gamma
        (Psi.extend y bIn (.delta i.val sv))
        (Term.openVar y e) bOut
        (ValExpr.subst x (.delta i.val sv) (v i)) tauV := by
  refine ⟨EvalCtx.avoidB Psi ∪ Delta.keys ∪ Gamma.keys ∪ {x}, ?_⟩
  intro y hy i
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨⟨hyPsi, hyDeltaKeys⟩, hyGammaKeys⟩, hyx⟩ := hy
  have hyDelta : y ∉ Delta := by
    intro hm
    exact hyDeltaKeys (Finmap.mem_keys.mpr hm)
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  obtain ⟨hsv⟩ := hs
  have ready : TermReady y (Finmap.insert x s Delta) Gamma :=
    (TermReady.ofWF hwf hyDelta hyGamma).insertL hyx
      (freshSpace_of_valid hyGamma hsv) hxGamma
  have hes := ESubst.delta (i := i.val) hxPsi hyPsi hxbIn hxsv hlcsv
  have hr := checkedRenameTermCore (Ne.symm hyx) (h i) ready
    (Or.inr ⟨i.val, sv, rfl⟩) hes
  have hDelta : renameLCtx x y Delta = Delta :=
    renameLCtx_eq_self hxDelta hyDelta
      (lctxFresh_of_ctxWF hwf hxGamma)
  have hGamma : renameNLCtx x y Gamma = Gamma :=
    renameNLCtx_eq_self hxGamma hyGamma
      (nlctxFresh_of_ctxWF hwf hxGamma)
  have hxS : x ∉ Space.fv s := freshSpace_of_valid hxGamma hsv
  have hsrcT : Term.subst x (.var y) (Term.openVar x e) =
      Term.openVar y e := (Term.subst_intro x (.var y) e hxe 0).symm
  rw [renameLCtx_insert, Equiv.swap_apply_left,
    Space.subst_fresh x (.var y) s hxS, hDelta, hGamma,
    hsrcT, Basis.subst_fresh x (.var y) bOut hxbOut,
    ValTy.subst_fresh x (.delta i.val sv) tauV hxtauV] at hr
  exact hr

/-- Once the cut recursion supplies a common target domain/codomain
realization and one symbolic target body per column, the complete linear
lambda rule is immediate. -/
theorem termLlam_of_symbolic_family
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {x : VName}
    {bIn bOut : Basis} {e : Term} {svIn svOut : ValSpace}
    {v : Fin (ValSpace.dofUB svIn) -> ValExpr}
    (hwf : V2.CtxWF' Delta Gamma)
    (hsIn : Nonempty (SValid Gamma (Basis.sof bIn)))
    (hxDelta : x ∉ Delta) (hxGamma : x ∉ Gamma)
    (hbody : forall i : Fin (ValSpace.dofUB svIn),
      C.Term (Finmap.insert x (Basis.sof bIn) Delta) Gamma
        (Psi.extend x bIn (.var x (.space svIn)))
        (Term.openVar x e) bOut (v i) (.space svOut))
    (hxPsi : x ∉ EvalCtx.avoidB Psi)
    (hxbIn : x ∉ Basis.fv bIn)
    (hxsvIn : x ∉ ValSpace.fv svIn)
    (hxe : x ∉ Term.fv e)
    (hxbOut : x ∉ Basis.fv bOut)
    (hxsvOut : x ∉ ValSpace.fv svOut)
    (hlcsvIn : ValSpace.lc svIn)
    (htofIn : Basis.tof bIn = .space (Basis.sof bIn))
    (ht : Nonempty (HasType Delta Gamma
      (.llam (Basis.sof bIn) (Basis.sof bOut) e)
      (Basis.tof (.tprod (.dual bIn) bOut))))
    (hbv : Basis.BasisValid Gamma (.tprod (.dual bIn) bOut))
    (hTy : C.TyAt Gamma Psi (.tprod (.dual bIn) bOut)
      (.space (.tprod svIn svOut)))
    (hspaceIn : C.Space Gamma Psi (Basis.sof bIn) svIn)
    (hspaceOut : C.Space Gamma Psi (Basis.sof bOut) svOut) :
    exists value,
      C.Term Delta Gamma Psi
        (.llam (Basis.sof bIn) (Basis.sof bOut) e)
        (.tprod (.dual bIn) bOut) value (.space (.tprod svIn svOut)) := by
  obtain ⟨L, hfamily⟩ := termLlam_arbitrary_family_cofinite_of_placeholder
    hwf hsIn hxDelta hxGamma hbody hxPsi hxbIn hxsvIn hxe hxbOut
    (by simp only [ValTy.fv]; exact hxsvOut) hlcsvIn
  let env : Fin (ValSpace.dofUB svIn) -> ValExpr := fun i =>
    ValExpr.subst x (.delta i.val svIn) (v i)
  refine ⟨_, C.Term.llam_assemble (env := env) htofIn ht hbv hTy
    hspaceIn hspaceOut L ?_⟩
  intro y hy i
  simpa only [env] using hfamily y hy i

/-- Alpha-package a checked evaluation of the binder variable at an
arbitrary re-anchored domain basis. -/
theorem checkedTerm_arbitrary_var_cofinite_of_fresh
    (laws : CheckedRenameLaws)
    {Gamma : NLCtx} {Psi : EvalCtx} {z : VName}
    {tau0 : Ty} {tauV0 tauAnchor : ValTy} {b0 bAnchor : Basis}
    {vAnchor : ValExpr}
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (htau0 : exists k, Nonempty (TValid Gamma tau0 k))
    (htof0 : Basis.tof b0 = tau0)
    (hb0 : Basis.BasisValid Gamma b0)
    (hzGamma : z ∉ Gamma)
    (h : C.Term (∅ : LCtx) (Finmap.insert z tau0 Gamma)
      (Psi.extend z b0 (.var z tauV0)) (.var z) bAnchor
      vAnchor tauAnchor)
    (hzPsi : z ∉ EvalCtx.avoidB Psi)
    (hzb0 : z ∉ Basis.fv b0)
    (hztauV0 : z ∉ ValTy.fv tauV0)
    (hzbAnchor : z ∉ Basis.fv bAnchor)
    (hztauAnchor : z ∉ ValTy.fv tauAnchor)
    (hlctauV0 : ValTy.lc tauV0)
    (hlcvAnchor : ValExpr.lc vAnchor) :
    exists L : Finset VName, forall y, y ∉ L ->
      C.Term (∅ : LCtx) (Finmap.insert y tau0 Gamma)
        (Psi.extend y b0 (.var y tauV0)) (.var y) bAnchor
        (ValExpr.openVar y tauV0 (ValExpr.closeRec 0 z vAnchor))
        tauAnchor := by
  refine ⟨EvalCtx.avoidB Psi ∪ Gamma.keys ∪ {z}, ?_⟩
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨hyPsi, hyGammaKeys⟩, hyz⟩ := hy
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  have hes := ESubst.rename hzPsi hyPsi hzb0 hztauV0 hlctauV0
  have hr := laws.term_nl hwf htau0 htof0 hb0 hzGamma hyGamma
    (Ne.symm hyz) hes h
  rw [show Term.subst z (.var y) (.var z) = .var y by
        simp [Term.subst],
      Basis.subst_fresh z (.var y) bAnchor hzbAnchor,
      ValTy.subst_fresh z (.var y tauV0) tauAnchor hztauAnchor] at hr
  rw [ValExpr.openVar_closeRec_of_lc z y tauV0 hlcvAnchor]
  exact hr

end CheckedSubstBinder

private theorem alignGram
    {x : VName} {bX : Basis} {tauVX : ValTy}
    {n : Term} {arg : ValExpr} {Gamma0 : NLCtx}
    {GammaS GammaT : NLCtx} {PsiS PsiT : EvalCtx}
    {b : Basis} {s : Space} {env : ValExpr} {sv : ValSpace}
    (hsof : Basis.sof b = s)
    (hi : C.Term ∅ GammaS PsiS (.inner s)
      (.tprod (.dual b) (.dual b)) env (.space (.tprod sv sv)))
    (ih : forall {Delta' : LCtx} {Gamma' : NLCtx} {Psi' : EvalCtx},
      SomeTermCutCtx x bX tauVX n arg Gamma0
        ∅ GammaS PsiS Delta' Gamma' Psi' ->
      exists vT tauT,
        C.Term Delta' Gamma' Psi' (Term.subst x n (.inner s))
          (Basis.subst x n (.tprod (.dual b) (.dual b))) vT tauT /\
        CutTyRel tauT (.space (.tprod sv sv)))
    (w : SomeTermCutCtx x bX tauVX n arg Gamma0
      ∅ GammaS PsiS ∅ GammaT PsiT) :
    exists svT envT,
      C.Space GammaT PsiT (Basis.sof (Basis.subst x n b)) svT /\
      C.Term ∅ GammaT PsiT (.inner (Basis.sof (Basis.subst x n b)))
        (.tprod (.dual (Basis.subst x n b)) (.dual (Basis.subst x n b)))
        envT (.space (.tprod svT svT)) /\
      ValSpace.dofUB svT = ValSpace.dofUB sv := by
  let bT := Basis.subst x n b
  obtain ⟨envRaw, tauRaw, hiRaw0, htyRel⟩ := ih w
  obtain ⟨svRel, rfl, hspaceRel⟩ := CutTyRel.space_inv htyRel
  have hiRaw : C.Term ∅ GammaT PsiT (Term.subst x n (.inner s))
      (.tprod (.dual bT) (.dual bT)) envRaw (.space svRel) := by
    simpa only [Basis.subst, bT] using hiRaw0
  obtain ⟨svEval, heq, hspaceGram⟩ :=
    RawCertifiedProgressScratch.checkedTyAt_space_inv_full rfl hiRaw.tyAt
  injection heq with heqSpace
  subst svEval
  obtain ⟨svT, svOtherT, rfl, hdualT, _⟩ :=
    checkedSpace_tprod_inv_full hspaceGram
  have hspaceT := checkedSpace_dual_inv_full hdualT
  have hdof : ValSpace.dofUB svT = ValSpace.dofUB sv :=
    CutSpaceRel.tprod_left_dof hspaceRel
  have hbvT : BasisValid GammaT
      (.tprod (.dual bT) (.dual bT)) := by
    simpa only [Basis.subst, bT] using
      w.source.typeCtx.basisValid hi.basisValid
  have hspaceDup : C.Space GammaT PsiT
      (Basis.sof (.tprod (.dual bT) (.dual bT)))
      (.tprod svT svT) :=
    .tprod hbvT.sof_valid
      (.dual hbvT.tprod_inv.1.sof_valid hspaceT)
      (.dual hbvT.tprod_inv.2.sof_valid hspaceT)
  have hTyDup : C.TyAt GammaT PsiT
      (.tprod (.dual bT) (.dual bT)) (.space (.tprod svT svT)) :=
    .space rfl hbvT hspaceDup
  let envT := ValExpr.reshap envRaw (.space (.tprod svT svT))
    (.space (.tprod svT svOtherT))
  have hiT0 : C.Term ∅ GammaT PsiT (Term.subst x n (.inner s))
      (.tprod (.dual bT) (.dual bT)) envT
      (.space (.tprod svT svT)) :=
    RawCertifiedProgressScratch.retag hiRaw hTyDup
  have hiT : C.Term ∅ GammaT PsiT (.inner (Basis.sof bT))
      (.tprod (.dual bT) (.dual bT)) envT
      (.space (.tprod svT svT)) := by
    simpa only [Term.subst, Basis.sof_subst, hsof, bT] using hiT0
  exact ⟨svT, envT, hspaceT, hiT, hdof⟩

/-! ## Five-way existential checked cut -/

set_option maxHeartbeats 3200000 in
theorem checkedTyAt_someSubstCore_of_rename
    (laws : CheckedRenameLaws)
    {x : VName} {bX : Basis} {tauVX : ValTy} {n : Term} {arg : ValExpr}
    {Gamma0 GammaS GammaT : NLCtx} {PsiS PsiT : EvalCtx}
    {b : Basis} {tauV : ValTy}
    (h : C.TyAt GammaS PsiS b tauV)
    (w : SomeCutCtx x bX tauVX n arg Gamma0 GammaS PsiS GammaT PsiT) :
    exists tauT, C.TyAt GammaT PsiT (Basis.subst x n b) tauT := by
  have result : forall {Gamma' Psi'},
      SomeCutCtx x bX tauVX n arg Gamma0 GammaS PsiS Gamma' Psi' ->
      exists tauT, C.TyAt Gamma' Psi' (Basis.subst x n b) tauT /\
        CutTyRel tauT tauV := C.TyAt.rec
    (motive_1 := fun Gamma Psi s sv _ =>
      forall {Gamma' Psi'},
        SomeCutCtx x bX tauVX n arg Gamma0 Gamma Psi Gamma' Psi' ->
        exists svT, C.Space Gamma' Psi' (Space.subst x n s) svT /\
          CutSpaceRel svT sv)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun Gamma Psi bb tauS _ =>
      forall {Gamma' Psi'},
        SomeCutCtx x bX tauVX n arg Gamma0 Gamma Psi Gamma' Psi' ->
        exists tauT, C.TyAt Gamma' Psi' (Basis.subst x n bb) tauT /\
          CutTyRel tauT tauS)
    (motive_4 := fun Gamma Psi b0 _ b1 _ =>
      forall {Gamma' Psi'},
        SomeCutCtx x bX tauVX n arg Gamma0 Gamma Psi Gamma' Psi' ->
        exists envT, C.Cob Gamma' Psi' (Basis.subst x n b0) envT
          (Basis.subst x n b1))
    (motive_5 := fun Delta Gamma Psi e bb _ tauS _ =>
      forall {Delta' Gamma' Psi'},
        SomeTermCutCtx x bX tauVX n arg Gamma0
          Delta Gamma Psi Delta' Gamma' Psi' ->
        exists vT tauT, C.Term Delta' Gamma' Psi'
          (Term.subst x n e) (Basis.subst x n bb) vT tauT /\
          CutTyRel tauT tauS)
    ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
    ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
    ?tySpace ?tyPi
    ?tyAtSpace ?tyAtFrame
    ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
    ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
    ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
    ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
    ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
    ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
    ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
    ?termAppL ?termAppI ?termNllam ?termAppNVal
    ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
    ?termZero ?termRlit h
  case spaceReal =>
    intro Gamma Psi Gamma' Psi' w
    exact ⟨.real, .real, .real⟩
  case spaceEmpty =>
    intro Gamma Psi Gamma' Psi' w
    exact ⟨.empty, .empty, .empty⟩
  case spaceDual =>
    intro Gamma Psi s sv hs h ih Gamma' Psi' w
    obtain ⟨svT, hT, hrel⟩ := ih w
    exact ⟨svT, .dual (hs.map w.source.svalid) hT, hrel⟩
  case spaceKer =>
    intro Gamma Psi s0 s1 e bb leev svb hs hb hcompat hS hE
      ihS ihE Gamma' Psi' w
    have htof := hcompat.tof_eq_space
    obtain ⟨svbT, hsvbT, hrel⟩ := ihS w
    have hTy : C.TyAt Gamma' Psi' (Basis.subst x n bb) (.space svbT) :=
      .space (Basis.tof_space_subst_checked htof)
        (w.source.basisValid hE.basisValid)
        (by simpa only [Basis.sof_subst] using hsvbT)
    obtain ⟨leevT, tauET, hERaw, _⟩ := ihE w.termEmpty
    let leevAligned := ValExpr.reshap leevT (.space svbT) tauET
    have hET : C.Term ∅ Gamma' Psi' (Term.subst x n e)
        (Basis.subst x n bb) leevAligned (.space svbT) :=
      RawCertifiedProgressScratch.retag hERaw hTy
    refine ⟨.ffs .kernel svbT (ValExpr.reshapBase leevAligned svbT),
      ?_, .ffs hrel⟩
    apply C.Space.ker (hs.map w.source.svalid)
      (by simpa only [Basis.sof_subst, Space.subst] using
        congrArg (Space.subst x n) hb)
      (hcompat.subst x n)
      (by simpa only [Basis.sof_subst] using hsvbT) hET
  case spaceCoker =>
    intro Gamma Psi s0 s1 e bb leev svb hs hb hcompat hS hE
      ihS ihE Gamma' Psi' w
    have htof := hcompat.tof_eq_space
    obtain ⟨svbT, hsvbT, hrel⟩ := ihS w
    have hTy : C.TyAt Gamma' Psi' (Basis.subst x n bb) (.space svbT) :=
      .space (Basis.tof_space_subst_checked htof)
        (w.source.basisValid hE.basisValid)
        (by simpa only [Basis.sof_subst] using hsvbT)
    obtain ⟨leevT, tauET, hERaw, _⟩ := ihE w.termEmpty
    let leevAligned := ValExpr.reshap leevT (.space svbT) tauET
    have hET : C.Term ∅ Gamma' Psi' (Term.subst x n e)
        (Basis.subst x n bb) leevAligned (.space svbT) :=
      RawCertifiedProgressScratch.retag hERaw hTy
    refine ⟨.ffs .cokernel svbT (ValExpr.reshapBase leevAligned svbT),
      ?_, .ffs hrel⟩
    apply C.Space.coker (hs.map w.source.svalid)
      (by simpa only [Basis.sof_subst, Space.subst] using
        congrArg (Space.subst x n) hb)
      (hcompat.subst x n)
      (by simpa only [Basis.sof_subst] using hsvbT) hET
  case spaceImg =>
    intro Gamma Psi s0 s1 e bb leev svb hs hb hcompat hS hE
      ihS ihE Gamma' Psi' w
    have htof := hcompat.tof_eq_space
    obtain ⟨svbT, hsvbT, hrel⟩ := ihS w
    have hTy : C.TyAt Gamma' Psi' (Basis.subst x n bb) (.space svbT) :=
      .space (Basis.tof_space_subst_checked htof)
        (w.source.basisValid hE.basisValid)
        (by simpa only [Basis.sof_subst] using hsvbT)
    obtain ⟨leevT, tauET, hERaw, _⟩ := ihE w.termEmpty
    let leevAligned := ValExpr.reshap leevT (.space svbT) tauET
    have hET : C.Term ∅ Gamma' Psi' (Term.subst x n e)
        (Basis.subst x n bb) leevAligned (.space svbT) :=
      RawCertifiedProgressScratch.retag hERaw hTy
    refine ⟨.ffs .image svbT (ValExpr.reshapBase leevAligned svbT),
      ?_, .ffs hrel⟩
    apply C.Space.img (hs.map w.source.svalid)
      (by simpa only [Basis.sof_subst, Space.subst] using
        congrArg (Space.subst x n) hb)
      (hcompat.subst x n)
      (by simpa only [Basis.sof_subst] using hsvbT) hET
  case spaceCoimg =>
    intro Gamma Psi s0 s1 e bb leev svb hs hb hcompat hS hE
      ihS ihE Gamma' Psi' w
    have htof := hcompat.tof_eq_space
    obtain ⟨svbT, hsvbT, hrel⟩ := ihS w
    have hTy : C.TyAt Gamma' Psi' (Basis.subst x n bb) (.space svbT) :=
      .space (Basis.tof_space_subst_checked htof)
        (w.source.basisValid hE.basisValid)
        (by simpa only [Basis.sof_subst] using hsvbT)
    obtain ⟨leevT, tauET, hERaw, _⟩ := ihE w.termEmpty
    let leevAligned := ValExpr.reshap leevT (.space svbT) tauET
    have hET : C.Term ∅ Gamma' Psi' (Term.subst x n e)
        (Basis.subst x n bb) leevAligned (.space svbT) :=
      RawCertifiedProgressScratch.retag hERaw hTy
    refine ⟨.ffs .coimage svbT (ValExpr.reshapBase leevAligned svbT),
      ?_, .ffs hrel⟩
    apply C.Space.coimg (hs.map w.source.svalid)
      (by simpa only [Basis.sof_subst, Space.subst] using
        congrArg (Space.subst x n) hb)
      (hcompat.subst x n)
      (by simpa only [Basis.sof_subst] using hsvbT) hET
  case spaceTprod =>
    intro Gamma Psi s0 s1 sv0 sv1 hs h0 h1 ih0 ih1 Gamma' Psi' w
    obtain ⟨sv0T, h0T, hr0⟩ := ih0 w
    obtain ⟨sv1T, h1T, hr1⟩ := ih1 w
    exact ⟨.tprod sv0T sv1T,
      .tprod (hs.map w.source.svalid) h0T h1T, .tprod hr0 hr1⟩
  case spaceDsum =>
    intro Gamma Psi s0 s1 sv0 sv1 hs h0 h1 ih0 ih1 Gamma' Psi' w
    obtain ⟨sv0T, h0T, hr0⟩ := ih0 w
    obtain ⟨sv1T, h1T, hr1⟩ := ih1 w
    exact ⟨.dsum sv0T sv1T,
      .dsum (hs.map w.source.svalid) h0T h1T, .dsum hr0 hr1⟩
  case tySpace => intros; trivial
  case tyPi => intros; trivial
  case tyAtSpace =>
    intro Gamma Psi bb sv htof hbv hspace ih Gamma' Psi' w
    obtain ⟨svT, hspaceT, hrel⟩ := ih w
    exact ⟨.space svT, .space (Basis.tof_space_subst_checked htof)
      (w.source.basisValid hbv)
      (by simpa only [Basis.sof_subst] using hspaceT), .space hrel⟩
  case tyAtFrame =>
    intro Gamma Psi b0 b1 tau0 tau1 hbv hdom L hcod
      ih0 ih1 Gamma' Psi' w
    obtain ⟨tau0T, hdomT, _⟩ := ih0 w
    have hbvT : BasisValid Gamma'
        (.frame (Basis.subst x n b0) (Basis.subst x n b1)) := by
      simpa only [Basis.subst] using w.source.basisValid hbv
    have hb0S : BasisValid Gamma b0 := hbv.frame_inv.1
    have hb0T : BasisValid Gamma' (Basis.subst x n b0) :=
      w.source.basisValid hb0S
    have hlc0T : ValTy.lc tau0T := evalT_lc hdomT.erase w.lc
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
      (L ∪ {x} ∪ Gamma0.keys ∪ Gamma'.keys ∪
        EvalCtx.avoidB Psi ∪ EvalCtx.avoidB Psi' ∪
        Basis.fv (Basis.subst x n bX) ∪
        Basis.fv (Basis.subst x n b0) ∪
        Basis.fv (Basis.subst x n b1) ∪ ValTy.fv tau0T)
    have hzL : z ∉ L := by intro hm; apply hz; simp [hm]
    have hzx : z ≠ x := by intro h; subst z; apply hz; simp
    have hz0k : z ∉ Gamma0.keys := by intro hm; apply hz; simp [hm]
    have hz0 : Gamma0.lookup z = none :=
      Finmap.lookup_eq_none.mpr (fun hm => hz0k (Finmap.mem_keys.mpr hm))
    have hzT : z ∉ Gamma' := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzPsiS : z ∉ EvalCtx.avoidB Psi := by
      intro hm; apply hz; simp [hm]
    have hzPsiT : z ∉ EvalCtx.avoidB Psi' := by
      intro hm; apply hz; simp [hm]
    have hzCut : z ∉ Basis.fv (Basis.subst x n bX) := by
      intro hm; apply hz; simp [hm]
    have hzb0T : z ∉ Basis.fv (Basis.subst x n b0) := by
      intro hm; apply hz; simp [hm]
    have hzb1T : z ∉ Basis.fv (Basis.subst x n b1) := by
      intro hm; apply hz; simp [hm]
    have hztau0T : z ∉ ValTy.fv tau0T := by
      intro hm; apply hz; simp [hm]
    have wz := w.extendNL z b0 tau0 tau0T hb0S hzx hz0 hzT
      (EvalCtx.avoidB_spec hzPsiS).1 (EvalCtx.avoidB_spec hzPsiT).1
      hzCut hlc0T
    obtain ⟨tauBodyT, hbodyT0, _⟩ := ih1 z hzL wz
    have hbodyT : C.TyAt
        (Finmap.insert z (Basis.tof (Basis.subst x n b0)) Gamma')
        (Psi'.extend z (Basis.subst x n b0) (.var z tau0T))
        (Basis.openVar z (Basis.subst x n b1)) tauBodyT := by
      simpa only [Basis.tof_subst,
        Basis.subst_openVar_ne_checked w.source.data.lc hzx] using hbodyT0
    have hlcBodyT : ValTy.lc tauBodyT :=
      evalT_lc hbodyT.erase (w.lc.extend (.var hlc0T))
    obtain ⟨LT, hfamily⟩ :=
      RawCertifiedPiBasisTransport.checkedTyAt_arbitrary_cofinite_of_fresh
        laws w.wf hb0T.tof_tvalid rfl hb0T hzT hbodyT hzPsiT
        hzb0T hztau0T hzb1T hlc0T hlcBodyT
    let tau1T := ValTy.closeRec 0 z tauBodyT
    exact ⟨.piTy tau0T tau1T,
      by simpa only [Basis.subst] using
        C.TyAt.frame hbvT hdomT LT
          (by simpa only [tau1T] using hfamily),
      .piTy⟩
  case cobInverse =>
    intro Gamma Psi b0 b1 env hb0 hb1 hc ih Gamma' Psi' w
    obtain ⟨envT, hcT⟩ := ih w
    exact ⟨.inv envT, .inverse (w.source.basisValid hb0)
      (w.source.basisValid hb1) hcT⟩
  case cobTrans =>
    intro Gamma Psi b0 b1 b2 env0 env1 sv hb0 hb2 h0 h1 hs
      ih0 ih1 ihs Gamma' Psi' w
    obtain ⟨env0T, h0T⟩ := ih0 w
    obtain ⟨env1T, h1T⟩ := ih1 w
    obtain ⟨svT, hsT, _⟩ := ihs w
    have hsT' : C.Space Gamma' Psi' (Basis.sof (Basis.subst x n b0)) svT := by
      simpa only [Basis.sof_subst] using hsT
    exact ⟨_, C.Cob.trans (sv := svT) (w.source.basisValid hb0)
      (w.source.basisValid hb2) h0T h1T hsT'⟩
  case cobTprod =>
    intro Gamma Psi b0 b1 b0' b1' env0 env1 hbS hbT h0 h1
      ih0 ih1 Gamma' Psi' w
    obtain ⟨env0T, h0T⟩ := ih0 w
    obtain ⟨env1T, h1T⟩ := ih1 w
    have hres := C.Cob.tprod (w.source.basisValid hbS)
      (w.source.basisValid hbT) h0T h1T
    exact ⟨_, by simpa only [Basis.subst] using hres⟩
  case cobDsum =>
    intro Gamma Psi b0 b1 b0' b1' env0 env1 hbS hbT h0 h1
      ih0 ih1 Gamma' Psi' w
    obtain ⟨env0T, h0T⟩ := ih0 w
    obtain ⟨env1T, h1T⟩ := ih1 w
    have hres := C.Cob.dsum (w.source.basisValid hbS)
      (w.source.basisValid hbT) h0T h1T
    exact ⟨_, by simpa only [Basis.subst] using hres⟩
  case cobDualStd =>
    intro Gamma Psi b0 env htof hbS hbT hc ih Gamma' Psi' w
    obtain ⟨envT, hcT⟩ := ih w
    have hbT' := w.source.basisValid hbT
    rw [← Basis.std_subst, ← Basis.tof_subst] at hcT hbT'
    exact ⟨_, by
      simpa only [Basis.subst, ← Basis.std_subst, ← Basis.tof_subst] using
        C.Cob.dual_std (Basis.tof_space_subst_checked htof)
          (w.source.basisValid hbS) hbT' hcT⟩
  case cobImage =>
    intro Gamma Psi b0 b0' env hbS hbT hcoker hc ih Gamma' Psi' w
    obtain ⟨envT, hcT⟩ := ih w
    obtain ⟨s0, s1, e, he⟩ := hcoker
    have hcokerT : Basis.sof (Basis.subst x n b0) =
        .coker (Space.subst x n s0) (Space.subst x n s1)
          (Term.subst x n e) := by
      simpa only [Basis.sof_subst, Space.subst] using
        congrArg (Space.subst x n) he
    have hres := C.Cob.image (w.source.basisValid hbS)
      (w.source.basisValid hbT) ⟨_, _, _, hcokerT⟩ hcT
    exact ⟨_, by simpa only [Basis.subst] using hres⟩
  case cobImageSvds =>
    intro Gamma Psi b0 b1 e leev s0 s1 svb hbS hbT hs0 hs1 hb0 hb1
      hsvb he ihs ihe Gamma' Psi' w
    obtain ⟨svbT, hsvbT0, _⟩ := ihs w
    obtain ⟨leevT, tauT, heT0, _⟩ := ihe w.termEmpty
    have hsvbT : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n (.tprod (.dual b0) b1))) svbT := by
      rw [Basis.sof_subst]
      exact hsvbT0
    have hTyT : C.TyAt Gamma' Psi'
        (Basis.subst x n (.tprod (.dual b0) b1)) (.space svbT) :=
      .space rfl (w.source.basisValid he.basisValid) hsvbT
    have heT := RawCertifiedProgressScratch.retag heT0 hTyT
    have hres := C.Cob.image_svds
      (w.source.basisValid hbS) (w.source.basisValid hbT)
      (by rw [Basis.sof_subst, hs0])
      (by rw [Basis.sof_subst, hs1])
      ((RenameProof.Basis.isStd_subst x n b0).symm ▸ hb0)
      ((RenameProof.Basis.isStd_subst x n b1).symm ▸ hb1)
      hsvbT heT
    exact ⟨_, by simpa only [Basis.subst, Space.subst] using hres⟩
  case cobProjKerCoker =>
    intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env2 env3
      sv0 sv1 sv sv' sv0' hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv0' hcob hembd hproj
      ihsv0 ihsv1 ihsv ihsv' ihsv0' ihcob ihembd ihproj
      Gamma' Psi' w
    obtain ⟨sv0T, hsv0T0, _⟩ := ihsv0 w
    obtain ⟨sv1T, hsv1T0, _⟩ := ihsv1 w
    obtain ⟨svT, hsvT, _⟩ := ihsv w
    obtain ⟨sv'T, hsv'T, _⟩ := ihsv' w
    obtain ⟨sv0'T, hsv0'T0, _⟩ := ihsv0' w
    obtain ⟨env2T, hcobT⟩ := ihcob w
    obtain ⟨env3T, tau3T, hembdT0, _⟩ := ihembd w.termEmpty
    obtain ⟨env1T, tau1T, hprojT0, _⟩ := ihproj w.termEmpty
    have hsv0T : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n b0)) sv0T := by
      simpa only [Basis.sof_subst] using hsv0T0
    have hsv1T : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n b1)) sv1T := by
      simpa only [Basis.sof_subst] using hsv1T0
    have hsv0'T : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n b0')) sv0'T := by
      simpa only [Basis.sof_subst] using hsv0'T0
    have hEmbdTy0 := checkedTyAt_tprod_dual
      (w.source.basisValid hembd.basisValid)
      (RenameProof.Basis.IsTyBasis.subst hembd.tyAt.isTyBasis)
      (b0 := Basis.subst x n (.proj s b0 b1))
      (b1 := Basis.subst x n b0) hsvT hsv0T
    have hEmbdTy : C.TyAt Gamma' Psi'
        (Basis.subst x n (.tprod (.dual (.proj s b0 b1)) b0))
        (.space (.tprod svT sv0T)) := by
      simpa only [Basis.subst] using hEmbdTy0
    have hProjTy0 := checkedTyAt_tprod_dual
      (w.source.basisValid hproj.basisValid)
      (RenameProof.Basis.IsTyBasis.subst hproj.tyAt.isTyBasis)
      (b0 := Basis.subst x n b0')
      (b1 := Basis.subst x n (.proj s b0' b1)) hsv0'T hsv'T
    have hProjTy : C.TyAt Gamma' Psi'
        (Basis.subst x n (.tprod (.dual b0') (.proj s b0' b1)))
        (.space (.tprod sv0'T sv'T)) := by
      simpa only [Basis.subst] using hProjTy0
    have hembdT := RawCertifiedProgressScratch.retag hembdT0 hEmbdTy
    have hprojT := RawCertifiedProgressScratch.retag hprojT0 hProjTy
    have hsT : Space.subst x n s =
        .ker (Space.subst x n s0) (Space.subst x n s1) (Term.subst x n e) ∨
        Space.subst x n s =
        .coker (Space.subst x n s0) (Space.subst x n s1) (Term.subst x n e) :=
      hs.imp (fun h => by simp only [h, Space.subst])
        (fun h => by simp only [h, Space.subst])
    have hres := C.Cob.proj_ker_coker
      (w.source.basisValid hbS) (w.source.basisValid hbT) hsT
      (by rw [Basis.sof_subst, hsofb0])
      (by rw [Basis.sof_subst, hsofb1])
      hsv0T hsv1T hsvT hsv'T hsv0'T hcobT
      (by simpa only [Term.subst, Basis.subst, Basis.sof_subst] using hembdT)
      (by simpa only [Term.subst, Basis.subst, Basis.sof_subst] using hprojT)
    exact ⟨_, by simpa only [Basis.subst, Space.subst] using hres⟩
  case cobProjImgCoimg =>
    intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env2 env3
      sv0 sv1 sv sv' sv1' hbS hbT hs hsofb0 hsofb1
      hsv0 hsv1 hsv hsv' hsv1' hcob hembd hproj
      ihsv0 ihsv1 ihsv ihsv' ihsv1' ihcob ihembd ihproj
      Gamma' Psi' w
    obtain ⟨sv0T, hsv0T0, _⟩ := ihsv0 w
    obtain ⟨sv1T, hsv1T0, _⟩ := ihsv1 w
    obtain ⟨svT, hsvT, _⟩ := ihsv w
    obtain ⟨sv'T, hsv'T, _⟩ := ihsv' w
    obtain ⟨sv1'T, hsv1'T0, _⟩ := ihsv1' w
    obtain ⟨env2T, hcobT⟩ := ihcob w
    obtain ⟨env3T, tau3T, hembdT0, _⟩ := ihembd w.termEmpty
    obtain ⟨env1T, tau1T, hprojT0, _⟩ := ihproj w.termEmpty
    have hsv0T : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n b0)) sv0T := by
      simpa only [Basis.sof_subst] using hsv0T0
    have hsv1T : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n b1)) sv1T := by
      simpa only [Basis.sof_subst] using hsv1T0
    have hsv1'T : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n b1')) sv1'T := by
      simpa only [Basis.sof_subst] using hsv1'T0
    have hEmbdTy0 := checkedTyAt_tprod_dual
      (w.source.basisValid hembd.basisValid)
      (RenameProof.Basis.IsTyBasis.subst hembd.tyAt.isTyBasis)
      (b0 := Basis.subst x n (.proj s b0 b1))
      (b1 := Basis.subst x n b1) hsvT hsv1T
    have hEmbdTy : C.TyAt Gamma' Psi'
        (Basis.subst x n (.tprod (.dual (.proj s b0 b1)) b1))
        (.space (.tprod svT sv1T)) := by
      simpa only [Basis.subst] using hEmbdTy0
    have hProjTy0 := checkedTyAt_tprod_dual
      (w.source.basisValid hproj.basisValid)
      (RenameProof.Basis.IsTyBasis.subst hproj.tyAt.isTyBasis)
      (b0 := Basis.subst x n b1')
      (b1 := Basis.subst x n (.proj s b0 b1')) hsv1'T hsv'T
    have hProjTy : C.TyAt Gamma' Psi'
        (Basis.subst x n (.tprod (.dual b1') (.proj s b0 b1')))
        (.space (.tprod sv1'T sv'T)) := by
      simpa only [Basis.subst] using hProjTy0
    have hembdT := RawCertifiedProgressScratch.retag hembdT0 hEmbdTy
    have hprojT := RawCertifiedProgressScratch.retag hprojT0 hProjTy
    have hsT : Space.subst x n s =
        .img (Space.subst x n s0) (Space.subst x n s1) (Term.subst x n e) ∨
        Space.subst x n s =
        .coimg (Space.subst x n s0) (Space.subst x n s1) (Term.subst x n e) :=
      hs.imp (fun h => by simp only [h, Space.subst])
        (fun h => by simp only [h, Space.subst])
    have hres := C.Cob.proj_img_coimg
      (w.source.basisValid hbS) (w.source.basisValid hbT) hsT
      (by rw [Basis.sof_subst, hsofb0])
      (by rw [Basis.sof_subst, hsofb1])
      hsv0T hsv1T hsvT hsv'T hsv1'T hcobT
      (by simpa only [Term.subst, Basis.subst, Basis.sof_subst] using hembdT)
      (by simpa only [Term.subst, Basis.subst, Basis.sof_subst] using hprojT)
    exact ⟨_, by simpa only [Basis.subst, Space.subst] using hres⟩
  case cobTermsRref =>
    intro Gamma Psi b0 b1 e es env0 env1 sv tauS hbS hbT hbb hch hsv
      ihbb ihch ihsv Gamma' Psi' w
    obtain ⟨env1T, hbbT⟩ := ihbb w
    obtain ⟨env0T, tauT, hchT0, _⟩ := ihch w.termEmpty
    obtain ⟨svT, hsvT0, _⟩ := ihsv w
    have hchT := hchT0
    rw [Term.subst_dsumChain, Basis.subst_dsumChain] at hchT
    have hchT' : C.Term ∅ Gamma' Psi'
        (Term.dsumChain (Term.subst x n e) (es.map (Term.subst x n)))
        (Basis.dsumChain (Basis.subst x n b1)
          (es.map (Term.subst x n)).length) env0T tauT := by
      rw [List.length_map]
      exact hchT
    have hsvT : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n b0)) svT := by
      rw [Basis.sof_subst]
      exact hsvT0
    have hres := C.Cob.terms_rref
      (b' := Basis.subst x n b1) (e := Term.subst x n e)
      (es := es.map (Term.subst x n))
      (w.source.basisValid hbS)
      (by simpa only [Basis.subst, Space.subst, Basis.sof_subst,
        List.map_cons] using w.source.basisValid hbT)
      hbbT hchT' hsvT
    exact ⟨_, by simpa only [Basis.subst, Space.subst, Basis.sof_subst,
      List.map_cons] using hres⟩
  case cobRefl =>
    intro Gamma Psi bb sv hb htof hs ihs Gamma' Psi' w
    obtain ⟨svT, hsT, _⟩ := ihs w
    have hsT' : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n bb)) svT := by
      simpa only [Basis.sof_subst] using hsT
    exact ⟨_, C.Cob.refl (sv := svT) (w.source.basisValid hb)
      (Basis.tof_space_subst_checked htof) hsT'⟩
  case cobProjKerCokerCod =>
    intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env3 sv0 sv sv'
      hbS hbT hs hsofb0 hsofb1 hsofb1' hsv0 hsv hsv' hembd hproj
      ihsv0 ihsv ihsv' ihembd ihproj Gamma' Psi' w
    obtain ⟨sv0T, hsv0T0, _⟩ := ihsv0 w
    obtain ⟨svT, hsvT, _⟩ := ihsv w
    obtain ⟨sv'T, hsv'T, _⟩ := ihsv' w
    obtain ⟨env3T, tau3T, hembdT0, _⟩ := ihembd w.termEmpty
    obtain ⟨env1T, tau1T, hprojT0, _⟩ := ihproj w.termEmpty
    have hsv0T : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n b0)) sv0T := by
      simpa only [Basis.sof_subst] using hsv0T0
    have hEmbdTy0 := checkedTyAt_tprod_dual
      (w.source.basisValid hembd.basisValid)
      (RenameProof.Basis.IsTyBasis.subst hembd.tyAt.isTyBasis)
      (b0 := Basis.subst x n (.proj s b0 b1))
      (b1 := Basis.subst x n b0) hsvT hsv0T
    have hEmbdTy : C.TyAt Gamma' Psi'
        (Basis.subst x n (.tprod (.dual (.proj s b0 b1)) b0))
        (.space (.tprod svT sv0T)) := by
      simpa only [Basis.subst] using hEmbdTy0
    have hProjTy0 := checkedTyAt_tprod_dual
      (w.source.basisValid hproj.basisValid)
      (RenameProof.Basis.IsTyBasis.subst hproj.tyAt.isTyBasis)
      (b0 := Basis.subst x n b0)
      (b1 := Basis.subst x n (.proj s b0 b1')) hsv0T hsv'T
    have hProjTy : C.TyAt Gamma' Psi'
        (Basis.subst x n (.tprod (.dual b0) (.proj s b0 b1')))
        (.space (.tprod sv0T sv'T)) := by
      simpa only [Basis.subst] using hProjTy0
    have hembdT := RawCertifiedProgressScratch.retag hembdT0 hEmbdTy
    have hprojT := RawCertifiedProgressScratch.retag hprojT0 hProjTy
    have hsT : Space.subst x n s =
        .ker (Space.subst x n s0) (Space.subst x n s1) (Term.subst x n e) ∨
        Space.subst x n s =
        .coker (Space.subst x n s0) (Space.subst x n s1) (Term.subst x n e) :=
      hs.imp (fun h => by simp only [h, Space.subst])
        (fun h => by simp only [h, Space.subst])
    have hres := C.Cob.proj_ker_coker_cod
      (w.source.basisValid hbS) (w.source.basisValid hbT) hsT
      (by rw [Basis.sof_subst, hsofb0])
      (by rw [Basis.sof_subst, hsofb1])
      (by rw [Basis.sof_subst, hsofb1'])
      hsv0T hsvT hsv'T
      (by simpa only [Term.subst, Basis.subst, Basis.sof_subst] using hembdT)
      (by simpa only [Term.subst, Basis.subst, Basis.sof_subst] using hprojT)
    exact ⟨_, by simpa only [Basis.subst, Space.subst] using hres⟩
  case cobProjImgCoimgDom =>
    intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env3 sv1 sv sv'
      hbS hbT hs hsofb0 hsofb1 hsofb0' hsv1 hsv hsv' hembd hproj
      ihsv1 ihsv ihsv' ihembd ihproj Gamma' Psi' w
    obtain ⟨sv1T, hsv1T0, _⟩ := ihsv1 w
    obtain ⟨svT, hsvT, _⟩ := ihsv w
    obtain ⟨sv'T, hsv'T, _⟩ := ihsv' w
    obtain ⟨env3T, tau3T, hembdT0, _⟩ := ihembd w.termEmpty
    obtain ⟨env1T, tau1T, hprojT0, _⟩ := ihproj w.termEmpty
    have hsv1T : C.Space Gamma' Psi'
        (Basis.sof (Basis.subst x n b1)) sv1T := by
      simpa only [Basis.sof_subst] using hsv1T0
    have hEmbdTy0 := checkedTyAt_tprod_dual
      (w.source.basisValid hembd.basisValid)
      (RenameProof.Basis.IsTyBasis.subst hembd.tyAt.isTyBasis)
      (b0 := Basis.subst x n (.proj s b0 b1))
      (b1 := Basis.subst x n b1) hsvT hsv1T
    have hEmbdTy : C.TyAt Gamma' Psi'
        (Basis.subst x n (.tprod (.dual (.proj s b0 b1)) b1))
        (.space (.tprod svT sv1T)) := by
      simpa only [Basis.subst] using hEmbdTy0
    have hProjTy0 := checkedTyAt_tprod_dual
      (w.source.basisValid hproj.basisValid)
      (RenameProof.Basis.IsTyBasis.subst hproj.tyAt.isTyBasis)
      (b0 := Basis.subst x n b1)
      (b1 := Basis.subst x n (.proj s b0' b1)) hsv1T hsv'T
    have hProjTy : C.TyAt Gamma' Psi'
        (Basis.subst x n (.tprod (.dual b1) (.proj s b0' b1)))
        (.space (.tprod sv1T sv'T)) := by
      simpa only [Basis.subst] using hProjTy0
    have hembdT := RawCertifiedProgressScratch.retag hembdT0 hEmbdTy
    have hprojT := RawCertifiedProgressScratch.retag hprojT0 hProjTy
    have hsT : Space.subst x n s =
        .img (Space.subst x n s0) (Space.subst x n s1) (Term.subst x n e) ∨
        Space.subst x n s =
        .coimg (Space.subst x n s0) (Space.subst x n s1) (Term.subst x n e) :=
      hs.imp (fun h => by simp only [h, Space.subst])
        (fun h => by simp only [h, Space.subst])
    have hres := C.Cob.proj_img_coimg_dom
      (w.source.basisValid hbS) (w.source.basisValid hbT) hsT
      (by rw [Basis.sof_subst, hsofb0])
      (by rw [Basis.sof_subst, hsofb1])
      (by rw [Basis.sof_subst, hsofb0'])
      hsv1T hsvT hsv'T
      (by simpa only [Term.subst, Basis.subst, Basis.sof_subst] using hembdT)
      (by simpa only [Term.subst, Basis.subst, Basis.sof_subst] using hprojT)
    exact ⟨_, by simpa only [Basis.subst, Space.subst] using hres⟩
  case termVarNlin =>
    intro Gamma Psi z bz v tauS hlook hGamma hbv hTy ihTy
      DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    by_cases hzx : z = x
    · subst z
      have hb : bz = bX := wt.eval.xonly bz v hlook
      subst bz
      obtain ⟨tauT, hTyT, hrel⟩ := ihTy wt.typeCtx
      simp only [Term.subst]
      exact ⟨_, tauT, RawCertifiedProgressScratch.retag wt.cut hTyT, hrel⟩
    · obtain ⟨vT, hlookT⟩ := wt.eval.fwd z bz v hzx hlook
      have hxz : x ≠ z := Ne.symm hzx
      obtain ⟨tauT, hTyT, hrel⟩ := ihTy wt.typeCtx
      have hbvT : BasisValid GammaT (Basis.subst x n bz) :=
        wt.source.typeCtx.basisValid hbv
      have hGammaT0 : GammaT.lookup z =
          some (Ty.subst x n (Basis.tof bz)) :=
        wt.source.typeCtx.target z _ (by
          simp only [tsubstCtx, if_neg hzx, asTypeCtx, hGamma,
            Option.orElse_some, Option.map_some])
      have hGammaT : GammaT.lookup z =
          some (Basis.tof (Basis.subst x n bz)) := by
        simpa only [Basis.tof_subst] using hGammaT0
      simp only [Term.subst, if_neg hxz]
      exact ⟨vT, tauT, C.Term.var_nlin hlookT hGammaT hbvT hTyT, hrel⟩
  case termVarLin =>
    intro Gamma Psi z bz v s tauS hlook htof hbv hTy ihTy
      DeltaT GammaT PsiT wt
    by_cases hzx : z = x
    · subst z
      have hb : bz = bX := wt.eval.xonly bz v hlook
      subst bz
      have hDeltaT : DeltaT = ∅ := wt.targetLinear_singleton_self
      subst DeltaT
      obtain ⟨tauT, hTyT, hrel⟩ := ihTy wt.typeCtx
      simp only [Term.subst, if_pos rfl]
      exact ⟨_, tauT, RawCertifiedProgressScratch.retag wt.cut hTyT, hrel⟩
    · obtain ⟨vT, hlookT⟩ := wt.eval.fwd z bz v hzx hlook
      obtain ⟨tauT, hTyT, hrel⟩ := ihTy wt.typeCtx
      have hbvT := wt.source.typeCtx.basisValid hbv
      have hg := ghastype_subst wt.source.data wt.source.inv
        (gvar_lin_tr z s (ε := Gamma))
      simp only [Term.subst, if_neg (Ne.symm hzx), Ty.subst] at hg
      have htofT : Basis.tof (Basis.subst x n bz) =
          .space (Space.subst x n s) := by
        rw [Basis.tof_subst, htof]
        rfl
      cases hg with
      | gvar hz hg haff =>
          rw [← htofT] at hz
          refine ⟨vT, tauT, ?_, hrel⟩
          simpa only [Term.subst, if_neg (Ne.symm hzx)] using
            checked_gvar_shape wt.source.target hz hg haff hlookT hbvT hTyT
  case termPromote =>
    intro Delta Gamma Gamma'' Psi e bb v tauS lin hdDelta hdGamma hfr hle ht hbv
      hTy he ihTy ihE DeltaT GammaT PsiT wt
    exact ihE ((wt.enterPromote hdDelta hdGamma).pullSource hle)
  case termCob =>
    intro Delta Gamma Psi e b0 b1 v envS sv tauS htof0 htof1 ht hbv
      hTy he hbb hes ihTy ihE ihBB ihS DeltaT GammaT PsiT wt
    have htof0T : Basis.tof (Basis.subst x n b0) =
        .space (Basis.sof (Basis.subst x n b0)) :=
      Basis.tof_space_subst_checked htof0
    have htof1T : Basis.tof (Basis.subst x n b1) =
        .space (Basis.sof (Basis.subst x n b1)) :=
      Basis.tof_space_subst_checked htof1
    have htT : Nonempty (HasType DeltaT GammaT (Term.subst x n e)
        (Basis.tof (Basis.subst x n b0))) := by
      simpa only [Basis.tof_subst] using ht.map wt.source.hasType
    have hbvT := wt.source.typeCtx.basisValid hbv
    obtain ⟨vT, tauT, heT, _⟩ := ihE wt
    obtain ⟨envT, hbbT⟩ := ihBB wt.typeCtx
    obtain ⟨svT, hesT, hrel⟩ := ihS wt.typeCtx
    have hTyT : C.TyAt GammaT PsiT (Basis.subst x n b0) (.space svT) :=
      .space htof0T hbvT (by simpa only [Basis.sof_subst] using hesT)
    exact ⟨_, .space svT,
      C.Term.cob htof0T htof1T htT hbvT hTyT heT hbbT
        (by simpa only [Basis.sof_subst] using hesT),
      .space hrel⟩
  case termReshape =>
    intro Delta Gamma Psi e bb v tauS tauS' ht hbv hTy he
      ihTy ihE DeltaT GammaT PsiT wt
    have htT : Nonempty (HasType DeltaT GammaT (Term.subst x n e)
        (Basis.tof (Basis.subst x n bb))) := by
      simpa only [Basis.tof_subst] using ht.map wt.source.hasType
    have hbvT := wt.source.typeCtx.basisValid hbv
    obtain ⟨tauT, hTyT, hrel⟩ := ihTy wt.typeCtx
    obtain ⟨vT, tauET, hET, _⟩ := ihE wt
    exact ⟨.reshap vT tauT tauET, tauT,
      C.Term.reshape_cob htT hbvT hTyT hET, hrel⟩
  case termAdd =>
    intro Delta Gamma Psi e0 e1 bb v0 v1 sv sv0 sv1 htof ht hbv hTy
      he0 he1 ihTy ih0 ih1 DeltaT GammaT PsiT wt
    have htofT : Basis.tof (Basis.subst x n bb) =
        .space (Basis.sof (Basis.subst x n bb)) :=
      Basis.tof_space_subst_checked htof
    have htT : Nonempty (HasType DeltaT GammaT
        (.add (Term.subst x n e0) (Term.subst x n e1))
        (Basis.tof (Basis.subst x n bb))) := by
      simpa only [Term.subst, Basis.tof_subst] using ht.map wt.source.hasType
    have hbvT := wt.source.typeCtx.basisValid hbv
    obtain ⟨tauT, hTyT, hrel⟩ := ihTy wt.typeCtx
    obtain ⟨svT, rfl, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full htofT hTyT
    obtain ⟨v0T, tau0T, he0T, _⟩ := ih0 wt
    obtain ⟨sv0T, rfl, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full htofT he0T.tyAt
    obtain ⟨v1T, tau1T, he1T, _⟩ := ih1 wt
    obtain ⟨sv1T, rfl, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full htofT he1T.tyAt
    exact ⟨.vadd svT v0T v1T, .space svT,
      C.Term.add htofT htT hbvT hTyT he0T he1T, hrel⟩
  case termScale =>
    intro Delta0 Delta1 Gamma Psi e0 e1 bb v0 v1 sv hdis htof ht hbv
      hTy he0 he1 ihTy ih0 ih1 DeltaT GammaT PsiT wt
    let ws := wt.split hdis
    have htT : Nonempty (HasType (ws.DeltaT0 ∪ ws.DeltaT1) GammaT
        (.smul (Term.subst x n e0) (Term.subst x n e1))
        (Basis.tof (Basis.subst x n bb))) := by
      rw [ws.union_eq]
      simpa only [Term.subst, Basis.tof_subst] using ht.map wt.source.hasType
    have htofT := Basis.tof_space_subst_checked (x := x) (n := n) htof
    have hbvT := wt.source.typeCtx.basisValid hbv
    obtain ⟨tauT, hTyT, hrel⟩ := ihTy wt.typeCtx
    obtain ⟨svT, rfl, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full htofT hTyT
    have hOneTy : C.TyAt GammaT PsiT .one (.space .real) :=
      .space rfl .one .real
    obtain ⟨v0T, tau0T, he0Raw, _⟩ := ih0 ws.left
    let v0A := ValExpr.reshap v0T (.space .real) tau0T
    have he0T : C.Term ws.DeltaT0 GammaT PsiT (Term.subst x n e0)
        .one v0A (.space .real) := by
      simpa only [Basis.subst] using
        RawCertifiedProgressScratch.retag he0Raw hOneTy
    obtain ⟨v1T, tau1T, he1Raw, _⟩ := ih1 ws.right
    let v1A := ValExpr.reshap v1T (.space svT) tau1T
    have he1T : C.Term ws.DeltaT1 GammaT PsiT (Term.subst x n e1)
        (Basis.subst x n bb) v1A (.space svT) :=
      RawCertifiedProgressScratch.retag he1Raw hTyT
    refine ⟨.scale v0A v1A, .space svT, ?_, hrel⟩
    rw [← ws.union_eq]
    exact C.Term.scale ws.disjoint htofT htT hbvT hTyT he0T he1T
  case termDsum =>
    intro Delta Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 htof0 htof1
      ht hbv hTy he0 he1 ihTy ih0 ih1 DeltaT GammaT PsiT wt
    have htof0T := Basis.tof_space_subst_checked (x := x) (n := n) htof0
    have htof1T := Basis.tof_space_subst_checked (x := x) (n := n) htof1
    have htT : Nonempty (HasType DeltaT GammaT
        (.dsumE (Term.subst x n e0) (Term.subst x n e1))
        (Basis.tof (.dsum (Basis.subst x n b0) (Basis.subst x n b1)))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.subst] using htT0
    have hbvT : BasisValid GammaT
        (.dsum (Basis.subst x n b0) (Basis.subst x n b1)) := by
      simpa only [Basis.subst] using wt.source.typeCtx.basisValid hbv
    obtain ⟨v0T, tau0T, he0T, hrel0⟩ := ih0 wt
    obtain ⟨sv0T, rfl, hs0T⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full htof0T he0T.tyAt
    cases hrel0 with
    | space hrel0 =>
      obtain ⟨v1T, tau1T, he1T, hrel1⟩ := ih1 wt
      obtain ⟨sv1T, rfl, hs1T⟩ :=
        RawCertifiedProgressScratch.checkedTyAt_space_inv_full htof1T he1T.tyAt
      cases hrel1 with
      | space hrel1 =>
        have hsT : C.Space GammaT PsiT
            (Basis.sof (.dsum (Basis.subst x n b0) (Basis.subst x n b1)))
            (.dsum sv0T sv1T) := .dsum hbvT.sof_valid hs0T hs1T
        have hTyT : C.TyAt GammaT PsiT
            (.dsum (Basis.subst x n b0) (Basis.subst x n b1))
            (.space (.dsum sv0T sv1T)) :=
          .space rfl hbvT hsT
        refine ⟨.dsumE v0T v1T, .space (.dsum sv0T sv1T), ?_,
          .space (.dsum hrel0 hrel1)⟩
        simpa only [Term.subst, Basis.subst] using
          C.Term.dsumE htof0T htof1T htT hbvT hTyT he0T he1T
  case termTprod =>
    intro Delta0 Delta1 Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 hdis
      htof0 htof1 ht hbv hTy he0 he1 ihTy ih0 ih1 DeltaT GammaT PsiT wt
    let ws := wt.split hdis
    have htof0T := Basis.tof_space_subst_checked (x := x) (n := n) htof0
    have htof1T := Basis.tof_space_subst_checked (x := x) (n := n) htof1
    have htT : Nonempty (HasType (ws.DeltaT0 ∪ ws.DeltaT1) GammaT
        (.tprodE (Term.subst x n e0) (Term.subst x n e1))
        (Basis.tof (.tprod (Basis.subst x n b0) (Basis.subst x n b1)))) := by
      rw [ws.union_eq]
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.subst] using htT0
    have hbvT : BasisValid GammaT
        (.tprod (Basis.subst x n b0) (Basis.subst x n b1)) := by
      simpa only [Basis.subst] using wt.source.typeCtx.basisValid hbv
    obtain ⟨v0T, tau0T, he0T, hrel0⟩ := ih0 ws.left
    obtain ⟨sv0T, rfl, hs0T⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full htof0T he0T.tyAt
    cases hrel0 with
    | space hrel0 =>
      obtain ⟨v1T, tau1T, he1T, hrel1⟩ := ih1 ws.right
      obtain ⟨sv1T, rfl, hs1T⟩ :=
        RawCertifiedProgressScratch.checkedTyAt_space_inv_full htof1T he1T.tyAt
      cases hrel1 with
      | space hrel1 =>
        have hsT : C.Space GammaT PsiT
            (Basis.sof (.tprod (Basis.subst x n b0) (Basis.subst x n b1)))
            (.tprod sv0T sv1T) := .tprod hbvT.sof_valid hs0T hs1T
        have hTyT : C.TyAt GammaT PsiT
            (.tprod (Basis.subst x n b0) (Basis.subst x n b1))
            (.space (.tprod sv0T sv1T)) :=
          .space rfl hbvT hsT
        refine ⟨.tprodE v0T v1T, .space (.tprod sv0T sv1T), ?_,
          .space (.tprod hrel0 hrel1)⟩
        simpa only [Term.subst, Basis.subst, ws.union_eq] using
          C.Term.tprodE ws.disjoint htof0T htof1T htT hbvT hTyT he0T he1T
  case termPinvTStd =>
    intro Gamma Psi b0 b1 e v sv0 sv1 hb0 hb1 ht hbv hTy he
      ihTy ihE DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    let b0T := Basis.subst x n b0
    let b1T := Basis.subst x n b1
    have htT : Nonempty (HasType (∅ : LCtx) GammaT
        (.pinvT (Basis.sof b1T) (Basis.sof b0T) (Term.subst x n e))
        (Basis.tof (.tprod (.dual b0T) b1T))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T, b1T] using htT0
    have hbvT : BasisValid GammaT (.tprod (.dual b0T) b1T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid hbv
    obtain ⟨tauOutT, hTyOutT, hrel⟩ := ihTy wt.typeCtx
    obtain ⟨svOutT, rfl, hspaceOutT⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full rfl hTyOutT
    obtain ⟨sv0T, sv1T, rfl, hdual0T, hspace1T⟩ :=
      checkedSpace_tprod_inv_full hspaceOutT
    have hspace0T := checkedSpace_dual_inv_full hdual0T
    have hbvInT : BasisValid GammaT (.tprod (.dual b1T) b0T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid he.basisValid
    have hspaceInT : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b1T) b0T)) (.tprod sv1T sv0T) :=
      .tprod hbvInT.sof_valid
        (.dual hbvInT.tprod_inv.1.sof_valid hspace1T) hspace0T
    have hTyInT : C.TyAt GammaT PsiT (.tprod (.dual b1T) b0T)
        (.space (.tprod sv1T sv0T)) :=
      .space rfl hbvInT hspaceInT
    obtain ⟨vRaw, tauRaw, heRaw, _⟩ := ihE wt
    let vT := ValExpr.reshap vRaw (.space (.tprod sv1T sv0T)) tauRaw
    have heT : C.Term ∅ GammaT PsiT (Term.subst x n e)
        (.tprod (.dual b1T) b0T) vT (.space (.tprod sv1T sv0T)) := by
      simpa only [Basis.subst, b0T, b1T] using
        RawCertifiedProgressScratch.retag heRaw hTyInT
    have out := C.Term.pinvT_std
      ((RenameProof.Basis.isStd_subst x n b0).symm ▸ hb0)
      ((RenameProof.Basis.isStd_subst x n b1).symm ▸ hb1)
      htT hbvT hTyOutT heT
    exact ⟨.pinv vT, .space (.tprod sv0T sv1T),
      by simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T, b1T]
        using out,
      hrel⟩
  case termPinvTGpinv =>
    intro Gamma Psi b0 b1 e v env0 env1 sv0 sv1 ht hbv hTy he hi0 hi1
      ihTy ihE ihI0 ihI1 DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    let b0T := Basis.subst x n b0
    let b1T := Basis.subst x n b1
    have htT : Nonempty (HasType (∅ : LCtx) GammaT
        (.pinvT (Basis.sof b1T) (Basis.sof b0T) (Term.subst x n e))
        (Basis.tof (.tprod (.dual b0T) b1T))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T, b1T] using htT0
    have hbvT : BasisValid GammaT (.tprod (.dual b0T) b1T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid hbv
    obtain ⟨tauOutT, hTyOutT, hrel⟩ := ihTy wt.typeCtx
    obtain ⟨svOutT, rfl, hspaceOutT⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full rfl hTyOutT
    obtain ⟨sv0T, sv1T, rfl, hdual0T, hspace1T⟩ :=
      checkedSpace_tprod_inv_full hspaceOutT
    have hspace0T := checkedSpace_dual_inv_full hdual0T
    have hbvInT : BasisValid GammaT (.tprod (.dual b1T) b0T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid he.basisValid
    have hspaceInT : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b1T) b0T)) (.tprod sv1T sv0T) :=
      .tprod hbvInT.sof_valid
        (.dual hbvInT.tprod_inv.1.sof_valid hspace1T) hspace0T
    have hTyInT : C.TyAt GammaT PsiT (.tprod (.dual b1T) b0T)
        (.space (.tprod sv1T sv0T)) :=
      .space rfl hbvInT hspaceInT
    obtain ⟨vRaw, tauRaw, heRaw, _⟩ := ihE wt
    let vT := ValExpr.reshap vRaw (.space (.tprod sv1T sv0T)) tauRaw
    have heT : C.Term ∅ GammaT PsiT (Term.subst x n e)
        (.tprod (.dual b1T) b0T) vT (.space (.tprod sv1T sv0T)) := by
      simpa only [Basis.subst, b0T, b1T] using
        RawCertifiedProgressScratch.retag heRaw hTyInT
    have hbvI0T : BasisValid GammaT
        (.tprod (.dual b0T) (.dual b0T)) := by
      simpa only [Basis.subst, b0T] using
        wt.source.typeCtx.basisValid hi0.basisValid
    have hspaceI0T : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b0T) (.dual b0T)))
        (.tprod sv0T sv0T) :=
      .tprod hbvI0T.sof_valid
        (.dual hbvI0T.tprod_inv.1.sof_valid hspace0T)
        (.dual hbvI0T.tprod_inv.2.sof_valid hspace0T)
    have hTyI0T : C.TyAt GammaT PsiT
        (.tprod (.dual b0T) (.dual b0T)) (.space (.tprod sv0T sv0T)) :=
      .space rfl hbvI0T hspaceI0T
    obtain ⟨env0Raw, tauI0, hi0Raw, _⟩ := ihI0 wt
    let env0T := ValExpr.reshap env0Raw (.space (.tprod sv0T sv0T)) tauI0
    have hi0T : C.Term ∅ GammaT PsiT (.inner (Basis.sof b0T))
        (.tprod (.dual b0T) (.dual b0T)) env0T
        (.space (.tprod sv0T sv0T)) := by
      simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T] using
        RawCertifiedProgressScratch.retag hi0Raw hTyI0T
    have hbvI1T : BasisValid GammaT
        (.tprod (.dual b1T) (.dual b1T)) := by
      simpa only [Basis.subst, b1T] using
        wt.source.typeCtx.basisValid hi1.basisValid
    have hspaceI1T : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b1T) (.dual b1T)))
        (.tprod sv1T sv1T) :=
      .tprod hbvI1T.sof_valid
        (.dual hbvI1T.tprod_inv.1.sof_valid hspace1T)
        (.dual hbvI1T.tprod_inv.2.sof_valid hspace1T)
    have hTyI1T : C.TyAt GammaT PsiT
        (.tprod (.dual b1T) (.dual b1T)) (.space (.tprod sv1T sv1T)) :=
      .space rfl hbvI1T hspaceI1T
    obtain ⟨env1Raw, tauI1, hi1Raw, _⟩ := ihI1 wt
    let env1T := ValExpr.reshap env1Raw (.space (.tprod sv1T sv1T)) tauI1
    have hi1T : C.Term ∅ GammaT PsiT (.inner (Basis.sof b1T))
        (.tprod (.dual b1T) (.dual b1T)) env1T
        (.space (.tprod sv1T sv1T)) := by
      simpa only [Term.subst, Basis.subst, Basis.sof_subst, b1T] using
        RawCertifiedProgressScratch.retag hi1Raw hTyI1T
    have out := C.Term.pinvT_gpinv htT hbvT hTyOutT heT hi0T hi1T
    exact ⟨.gpinv vT env1T env0T, .space (.tprod sv0T sv1T),
      by simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T, b1T]
        using out,
      hrel⟩
  case termPinvDStd =>
    intro Gamma Psi b0 b1 e v sv1 hsofb0 hb0 hb1 ht hbv hTy he
      ihTy ihE DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    let b0T := Basis.subst x n b0
    let b1T := Basis.subst x n b1
    have hsofb0T : Basis.sof b0T = .real := by
      dsimp [b0T]
      rw [Basis.sof_subst, hsofb0]
      rfl
    have htT : Nonempty (HasType (∅ : LCtx) GammaT
        (.pinvD (Basis.sof b1T) (Term.subst x n e))
        (Basis.tof (.tprod (.dual b0T) b1T))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T, b1T] using htT0
    have hbvT : BasisValid GammaT (.tprod (.dual b0T) b1T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid hbv
    obtain ⟨tauOutT, hTyOutT, hrel⟩ := ihTy wt.typeCtx
    obtain ⟨svOutT, rfl, hspaceOutT⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full rfl hTyOutT
    obtain ⟨svScalarT, sv1T, rfl, hdualScalarT, hspace1T⟩ :=
      checkedSpace_tprod_inv_full hspaceOutT
    have hscalarT := checkedSpace_dual_inv_full hdualScalarT
    rw [hsofb0T] at hscalarT
    have hscalarEq : svScalarT = .real := checkedSpace_real_eq hscalarT
    subst svScalarT
    have hbvInT : BasisValid GammaT (.dual b1T) := by
      simpa only [Basis.subst, b1T] using
        wt.source.typeCtx.basisValid he.basisValid
    have hspaceInT : C.Space GammaT PsiT (Basis.sof (.dual b1T)) sv1T :=
      .dual hbvInT.sof_valid hspace1T
    have hTyInT : C.TyAt GammaT PsiT (.dual b1T) (.space sv1T) :=
      .space rfl hbvInT hspaceInT
    obtain ⟨vRaw, tauRaw, heRaw, _⟩ := ihE wt
    let vT := ValExpr.reshap vRaw (.space sv1T) tauRaw
    have heT : C.Term ∅ GammaT PsiT (Term.subst x n e)
        (.dual b1T) vT (.space sv1T) := by
      simpa only [Basis.subst, b1T] using
        RawCertifiedProgressScratch.retag heRaw hTyInT
    have out := C.Term.pinvD_std hsofb0T
      ((RenameProof.Basis.isStd_subst x n b0).symm ▸ hb0)
      ((RenameProof.Basis.isStd_subst x n b1).symm ▸ hb1)
      htT hbvT hTyOutT heT
    exact ⟨.pinv (.reshap vT (.space (.tprod sv1T .real)) (.space sv1T)),
      .space (.tprod .real sv1T),
      by simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T, b1T]
        using out,
      hrel⟩
  case termPinvDGpinv =>
    intro Gamma Psi b0 b1 e v env0 env1 sv1 hsofb0 hb0 ht hbv hTy he
      hi0 hi1 ihTy ihE ihI0 ihI1 DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    let b0T := Basis.subst x n b0
    let b1T := Basis.subst x n b1
    have hsofb0T : Basis.sof b0T = .real := by
      dsimp [b0T]
      rw [Basis.sof_subst, hsofb0]
      rfl
    have htT : Nonempty (HasType (∅ : LCtx) GammaT
        (.pinvD (Basis.sof b1T) (Term.subst x n e))
        (Basis.tof (.tprod (.dual b0T) b1T))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T, b1T] using htT0
    have hbvT : BasisValid GammaT (.tprod (.dual b0T) b1T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid hbv
    obtain ⟨tauOutT, hTyOutT, hrel⟩ := ihTy wt.typeCtx
    obtain ⟨svOutT, rfl, hspaceOutT⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full rfl hTyOutT
    obtain ⟨svScalarT, sv1T, rfl, hdualScalarT, hspace1T⟩ :=
      checkedSpace_tprod_inv_full hspaceOutT
    have hscalarT := checkedSpace_dual_inv_full hdualScalarT
    rw [hsofb0T] at hscalarT
    have hscalarEq : svScalarT = .real := checkedSpace_real_eq hscalarT
    subst svScalarT
    have hscalarB0T : C.Space GammaT PsiT (Basis.sof b0T) .real := by
      rw [hsofb0T]
      exact hscalarT
    have hbvInT : BasisValid GammaT (.dual b1T) := by
      simpa only [Basis.subst, b1T] using
        wt.source.typeCtx.basisValid he.basisValid
    have hspaceInT : C.Space GammaT PsiT (Basis.sof (.dual b1T)) sv1T :=
      .dual hbvInT.sof_valid hspace1T
    have hTyInT : C.TyAt GammaT PsiT (.dual b1T) (.space sv1T) :=
      .space rfl hbvInT hspaceInT
    obtain ⟨vRaw, tauRaw, heRaw, _⟩ := ihE wt
    let vT := ValExpr.reshap vRaw (.space sv1T) tauRaw
    have heT : C.Term ∅ GammaT PsiT (Term.subst x n e)
        (.dual b1T) vT (.space sv1T) := by
      simpa only [Basis.subst, b1T] using
        RawCertifiedProgressScratch.retag heRaw hTyInT
    have hbvI0T : BasisValid GammaT
        (.tprod (.dual b0T) (.dual b0T)) := by
      simpa only [Basis.subst, b0T] using
        wt.source.typeCtx.basisValid hi0.basisValid
    have hspaceI0T : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b0T) (.dual b0T)))
      (.tprod .real .real) :=
      .tprod hbvI0T.sof_valid
        (.dual hbvI0T.tprod_inv.1.sof_valid hscalarB0T)
        (.dual hbvI0T.tprod_inv.2.sof_valid hscalarB0T)
    have hTyI0T : C.TyAt GammaT PsiT
        (.tprod (.dual b0T) (.dual b0T)) (.space (.tprod .real .real)) :=
      .space rfl hbvI0T hspaceI0T
    obtain ⟨env0Raw, tauI0, hi0Raw, _⟩ := ihI0 wt
    let env0T := ValExpr.reshap env0Raw (.space (.tprod .real .real)) tauI0
    have hi0T : C.Term ∅ GammaT PsiT (.inner (Basis.sof b0T))
        (.tprod (.dual b0T) (.dual b0T)) env0T
        (.space (.tprod .real .real)) := by
      simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T] using
        RawCertifiedProgressScratch.retag hi0Raw hTyI0T
    have hbvI1T : BasisValid GammaT
        (.tprod (.dual b1T) (.dual b1T)) := by
      simpa only [Basis.subst, b1T] using
        wt.source.typeCtx.basisValid hi1.basisValid
    have hspaceI1T : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b1T) (.dual b1T)))
        (.tprod sv1T sv1T) :=
      .tprod hbvI1T.sof_valid
        (.dual hbvI1T.tprod_inv.1.sof_valid hspace1T)
        (.dual hbvI1T.tprod_inv.2.sof_valid hspace1T)
    have hTyI1T : C.TyAt GammaT PsiT
        (.tprod (.dual b1T) (.dual b1T)) (.space (.tprod sv1T sv1T)) :=
      .space rfl hbvI1T hspaceI1T
    obtain ⟨env1Raw, tauI1, hi1Raw, _⟩ := ihI1 wt
    let env1T := ValExpr.reshap env1Raw (.space (.tprod sv1T sv1T)) tauI1
    have hi1T : C.Term ∅ GammaT PsiT (.inner (Basis.sof b1T))
        (.tprod (.dual b1T) (.dual b1T)) env1T
        (.space (.tprod sv1T sv1T)) := by
      simpa only [Term.subst, Basis.subst, Basis.sof_subst, b1T] using
        RawCertifiedProgressScratch.retag hi1Raw hTyI1T
    have out := C.Term.pinvD_gpinv hsofb0T
      ((RenameProof.Basis.isStd_subst x n b0).symm ▸ hb0)
      htT hbvT hTyOutT heT hi0T hi1T
    exact ⟨.gpinv
        (.reshap vT (.space (.tprod sv1T .real)) (.space sv1T)) env1T env0T,
      .space (.tprod .real sv1T),
      by simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T, b1T]
        using out,
      hrel⟩
  case termAppNVal =>
    intro Gamma Psi b0 b1 e0 e1 v0 v1 tauF0 tauF1 tauArg tauOut
      ht hbv hTy he0 he1 ihTy ih0 ih1 DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    have hinst : Basis.subst x n (Basis.instantiate e1 b1) =
        Basis.instantiate (Term.subst x n e1) (Basis.subst x n b1) :=
      Basis.subst_openRec x n wt.source.data.lc b1 0 e1
    have htT : Nonempty (HasType ∅ GammaT
        (.appN (Term.subst x n e0) (Term.subst x n e1))
        (Basis.tof (Basis.subst x n (Basis.instantiate e1 b1)))) := by
      simpa only [Term.subst, Basis.tof_subst] using ht.map wt.source.hasType
    rw [hinst] at htT
    have hbvT := wt.source.typeCtx.basisValid hbv
    rw [hinst] at hbvT
    obtain ⟨tauOutT, hTyT, hrel⟩ := ihTy wt.typeCtx
    rw [hinst] at hTyT
    obtain ⟨v0T, tauFT, he0T, _⟩ := ih0 wt
    have he0At : C.TyAt GammaT PsiT
        (.frame (Basis.subst x n b0) (Basis.subst x n b1)) tauFT := by
      simpa only [Basis.subst] using he0T.tyAt
    obtain ⟨tauF0T, tauF1T, rfl, _, _, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_frame_inv_full he0At
    have he0T' : C.Term ∅ GammaT PsiT (Term.subst x n e0)
        (.frame (Basis.subst x n b0) (Basis.subst x n b1)) v0T
        (.piTy tauF0T tauF1T) := by
      simpa only [Basis.subst] using he0T
    obtain ⟨v1T, tauArgT, he1T, _⟩ := ih1 wt
    have out := C.Term.appN_val htT hbvT hTyT he0T' he1T
    exact ⟨.applyAt v0T v1T tauOutT, tauOutT,
      by simpa only [Term.subst, hinst] using out, hrel⟩
  case termAppL =>
    intro Delta0 Delta1 Gamma Psi b0 b1 e0 e1 v0 v1
      sv svOut svMat0 svMat1 svArg hdis htof1 ht hbv hsv hTy he0 he1
      ihS ihTy ih0 ih1 DeltaT GammaT PsiT wt
    let ws := wt.split hdis
    let b0T := Basis.subst x n b0
    let b1T := Basis.subst x n b1
    have htof1T : Basis.tof b1T = .space (Basis.sof b1T) :=
      Basis.tof_space_subst_checked htof1
    have htT : Nonempty (HasType (ws.DeltaT0 ∪ ws.DeltaT1) GammaT
        (.appL (Basis.sof b0T) (Basis.sof b1T)
          (Term.subst x n e0) (Term.subst x n e1)) (Basis.tof b1T)) := by
      rw [ws.union_eq]
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.sof_subst, b0T, b1T] using htT0
    have hbvT : BasisValid GammaT b1T := wt.source.typeCtx.basisValid hbv
    obtain ⟨svT, hsvT0, _⟩ := ihS wt.typeCtx
    have hsvT : C.Space GammaT PsiT (Basis.sof b0T) svT := by
      simpa only [Basis.sof_subst, b0T] using hsvT0
    obtain ⟨tauOutT, hTyT0, hrelOut⟩ := ihTy wt.typeCtx
    obtain ⟨svOutT, rfl, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full htof1T hTyT0
    obtain ⟨env0T, tauMatT, he0T0, _⟩ := ih0 ws.left
    have he0At : C.TyAt GammaT PsiT (.tprod (.dual b0T) b1T) tauMatT := by
      simpa only [Basis.subst, b0T, b1T] using he0T0.tyAt
    obtain ⟨svMatT, rfl, hspaceMatT⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full rfl he0At
    obtain ⟨svMat0T, svMat1T, rfl⟩ :=
      checkedSpace_tprod_value_inv hspaceMatT
    have he0T : C.Term ws.DeltaT0 GammaT PsiT (Term.subst x n e0)
        (.tprod (.dual b0T) b1T) env0T
        (.space (.tprod svMat0T svMat1T)) := by
      simpa only [Basis.subst, b0T, b1T] using he0T0
    obtain ⟨env1T, tauArgT, he1T0, _⟩ := ih1 ws.right
    have hArgTof : Basis.tof b0T = .space (Basis.sof b0T) :=
      Basis.tof_space_subst_checked (checkedTyAt_space_tof_eq he1.tyAt)
    obtain ⟨svArgT, rfl, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full hArgTof he1T0.tyAt
    have he1T : C.Term ws.DeltaT1 GammaT PsiT (Term.subst x n e1)
        b0T env1T (.space svArgT) := by
      simpa only [b0T] using he1T0
    have out := C.Term.appL_lin ws.disjoint htof1T htT hbvT hsvT
      hTyT0 he0T he1T
    refine ⟨ValExpr.reshapBase (.ttv svT env0T env1T) svOutT,
      .space svOutT, ?_, hrelOut⟩
    simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T, b1T,
      ws.union_eq] using out
  case termAppI =>
    intro Delta0 Delta1 Gamma Psi b0 e0 e1 v0 v1 sv svFun svArg
      hdis ht hsv hTy he0 he1 ihS ihTy ih0 ih1 DeltaT GammaT PsiT wt
    let ws := wt.split hdis
    let b0T := Basis.subst x n b0
    have htT : Nonempty (HasType (ws.DeltaT0 ∪ ws.DeltaT1) GammaT
        (.appI (Basis.sof b0T) (Term.subst x n e0) (Term.subst x n e1))
        (Basis.tof .one)) := by
      rw [ws.union_eq]
      simpa only [Term.subst, Basis.tof_subst, Basis.sof_subst, b0T] using
        ht.map wt.source.hasType
    obtain ⟨svT, hsvT0, _⟩ := ihS wt.typeCtx
    have hsvT : C.Space GammaT PsiT (Basis.sof b0T) svT := by
      simpa only [Basis.sof_subst, b0T] using hsvT0
    have hTyT : C.TyAt GammaT PsiT .one (.space .real) :=
      .space rfl .one .real
    obtain ⟨env0T, tauFunT, he0T0, _⟩ := ih0 ws.left
    obtain ⟨svFunT, rfl, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full rfl
        (by simpa only [Basis.subst, b0T] using he0T0.tyAt)
    have he0T : C.Term ws.DeltaT0 GammaT PsiT (Term.subst x n e0)
        (.dual b0T) env0T (.space svFunT) := by
      simpa only [Basis.subst, b0T] using he0T0
    obtain ⟨env1T, tauArgT, he1T0, _⟩ := ih1 ws.right
    have hArgTof : Basis.tof b0T = .space (Basis.sof b0T) :=
      Basis.tof_space_subst_checked (checkedTyAt_space_tof_eq he1.tyAt)
    obtain ⟨svArgT, rfl, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_space_inv_full hArgTof he1T0.tyAt
    have he1T : C.Term ws.DeltaT1 GammaT PsiT (Term.subst x n e1)
        b0T env1T (.space svArgT) := by
      simpa only [b0T] using he1T0
    have out := C.Term.appI_lin ws.disjoint htT hsvT hTyT he0T he1T
    refine ⟨.ttv svT
        (.reshap env0T (.space (.tprod svT .real)) (.space svT)) env1T,
      .space .real, ?_, .space .real⟩
    simpa only [Term.subst, Basis.subst, Basis.sof_subst, b0T,
      ws.union_eq] using out
  case termZero =>
    intro Delta Gamma Psi bb sv htof ht hbv hTy hs ihTy ihs
      DeltaT GammaT PsiT wt
    have htofT : Basis.tof (Basis.subst x n bb) =
        .space (Basis.sof (Basis.subst x n bb)) :=
      Basis.tof_space_subst_checked htof
    have htT : Nonempty (HasType DeltaT GammaT
        (.zero (Basis.sof (Basis.subst x n bb)))
        (Basis.tof (Basis.subst x n bb))) := by
      simpa only [Term.subst, Basis.tof_subst, Basis.sof_subst] using
        ht.map wt.source.hasType
    have hbvT := wt.source.typeCtx.basisValid hbv
    obtain ⟨svT, hsT0, hrel⟩ := ihs wt.typeCtx
    have hsT : C.Space GammaT PsiT
        (Basis.sof (Basis.subst x n bb)) svT := by
      simpa only [Basis.sof_subst] using hsT0
    have hTyT : C.TyAt GammaT PsiT (Basis.subst x n bb) (.space svT) :=
      .space htofT hbvT hsT
    exact ⟨.zero svT, .space svT,
      by simpa only [Term.subst, Basis.sof_subst] using
        C.Term.zero htofT htT hbvT hTyT hsT,
      .space hrel⟩
  case termRlit =>
    intro Gamma Psi r ht hTy ihTy DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    have htT : Nonempty (HasType ∅ GammaT (.real r) (Basis.tof .one)) := by
      simpa only [Term.subst, Basis.tof_subst] using ht.map wt.source.hasType
    have hbvT : BasisValid GammaT (.one : Basis) := .one
    have hTyT : C.TyAt GammaT PsiT .one (.space .real) :=
      .space rfl hbvT .real
    exact ⟨.rlit r, .space .real,
      by simpa only [Term.subst, Basis.subst] using C.Term.rlit r htT hTyT,
      .space .real⟩
  case termInnerStd =>
    intro Gamma Psi b0 s sv hb0 hsof ht hbv hTy hs ihTy ihs
      DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    let b0T := Basis.subst x n b0
    have hsofT : Basis.sof b0T = Space.subst x n s := by
      dsimp [b0T]
      rw [Basis.sof_subst, hsof]
    have htT : Nonempty (HasType ∅ GammaT
        (.inner (Space.subst x n s))
        (Basis.tof (.tprod (.dual b0T) (.dual b0T)))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.subst] using htT0
    have hbvT : BasisValid GammaT
        (.tprod (.dual b0T) (.dual b0T)) := by
      dsimp [b0T]
      simpa only [Basis.subst] using wt.source.typeCtx.basisValid hbv
    obtain ⟨svT, hsT0, hrel⟩ := ihs wt.typeCtx
    have hsT : C.Space GammaT PsiT (Basis.sof b0T) svT := by
      rw [hsofT]
      exact hsT0
    have hsOut : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b0T) (.dual b0T)))
        (.tprod svT svT) :=
      .tprod hbvT.sof_valid (.dual (hsT.toS.svalid.map SValid.dual) hsT)
        (.dual (hsT.toS.svalid.map SValid.dual) hsT)
    have hTyT : C.TyAt GammaT PsiT
        (.tprod (.dual b0T) (.dual b0T)) (.space (.tprod svT svT)) :=
      .space rfl hbvT hsOut
    have out := C.Term.inner_std
      ((RenameProof.Basis.isStd_subst x n b0).symm ▸ hb0) hsofT
      htT hbvT hTyT hsT0
    exact ⟨.idelta svT, .space (.tprod svT svT),
      by simpa only [Term.subst, Basis.subst, b0T] using out,
      .space (.tprod hrel hrel)⟩
  case termEmbedKer =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
      hTy hi0 hi1 he ihTy ihI0 ihI1 ihE DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    let b0T := Basis.subst x n b0
    let b1T := Basis.subst x n b1
    let s0T := Space.subst x n s0
    let s1T := Space.subst x n s1
    have hs0T : Basis.sof b0T = s0T := by
      dsimp [b0T, s0T]
      rw [Basis.sof_subst, hs0]
    have hs1T : Basis.sof b1T = s1T := by
      dsimp [b1T, s1T]
      rw [Basis.sof_subst, hs1]
    obtain ⟨sv0T, env0T, hspace0T, hi0T, hdof0⟩ :=
      alignGram hs0 hi0 ihI0 wt
    obtain ⟨sv1T, env1T, hspace1T, hi1T, hdof1⟩ :=
      alignGram hs1 hi1 ihI1 wt
    have hi0T' : C.Term ∅ GammaT PsiT (.inner s0T)
        (.tprod (.dual b0T) (.dual b0T)) env0T
        (.space (.tprod sv0T sv0T)) := by
      rw [← hs0T]
      exact hi0T
    have hi1T' : C.Term ∅ GammaT PsiT (.inner s1T)
        (.tprod (.dual b1T) (.dual b1T)) env1T
        (.space (.tprod sv1T sv1T)) := by
      rw [← hs1T]
      exact hi1T
    have hbvMapT : BasisValid GammaT (.tprod (.dual b0T) b1T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid he.basisValid
    have hspaceMapT : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b0T) b1T)) (.tprod sv0T sv1T) :=
      .tprod hbvMapT.sof_valid
        (.dual hbvMapT.tprod_inv.1.sof_valid hspace0T) hspace1T
    have hTyMapT : C.TyAt GammaT PsiT (.tprod (.dual b0T) b1T)
        (.space (.tprod sv0T sv1T)) :=
      .space rfl hbvMapT hspaceMapT
    obtain ⟨vRaw, tauRaw, heRaw, _⟩ := ihE wt
    let vT := ValExpr.reshap vRaw (.space (.tprod sv0T sv1T)) tauRaw
    have heT : C.Term ∅ GammaT PsiT (Term.subst x n e)
        (.tprod (.dual b0T) b1T) vT (.space (.tprod sv0T sv1T)) := by
      simpa only [Basis.subst, b0T, b1T] using
        RawCertifiedProgressScratch.retag heRaw hTyMapT
    let boutT : Basis := .tprod
      (.dual (.proj (.ker s0T s1T (Term.subst x n e)) b0T b1T)) b0T
    have htT : Nonempty (HasType (∅ : LCtx) GammaT
        (.embed (.ker s0T s1T (Term.subst x n e))) (Basis.tof boutT)) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Space.subst, Basis.subst, b0T, b1T,
        s0T, s1T, boutT] using htT0
    have hbvOutT : BasisValid GammaT boutT := by
      dsimp [boutT, b0T, b1T, s0T, s1T]
      simpa only [Basis.subst, Space.subst] using
        wt.source.typeCtx.basisValid hbv
    have hkerT : C.Space GammaT PsiT
        (.ker s0T s1T (Term.subst x n e))
        (.ffs .kernel (.tprod sv0T sv1T)
          (ValExpr.reshapBase vT (.tprod sv0T sv1T))) := by
      apply C.Space.ker hbvOutT.tprod_inv.1.dual_inv.sof_valid
        (by simp only [Basis.sof, hs0T, hs1T])
        ⟨b0T, b1T, rfl⟩ hspaceMapT heT
    have hspaceOutT : C.Space GammaT PsiT (Basis.sof boutT)
        (.tprod
          (.ffs .kernel (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv0T) :=
      .tprod hbvOutT.sof_valid
        (.dual hbvOutT.tprod_inv.1.sof_valid hkerT) hspace0T
    have hTyOutT : C.TyAt GammaT PsiT boutT
        (.space (.tprod
          (.ffs .kernel (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv0T)) :=
      .space rfl hbvOutT hspaceOutT
    have out := C.Term.embed_ker hs0T hs1T htT hbvOutT hTyOutT
      hi0T' hi1T' heT
    have hParent : CutSpaceRel (.tprod sv0T sv1T) (.tprod sv0 sv1) :=
      .tprodOfDof hdof0 hdof1
    have hOutRel : CutSpaceRel
        (.tprod
          (.ffs .kernel (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv0T)
        (.tprod
          (.ffs .kernel (.tprod sv0 sv1)
            (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) :=
      .ffsTail hParent hdof0
    refine ⟨.vtrans (.gsvdUI vT env0T env1T), _, ?_, .space hOutRel⟩
    simpa only [Term.subst, Space.subst, Basis.subst, b0T, b1T,
      s0T, s1T, boutT] using out
  case termEmbedCoker =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
      hTy hi0 hi1 he ihTy ihI0 ihI1 ihE DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    let b0T := Basis.subst x n b0
    let b1T := Basis.subst x n b1
    let s0T := Space.subst x n s0
    let s1T := Space.subst x n s1
    have hs0T : Basis.sof b0T = s0T := by
      dsimp [b0T, s0T]
      rw [Basis.sof_subst, hs0]
    have hs1T : Basis.sof b1T = s1T := by
      dsimp [b1T, s1T]
      rw [Basis.sof_subst, hs1]
    obtain ⟨sv0T, env0T, hspace0T, hi0T, hdof0⟩ :=
      alignGram hs0 hi0 ihI0 wt
    obtain ⟨sv1T, env1T, hspace1T, hi1T, hdof1⟩ :=
      alignGram hs1 hi1 ihI1 wt
    have hi0T' : C.Term ∅ GammaT PsiT (.inner s0T)
        (.tprod (.dual b0T) (.dual b0T)) env0T
        (.space (.tprod sv0T sv0T)) := by
      rw [← hs0T]
      exact hi0T
    have hi1T' : C.Term ∅ GammaT PsiT (.inner s1T)
        (.tprod (.dual b1T) (.dual b1T)) env1T
        (.space (.tprod sv1T sv1T)) := by
      rw [← hs1T]
      exact hi1T
    have hbvMapT : BasisValid GammaT (.tprod (.dual b0T) b1T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid he.basisValid
    have hspaceMapT : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b0T) b1T)) (.tprod sv0T sv1T) :=
      .tprod hbvMapT.sof_valid
        (.dual hbvMapT.tprod_inv.1.sof_valid hspace0T) hspace1T
    have hTyMapT : C.TyAt GammaT PsiT (.tprod (.dual b0T) b1T)
        (.space (.tprod sv0T sv1T)) :=
      .space rfl hbvMapT hspaceMapT
    obtain ⟨vRaw, tauRaw, heRaw, _⟩ := ihE wt
    let vT := ValExpr.reshap vRaw (.space (.tprod sv0T sv1T)) tauRaw
    have heT : C.Term ∅ GammaT PsiT (Term.subst x n e)
        (.tprod (.dual b0T) b1T) vT (.space (.tprod sv0T sv1T)) := by
      simpa only [Basis.subst, b0T, b1T] using
        RawCertifiedProgressScratch.retag heRaw hTyMapT
    let boutT : Basis := .tprod
      (.dual (.proj (.coker s0T s1T (Term.subst x n e)) b0T b1T)) b0T
    have htT : Nonempty (HasType (∅ : LCtx) GammaT
        (.embed (.coker s0T s1T (Term.subst x n e))) (Basis.tof boutT)) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Space.subst, Basis.subst, b0T, b1T,
        s0T, s1T, boutT] using htT0
    have hbvOutT : BasisValid GammaT boutT := by
      dsimp [boutT, b0T, b1T, s0T, s1T]
      simpa only [Basis.subst, Space.subst] using
        wt.source.typeCtx.basisValid hbv
    have hcokerT : C.Space GammaT PsiT
        (.coker s0T s1T (Term.subst x n e))
        (.ffs .cokernel (.tprod sv0T sv1T)
          (ValExpr.reshapBase vT (.tprod sv0T sv1T))) := by
      apply C.Space.coker hbvOutT.tprod_inv.1.dual_inv.sof_valid
        (by simp only [Basis.sof, hs0T, hs1T])
        ⟨b0T, b1T, rfl⟩ hspaceMapT heT
    have hspaceOutT : C.Space GammaT PsiT (Basis.sof boutT)
        (.tprod
          (.ffs .cokernel (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv0T) :=
      .tprod hbvOutT.sof_valid
        (.dual hbvOutT.tprod_inv.1.sof_valid hcokerT) hspace0T
    have hTyOutT : C.TyAt GammaT PsiT boutT
        (.space (.tprod
          (.ffs .cokernel (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv0T)) :=
      .space rfl hbvOutT hspaceOutT
    have out := C.Term.embed_coker hs0T hs1T htT hbvOutT hTyOutT
      hi0T' hi1T' heT
    have hParent : CutSpaceRel (.tprod sv0T sv1T) (.tprod sv0 sv1) :=
      .tprodOfDof hdof0 hdof1
    have hOutRel : CutSpaceRel
        (.tprod
          (.ffs .cokernel (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv0T)
        (.tprod
          (.ffs .cokernel (.tprod sv0 sv1)
            (ValExpr.reshapBase v (.tprod sv0 sv1))) sv0) :=
      .ffsTail hParent hdof0
    refine ⟨.vtrans (.gsvdU vT env0T env1T), _, ?_, .space hOutRel⟩
    simpa only [Term.subst, Space.subst, Basis.subst, b0T, b1T,
      s0T, s1T, boutT] using out
  case termEmbedImg =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
      hTy hi0 hi1 he ihTy ihI0 ihI1 ihE DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    let b0T := Basis.subst x n b0
    let b1T := Basis.subst x n b1
    let s0T := Space.subst x n s0
    let s1T := Space.subst x n s1
    have hs0T : Basis.sof b0T = s0T := by
      dsimp [b0T, s0T]
      rw [Basis.sof_subst, hs0]
    have hs1T : Basis.sof b1T = s1T := by
      dsimp [b1T, s1T]
      rw [Basis.sof_subst, hs1]
    obtain ⟨sv0T, env0T, hspace0T, hi0T, hdof0⟩ :=
      alignGram hs0 hi0 ihI0 wt
    obtain ⟨sv1T, env1T, hspace1T, hi1T, hdof1⟩ :=
      alignGram hs1 hi1 ihI1 wt
    have hi0T' : C.Term ∅ GammaT PsiT (.inner s0T)
        (.tprod (.dual b0T) (.dual b0T)) env0T
        (.space (.tprod sv0T sv0T)) := by
      rw [← hs0T]
      exact hi0T
    have hi1T' : C.Term ∅ GammaT PsiT (.inner s1T)
        (.tprod (.dual b1T) (.dual b1T)) env1T
        (.space (.tprod sv1T sv1T)) := by
      rw [← hs1T]
      exact hi1T
    have hbvMapT : BasisValid GammaT (.tprod (.dual b0T) b1T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid he.basisValid
    have hspaceMapT : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b0T) b1T)) (.tprod sv0T sv1T) :=
      .tprod hbvMapT.sof_valid
        (.dual hbvMapT.tprod_inv.1.sof_valid hspace0T) hspace1T
    have hTyMapT : C.TyAt GammaT PsiT (.tprod (.dual b0T) b1T)
        (.space (.tprod sv0T sv1T)) :=
      .space rfl hbvMapT hspaceMapT
    obtain ⟨vRaw, tauRaw, heRaw, _⟩ := ihE wt
    let vT := ValExpr.reshap vRaw (.space (.tprod sv0T sv1T)) tauRaw
    have heT : C.Term ∅ GammaT PsiT (Term.subst x n e)
        (.tprod (.dual b0T) b1T) vT (.space (.tprod sv0T sv1T)) := by
      simpa only [Basis.subst, b0T, b1T] using
        RawCertifiedProgressScratch.retag heRaw hTyMapT
    let boutT : Basis := .tprod
      (.dual (.proj (.img s0T s1T (Term.subst x n e)) b0T b1T)) b1T
    have htT : Nonempty (HasType (∅ : LCtx) GammaT
        (.embed (.img s0T s1T (Term.subst x n e))) (Basis.tof boutT)) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Space.subst, Basis.subst, b0T, b1T,
        s0T, s1T, boutT] using htT0
    have hbvOutT : BasisValid GammaT boutT := by
      dsimp [boutT, b0T, b1T, s0T, s1T]
      simpa only [Basis.subst, Space.subst] using
        wt.source.typeCtx.basisValid hbv
    have hffsT : C.Space GammaT PsiT
        (.img s0T s1T (Term.subst x n e))
        (.ffs .image (.tprod sv0T sv1T)
          (ValExpr.reshapBase vT (.tprod sv0T sv1T))) := by
      apply C.Space.img hbvOutT.tprod_inv.1.dual_inv.sof_valid
        (by simp only [Basis.sof, hs0T, hs1T])
        ⟨b0T, b1T, rfl⟩ hspaceMapT heT
    have hspaceOutT : C.Space GammaT PsiT (Basis.sof boutT)
        (.tprod
          (.ffs .image (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv1T) :=
      .tprod hbvOutT.sof_valid
        (.dual hbvOutT.tprod_inv.1.sof_valid hffsT) hspace1T
    have hTyOutT : C.TyAt GammaT PsiT boutT
        (.space (.tprod
          (.ffs .image (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv1T)) :=
      .space rfl hbvOutT hspaceOutT
    have out := C.Term.embed_img hs0T hs1T htT hbvOutT hTyOutT
      hi0T' hi1T' heT
    have hParent : CutSpaceRel (.tprod sv0T sv1T) (.tprod sv0 sv1) :=
      .tprodOfDof hdof0 hdof1
    have hOutRel : CutSpaceRel
        (.tprod
          (.ffs .image (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv1T)
        (.tprod
          (.ffs .image (.tprod sv0 sv1)
            (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) :=
      .ffsTail hParent hdof1
    refine ⟨.vtrans (.gsvdV vT env0T env1T), _, ?_, .space hOutRel⟩
    simpa only [Term.subst, Space.subst, Basis.subst, b0T, b1T,
      s0T, s1T, boutT] using out
  case termEmbedCoimg =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
      hTy hi0 hi1 he ihTy ihI0 ihI1 ihE DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    let b0T := Basis.subst x n b0
    let b1T := Basis.subst x n b1
    let s0T := Space.subst x n s0
    let s1T := Space.subst x n s1
    have hs0T : Basis.sof b0T = s0T := by
      dsimp [b0T, s0T]
      rw [Basis.sof_subst, hs0]
    have hs1T : Basis.sof b1T = s1T := by
      dsimp [b1T, s1T]
      rw [Basis.sof_subst, hs1]
    obtain ⟨sv0T, env0T, hspace0T, hi0T, hdof0⟩ :=
      alignGram hs0 hi0 ihI0 wt
    obtain ⟨sv1T, env1T, hspace1T, hi1T, hdof1⟩ :=
      alignGram hs1 hi1 ihI1 wt
    have hi0T' : C.Term ∅ GammaT PsiT (.inner s0T)
        (.tprod (.dual b0T) (.dual b0T)) env0T
        (.space (.tprod sv0T sv0T)) := by
      rw [← hs0T]
      exact hi0T
    have hi1T' : C.Term ∅ GammaT PsiT (.inner s1T)
        (.tprod (.dual b1T) (.dual b1T)) env1T
        (.space (.tprod sv1T sv1T)) := by
      rw [← hs1T]
      exact hi1T
    have hbvMapT : BasisValid GammaT (.tprod (.dual b0T) b1T) := by
      simpa only [Basis.subst, b0T, b1T] using
        wt.source.typeCtx.basisValid he.basisValid
    have hspaceMapT : C.Space GammaT PsiT
        (Basis.sof (.tprod (.dual b0T) b1T)) (.tprod sv0T sv1T) :=
      .tprod hbvMapT.sof_valid
        (.dual hbvMapT.tprod_inv.1.sof_valid hspace0T) hspace1T
    have hTyMapT : C.TyAt GammaT PsiT (.tprod (.dual b0T) b1T)
        (.space (.tprod sv0T sv1T)) :=
      .space rfl hbvMapT hspaceMapT
    obtain ⟨vRaw, tauRaw, heRaw, _⟩ := ihE wt
    let vT := ValExpr.reshap vRaw (.space (.tprod sv0T sv1T)) tauRaw
    have heT : C.Term ∅ GammaT PsiT (Term.subst x n e)
        (.tprod (.dual b0T) b1T) vT (.space (.tprod sv0T sv1T)) := by
      simpa only [Basis.subst, b0T, b1T] using
        RawCertifiedProgressScratch.retag heRaw hTyMapT
    let boutT : Basis := .tprod
      (.dual (.proj (.coimg s0T s1T (Term.subst x n e)) b0T b1T)) b1T
    have htT : Nonempty (HasType (∅ : LCtx) GammaT
        (.embed (.coimg s0T s1T (Term.subst x n e))) (Basis.tof boutT)) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Space.subst, Basis.subst, b0T, b1T,
        s0T, s1T, boutT] using htT0
    have hbvOutT : BasisValid GammaT boutT := by
      dsimp [boutT, b0T, b1T, s0T, s1T]
      simpa only [Basis.subst, Space.subst] using
        wt.source.typeCtx.basisValid hbv
    have hffsT : C.Space GammaT PsiT
        (.coimg s0T s1T (Term.subst x n e))
        (.ffs .coimage (.tprod sv0T sv1T)
          (ValExpr.reshapBase vT (.tprod sv0T sv1T))) := by
      apply C.Space.coimg hbvOutT.tprod_inv.1.dual_inv.sof_valid
        (by simp only [Basis.sof, hs0T, hs1T])
        ⟨b0T, b1T, rfl⟩ hspaceMapT heT
    have hspaceOutT : C.Space GammaT PsiT (Basis.sof boutT)
        (.tprod
          (.ffs .coimage (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv1T) :=
      .tprod hbvOutT.sof_valid
        (.dual hbvOutT.tprod_inv.1.sof_valid hffsT) hspace1T
    have hTyOutT : C.TyAt GammaT PsiT boutT
        (.space (.tprod
          (.ffs .coimage (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv1T)) :=
      .space rfl hbvOutT hspaceOutT
    have out := C.Term.embed_coimg hs0T hs1T htT hbvOutT hTyOutT
      hi0T' hi1T' heT
    have hParent : CutSpaceRel (.tprod sv0T sv1T) (.tprod sv0 sv1) :=
      .tprodOfDof hdof0 hdof1
    have hOutRel : CutSpaceRel
        (.tprod
          (.ffs .coimage (.tprod sv0T sv1T)
            (ValExpr.reshapBase vT (.tprod sv0T sv1T))) sv1T)
        (.tprod
          (.ffs .coimage (.tprod sv0 sv1)
            (ValExpr.reshapBase v (.tprod sv0 sv1))) sv1) :=
      .ffsTail hParent hdof1
    refine ⟨.vtrans (.gsvdVI vT env0T env1T), _, ?_, .space hOutRel⟩
    simpa only [Term.subst, Space.subst, Basis.subst, b0T, b1T,
      s0T, s1T, boutT] using out
  case termNllam =>
    intro Gamma Psi b0 b1 tau0 tau1 e tauV0 tauV1 env hb0 hb1 ht hbv
      hTy hdom L he hcod ihTy ihDom ihBody ihCod
    intro DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    have hb0S : Basis.BasisValid Gamma b0 := hbv.frame_inv.1
    have hb0T : Basis.BasisValid GammaT (Basis.subst x n b0) :=
      wt.source.typeCtx.basisValid hb0S
    have hbvT : Basis.BasisValid GammaT
        (.frame (Basis.subst x n b0) (Basis.subst x n b1)) := by
      simpa only [Basis.subst] using wt.source.typeCtx.basisValid hbv
    have htof0T : Basis.tof (Basis.subst x n b0) = Ty.subst x n tau0 := by
      rw [Basis.tof_subst, hb0]
    have htT0 : Nonempty (HasType ∅ GammaT
        (.nllam (Ty.subst x n tau0) (Term.subst x n e))
        (Basis.tof (.frame (Basis.subst x n b0) (Basis.subst x n b1)))) := by
      have htT := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT
      simpa only [Term.subst, Basis.subst] using htT
    rw [← htof0T] at htT0
    obtain ⟨tau0T, hdomT, _⟩ := ihDom wt.typeCtx
    have hlc0T : ValTy.lc tau0T := evalT_lc hdomT.erase wt.lc
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
      (L ∪ {x} ∪ Gamma0.keys ∪ GammaT.keys ∪
        EvalCtx.avoidB Psi ∪ EvalCtx.avoidB PsiT ∪
        Basis.fv (Basis.subst x n bX) ∪
        Basis.fv (Basis.subst x n b0) ∪
        Basis.fv (Basis.subst x n b1) ∪
        ValTy.fv tau0T ∪ Term.fv (Term.subst x n e))
    have hzL : z ∉ L := by intro hm; apply hz; simp [hm]
    have hzx : z ≠ x := by intro h; subst z; apply hz; simp
    have hz0k : z ∉ Gamma0.keys := by intro hm; apply hz; simp [hm]
    have hz0 : Gamma0.lookup z = none :=
      Finmap.lookup_eq_none.mpr (fun hm => hz0k (Finmap.mem_keys.mpr hm))
    have hzT : z ∉ GammaT := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzPsiS : z ∉ EvalCtx.avoidB Psi := by
      intro hm; apply hz; simp [hm]
    have hzPsiT : z ∉ EvalCtx.avoidB PsiT := by
      intro hm; apply hz; simp [hm]
    have hzCut : z ∉ Basis.fv (Basis.subst x n bX) := by
      intro hm; apply hz; simp [hm]
    have hzb0T : z ∉ Basis.fv (Basis.subst x n b0) := by
      intro hm; apply hz; simp [hm]
    have hzb1T : z ∉ Basis.fv (Basis.subst x n b1) := by
      intro hm; apply hz; simp [hm]
    have hztau0T : z ∉ ValTy.fv tau0T := by
      intro hm; apply hz; simp [hm]
    have hzeT : z ∉ Term.fv (Term.subst x n e) := by
      intro hm; apply hz; simp [hm]
    have wz := wt.extendNL z b0 tauV0 tau0T hb0S hzx hz0
      Finmap.notMem_empty Finmap.notMem_empty hzT
      (EvalCtx.avoidB_spec hzPsiS).1 (EvalCtx.avoidB_spec hzPsiT).1
      hzCut hlc0T
    rw [hb0] at wz
    obtain ⟨vBodyT, tauBodyT, hbodyT0, _⟩ := ihBody z hzL wz
    have hbodyT : C.Term ∅
        (Finmap.insert z (Ty.subst x n tau0) GammaT)
        (PsiT.extend z (Basis.subst x n b0) (.var z tau0T))
        (Term.openVar z (Term.subst x n e))
        (Basis.openVar z (Basis.subst x n b1)) vBodyT tauBodyT := by
      simpa only [Basis.tof_subst,
        Graded.Term.subst_openVar_ne wt.source.data.lc hzx,
        Basis.subst_openVar_ne_checked wt.source.data.lc hzx] using hbodyT0
    rw [← htof0T] at hbodyT
    have hlcvBodyT : ValExpr.lc vBodyT :=
      opStep_lc hbodyT.erase (wt.lc.extend (.var hlc0T))
    have hlctauBodyT : ValTy.lc tauBodyT :=
      evalT_lc hbodyT.tyAt.erase (wt.lc.extend (.var hlc0T))
    obtain ⟨vOut, tauOut, hout⟩ :=
      CheckedSubstBinder.termNllam_of_one_fresh laws wt.wf hbvT
        (Basis.IsTyBasis.subst_checked hTy.isTyBasis) htT0 hdomT hbodyT
        hbodyT.tyAt hzT hzPsiT hzb0T hztau0T hzeT hzb1T hlc0T
        hlcvBodyT hlctauBodyT
    obtain ⟨tauOut0, tauOut1, htauOut, _, _, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_frame_inv_full hout.tyAt
    subst tauOut
    exact ⟨vOut, .piTy tauOut0 tauOut1,
      by simpa only [Term.subst, Basis.subst, htof0T] using hout, .piTy⟩
  case termFrameReanchor =>
    intro Gamma Psi b0 b0' b1 n0 leev env1 tauV0 tauV0' tauV1 tauV1'
      htof ht hbv hTy h0 hfn hdom L hx hcod
      ihTy ih0 ihFn ihDom ihX ihCod
    intro DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    have hb0S : Basis.BasisValid Gamma b0 := hbv.frame_inv.1
    have hb0T : Basis.BasisValid GammaT (Basis.subst x n b0) :=
      wt.source.typeCtx.basisValid hb0S
    have hb0'T : Basis.BasisValid GammaT (Basis.subst x n b0') :=
      wt.source.typeCtx.basisValid hfn.basisValid.frame_inv.1
    have hbvT : Basis.BasisValid GammaT
        (.frame (Basis.subst x n b0) (Basis.subst x n b1)) := by
      simpa only [Basis.subst] using wt.source.typeCtx.basisValid hbv
    have htofT : Basis.tof (Basis.subst x n b0') =
        Basis.tof (Basis.subst x n b0) := by
      rw [Basis.tof_subst, Basis.tof_subst, htof]
    have htT : Nonempty (HasType ∅ GammaT (Term.subst x n n0)
        (Basis.tof (.frame (Basis.subst x n b0) (Basis.subst x n b1)))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Basis.subst] using htT0
    obtain ⟨tau0T, h0T, _⟩ := ih0 wt.typeCtx
    have hlc0T : ValTy.lc tau0T := evalT_lc h0T.erase wt.lc
    obtain ⟨vFnT, tauFnT, hfnT0, _⟩ := ihFn wt
    have hfnAt : C.TyAt GammaT PsiT
        (.frame (Basis.subst x n b0') (Basis.subst x n b1)) tauFnT := by
      simpa only [Basis.subst] using hfnT0.tyAt
    obtain ⟨tauFn0T, tauFn1T, htauFnT, hdomFnT, _, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_frame_inv_full hfnAt
    subst tauFnT
    have hfnT : C.Term ∅ GammaT PsiT (Term.subst x n n0)
        (.frame (Basis.subst x n b0') (Basis.subst x n b1)) vFnT
        (.piTy tauFn0T tauFn1T) := by
      simpa only [Basis.subst] using hfnT0
    have hlcFn0T : ValTy.lc tauFn0T := evalT_lc hdomFnT.erase wt.lc
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
      (L ∪ {x} ∪ Gamma0.keys ∪ GammaT.keys ∪
        EvalCtx.avoidB Psi ∪ EvalCtx.avoidB PsiT ∪
        Basis.fv (Basis.subst x n bX) ∪
        Basis.fv (Basis.subst x n b0) ∪
        Basis.fv (Basis.subst x n b0') ∪
        Basis.fv (Basis.subst x n b1) ∪
        ValTy.fv tau0T ∪ ValTy.fv tauFn0T)
    have hzL : z ∉ L := by intro hm; apply hz; simp [hm]
    have hzx : z ≠ x := by intro h; subst z; apply hz; simp
    have hz0k : z ∉ Gamma0.keys := by intro hm; apply hz; simp [hm]
    have hz0 : Gamma0.lookup z = none :=
      Finmap.lookup_eq_none.mpr (fun hm => hz0k (Finmap.mem_keys.mpr hm))
    have hzT : z ∉ GammaT := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzPsiS : z ∉ EvalCtx.avoidB Psi := by
      intro hm; apply hz; simp [hm]
    have hzPsiT : z ∉ EvalCtx.avoidB PsiT := by
      intro hm; apply hz; simp [hm]
    have hzCut : z ∉ Basis.fv (Basis.subst x n bX) := by
      intro hm; apply hz; simp [hm]
    have hzb0T : z ∉ Basis.fv (Basis.subst x n b0) := by
      intro hm; apply hz; simp [hm]
    have hzb0'T : z ∉ Basis.fv (Basis.subst x n b0') := by
      intro hm; apply hz; simp [hm]
    have hzb1T : z ∉ Basis.fv (Basis.subst x n b1) := by
      intro hm; apply hz; simp [hm]
    have hztau0T : z ∉ ValTy.fv tau0T := by
      intro hm; apply hz; simp [hm]
    have hztauFn0T : z ∉ ValTy.fv tauFn0T := by
      intro hm; apply hz; simp [hm]
    have wz := wt.extendNL z b0 tauV0 tau0T hb0S hzx hz0
      Finmap.notMem_empty Finmap.notMem_empty hzT
      (EvalCtx.avoidB_spec hzPsiS).1 (EvalCtx.avoidB_spec hzPsiT).1
      hzCut hlc0T
    obtain ⟨vAnchorT, tauAnchorT, hAnchorT0, _⟩ := ihX z hzL wz
    have hAnchorRaw : C.Term ∅
        (Finmap.insert z (Basis.tof (Basis.subst x n b0)) GammaT)
        (PsiT.extend z (Basis.subst x n b0) (.var z tau0T))
        (.var z) (Basis.subst x n b0') vAnchorT tauAnchorT := by
      simpa only [Basis.tof_subst, Term.subst, if_neg (Ne.symm hzx)] using
        hAnchorT0
    have hinc : NLCtxIncl GammaT
        (Finmap.insert z (Basis.tof (Basis.subst x n b0)) GammaT) :=
      (NLCtxIncl.refl GammaT).insert_right hzT _
    have hdomFnExt : C.TyAt
        (Finmap.insert z (Basis.tof (Basis.subst x n b0)) GammaT)
        (PsiT.extend z (Basis.subst x n b0) (.var z tau0T))
        (Basis.subst x n b0') tauFn0T := by
      refine C.TyAt.weaken ?_ hinc
      exact RawCertifiedPiBasisTransport.checkedTyAt_extend hdomFnT hzPsiT
    let vAnchorA := ValExpr.reshap vAnchorT tauFn0T tauAnchorT
    have hAnchorT : C.Term ∅
        (Finmap.insert z (Basis.tof (Basis.subst x n b0)) GammaT)
        (PsiT.extend z (Basis.subst x n b0) (.var z tau0T))
        (.var z) (Basis.subst x n b0') vAnchorA tauFn0T :=
      RawCertifiedProgressScratch.retag hAnchorRaw hdomFnExt
    have hlcvAnchorA : ValExpr.lc vAnchorA :=
      opStep_lc hAnchorT.erase (wt.lc.extend (.var hlc0T))
    obtain ⟨tauCodT, hcodT0, _⟩ := ihCod z hzL wz.typeCtx
    have hcodT : C.TyAt
        (Finmap.insert z (Basis.tof (Basis.subst x n b0)) GammaT)
        (PsiT.extend z (Basis.subst x n b0) (.var z tau0T))
        (Basis.openVar z (Basis.subst x n b1)) tauCodT := by
      simpa only [Basis.tof_subst,
        Basis.subst_openVar_ne_checked wt.source.data.lc hzx] using hcodT0
    have hlcCodT : ValTy.lc tauCodT :=
      evalT_lc hcodT.erase (wt.lc.extend (.var hlc0T))
    obtain ⟨LA, hanchors⟩ := CheckedSubstBinder.checkedTerm_arbitrary_var_cofinite_of_fresh
      laws wt.wf hb0T.tof_tvalid rfl hb0T hzT hAnchorT hzPsiT
      hzb0T hztau0T hzb0'T hztauFn0T hlc0T hlcvAnchorA
    obtain ⟨LC, hcods⟩ :=
      RawCertifiedPiBasisTransport.checkedTyAt_arbitrary_cofinite_of_fresh
        laws wt.wf hb0T.tof_tvalid rfl hb0T hzT hcodT hzPsiT
        hzb0T hztau0T hzb1T hlc0T hlcCodT
    let env1T := ValExpr.closeRec 0 z vAnchorA
    let tau1T := ValTy.closeRec 0 z tauCodT
    have hTyT : C.TyAt GammaT PsiT
        (.frame (Basis.subst x n b0) (Basis.subst x n b1))
        (.piTy tau0T tau1T) :=
      .frame hbvT h0T LC (by simpa only [tau1T] using hcods)
    have hout := C.Term.frame_reanchor htofT htT hbvT hTyT h0T hfnT
      hdomFnT (LA ∪ LC)
      (fun y hy => by
        have hyA : y ∉ LA := fun hm => hy (Finset.mem_union_left _ hm)
        simpa only [env1T] using hanchors y hyA)
      (fun y hy => by
        have hyC : y ∉ LC := fun hm => hy (Finset.mem_union_right _ hm)
        simpa only [tau1T] using hcods y hyC)
    exact ⟨_, .piTy tau0T tau1T,
      by simpa only [Basis.subst] using hout, .piTy⟩
  case termFrameEta =>
    intro Gamma Psi b0 b1 n0 tauV0 tauV1 env ht hbv hTy hdom L he hcod
      ihTy ihDom ihBody ihCod
    intro DeltaT GammaT PsiT wt
    have hDeltaT : DeltaT = (∅ : LCtx) := wt.targetLinear_empty
    subst DeltaT
    have hb0S : Basis.BasisValid Gamma b0 := hbv.frame_inv.1
    have hbvT : Basis.BasisValid GammaT
        (.frame (Basis.subst x n b0) (Basis.subst x n b1)) := by
      simpa only [Basis.subst] using wt.source.typeCtx.basisValid hbv
    have htT : Nonempty (HasType ∅ GammaT (Term.subst x n n0)
        (Basis.tof (.frame (Basis.subst x n b0) (Basis.subst x n b1)))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Basis.subst] using htT0
    obtain ⟨tau0T, hdomT, _⟩ := ihDom wt.typeCtx
    have hlc0T : ValTy.lc tau0T := evalT_lc hdomT.erase wt.lc
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
      (L ∪ {x} ∪ Gamma0.keys ∪ GammaT.keys ∪
        EvalCtx.avoidB Psi ∪ EvalCtx.avoidB PsiT ∪
        Basis.fv (Basis.subst x n bX) ∪
        Basis.fv (Basis.subst x n b0) ∪
        Basis.fv (Basis.subst x n b1) ∪
        ValTy.fv tau0T ∪ Term.fv (Term.subst x n n0))
    have hzL : z ∉ L := by intro hm; apply hz; simp [hm]
    have hzx : z ≠ x := by intro h; subst z; apply hz; simp
    have hz0k : z ∉ Gamma0.keys := by intro hm; apply hz; simp [hm]
    have hz0 : Gamma0.lookup z = none :=
      Finmap.lookup_eq_none.mpr (fun hm => hz0k (Finmap.mem_keys.mpr hm))
    have hzT : z ∉ GammaT := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzPsiS : z ∉ EvalCtx.avoidB Psi := by
      intro hm; apply hz; simp [hm]
    have hzPsiT : z ∉ EvalCtx.avoidB PsiT := by
      intro hm; apply hz; simp [hm]
    have hzCut : z ∉ Basis.fv (Basis.subst x n bX) := by
      intro hm; apply hz; simp [hm]
    have hzb0T : z ∉ Basis.fv (Basis.subst x n b0) := by
      intro hm; apply hz; simp [hm]
    have hzb1T : z ∉ Basis.fv (Basis.subst x n b1) := by
      intro hm; apply hz; simp [hm]
    have hztau0T : z ∉ ValTy.fv tau0T := by
      intro hm; apply hz; simp [hm]
    have hzn0T : z ∉ Term.fv (Term.subst x n n0) := by
      intro hm; apply hz; simp [hm]
    have wz := wt.extendNL z b0 tauV0 tau0T hb0S hzx hz0
      Finmap.notMem_empty Finmap.notMem_empty hzT
      (EvalCtx.avoidB_spec hzPsiS).1 (EvalCtx.avoidB_spec hzPsiT).1
      hzCut hlc0T
    obtain ⟨vBodyT, tauBodyT, hbodyT0, _⟩ := ihBody z hzL wz
    have hbodyT : C.Term ∅
        (Finmap.insert z (Basis.tof (Basis.subst x n b0)) GammaT)
        (PsiT.extend z (Basis.subst x n b0) (.var z tau0T))
        (.appN (Term.subst x n n0) (.var z))
        (Basis.openVar z (Basis.subst x n b1)) vBodyT tauBodyT := by
      simpa only [Basis.tof_subst, Term.subst, if_neg (Ne.symm hzx),
        Basis.subst_openVar_ne_checked wt.source.data.lc hzx] using hbodyT0
    have hlcvBodyT : ValExpr.lc vBodyT :=
      opStep_lc hbodyT.erase (wt.lc.extend (.var hlc0T))
    have hlctauBodyT : ValTy.lc tauBodyT :=
      evalT_lc hbodyT.tyAt.erase (wt.lc.extend (.var hlc0T))
    obtain ⟨vOut, tauOut, hout⟩ :=
      CheckedSubstBinder.termFrameEta_of_one_fresh laws wt.wf hbvT
        (Basis.IsTyBasis.subst_checked hTy.isTyBasis) htT hdomT hbodyT
        hbodyT.tyAt hzT hzPsiT hzb0T hztau0T hzn0T hzb1T hlc0T
        hlcvBodyT hlctauBodyT
    obtain ⟨tauOut0, tauOut1, htauOut, _, _, _⟩ :=
      RawCertifiedProgressScratch.checkedTyAt_frame_inv_full hout.tyAt
    subst tauOut
    exact ⟨vOut, .piTy tauOut0 tauOut1,
      by simpa only [Basis.subst] using hout, .piTy⟩
  case termLlam =>
    intro Delta Gamma Psi bIn bOut e svIn svOut env htofIn ht hbv
      hTy hspaceIn hspaceOut L hfamily ihTy ihSpaceIn ihSpaceOut ihFamily
    intro DeltaT GammaT PsiT wt
    let bInT := Basis.subst x n bIn
    let bOutT := Basis.subst x n bOut
    have hbInS : Basis.BasisValid Gamma bIn := hbv.tprod_inv.1.dual_inv
    have hbInT : Basis.BasisValid GammaT bInT :=
      wt.source.typeCtx.basisValid hbInS
    have hbOutT : Basis.BasisValid GammaT bOutT :=
      wt.source.typeCtx.basisValid hbv.tprod_inv.2
    have hbvT : Basis.BasisValid GammaT (.tprod (.dual bInT) bOutT) := by
      simpa only [Basis.subst, bInT, bOutT] using
        wt.source.typeCtx.basisValid hbv
    obtain ⟨svInT, hspaceInT0, hrelIn⟩ := ihSpaceIn wt.typeCtx
    have hspaceInT : C.Space GammaT PsiT (Basis.sof bInT) svInT := by
      simpa only [Basis.sof_subst, bInT] using hspaceInT0
    obtain ⟨svOutT, hspaceOutT0, hrelOut⟩ := ihSpaceOut wt.typeCtx
    have hspaceOutT : C.Space GammaT PsiT (Basis.sof bOutT) svOutT := by
      simpa only [Basis.sof_subst, bOutT] using hspaceOutT0
    have hisPairS : Basis.IsSpaceBasis (.tprod (.dual bIn) bOut) :=
      hTy.isTyBasis
    have hisInS : Basis.IsSpaceBasis bIn := hisPairS.1
    have hisOutS : Basis.IsSpaceBasis bOut := hisPairS.2
    have hisInT : Basis.IsTyBasis bInT :=
      Basis.IsTyBasis.subst_checked hisInS.toIsTyBasis
    have hisOutT : Basis.IsTyBasis bOutT :=
      Basis.IsTyBasis.subst_checked hisOutS.toIsTyBasis
    have htofInT : Basis.tof bInT = .space (Basis.sof bInT) := by
      simpa only [bInT] using Basis.tof_space_subst_checked htofIn
    have htofOutT : Basis.tof bOutT = .space (Basis.sof bOutT) := by
      simpa only [bOutT] using
        Basis.tof_space_subst_checked (x := x) (n := n) hisOutS.tof_eq
    have hTyOutT : C.TyAt GammaT PsiT bOutT (.space svOutT) :=
      .space htofOutT hbOutT hspaceOutT
    have hTyInT : C.TyAt GammaT PsiT bInT (.space svInT) :=
      .space htofInT hbInT hspaceInT
    have hlcsvInT : ValSpace.lc svInT := by
      exact realize_lc_joint.1 hspaceInT.erase wt.lc
    have htT : Nonempty (HasType DeltaT GammaT
        (.llam (Basis.sof bInT) (Basis.sof bOutT) (Term.subst x n e))
        (Basis.tof (.tprod (.dual bInT) bOutT))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.subst, ← Basis.sof_subst,
        bInT, bOutT] using htT0
    have hTyT : C.TyAt GammaT PsiT (.tprod (.dual bInT) bOutT)
        (.space (.tprod svInT svOutT)) :=
      checkedTyAt_tprod_dual hbvT
        (by simpa only [bInT, bOutT] using
          Basis.IsTyBasis.subst_checked hTy.isTyBasis)
        hspaceInT hspaceOutT
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
      (L ∪ {x} ∪ Gamma0.keys ∪ DeltaT.keys ∪ Gamma.keys ∪ GammaT.keys ∪
        EvalCtx.avoidB Psi ∪ EvalCtx.avoidB PsiT ∪
        Basis.fv bInT ∪ ValSpace.fv svInT ∪
        Term.fv (Term.subst x n e) ∪ Basis.fv bOutT ∪
        ValSpace.fv svOutT)
    have hzL : z ∉ L := by intro hm; apply hz; simp [hm]
    have hzx : z ≠ x := by intro h; subst z; apply hz; simp
    have hz0k : z ∉ Gamma0.keys := by intro hm; apply hz; simp [hm]
    have hz0 : Gamma0.lookup z = none :=
      Finmap.lookup_eq_none.mpr (fun hm => hz0k (Finmap.mem_keys.mpr hm))
    have hzDeltaT : z ∉ DeltaT := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzGammaS : z ∉ Gamma := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzGammaT : z ∉ GammaT := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzPsiS : z ∉ EvalCtx.avoidB Psi := by
      intro hm; apply hz; simp [hm]
    have hzPsiT : z ∉ EvalCtx.avoidB PsiT := by
      intro hm; apply hz; simp [hm]
    have hzbInT : z ∉ Basis.fv bInT := by
      intro hm; apply hz; simp [hm]
    have hzsvInT : z ∉ ValSpace.fv svInT := by
      intro hm; apply hz; simp [hm]
    have hzeT : z ∉ Term.fv (Term.subst x n e) := by
      intro hm; apply hz; simp [hm]
    have hzbOutT : z ∉ Basis.fv bOutT := by
      intro hm; apply hz; simp [hm]
    have hzsvOutT : z ∉ ValSpace.fv svOutT := by
      intro hm; apply hz; simp [hm]
    have hbodyExists : forall i : Fin (ValSpace.dofUB svInT), exists vBodyT,
        C.Term (Finmap.insert z (Basis.sof bInT) DeltaT) GammaT
          (PsiT.extend z bInT (.var z (.space svInT)))
          (Term.openVar z (Term.subst x n e)) bOutT vBodyT
          (.space svOutT) := by
      intro i
      let j : Fin (ValSpace.dofUB svIn) := Fin.cast hrelIn.dofUB_eq i
      let wz := wt.extendLin z bIn (.delta j.val svIn)
        (.var z (.space svInT)) hbInS hzx hz0 hzGammaS hzGammaT
        hzDeltaT (EvalCtx.avoidB_spec hzPsiS).1
        (EvalCtx.avoidB_spec hzPsiT).1 (.var (.space hlcsvInT))
      obtain ⟨vBodyT, tauBodyT, hBodyT0, _⟩ := ihFamily z hzL j wz
      have hBodyT : C.Term
          (Finmap.insert z (Basis.sof bInT) DeltaT) GammaT
          (PsiT.extend z bInT (.var z (.space svInT)))
          (Term.openVar z (Term.subst x n e)) bOutT vBodyT tauBodyT := by
        simpa only [Basis.sof_subst,
          Graded.Term.subst_openVar_ne wt.source.data.lc hzx,
          bInT, bOutT] using hBodyT0
      have hTyOutExt : C.TyAt GammaT
          (PsiT.extend z bInT (.var z (.space svInT)))
          bOutT (.space svOutT) :=
        RawCertifiedPiBasisTransport.checkedTyAt_extend hTyOutT hzPsiT
      exact ⟨_, RawCertifiedProgressScratch.retag hBodyT hTyOutExt⟩
    choose bodyT hbodyT using hbodyExists
    obtain ⟨vOut, hout⟩ :=
      CheckedSubstBinder.termLlam_of_symbolic_family wt.wf
        hspaceInT.toS.svalid hzDeltaT hzGammaT hbodyT hzPsiT
        hzbInT hzsvInT hzeT hzbOutT hzsvOutT hlcsvInT htofInT
        htT hbvT hTyT hspaceInT hspaceOutT
    exact ⟨vOut, .space (.tprod svInT svOutT),
      by simpa only [Term.subst, Basis.subst, ← Basis.sof_subst,
        bInT, bOutT] using hout,
      .space (.tprod hrelIn hrelOut)⟩
  case termLlamReal =>
    intro Delta Gamma Psi bIn e svIn env htofIn ht hbv hTy
      hspaceIn L hfamily ihTy ihSpaceIn ihFamily
    intro DeltaT GammaT PsiT wt
    let bInT := Basis.subst x n bIn
    have hbInS : Basis.BasisValid Gamma bIn := hbv.dual_inv
    have hbInT : Basis.BasisValid GammaT bInT :=
      wt.source.typeCtx.basisValid hbInS
    have hbvT : Basis.BasisValid GammaT (.dual bInT) := by
      simpa only [Basis.subst, bInT] using
        wt.source.typeCtx.basisValid hbv
    obtain ⟨svInT, hspaceInT0, hrelIn⟩ := ihSpaceIn wt.typeCtx
    have hspaceInT : C.Space GammaT PsiT (Basis.sof bInT) svInT := by
      simpa only [Basis.sof_subst, bInT] using hspaceInT0
    have htofInT : Basis.tof bInT = .space (Basis.sof bInT) := by
      simpa only [bInT] using Basis.tof_space_subst_checked htofIn
    have hTyT : C.TyAt GammaT PsiT (.dual bInT) (.space svInT) :=
      .space rfl hbvT (.dual hbvT.sof_valid hspaceInT)
    have hTyOneT : C.TyAt GammaT PsiT .one (.space .real) :=
      .space rfl .one .real
    have hlcsvInT : ValSpace.lc svInT :=
      realize_lc_joint.1 hspaceInT.erase wt.lc
    have htT : Nonempty (HasType DeltaT GammaT
        (.llam (Basis.sof bInT) .real (Term.subst x n e))
        (Basis.tof (.dual bInT))) := by
      have htT0 := ht.map wt.source.hasType
      rw [← Basis.tof_subst] at htT0
      simpa only [Term.subst, Basis.subst, ← Basis.sof_subst,
        Space.subst, bInT] using htT0
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
      (L ∪ {x} ∪ Gamma0.keys ∪ DeltaT.keys ∪ Gamma.keys ∪
        GammaT.keys ∪ EvalCtx.avoidB Psi ∪ EvalCtx.avoidB PsiT ∪
        Basis.fv bInT ∪ ValSpace.fv svInT ∪
        Term.fv (Term.subst x n e))
    have hzL : z ∉ L := by intro hm; apply hz; simp [hm]
    have hzx : z ≠ x := by intro h; subst z; apply hz; simp
    have hz0k : z ∉ Gamma0.keys := by intro hm; apply hz; simp [hm]
    have hz0 : Gamma0.lookup z = none :=
      Finmap.lookup_eq_none.mpr (fun hm => hz0k (Finmap.mem_keys.mpr hm))
    have hzDeltaT : z ∉ DeltaT := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzGammaS : z ∉ Gamma := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzGammaT : z ∉ GammaT := by
      intro hm; apply hz; simp [Finmap.mem_keys.mpr hm]
    have hzPsiS : z ∉ EvalCtx.avoidB Psi := by
      intro hm; apply hz; simp [hm]
    have hzPsiT : z ∉ EvalCtx.avoidB PsiT := by
      intro hm; apply hz; simp [hm]
    have hzbInT : z ∉ Basis.fv bInT := by
      intro hm; apply hz; simp [hm]
    have hzsvInT : z ∉ ValSpace.fv svInT := by
      intro hm; apply hz; simp [hm]
    have hzeT : z ∉ Term.fv (Term.subst x n e) := by
      intro hm; apply hz; simp [hm]
    have hbodyExists : forall i : Fin (ValSpace.dofUB svInT), exists vBodyT,
        C.Term (Finmap.insert z (Basis.sof bInT) DeltaT) GammaT
          (PsiT.extend z bInT (.var z (.space svInT)))
          (Term.openVar z (Term.subst x n e)) .one vBodyT
          (.space .real) := by
      intro i
      let j : Fin (ValSpace.dofUB svIn) := Fin.cast hrelIn.dofUB_eq i
      let wz := wt.extendLin z bIn (.delta j.val svIn)
        (.var z (.space svInT)) hbInS hzx hz0 hzGammaS hzGammaT
        hzDeltaT (EvalCtx.avoidB_spec hzPsiS).1
        (EvalCtx.avoidB_spec hzPsiT).1 (.var (.space hlcsvInT))
      obtain ⟨vBodyT, tauBodyT, hBodyT0, _⟩ := ihFamily z hzL j wz
      have hBodyT : C.Term
          (Finmap.insert z (Basis.sof bInT) DeltaT) GammaT
          (PsiT.extend z bInT (.var z (.space svInT)))
          (Term.openVar z (Term.subst x n e)) .one vBodyT tauBodyT := by
        simpa only [Basis.sof_subst,
          Graded.Term.subst_openVar_ne wt.source.data.lc hzx,
          Basis.subst, bInT] using hBodyT0
      have hTyOneExt : C.TyAt GammaT
          (PsiT.extend z bInT (.var z (.space svInT)))
          .one (.space .real) :=
        RawCertifiedPiBasisTransport.checkedTyAt_extend hTyOneT hzPsiT
      exact ⟨_, RawCertifiedProgressScratch.retag hBodyT hTyOneExt⟩
    choose bodyT hbodyT using hbodyExists
    obtain ⟨Lout, hfamilyOut⟩ :=
      CheckedSubstBinder.termLlam_arbitrary_family_cofinite_of_placeholder
        wt.wf hspaceInT.toS.svalid hzDeltaT hzGammaT hbodyT hzPsiT
        hzbInT hzsvInT hzeT (by simp [Basis.fv])
        (by simp [ValTy.fv, ValSpace.fv]) hlcsvInT
    let envT : Fin (ValSpace.dofUB svInT) -> ValExpr := fun i =>
      ValExpr.subst z (.delta i.val svInT) (bodyT i)
    have hout := C.Term.llam_assemble_real (env := envT) htofInT
      htT hbvT hTyT hspaceInT Lout (fun y hy i => by
        simpa only [envT] using hfamilyOut y hy i)
    exact ⟨_, .space svInT,
      by simpa only [Term.subst, Basis.subst, ← Basis.sof_subst,
        Space.subst, bInT] using hout,
      .space hrelIn⟩
  obtain ⟨tauT, hT, _⟩ := result w
  exact ⟨tauT, hT⟩

/-- The existential cut theorem parameterized only by the public constructive
renaming interface. -/
theorem checkedTyAtAppCut_of_rename
    (laws : CheckedRenameLaws) :
    RawCertifiedProgressScratch.CheckedTyAtAppCut := by
  intro Gamma Psi y b0 b1 tauv0 tauv1 n1 arg
    hwf hlc hyGamma hyb0 hes harg hyb1 hcod
  have hargTy : HasType ∅ Gamma n1 (Basis.tof b0) := by
    simpa only [Basis.subst_fresh y n1 b0 hyb0] using harg.hasType.some
  let world : SomeCutCtx y b0 tauv0 n1 arg Gamma
      (Finmap.insert y (Basis.tof b0) Gamma)
      (Psi.extend y b0 (.var y tauv0)) Gamma Psi :=
    ⟨SourceCutCtx.root hwf hyGamma hargTy,
      LooseEvalCut.ofESubst hes, harg, hwf, hlc⟩
  obtain ⟨tauOut, hcut⟩ :=
    checkedTyAt_someSubstCore_of_rename laws hcod world
  rw [show Basis.subst y n1 (Basis.openVar y b1) =
      Basis.instantiate n1 b1 from
      (Basis.subst_intro y n1 b1 hyb1 0).symm] at hcut
  exact ⟨tauOut, hcut⟩

/-- Constructive inhabitant used by checked nonlinear-application progress. -/
theorem checkedTyAtAppCut :
    RawCertifiedProgressScratch.CheckedTyAtAppCut :=
  checkedTyAtAppCut_of_rename RenameProof.checkedRenameLaws

end RawCertifiedOperational
end GLang
