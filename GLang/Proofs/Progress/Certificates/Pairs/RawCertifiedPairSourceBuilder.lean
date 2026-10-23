import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairCertificate
import GLang.Proofs.Progress.ContextExtension
import GLang.Proofs.Progress.Certificates.RawCertifiedWorldProgressArms

/-!
# Constructing pair-local source trees from the variable seam

The pair certificate alternates between basis syntax and source syntax.  This
module isolates the source half of that alternation.  At a fixed pair depth
`n`, all source constructors are structural; only `var_lin` and `var_nlin`
cross back to a basis request.  `CheckedPairDepthLeafResolver` is exactly that
two-case seam.

The construction is deliberately indexed by a root nonlinear context.  It
threads `NLCtxIncl` and `CtxWF'` through the source derivation.  Promotion is
excluded hereditarily, while cofinite-binder hygiene supplies the freshness
needed to extend both invariants below nonlinear binders.  No evaluator or
basis-history recursion occurs here.
-/

namespace GLang
namespace RawCertifiedPairSourceBuilder

open RawCertifiedHereditaryStore
open RawCertifiedCobProgressMutualSpike
open RawCertifiedPairCertificate

/-- The only non-structural input to the fixed-depth source traversal.

Each callback receives the exact nonlinear context and its two independently
useful certificates: it extends the raw root, and it is well formed with the
linear context of the variable rule.  The conclusion is precisely the
proof-indexed selected-basis obligation used by `CheckedPairLocalSide*`.
-/
structure CheckedPairDepthLeafResolver
    (Psi0 : EvalCtx) (Gamma0 : NLCtx) (n : Nat) : Prop where
  lin : forall {Gamma : NLCtx} {x : VName} {s : Space},
    NLCtxIncl Gamma0 Gamma ->
    V2.CtxWF' (Finmap.singleton x s) Gamma ->
    forall (Psi : EvalCtx), CheckedStdFuture Psi0 Psi ->
      (exists b v, EvalCtx.lookup Psi (x, b) = some v /\
        Basis.tof b = .space s /\
        exists _hb : Basis.BasisValid Gamma b,
          CheckedPairBasisDepth Psi0 n Gamma b
            (Basis.std (Basis.tof b))) /\
      (forall b v, EvalCtx.lookup Psi (x, b) = some v ->
        Basis.tof b = .space s -> Basis.BasisValid Gamma b)
  nlin : forall {Gamma : NLCtx} {x : VName} {tau : Ty},
    (hGamma : Gamma.lookup x = some tau) ->
    NLCtxIncl Gamma0 Gamma ->
    V2.CtxWF' (∅ : LCtx) Gamma ->
    forall (Psi : EvalCtx), CheckedStdFuture Psi0 Psi ->
      (exists b v, EvalCtx.lookup Psi (x, b) = some v /\
        Basis.tof b = tau /\
        exists _hb : Basis.BasisValid Gamma b,
          CheckedPairBasisDepth Psi0 n Gamma b
            (Basis.std (Basis.tof b))) /\
      (forall b v, EvalCtx.lookup Psi (x, b) = some v ->
        Basis.tof b = tau -> Basis.BasisValid Gamma b)

private theorem not_mem_context_of_keys_subset
    {Gamma : NLCtx} {L : Finset Name} {y : Name}
    (hkeys : Gamma.keys ⊆ L) (hy : y ∉ L) : y ∉ Gamma := by
  intro hyGamma
  exact hy (hkeys (Finmap.mem_keys.mpr hyGamma))

private theorem not_mem_lctx_of_keys_subset
    {Delta : LCtx} {L : Finset Name} {y : Name}
    (hkeys : Delta.keys ⊆ L) (hy : y ∉ L) : y ∉ Delta := by
  intro hyDelta
  exact hy (hkeys (Finmap.mem_keys.mpr hyDelta))

private theorem leafDeep
    {Psi0 : EvalCtx} {Gamma0 : NLCtx} {n : Nat}
    (resolve : CheckedPairDepthLeafResolver Psi0 Gamma0 n)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau)
    (hinc : NLCtxIncl Gamma0 Gamma) (hwf : V2.CtxWF' Delta Gamma) :
    CheckedLocalTermSideBasisWith
      (CheckedPairSelectedAt Psi0 n) Psi0 h := by
  cases h with
  | var_lin =>
      intro Psi hfuture
      let resolved := resolve.lin hinc hwf Psi hfuture
      exact ⟨fun _hcov => resolved.1, resolved.2⟩
  | var_nlin hGamma =>
      intro Psi hfuture
      let resolved := resolve.nlin hGamma hinc hwf Psi hfuture
      exact ⟨fun _hcov => resolved.1, resolved.2⟩
  | zero | smul | add | inner | real_lit | app_linear | app_inner
  | app_nonlinear | pinv_tensor | pinv_dual | promote | dsumE | tprodE
  | llam_real | llam_tensor | embed | nllam => exact True.intro

private theorem leafShallow
    {Psi0 : EvalCtx} {Gamma0 : NLCtx} {n : Nat}
    (resolve : CheckedPairDepthLeafResolver Psi0 Gamma0 n)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau)
    (hinc : NLCtxIncl Gamma0 Gamma) (hwf : V2.CtxWF' Delta Gamma) :
    CheckedLocalTermSideBasis Psi0 h := by
  cases h with
  | var_lin =>
      intro b v hlookup htof
      exact (resolve.lin hinc hwf Psi0 (CheckedStdFuture.refl _)).2
        b v hlookup htof
  | var_nlin hGamma =>
      intro b v hlookup htof
      exact (resolve.nlin hGamma hinc hwf Psi0 (CheckedStdFuture.refl _)).2
        b v hlookup htof
  | zero | smul | add | inner | real_lit | app_linear | app_inner
  | app_nonlinear | pinv_tensor | pinv_dual | promote | dsumE | tprodE
  | llam_real | llam_tensor | embed | nllam => exact True.intro

private def tvalid_pi_domain
    {Gamma : NLCtx} {tau0 tau1 : Ty} {k0 k1 : Kind}
    (h : TValid Gamma (.piTy tau0 tau1) (.arrow k0 k1)) :
    TValid Gamma tau0 k0 := by
  cases h with
  | piTy _ ht0 _ => exact ht0

mutual

/-- Build the fixed-depth pair-local tree of a space derivation. -/
noncomputable def ofS
    {Psi0 : EvalCtx} {Gamma0 : NLCtx} {n : Nat} {A : Finset Name}
    (resolve : CheckedPairDepthLeafResolver Psi0 Gamma0 n)
    {Gamma : NLCtx} {s : Space} (h : SValid Gamma s)
    (hinc : NLCtxIncl Gamma0 Gamma)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hfree : Graded.SPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.SBinderHygiene A h) :
    CheckedPairLocalSideS Psi0 n h :=
  match h with
  | .empty =>
      CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, PUnit.unit⟩ ⟨True.intro, PUnit.unit⟩
  | .real =>
      CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, PUnit.unit⟩ ⟨True.intro, PUnit.unit⟩
  | .dual hs =>
      let side := ofS resolve hs hinc hwf hfree hhyg
      CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, side.deep⟩⟩
  | .dsum hs0 hs1 =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2 hhyg.2
      CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨True.intro, side1.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨True.intro, side1.deep⟩⟩⟩
  | .tprod hs0 hs1 =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2 hhyg.2
      CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨True.intro, side1.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨True.intro, side1.deep⟩⟩⟩
  | .ker hs0 hs1 ht =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2.1 hhyg.2.1
      let sideT := ofH resolve ht hinc hwf hfree.2.2 hhyg.2.2
      CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨⟨True.intro, side1.shallow.descendants⟩,
            ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨⟨True.intro, side1.deep⟩,
            ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩
  | .coker hs0 hs1 ht =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2.1 hhyg.2.1
      let sideT := ofH resolve ht hinc hwf hfree.2.2 hhyg.2.2
      CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨⟨True.intro, side1.shallow.descendants⟩,
            ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨⟨True.intro, side1.deep⟩,
            ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩
  | .img hs0 hs1 ht =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2.1 hhyg.2.1
      let sideT := ofH resolve ht hinc hwf hfree.2.2 hhyg.2.2
      CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨⟨True.intro, side1.shallow.descendants⟩,
            ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨⟨True.intro, side1.deep⟩,
            ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩
  | .coimg hs0 hs1 ht =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2.1 hhyg.2.1
      let sideT := ofH resolve ht hinc hwf hfree.2.2 hhyg.2.2
      CheckedLocalSideSWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨⟨True.intro, side1.shallow.descendants⟩,
            ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨⟨True.intro, side1.deep⟩,
            ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

/-- Build the fixed-depth pair-local tree of a type-validity derivation. -/
noncomputable def ofT
    {Psi0 : EvalCtx} {Gamma0 : NLCtx} {n : Nat} {A : Finset Name}
    (resolve : CheckedPairDepthLeafResolver Psi0 Gamma0 n)
    {Gamma : NLCtx} {tau : Ty} {k : Kind} (h : TValid Gamma tau k)
    (hinc : NLCtxIncl Gamma0 Gamma)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hfree : Graded.TPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.TBinderHygiene A h) :
    CheckedPairLocalSideT Psi0 n h :=
  match h with
  | .space hs =>
      let side := ofS resolve hs hinc hwf hfree hhyg
      CheckedLocalSideTWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, side.deep⟩⟩
  | @TValid.piTy Gamma tau0 tau1 k0 k1 L ht0 hbody =>
      let side0 := ofT resolve ht0 hinc hwf hfree.1 hhyg.2.2.1
      let sideBody := fun y (hy : y ∉ L) =>
        let hyGamma : y ∉ Gamma :=
          not_mem_context_of_keys_subset hhyg.2.1 hy
        let hincY : NLCtxIncl Gamma0 (Finmap.insert y tau0 Gamma) :=
          hinc.insert_right hyGamma tau0
        let hwfY : V2.CtxWF' (∅ : LCtx)
            (Finmap.insert y tau0 Gamma) := by
          simpa only [Basis.tof_std] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
              (b := Basis.std tau0) hwf Finmap.notMem_empty hyGamma
              (Basis.std_valid tau0 ht0)
        ofT resolve (hbody y hy) hincY hwfY
          (hfree.2 y hy) (hhyg.2.2.2 y hy)
      CheckedLocalSideTWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          fun y hy => ⟨True.intro, (sideBody y hy).shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          fun y hy => ⟨True.intro, (sideBody y hy).deep⟩⟩⟩

/-- Build the fixed-depth pair-local tree of a subtyping derivation. -/
noncomputable def ofSub
    {Psi0 : EvalCtx} {Gamma0 : NLCtx} {n : Nat} {A : Finset Name}
    (resolve : CheckedPairDepthLeafResolver Psi0 Gamma0 n)
    {Gamma : NLCtx} {s0 s1 : Space} (h : SubType Gamma s0 s1)
    (hinc : NLCtxIncl Gamma0 Gamma)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hfree : Graded.SubPromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.SubBinderHygiene A h) :
    CheckedPairLocalSideSub Psi0 n h :=
  match h with
  | .sub_ker hs0 hs1 ht =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2.1 hhyg.2.1
      let sideT := ofH resolve ht hinc hwf hfree.2.2 hhyg.2.2
      CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨⟨True.intro, side1.shallow.descendants⟩,
            ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨⟨True.intro, side1.deep⟩,
            ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩
  | .sub_coker hs0 hs1 ht =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2.1 hhyg.2.1
      let sideT := ofH resolve ht hinc hwf hfree.2.2 hhyg.2.2
      CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨⟨True.intro, side1.shallow.descendants⟩,
            ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨⟨True.intro, side1.deep⟩,
            ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩
  | .sub_img hs0 hs1 ht =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2.1 hhyg.2.1
      let sideT := ofH resolve ht hinc hwf hfree.2.2 hhyg.2.2
      CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨⟨True.intro, side1.shallow.descendants⟩,
            ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨⟨True.intro, side1.deep⟩,
            ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩
  | .sub_coimg hs0 hs1 ht =>
      let side0 := ofS resolve hs0 hinc hwf hfree.1 hhyg.1
      let side1 := ofS resolve hs1 hinc hwf hfree.2.1 hhyg.2.1
      let sideT := ofH resolve ht hinc hwf hfree.2.2 hhyg.2.2
      CheckedLocalSideSubWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, side0.shallow.descendants⟩,
          ⟨⟨True.intro, side1.shallow.descendants⟩,
            ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, side0.deep⟩,
          ⟨⟨True.intro, side1.deep⟩,
            ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩

/-- Build the fixed-depth pair-local tree of a promotion-free, hygienic term
typing derivation. -/
noncomputable def ofH
    {Psi0 : EvalCtx} {Gamma0 : NLCtx} {n : Nat} {A : Finset Name}
    (resolve : CheckedPairDepthLeafResolver Psi0 Gamma0 n)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau)
    (hinc : NLCtxIncl Gamma0 Gamma)
    (hwf : V2.CtxWF' Delta Gamma)
    (hfree : Graded.PromotionFree h)
    (hhyg : Adequacy.CofiniteFreshen.BinderHygiene A h) :
    CheckedPairLocalSideBases Psi0 n h :=
  match h with
  | .zero hs => by
      let sideS := ofS resolve hs hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf) hfree hhyg
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, sideS.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, sideS.deep⟩⟩
  | .smul hs hdisj h0 h1 => by
      let sideS := ofS resolve hs hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf) hfree.1 hhyg.1
      let side0 := ofH resolve h0 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_left hwf)
        hfree.2.1 hhyg.2.1
      let side1 := ofH resolve h1 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf)
        hfree.2.2 hhyg.2.2
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS.shallow.descendants⟩,
          ⟨⟨side0.shallow.here, side0.shallow.descendants⟩,
            ⟨side1.shallow.here, side1.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS.deep⟩,
          ⟨⟨side0.deepHere, side0.deepDescendants⟩,
            ⟨side1.deepHere, side1.deepDescendants⟩⟩⟩⟩
  | .add hs h0 h1 => by
      let sideS := ofS resolve hs hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf) hfree.1 hhyg.1
      let side0 := ofH resolve h0 hinc hwf hfree.2.1 hhyg.2.1
      let side1 := ofH resolve h1 hinc hwf hfree.2.2 hhyg.2.2
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS.shallow.descendants⟩,
          ⟨⟨side0.shallow.here, side0.shallow.descendants⟩,
            ⟨side1.shallow.here, side1.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS.deep⟩,
          ⟨⟨side0.deepHere, side0.deepDescendants⟩,
            ⟨side1.deepHere, side1.deepDescendants⟩⟩⟩⟩
  | .inner hs => by
      let sideS := ofS resolve hs hinc hwf hfree hhyg
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, sideS.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, sideS.deep⟩⟩
  | .real_lit _ => by
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, PUnit.unit⟩ ⟨True.intro, PUnit.unit⟩
  | .app_linear hs0 hs1 hdisj h0 h1 => by
      let hwf0 := RawCertifiedWorldProgressArms.ctxWF_union_left hwf
      let hwf1 := RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf
      let sideS0 := ofS resolve hs0 hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf) hfree.1 hhyg.1
      let sideS1 := ofS resolve hs1 hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf) hfree.2.1 hhyg.2.1
      let side0 := ofH resolve h0 hinc hwf0 hfree.2.2.1 hhyg.2.2.1
      let side1 := ofH resolve h1 hinc hwf1 hfree.2.2.2 hhyg.2.2.2
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS0.shallow.descendants⟩,
          ⟨⟨True.intro, sideS1.shallow.descendants⟩,
            ⟨⟨side0.shallow.here, side0.shallow.descendants⟩,
              ⟨side1.shallow.here, side1.shallow.descendants⟩⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS0.deep⟩,
          ⟨⟨True.intro, sideS1.deep⟩,
            ⟨⟨side0.deepHere, side0.deepDescendants⟩,
              ⟨side1.deepHere, side1.deepDescendants⟩⟩⟩⟩⟩
  | .app_inner hs hdisj h0 h1 => by
      let sideS := ofS resolve hs hinc
        (RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf) hfree.1 hhyg.1
      let side0 := ofH resolve h0 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_left hwf)
        hfree.2.1 hhyg.2.1
      let side1 := ofH resolve h1 hinc
        (RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf)
        hfree.2.2 hhyg.2.2
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS.shallow.descendants⟩,
          ⟨⟨side0.shallow.here, side0.shallow.descendants⟩,
            ⟨side1.shallow.here, side1.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS.deep⟩,
          ⟨⟨side0.deepHere, side0.deepDescendants⟩,
            ⟨side1.deepHere, side1.deepDescendants⟩⟩⟩⟩
  | .app_nonlinear h0 h1 => by
      let side0 := ofH resolve h0 hinc hwf hfree.1 hhyg.1
      let side1 := ofH resolve h1 hinc hwf hfree.2 hhyg.2
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨side0.shallow.here, side0.shallow.descendants⟩,
          ⟨side1.shallow.here, side1.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨side0.deepHere, side0.deepDescendants⟩,
          ⟨side1.deepHere, side1.deepDescendants⟩⟩⟩
  | .var_lin => by
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨leafShallow resolve .var_lin hinc hwf, PUnit.unit⟩
        ⟨leafDeep resolve .var_lin hinc hwf, PUnit.unit⟩
  | .var_nlin hGamma => by
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨leafShallow resolve (.var_nlin hGamma) hinc hwf, PUnit.unit⟩
        ⟨leafDeep resolve (.var_nlin hGamma) hinc hwf, PUnit.unit⟩
  | .pinv_tensor hs0 hs1 ht => by
      let hwf0 := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
      let sideS0 := ofS resolve hs0 hinc hwf0 hfree.1 hhyg.1
      let sideS1 := ofS resolve hs1 hinc hwf0 hfree.2.1 hhyg.2.1
      let sideT := ofH resolve ht hinc hwf hfree.2.2 hhyg.2.2
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS0.shallow.descendants⟩,
          ⟨⟨True.intro, sideS1.shallow.descendants⟩,
            ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS0.deep⟩,
          ⟨⟨True.intro, sideS1.deep⟩,
            ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩⟩
  | .pinv_dual hs ht => by
      let sideS := ofS resolve hs hinc hwf hfree.1 hhyg.1
      let sideT := ofH resolve ht hinc hwf hfree.2 hhyg.2
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS.shallow.descendants⟩,
          ⟨sideT.shallow.here, sideT.shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS.deep⟩,
          ⟨sideT.deepHere, sideT.deepDescendants⟩⟩⟩
  | .promote _ _ _ _ _ => False.elim hfree
  | .dsumE hs0 hs1 h0 h1 => by
      let hwf0 := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
      let sideS0 := ofS resolve hs0 hinc hwf0 hfree.1 hhyg.1
      let sideS1 := ofS resolve hs1 hinc hwf0 hfree.2.1 hhyg.2.1
      let side0 := ofH resolve h0 hinc hwf hfree.2.2.1 hhyg.2.2.1
      let side1 := ofH resolve h1 hinc hwf hfree.2.2.2 hhyg.2.2.2
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS0.shallow.descendants⟩,
          ⟨⟨True.intro, sideS1.shallow.descendants⟩,
            ⟨⟨side0.shallow.here, side0.shallow.descendants⟩,
              ⟨side1.shallow.here, side1.shallow.descendants⟩⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS0.deep⟩,
          ⟨⟨True.intro, sideS1.deep⟩,
            ⟨⟨side0.deepHere, side0.deepDescendants⟩,
              ⟨side1.deepHere, side1.deepDescendants⟩⟩⟩⟩⟩
  | .tprodE hs0 hs1 hdisj h0 h1 => by
      let hwf0 := RawCertifiedWorldProgressArms.ctxWF_union_left hwf
      let hwf1 := RawCertifiedWorldProgressArms.ctxWF_union_right hdisj hwf
      let hwfEmpty := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
      let sideS0 := ofS resolve hs0 hinc hwfEmpty hfree.1 hhyg.1
      let sideS1 := ofS resolve hs1 hinc hwfEmpty hfree.2.1 hhyg.2.1
      let side0 := ofH resolve h0 hinc hwf0 hfree.2.2.1 hhyg.2.2.1
      let side1 := ofH resolve h1 hinc hwf1 hfree.2.2.2 hhyg.2.2.2
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS0.shallow.descendants⟩,
          ⟨⟨True.intro, sideS1.shallow.descendants⟩,
            ⟨⟨side0.shallow.here, side0.shallow.descendants⟩,
              ⟨side1.shallow.here, side1.shallow.descendants⟩⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS0.deep⟩,
          ⟨⟨True.intro, sideS1.deep⟩,
            ⟨⟨side0.deepHere, side0.deepDescendants⟩,
              ⟨side1.deepHere, side1.deepDescendants⟩⟩⟩⟩⟩
  | @HasType.llam_real Delta Gamma s e L hs hbody => by
      let hwfEmpty := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
      let sideS := ofS resolve hs hinc hwfEmpty hfree.1 hhyg.2.2.2.1
      let sideBody := fun y (hy : y ∉ L) =>
        let hyDelta := not_mem_lctx_of_keys_subset hhyg.2.1 hy
        let hyGamma := not_mem_context_of_keys_subset hhyg.2.2.1 hy
        let hwfY : V2.CtxWF' (Finmap.insert y s Delta) Gamma := by
          simpa only [Basis.sof_stdSpace] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
              (b := Basis.stdSpace s) hwf hyDelta hyGamma
              (Basis.stdSpace_valid s hs)
        ofH resolve (hbody y hy) hinc hwfY
          (hfree.2 y hy) (hhyg.2.2.2.2 y hy)
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS.shallow.descendants⟩,
          fun y hy => ⟨(sideBody y hy).shallow.here,
            (sideBody y hy).shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS.deep⟩,
          fun y hy => ⟨(sideBody y hy).deepHere,
            (sideBody y hy).deepDescendants⟩⟩⟩
  | @HasType.llam_tensor Delta Gamma s0 s e L hne hs0 hs hbody => by
      let hwfEmpty := RawCertifiedWorldBinderProgress.ctxWF_dropLin hwf
      let sideS0 := ofS resolve hs0 hinc hwfEmpty hfree.1 hhyg.2.2.2.1
      let sideS := ofS resolve hs hinc hwfEmpty hfree.2.1 hhyg.2.2.2.2.1
      let sideBody := fun y (hy : y ∉ L) =>
        let hyDelta := not_mem_lctx_of_keys_subset hhyg.2.1 hy
        let hyGamma := not_mem_context_of_keys_subset hhyg.2.2.1 hy
        let hwfY : V2.CtxWF' (Finmap.insert y s0 Delta) Gamma := by
          simpa only [Basis.sof_stdSpace] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
              (b := Basis.stdSpace s0) hwf hyDelta hyGamma
              (Basis.stdSpace_valid s0 hs0)
        ofH resolve (hbody y hy) hinc hwfY
          (hfree.2.2 y hy) (hhyg.2.2.2.2.2 y hy)
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideS0.shallow.descendants⟩,
          ⟨⟨True.intro, sideS.shallow.descendants⟩,
            fun y hy => ⟨(sideBody y hy).shallow.here,
              (sideBody y hy).shallow.descendants⟩⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideS0.deep⟩,
          ⟨⟨True.intro, sideS.deep⟩,
            fun y hy => ⟨(sideBody y hy).deepHere,
              (sideBody y hy).deepDescendants⟩⟩⟩⟩
  | .embed hsub => by
      let side := ofSub resolve hsub hinc hwf hfree hhyg
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨True.intro, side.shallow.descendants⟩⟩
        ⟨True.intro, ⟨True.intro, side.deep⟩⟩
  | @HasType.nllam Gamma tau0 tau1 k0 k1 e L ht hbody => by
      let sideT := ofT resolve ht hinc hwf hfree.1 hhyg.2.2.1
      let sideBody := fun y (hy : y ∉ L) => by
        have hyGamma : y ∉ Gamma :=
          not_mem_context_of_keys_subset hhyg.2.1 hy
        have hincY : NLCtxIncl Gamma0 (Finmap.insert y tau0 Gamma) :=
          hinc.insert_right hyGamma tau0
        let ht0 := tvalid_pi_domain ht
        have hwfY : V2.CtxWF' (∅ : LCtx)
            (Finmap.insert y tau0 Gamma) := by
          simpa only [Basis.tof_std] using
            RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
              (b := Basis.std tau0) hwf Finmap.notMem_empty hyGamma
              (Basis.std_valid tau0 ht0)
        exact ofH resolve (hbody y hy) hincY hwfY
          (hfree.2 y hy) (hhyg.2.2.2 y hy)
      exact CheckedLocalSideBasesWith.ofBelowPair
        ⟨True.intro, ⟨⟨True.intro, sideT.shallow.descendants⟩,
          fun y hy => ⟨(sideBody y hy).shallow.here,
            (sideBody y hy).shallow.descendants⟩⟩⟩
        ⟨True.intro, ⟨⟨True.intro, sideT.deep⟩,
          fun y hy => ⟨(sideBody y hy).deepHere,
            (sideBody y hy).deepDescendants⟩⟩⟩

end

end RawCertifiedPairSourceBuilder
end GLang
