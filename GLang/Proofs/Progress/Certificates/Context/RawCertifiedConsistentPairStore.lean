import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairReadiness
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairFutureRebase
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairLookupResolver
import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairSourceBuilder

/-! Finite selected-pair stores from a raw-consistent evaluator. Well-founded induction on entry creation constructs certificates from the preceding entries used by each stored basis. -/

namespace GLang
namespace RawCertifiedConsistentPairStore

open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedPairCertificate
open RawCertifiedPairReadiness
open RawCertifiedPairDepthMonotonicity

/-- Evaluator growth by keys at genuinely fresh names, with no restriction
on the added bases.  This is the world relation required by the dedicated
pair-frame clause: its endpoint domain can be nonstandard.  Name uniqueness
rules out a second basis under one locally bound name. -/
structure CheckedFreshFuture (Psi0 Psi : EvalCtx) : Prop where
  subctx : Psi0.Subctx Psi
  extra_name_fresh : forall x b, (x, b) ∈ Psi -> (x, b) ∉ Psi0 ->
    x ∉ Psi0.names
  extra_name_unique : forall x b0 b1,
    (x, b0) ∈ Psi -> (x, b0) ∉ Psi0 -> (x, b1) ∈ Psi -> b0 = b1

theorem CheckedFreshFuture.refl (Psi : EvalCtx) :
    CheckedFreshFuture Psi Psi where
  subctx := EvalCtx.Subctx.refl Psi
  extra_name_fresh := by
    intro x b hmem hnot
    exact False.elim (hnot hmem)
  extra_name_unique := by
    intro x b0 b1 hmem hnot _
    exact False.elim (hnot hmem)

/-- Standard-only futures are a special case of fresh arbitrary futures. -/
theorem CheckedStdFuture.toFresh
    {Psi0 Psi : EvalCtx} (h : CheckedStdFuture Psi0 Psi) :
    CheckedFreshFuture Psi0 Psi where
  subctx := h.subctx
  extra_name_fresh := h.extra_name_fresh
  extra_name_unique := h.extra_name_unique

/-- Fresh arbitrary futures compose. -/
theorem CheckedFreshFuture.trans
    {Psi0 Psi1 Psi2 : EvalCtx}
    (h01 : CheckedFreshFuture Psi0 Psi1)
    (h12 : CheckedFreshFuture Psi1 Psi2) :
    CheckedFreshFuture Psi0 Psi2 where
  subctx := h01.subctx.trans h12.subctx
  extra_name_fresh := by
    intro x b hmem hnot0
    by_cases hmem1 : (x, b) ∈ Psi1
    · exact h01.extra_name_fresh x b hmem1 hnot0
    · have hnotNames1 := h12.extra_name_fresh x b hmem hmem1
      exact fun hx0 => hnotNames1
        (EvalCtx.Subctx.names_subset h01.subctx hx0)
  extra_name_unique := by
    intro x b0 b1 hmem0 hnot0 hmem1
    by_cases hmem01 : (x, b0) ∈ Psi1
    · by_cases hmem11 : (x, b1) ∈ Psi1
      · exact h01.extra_name_unique x b0 b1 hmem01 hnot0 hmem11
      · have hx1 : x ∈ Psi1.names := by
          obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp hmem01
          exact EvalCtx.mem_names_of_lookup hlookup0
        exact False.elim (h12.extra_name_fresh x b1 hmem1 hmem11 hx1)
    · exact h12.extra_name_unique x b0 b1 hmem0 hmem01 hmem1

/-- One arbitrary key at a fresh name preserves `CheckedFreshFuture`. -/
theorem CheckedFreshFuture.extend
    {Psi0 Psi : EvalCtx} (h : CheckedFreshFuture Psi0 Psi)
    {x : VName} (hx : x ∉ Psi.names) (b : Basis) (v : ValExpr) :
    CheckedFreshFuture Psi0 (Psi.extend x b v) where
  subctx := h.subctx.trans
    (EvalCtx.Subctx.extend_right_of_name_fresh hx b v)
  extra_name_fresh := by
    intro y bY hmem hnot
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hold
    · have hyx : y = x := (Prod.mk.inj heq).1
      subst y
      intro hx0
      exact hx (EvalCtx.Subctx.names_subset h.subctx hx0)
    · exact h.extra_name_fresh y bY hold hnot
  extra_name_unique := by
    intro y b0 b1 hmem0 hnot0 hmem1
    simp only [EvalCtx.extend] at hmem0 hmem1
    rcases Finmap.mem_insert.mp hmem0 with heq0 | hold0
    · have hyx : y = x := (Prod.mk.inj heq0).1
      have hb0 : b0 = b := (Prod.mk.inj heq0).2
      subst y
      subst b0
      rcases Finmap.mem_insert.mp hmem1 with heq1 | hold1
      · exact (Prod.mk.inj heq1).2.symm
      · exact False.elim (hx (Finset.mem_image.mpr
          ⟨(x, b1), Finmap.mem_keys.mpr hold1, rfl⟩))
    · have hyx : y ≠ x := by
        intro hyx
        subst y
        exact hx (Finset.mem_image.mpr
          ⟨(x, b0), Finmap.mem_keys.mpr hold0, rfl⟩)
      rcases Finmap.mem_insert.mp hmem1 with heq1 | hold1
      · exact False.elim (hyx (Prod.mk.inj heq1).1)
      · exact h.extra_name_unique y b0 b1 hold0 hnot0 hold1

/-- An extension cannot add a second key below a name already owned by its
root.  This is the root branch of the variable-lookup peel used by an
FV-aware source builder. -/
theorem CheckedFreshFuture.mem_root_of_root_name
    {Psi0 Psi : EvalCtx} (h : CheckedFreshFuture Psi0 Psi)
    {x : VName} {b : Basis}
    (hx : x ∈ Psi0.names) (hmem : (x, b) ∈ Psi) :
    (x, b) ∈ Psi0 := by
  by_contra hnot
  exact h.extra_name_fresh x b hmem hnot hx

/-- Lookup-value form of `mem_root_of_root_name`. -/
theorem CheckedFreshFuture.lookup_root_of_root_name
    {Psi0 Psi : EvalCtx} (h : CheckedFreshFuture Psi0 Psi)
    {x : VName} {b : Basis} {v : ValExpr}
    (hx : x ∈ Psi0.names)
    (hlookup : EvalCtx.lookup Psi (x, b) = some v) :
    EvalCtx.lookup Psi0 (x, b) = some v := by
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp
    (h.mem_root_of_root_name hx hmem)
  have hlookup1 := h.subctx (x, b) v0 hlookup0
  have hv : v0 = v := Option.some.inj (hlookup1.symm.trans hlookup)
  simpa only [hv] using hlookup0

/-- The four orientations constructed together by the structural basis
induction.  Dependent frames use all four: endpoint self pairs, forward
selected-to-standard transport, reverse standard-to-selected transport for
the contravariant domain, and standard self transport. -/
structure CheckedPairDepthQuad (Psi : EvalCtx) (depth : Nat)
    (Gamma : NLCtx) (b : Basis) : Prop where
  self : CheckedPairBasisDepth Psi depth Gamma b b
  toStd : CheckedPairBasisDepth Psi depth Gamma b
    (Basis.std (Basis.tof b))
  fromStd : CheckedPairBasisDepth Psi depth Gamma
    (Basis.std (Basis.tof b)) b
  stdSelf : CheckedPairBasisDepth Psi depth Gamma
    (Basis.std (Basis.tof b)) (Basis.std (Basis.tof b))

/-- Pointwise finite quad with one common depth for its four orientations. -/
def CheckedPairDepthQuadFinite (Psi : EvalCtx) (Gamma : NLCtx)
    (b : Basis) : Prop :=
  exists n, CheckedPairDepthQuad Psi n Gamma b

/-- A stored-basis quad can be rebuilt after arbitrary fresh-name evaluator
growth and nonlinear-context growth.  A pair-frame callback may install a
nonstandard endpoint domain, so standard-only future transport is not enough.
The current context is required to be genuinely well formed when the syntax
layer is rebuilt.  The depth existential intentionally precedes the world
quantifiers: a frame fixes its numeric depth before its callbacks choose
their future worlds. -/
def CheckedPairFreshDepthQuadFinite
    (Psi : EvalCtx) (Gamma : NLCtx) (b : Basis) : Prop :=
  exists depth, forall {Psi' : EvalCtx} {Gamma' : NLCtx},
    CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
    V2.CtxWF' (∅ : LCtx) Gamma' ->
      CheckedPairDepthQuad Psi' depth Gamma' b

/-- Use fresh-world evidence at its original root and context. -/
theorem CheckedPairFreshDepthQuadFinite.toRoot
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis}
    (h : CheckedPairFreshDepthQuadFinite Psi Gamma b)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma) :
    CheckedPairDepthQuadFinite Psi Gamma b := by
  obtain ⟨depth, h⟩ := h
  exact ⟨depth,
    h (CheckedFreshFuture.refl Psi) (NLCtxIncl.refl Gamma) hwf⟩

/-- Rebase the package itself along fresh evaluator/context growth. -/
theorem CheckedPairFreshDepthQuadFinite.rebase
    {Psi Psi' : EvalCtx} {Gamma Gamma' : NLCtx} {b : Basis}
    (h : CheckedPairFreshDepthQuadFinite Psi Gamma b)
    (hfuture : CheckedFreshFuture Psi Psi')
    (hGamma : NLCtxIncl Gamma Gamma') :
    CheckedPairFreshDepthQuadFinite Psi' Gamma' b := by
  obtain ⟨depth, h⟩ := h
  refine ⟨depth, ?_⟩
  intro Psi'' Gamma'' hfuture' hGamma' hwf
  exact h (hfuture.trans hfuture') (hGamma.trans hGamma') hwf

/-- Retain the selected-to-standard component of a finite exact quad. -/
theorem CheckedPairDepthQuadFinite.toStd
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis}
    (h : CheckedPairDepthQuadFinite Psi Gamma b) :
    CheckedPairBasisFinite Psi Gamma b (Basis.std (Basis.tof b)) := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.toStd⟩

def CheckedPairDepthQuadSelectedStore
    (Psi : EvalCtx) (Gamma : NLCtx) : Prop :=
  forall {x : VName} {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi (x, b) = some v ->
      CheckedPairDepthQuadFinite Psi Gamma b

/-- The induction-facing store can rebuild an exact quad after arbitrary
fresh nonstandard evaluator extensions. -/
def CheckedPairFreshDepthQuadSelectedStore
    (Psi : EvalCtx) (Gamma : NLCtx) : Prop :=
  forall {x : VName} {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi (x, b) = some v ->
      CheckedPairFreshDepthQuadFinite Psi Gamma b

/-- Its weaker, public pointwise-finite projection. -/
def CheckedPairFiniteSelectedStore (Psi : EvalCtx) (Gamma : NLCtx) : Prop :=
  forall {x : VName} {b : Basis} {v : ValExpr},
    EvalCtx.lookup Psi (x, b) = some v ->
      CheckedPairBasisFinite Psi Gamma b (Basis.std (Basis.tof b))

/-- Project the construction-facing exact quad store to the public finite
selected-to-standard store. -/
theorem CheckedPairDepthQuadSelectedStore.toFinite
    {Psi : EvalCtx} {Gamma : NLCtx}
    (h : CheckedPairDepthQuadSelectedStore Psi Gamma) :
    CheckedPairFiniteSelectedStore Psi Gamma := by
  intro x b v hlookup
  exact CheckedPairDepthQuadFinite.toStd (h hlookup)

/-- Forget fresh-world stability at the evaluator root. -/
theorem CheckedPairFreshDepthQuadSelectedStore.toQuad
    {Psi : EvalCtx} {Gamma : NLCtx}
    (h : CheckedPairFreshDepthQuadSelectedStore Psi Gamma)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma) :
    CheckedPairDepthQuadSelectedStore Psi Gamma := by
  intro x b v hlookup
  exact CheckedPairFreshDepthQuadFinite.toRoot (h hlookup) hwf

/-- The exact recursive input for constructing the pair belonging to one
stored basis.  Only evaluator entries whose owner occurs free in the outer
basis are exposed.  Each result has one depth uniform over fresh callback
worlds, since the later syntax construction must choose a common depth and
use it under binders.  Root validity is returned separately: positive-depth
pair evidence intentionally does not contain it, while a variable leaf needs
to weaken that validity to its current binder-extended source context.

Each free source name chooses one concrete predecessor representation.  Other
representations of that name need only be valid; they are not retroactively
made dependencies of this certificate. -/
structure CheckedPairDepthBasisLeaves
    (Psi : EvalCtx) (Gamma : NLCtx) (outer : Basis) : Prop where
  resolve : forall {y : VName}, y ∈ Basis.fv outer ->
    exists b : Basis, exists v : ValExpr,
      EvalCtx.lookup Psi (y, b) = some v /\
        exists _hb : Basis.BasisValid Gamma b,
          CheckedPairFreshDepthQuadFinite Psi Gamma b

/-- Fixed-depth form of the FV-only dependency service.  One depth works for
every selected dependency and for every fresh callback world. -/
structure CheckedPairDepthBasisLeavesAt
    (Psi : EvalCtx) (Gamma : NLCtx) (outer : Basis) (depth : Nat) : Prop where
  resolve : forall {y : VName}, y ∈ Basis.fv outer ->
    exists b : Basis, exists v : ValExpr,
      EvalCtx.lookup Psi (y, b) = some v /\
        exists _hb : Basis.BasisValid Gamma b,
          forall {Psi' : EvalCtx} {Gamma' : NLCtx},
            CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
            V2.CtxWF' (∅ : LCtx) Gamma' ->
              CheckedPairDepthQuad Psi' depth Gamma' b

theorem CheckedPairDepthQuad.monoDepth
    {Psi : EvalCtx} {Gamma : NLCtx} {b : Basis} {n m : Nat}
    (hnm : n ≤ m) (q : CheckedPairDepthQuad Psi n Gamma b) :
    CheckedPairDepthQuad Psi m Gamma b where
  self := pairDepth_mono hnm q.self
  toStd := pairDepth_mono hnm q.toStd
  fromStd := pairDepth_mono hnm q.fromStd
  stdSelf := pairDepth_mono hnm q.stdSelf

private noncomputable def CheckedPairDepthBasisLeaves.depthAt
    {Psi : EvalCtx} {Gamma : NLCtx} {outer : Basis}
    (leaves : CheckedPairDepthBasisLeaves Psi Gamma outer) :
    VName -> Nat
  | y =>
      if hy : y ∈ Basis.fv outer then
        let resolved := leaves.resolve hy
        let resolvedB := Classical.choose_spec resolved
        let resolvedV := Classical.choose_spec resolvedB
        let package := Classical.choose_spec resolvedV.2
        Classical.choose package
      else 0

private theorem CheckedPairDepthBasisLeaves.depthAt_spec
    {Psi : EvalCtx} {Gamma : NLCtx} {outer : Basis}
    (leaves : CheckedPairDepthBasisLeaves Psi Gamma outer)
    {y : VName} (hy : y ∈ Basis.fv outer) :
    exists b : Basis, exists v : ValExpr,
      EvalCtx.lookup Psi (y, b) = some v /\
      exists _hb : Basis.BasisValid Gamma b,
      forall {Psi' : EvalCtx} {Gamma' : NLCtx},
        CheckedFreshFuture Psi Psi' -> NLCtxIncl Gamma Gamma' ->
        V2.CtxWF' (∅ : LCtx) Gamma' ->
          CheckedPairDepthQuad Psi' (leaves.depthAt y) Gamma' b := by
  simp only [CheckedPairDepthBasisLeaves.depthAt, dif_pos hy]
  let resolved := leaves.resolve hy
  let b := Classical.choose resolved
  let resolvedB := Classical.choose_spec resolved
  let v := Classical.choose resolvedB
  let resolvedV := Classical.choose_spec resolvedB
  let package := Classical.choose_spec resolvedV.2
  refine ⟨b, v, resolvedV.1, Classical.choose resolvedV.2, ?_⟩
  intro Psi' Gamma' hfuture hGamma hwf
  exact (Classical.choose_spec package)
    hfuture hGamma hwf

/-- Finiteness of the evaluator turns pointwise finite FV dependencies into
the one fixed depth required by a source/basis syntax traversal.  Crucially,
the supremum is taken after each dependency has already supplied one depth
uniform over callback worlds. -/
theorem CheckedPairDepthBasisLeaves.exists_atDepth
    {Psi : EvalCtx} {Gamma : NLCtx} {outer : Basis}
    (leaves : CheckedPairDepthBasisLeaves Psi Gamma outer) :
    exists depth, CheckedPairDepthBasisLeavesAt
      Psi Gamma outer depth := by
  classical
  let depth := (Basis.fv outer).sup leaves.depthAt
  refine ⟨depth, ⟨?_⟩⟩
  intro y hy
  obtain ⟨b, v, hlookup, hb, pair⟩ := leaves.depthAt_spec hy
  refine ⟨b, v, hlookup, hb, ?_⟩
  intro Psi' Gamma' hfuture hGamma hwf
  have hle : leaves.depthAt y ≤ depth := Finset.le_sup hy
  exact CheckedPairDepthQuad.monoDepth hle
    (pair hfuture hGamma hwf)

/-- The single missing syntax layer, stated without any global store
assumption. -/
def CheckedPairDepthLayerBuilder (Psi : EvalCtx) (Gamma : NLCtx) : Prop :=
  forall {b : Basis},
    Basis.fv b ⊆ Psi.keyNames ->
    Basis.BasisValid Gamma b ->
    V2.CtxWF' (∅ : LCtx) Gamma ->
    CheckedPairDepthBasisLeaves Psi Gamma b ->
      CheckedPairFreshDepthQuadFinite Psi Gamma b

end RawCertifiedConsistentPairStore

/-- Raw consistency supplies the full proof-relevant source-context
well-formedness needed by the source-tree constructor.  Every telescope
extension carries a valid selected basis; the linear rule's shape equation
identifies its stored source space with `Basis.sof b`. -/
theorem RawConsistent.ctxWFPrime
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    V2.CtxWF' Delta Gamma := by
  induction h with
  | empty =>
      exact {
        disjoint := fun _ hm => absurd hm Finmap.notMem_empty
        lin_fv := fun _ _ hm => absurd
          (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
        nl_fv := fun _ _ hm => absurd
          (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
        lin_valid := fun _ _ hm => absurd
          (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty
        nl_valid := fun _ _ hm => absurd
          (Finmap.mem_of_lookup_eq_some hm) Finmap.notMem_empty }
  | extend_lin hprefix hx htof hb hTy hinfer hinferSpace
      hfvv hlc hnr hxs hden hagree hdims ih =>
      have hwf := RawLocalCtxWFInsertionScratch.ctxWF_insert_lin
        ih hx.1 hx.2 hb
      simpa only [Basis.sof_eq_of_tof_eq_space htof] using hwf
  | extend_nl hprefix hx hb hTy hinfer hinferSpace
      hfvv hlc hnr hxs hden hagree hdims _hanchor ih =>
      exact RawLocalCtxWFInsertionScratch.ctxWF_insert_nl
        ih hx.1 hx.2 hb
  | extend_rep hprefix hkey hsource hsigma hb hTy hinfer hinferSpace
      hfvv hlc hxs hden hagree hdims hanchor ih =>
      exact ih

/-- Nonlinear-only view of full raw source-context well-formedness. -/
theorem RawConsistent.ctxWFPrime_nl
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    V2.CtxWF' (∅ : LCtx) Gamma :=
  RawCertifiedWorldBinderProgress.ctxWF_dropLin
    h.ctxWFPrime

/-- The ordinary linear/nonlinear disjointness required by the source
typing bridge is a direct projection of raw context well-formedness. -/
theorem RawConsistent.ctxDisj
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    Graded.CtxDisj Delta Gamma :=
  h.ctxWFPrime.disjoint

namespace RawCertifiedConsistentPairStore

/-- Creation-rank induction closes the entire fresh exact-quad store from the local
one-basis builder.  This is the evaluator-history theorem: all recursive
calls made by `leaves.resolve` are justified by the strict predecessor fact
already derivable from `RawConsistent`. -/
theorem RawConsistent.checkedPairFreshDepthQuadSelectedStore_of_layer
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (hconsistent : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (build : CheckedPairDepthLayerBuilder Psi Gamma) :
    CheckedPairFreshDepthQuadSelectedStore Psi Gamma := by
  obtain ⟨rank, hpredecessors⟩ :=
    RawConsistentRank.RawConsistent.exists_ranked_lookup_predecessors
      hconsistent
  intro x b v hlookup
  suffices go : forall n, forall {x : VName} {b : Basis}, rank (x, b) = n ->
      forall {v : ValExpr},
        EvalCtx.lookup Psi (x, b) = some v ->
          CheckedPairFreshDepthQuadFinite Psi Gamma b by
    exact go (rank (x, b)) rfl hlookup
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x b hx v hlookup
      have hb : Basis.BasisValid Gamma b :=
        hconsistent.lookup_basisValid_mono hlookup (NLCtxIncl.refl Gamma)
      apply build (hconsistent.stored_fv x b v hlookup).1
        hb (RawConsistent.ctxWFPrime_nl hconsistent)
      refine ⟨?_⟩
      intro y hy
      obtain ⟨bY, vY, hlookupY, hyrank⟩ :=
        hpredecessors hlookup y hy
      exact ⟨bY, vY, hlookupY,
        hconsistent.lookup_basisValid_mono hlookupY
          (NLCtxIncl.refl Gamma),
        ih (rank (y, bY)) (by simpa only [hx] using hyrank)
          rfl hlookupY⟩

/-- Root projection of the fresh-world rank induction. -/
theorem RawConsistent.checkedPairDepthQuadSelectedStore_of_layer
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (hconsistent : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (build : CheckedPairDepthLayerBuilder Psi Gamma) :
    CheckedPairDepthQuadSelectedStore Psi Gamma :=
  CheckedPairFreshDepthQuadSelectedStore.toQuad
    (RawConsistent.checkedPairFreshDepthQuadSelectedStore_of_layer
      hconsistent build)
    (RawConsistent.ctxWFPrime_nl hconsistent)

/-- Public finite-store corollary.  No common numeric depth is asserted
across distinct evaluator keys. -/
theorem RawConsistent.checkedPairFiniteSelectedStore_of_layer
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {GammaV : ValCtx}
    {sigma : DEnv} {rho : ValEnvSem}
    (hconsistent : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (build : CheckedPairDepthLayerBuilder Psi Gamma) :
    CheckedPairFiniteSelectedStore Psi Gamma :=
  CheckedPairDepthQuadSelectedStore.toFinite
    (RawConsistent.checkedPairDepthQuadSelectedStore_of_layer
      hconsistent build)

end RawCertifiedConsistentPairStore
end GLang
