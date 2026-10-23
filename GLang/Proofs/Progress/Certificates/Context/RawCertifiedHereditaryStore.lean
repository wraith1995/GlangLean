import GLang.Proofs.Progress.Certificates.RawCertifiedCobProgress
import GLang.Proofs.Adequacy.Raw.Context.RawConsistent

namespace GLang
namespace RawCertifiedHereditaryStore

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch

/-- A future-stable recipe for one evaluator entry.  It does not bake in a
source `Delta` or `Gamma`: the caller supplies a direct checked variable node
at the stored basis, and the recipe changes only that node's basis to the
literal standard basis of the same source type. -/
def CheckedVarRecipeFrom
    (Psi0 : EvalCtx) (x : VName) (b : Basis) (v : ValExpr) : Prop :=
  forall (Psi : EvalCtx), Psi0.Subctx Psi ->
    forall (Delta : LCtx) (Gamma : NLCtx) (tauv : ValTy),
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
      Basis.BasisValid Gamma b ->
      C.Term Delta Gamma Psi (.var x) b v tauv ->
      exists w tauw,
        C.Term Delta Gamma Psi (.var x) (Basis.std (Basis.tof b)) w tauw

/-- A checked store retains a future-stable recipe for every literal lookup
currently present in `Psi`.  The recipe itself is proof-relevant; it is not
recovered from `StdComplete`. -/
structure CheckedStdStore (Psi : EvalCtx) : Prop where
  recipe : forall (x : VName) (b : Basis) (v : ValExpr),
    EvalCtx.lookup Psi (x, b) = some v -> CheckedVarRecipeFrom Psi x b v

/-- The empty evaluator has an empty checked store. -/
theorem CheckedStdStore.empty : CheckedStdStore (∅ : EvalCtx) := by
  constructor
  intro x b v hlookup
  simp [EvalCtx.lookup] at hlookup

/-- Install one creation-time recipe. -/
theorem CheckedStdStore.extend
    {Psi : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
    (h : CheckedStdStore Psi)
    (hpair : (x, b) ∉ Psi)
    (hnew : CheckedVarRecipeFrom (Psi.extend x b v) x b v) :
    CheckedStdStore (Psi.extend x b v) := by
  constructor
  intro y b' v' hlookup
  classical
  by_cases hkey : (y, b') = (x, b)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkey
    rw [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert] at hlookup
    obtain rfl := Option.some.inj hlookup
    exact hnew
  · have hold : EvalCtx.lookup Psi (y, b') = some v' := by
      simpa only [EvalCtx.lookup, EvalCtx.extend,
        Finmap.lookup_insert_of_ne _ hkey] using hlookup
    have hsub : Psi.Subctx (Psi.extend x b v) :=
      EvalCtx.Subctx.extend_right_of_key_fresh hpair v
    have hrecipe := h.recipe y b' v' hold
    intro Psi' hsub' Delta Gamma tauv hP hcov hstored hwf hbv hterm
    exact hrecipe Psi' (hsub.trans hsub') Delta Gamma tauv
      hP hcov hstored hwf hbv hterm

/-- A checked arbitrary-basis transport theorem supplies a future-stable
recipe for every entry.  This is useful for the frame half and also shows
that the recipe interface asks for no extra result equality: the literal
result returned by checked transport is retained. -/
theorem checkedVarRecipeFrom_of_basisTransport
    (htransport : CheckedBasisTransport)
    (Psi0 : EvalCtx) (x : VName) (b : Basis) (v : ValExpr) :
    CheckedVarRecipeFrom Psi0 x b v := by
  intro Psi _hsub Delta Gamma tauv hP hcov hstored _hwf hbv hterm
  obtain ⟨k, ⟨htofValid⟩⟩ := hbv.tof_tvalid
  have hstdValid : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) :=
    Basis.std_valid (Basis.tof b) htofValid
  obtain ⟨w, tauw, hw⟩ := htransport Delta Gamma Psi (.var x)
    b (Basis.std (Basis.tof b)) v tauv hP hcov hstored hbv
    hterm.tyAt.isTyBasis
    hstdValid (Basis.isTyBasis_std (Basis.tof b))
    (Basis.tof_std (Basis.tof b)) hterm
  exact ⟨w, tauw, hw⟩

/-- In particular, a global checked transport theorem populates a checked
store over any evaluator. -/
theorem checkedStdStore_of_basisTransport
    (htransport : CheckedBasisTransport) (Psi : EvalCtx) :
    CheckedStdStore Psi := by
  constructor
  intro x b v _hlookup
  exact checkedVarRecipeFrom_of_basisTransport htransport Psi x b v

/-- The space fragment of a recipe is exactly checked COB-to-standard
progress. -/
theorem checkedVarRecipeFrom_space_of_cob
    (hcob : CheckedCobToStd)
    {Psi0 : EvalCtx} {x : VName} {b : Basis} {v : ValExpr} {s : Space}
    (htof : Basis.tof b = .space s) :
    CheckedVarRecipeFrom Psi0 x b v := by
  intro Psi _hsub Delta Gamma tauv hP hcov hstored _hwf hbv hterm
  have hspaceB : Basis.IsSpaceBasis b :=
    hterm.tyAt.isTyBasis.toIsSpaceBasis (Basis.ne_frame_of_tof_space htof)
  have hstdValid : Basis.BasisValid Gamma (Basis.std (Basis.tof b)) := by
    obtain ⟨k, ⟨ht⟩⟩ := hbv.tof_tvalid
    exact Basis.std_valid _ ht
  have hspaceStd : Basis.IsSpaceBasis (Basis.std (Basis.tof b)) := by
    rw [htof]
    exact Basis.isSpaceBasis_stdSpace s
  obtain ⟨sv, htauv, _hspace⟩ :=
    checkedTyAt_space_inv htof hterm.tyAt
  subst tauv
  obtain ⟨_env, _hcobBetween, hout⟩ :=
    checkedSpaceTermTransport_of_toStd hcob hP hcov hstored
      hbv hspaceB hstdValid hspaceStd (Basis.tof_std (Basis.tof b)) hterm
  exact ⟨_, _, hout⟩

/-! ## Direct consumers: the two variable arms -/

/-- Once the caller has the rule-local stored-basis facts, a linear variable
is standardized by the hereditary recipe. -/
theorem checked_var_lin_of_store
    {Psi : EvalCtx} (hstore : CheckedStdStore Psi)
    {Gamma : NLCtx} {x : VName} {b : Basis} {v : ValExpr}
    {s : Space} {tauv : ValTy}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (Finmap.singleton x s) Gamma)
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (htof : Basis.tof b = .space s)
    (hbv : Basis.BasisValid Gamma b)
    (htauv : C.TyAt Gamma Psi b tauv) :
    exists w tauw,
      C.Term (Finmap.singleton x s) Gamma Psi (.var x)
        (Basis.std (.space s)) w tauw := by
  have hdirect : C.Term (Finmap.singleton x s) Gamma Psi (.var x) b v tauv :=
    .var_lin hlookup htof hbv htauv
  obtain ⟨w, tauw, hw⟩ := hstore.recipe x b v hlookup
    Psi (EvalCtx.Subctx.refl Psi) (Finmap.singleton x s) Gamma tauv
    hP hcov hstored hwf hbv hdirect
  rw [htof] at hw
  exact ⟨w, tauw, hw⟩

/-- The nonlinear variable arm is the same construction; only its direct
checked leaf uses the nonlinear source lookup. -/
theorem checked_var_nlin_of_store
    {Psi : EvalCtx} (hstore : CheckedStdStore Psi)
    {Gamma : NLCtx} {x : VName} {b : Basis} {v : ValExpr}
    {tau : Ty} {tauv : ValTy}
    (hP : V2.PCarrier Psi) (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hlookup : EvalCtx.lookup Psi (x, b) = some v)
    (hGamma : Gamma.lookup x = some tau)
    (htof : Basis.tof b = tau)
    (hbv : Basis.BasisValid Gamma b)
    (htauv : C.TyAt Gamma Psi b tauv) :
    exists w tauw,
      C.Term (∅ : LCtx) Gamma Psi (.var x) (Basis.std tau) w tauw := by
  have hGamma' : Gamma.lookup x = some (Basis.tof b) := by
    rw [htof]
    exact hGamma
  have hdirect : C.Term (∅ : LCtx) Gamma Psi (.var x) b v tauv :=
    .var_nlin hlookup hGamma' hbv htauv
  obtain ⟨w, tauw, hw⟩ := hstore.recipe x b v hlookup
    Psi (EvalCtx.Subctx.refl Psi) (∅ : LCtx) Gamma tauv
    hP hcov hstored hwf hbv hdirect
  rw [htof] at hw
  exact ⟨w, tauw, hw⟩

/-! ## Explicit creation history -/

/-- A proof-relevant evaluator telescope which installs one standardization
recipe at the moment each entry is created.  Its induction order is the
operational non-recursion order, not an induction over an erased final map. -/
inductive CheckedStoreTele : EvalCtx -> Prop
  | empty : CheckedStoreTele (∅ : EvalCtx)
  | extend {Psi : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
      (prev : CheckedStoreTele Psi)
      (fresh : (x, b) ∉ Psi)
      (recipe : CheckedVarRecipeFrom (Psi.extend x b v) x b v) :
      CheckedStoreTele (Psi.extend x b v)

/-- The explicit history folds to the extensional checked-store consumer. -/
theorem CheckedStoreTele.toStore : forall {Psi : EvalCtx},
    CheckedStoreTele Psi -> CheckedStdStore Psi
  | _, .empty => CheckedStdStore.empty
  | _, .extend prev fresh recipe =>
      (CheckedStoreTele.toStore prev).extend fresh recipe

/-- The exact creation callback needed to upgrade current
`RawConsistent`.  It sees the prefix consistency and already-built checked
store, exact pair-key freshness, the new entry's prefix-valid basis and exact
type certificate, and the intrinsic `IsTyBasis` guard recorded by the raw
extension.  Its conclusion is one future-stable recipe rooted at the extended
evaluator. -/
def CheckedRawEntryBuilder : Prop :=
  forall (orc : FFSOracleSem)
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (rho : ValEnvSem)
    (x : VName) (b : Basis) (v : ValExpr) (tauv : ValTy),
    RawConsistent orc Delta Gamma Psi GammaV sigma rho ->
    CheckedStdStore Psi ->
    (x, b) ∉ Psi ->
    Basis.BasisValid Gamma b -> Basis.IsTyBasis b ->
    CheckedVarRecipeFrom (Psi.extend x b v) x b v

/-- Current raw consistency upgrades to the hereditary checked store by
induction on creation history, provided precisely the one-entry builder.
   The entry-local `IsTyBasis` guard is derived from the corresponding stored
   `BasisValid`.  No checked evidence is reconstructed from a final erased
   lookup. -/
theorem checkedStdStore_of_rawConsistent
    (hbuild : CheckedRawEntryBuilder) :
    forall {orc : FFSOracleSem}
      {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
      {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem},
      RawConsistent orc Delta Gamma Psi GammaV sigma rho ->
      CheckedStdStore Psi := by
  intro orc Delta Gamma Psi GammaV sigma rho hraw
  induction hraw with
  | empty =>
      exact CheckedStdStore.empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x b v tauv xs s yV
      hprefix hx htof hb hTy hinfer hinferSpace hfvv hlc hnr
      hxs hden hagree hdims ih =>
      have hp : CheckedStdStore Psi := ih
      have hrecipe : CheckedVarRecipeFrom (Psi.extend x b v) x b v :=
        hbuild orc Delta Gamma Psi GammaV sigma rho x b v tauv
          hprefix hp (hprefix.freshEvalName hx b) hb
          hb.isTyBasis
      exact hp.extend (hprefix.freshEvalName hx b) hrecipe
  | @extend_nl Delta Gamma Psi GammaV sigma rho x b v tauv xs yV
      hprefix hx hb hTy hinfer hinferSpace hfvv hlc hnr
      hxs hden hagree hdims _hanchor ih =>
      have hp : CheckedStdStore Psi := ih
      have hrecipe : CheckedVarRecipeFrom (Psi.extend x b v) x b v :=
        hbuild orc Delta Gamma Psi GammaV sigma rho x b v tauv
          hprefix hp (hprefix.freshEvalName hx b) hb
          hb.isTyBasis
      exact hp.extend (hprefix.freshEvalName hx b) hrecipe
  | @extend_rep Delta Gamma Psi GammaV sigma rho x b v tauv xs yV
      hprefix hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc
      hxs hden hagree hdims _hanchor ih =>
      have hp : CheckedStdStore Psi := ih
      have hrecipe : CheckedVarRecipeFrom (Psi.extend x b v) x b v :=
        hbuild orc Delta Gamma Psi GammaV sigma rho x b v tauv
          hprefix hp hkey hb hb.isTyBasis
      exact hp.extend hkey hrecipe

theorem checkedStdStore_of_rawConsistent_ctxTele
    (hbuild : CheckedRawEntryBuilder)
    (hraw : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    (htele : V2.CtxTele Delta Gamma Psi) : CheckedStdStore Psi :=
  checkedStdStore_of_rawConsistent hbuild hraw

structure RawCheckedStoreInput (orc : FFSOracleSem)
    (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (rho : ValEnvSem) : Prop where
  consistent : RawConsistent orc Delta Gamma Psi GammaV sigma rho

/-- Raw-specific checked-store construction.  Self placeholders are accepted:
neither `ValExpr.fv v \subseteq Psi.keyNames` nor a `CtxTele` is a premise. -/
theorem checkedStdStore_of_rawInput
    (hbuild : CheckedRawEntryBuilder)
    (h : RawCheckedStoreInput orc Delta Gamma Psi GammaV sigma rho) :
    CheckedStdStore Psi :=
  checkedStdStore_of_rawConsistent hbuild h.consistent

/-! ## A root store and its standard-only binder futures -/

/-- The root input used by the local checked-progress master.  Keeping the
hereditary key-shape invariant beside the proof-relevant recipes makes the
two genuinely mutual inputs explicit; no `CtxTele` is hidden in this
package. -/
structure CheckedStdStoreRoot (Psi : EvalCtx) : Prop where
  store : CheckedStdStore Psi
  storedWF : V2.StoredWF Psi

/-- Current raw consistency supplies both halves of the root package:
proof-relevant standardization recipes from creation history and hereditary
basis shape from the intrinsic guard on each stored `TyAt`. -/
theorem checkedStdStoreRoot_of_rawConsistent
    (hbuild : CheckedRawEntryBuilder)
    (hraw : RawConsistent orc Delta Gamma Psi GammaV sigma rho) :
    CheckedStdStoreRoot Psi where
  store := checkedStdStore_of_rawConsistent hbuild hraw
  storedWF := hraw.storedWF

/-- Evaluator worlds reached below a fixed progress call preserve every root
lookup and add only literal standard-basis keys at genuinely fresh names.
Every extra name has exactly one key, as it does in the evaluator extensions
created by the binder rules.  Source-type alignment is checked at the point
where a variable consumes the key (see `CheckedLocalTermSideBasisWithWorld`):
the future relation alone deliberately does not invent a typing context. -/
structure CheckedStdFuture (Psi0 Psi : EvalCtx) : Prop where
  subctx : Psi0.Subctx Psi
  extra_standard : forall x b, (x, b) ∈ Psi -> (x, b) ∉ Psi0 ->
    b = Basis.std (Basis.tof b)
  extra_name_fresh : forall x b, (x, b) ∈ Psi -> (x, b) ∉ Psi0 ->
    x ∉ Psi0.names
  extra_name_unique : forall x b0 b1,
    (x, b0) ∈ Psi -> (x, b0) ∉ Psi0 -> (x, b1) ∈ Psi -> b0 = b1

theorem CheckedStdFuture.refl (Psi : EvalCtx) : CheckedStdFuture Psi Psi where
  subctx := EvalCtx.Subctx.refl Psi
  extra_standard := by
    intro x b _hmem hnot
    exact False.elim (hnot _hmem)
  extra_name_fresh := by
    intro x b hmem hnot
    exact False.elim (hnot hmem)
  extra_name_unique := by
    intro x b0 b1 hmem hnot _
    exact False.elim (hnot hmem)

/-- One fresh standard placeholder preserves the root/future relation. -/
theorem CheckedStdFuture.extend_std
    {Psi0 Psi : EvalCtx} (h : CheckedStdFuture Psi0 Psi)
    {x : VName} (hx : x ∉ Psi.names) (tau : Ty) (v : ValExpr) :
    CheckedStdFuture Psi0 (Psi.extend x (Basis.std tau) v) := by
  constructor
  · exact h.subctx.trans
      (EvalCtx.Subctx.extend_right_of_name_fresh hx (Basis.std tau) v)
  · intro y b hmem hnot
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hold
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      simp only [Basis.tof_std]
    · exact h.extra_standard y b hold hnot
  · intro y b hmem hnot
    simp only [EvalCtx.extend] at hmem
    rcases Finmap.mem_insert.mp hmem with heq | hold
    · have hyx : y = x := (Prod.mk.inj heq).1
      have hb : b = Basis.std tau := (Prod.mk.inj heq).2
      subst y
      subst b
      intro hx0
      obtain ⟨⟨y, b0⟩, hkey0, hy⟩ := Finset.mem_image.mp hx0
      simp only at hy
      subst y
      obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp
        (Finmap.mem_keys.mp hkey0)
      exact hx (EvalCtx.mem_names_of_lookup
        (h.subctx (x, b0) v0 hlookup0))
    · exact h.extra_name_fresh y b hold hnot
  · intro y b0 b1 hmem0 hnot0 hmem1
    simp only [EvalCtx.extend] at hmem0 hmem1
    rcases Finmap.mem_insert.mp hmem0 with heq0 | hold0
    · have hyx : y = x := (Prod.mk.inj heq0).1
      have hb0 : b0 = Basis.std tau := (Prod.mk.inj heq0).2
      subst y
      subst b0
      rcases Finmap.mem_insert.mp hmem1 with heq1 | hold1
      · exact (Prod.mk.inj heq1).2.symm
      · exact False.elim (hx (by
          exact Finset.mem_image.mpr ⟨(x, b1),
            Finmap.mem_keys.mpr hold1, rfl⟩))
    · have hyx : y ≠ x := by
        intro hyx
        subst y
        exact hx (Finset.mem_image.mpr ⟨(x, b0),
          Finmap.mem_keys.mpr hold0, rfl⟩)
      rcases Finmap.mem_insert.mp hmem1 with heq1 | hold1
      · exact False.elim (hyx (Prod.mk.inj heq1).1)
      · exact h.extra_name_unique y b0 b1 hold0 hnot0 hold1

/-- A future cannot smuggle a second basis underneath a name already owned by
the root store. -/
theorem CheckedStdFuture.mem_root_of_root_name
    {Psi0 Psi : EvalCtx} (h : CheckedStdFuture Psi0 Psi)
    {x : VName} {b : Basis}
    (hx : x ∈ Psi0.names) (hmem : (x, b) ∈ Psi) : (x, b) ∈ Psi0 := by
  classical
  by_contra hnot
  exact h.extra_name_fresh x b hmem hnot hx

/-- Standard-only future growth preserves hereditary key shape. -/
theorem CheckedStdFuture.storedWF
    {Psi0 Psi : EvalCtx} (h : CheckedStdFuture Psi0 Psi)
    (hroot : V2.StoredWF Psi0) : V2.StoredWF Psi := by
  intro x b hmem
  classical
  by_cases hbase : (x, b) ∈ Psi0
  · exact hroot x b hbase
  · rw [h.extra_standard x b hmem hbase]
    exact Basis.isTyBasis_std _

/-- A recipe rooted at a literal standard key is the identity recipe. -/
theorem checkedVarRecipeFrom_std
    (Psi : EvalCtx) (x : VName) (tau : Ty) (v : ValExpr) :
    CheckedVarRecipeFrom Psi x (Basis.std tau) v := by
  intro Psi' _hsub Delta Gamma tauv hP hcov hstored _hwf hbv hterm
  exact ⟨v, tauv, by simpa only [Basis.tof_std] using hterm⟩

/-- The root recipes extend extensionally to every standard-only binder
future. -/
theorem CheckedStdFuture.checkedStore
    {Psi0 Psi : EvalCtx} (h : CheckedStdFuture Psi0 Psi)
    (hroot : CheckedStdStore Psi0) : CheckedStdStore Psi := by
  constructor
  intro x b v hlookup
  classical
  have hmem : (x, b) ∈ Psi := Finmap.mem_of_lookup_eq_some hlookup
  by_cases hbase : (x, b) ∈ Psi0
  · obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp hbase
    have hlookup' := h.subctx (x, b) v0 hlookup0
    have hv : v0 = v := Option.some.inj (hlookup'.symm.trans hlookup)
    subst v0
    have hrecipe := hroot.recipe x b v hlookup0
    intro Psi' hsub' Delta Gamma tauv hP hcov hstored hwf hbv hterm
    exact hrecipe Psi' (h.subctx.trans hsub') Delta Gamma tauv
      hP hcov hstored hwf hbv hterm
  · have hb := h.extra_standard x b hmem hbase
    intro Psi' hsub Delta Gamma tauv hP hcov hstored _hwf hbv hterm
    exact ⟨v, tauv, hb ▸ hterm⟩

/-! ## The remaining promotion-side linkage -/

/-- The smallest rule-local side-basis obligation.  This is deliberately
indexed by the *typing proof*: a promoted variable and its inner variable leaf
are different nodes and therefore receive obligations at their respective
nonlinear contexts. -/
def CheckedLocalTermSideBasis (Psi : EvalCtx) :
    {Delta : LCtx} -> {Gamma : NLCtx} -> {e : Term} -> {tau : Ty} ->
      HasType Delta Gamma e tau -> Prop
  | _, Gamma, _, _, @HasType.var_lin _ x s =>
      forall b v, EvalCtx.lookup Psi (x, b) = some v ->
        Basis.tof b = .space s ->
        Basis.BasisValid Gamma b
  | _, Gamma, _, _, @HasType.var_nlin _ x tau _ =>
      forall b v, EvalCtx.lookup Psi (x, b) = some v ->
        Basis.tof b = tau ->
        Basis.BasisValid Gamma b
  | _, _, _, _, _ => True

private def checkedLocalSideSMotive (Psi : EvalCtx)
    {Gamma : NLCtx} {s : Space} (_h : SValid Gamma s) : Prop := True

private def checkedLocalSideTMotive (Psi : EvalCtx)
    {Gamma : NLCtx} {tau : Ty} {k : Kind}
    (_h : TValid Gamma tau k) : Prop := True

private def checkedLocalSideSubMotive (Psi : EvalCtx)
    {Gamma : NLCtx} {s0 s1 : Space}
    (_h : SubType Gamma s0 s1) : Prop := True

/-- Local-side tree rooted at a space-validity derivation.  Its only
nontrivial nodes are term witnesses appearing inside FFS spaces. -/
structure CheckedLocalSideS (Psi : EvalCtx)
    {Gamma : NLCtx} {s : Space} (h : SValid Gamma s) : Type where
  descendants :
    @SValid.below
      (fun _ _ hs => checkedLocalSideSMotive Psi hs)
      (fun _ _ _ ht => checkedLocalSideTMotive Psi ht)
      (fun _ _ _ hsub => checkedLocalSideSubMotive Psi hsub)
      (fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he)
      Gamma s h

/-- Local-side tree rooted at a type-validity derivation.  In particular its
cofinite Pi branch retains the side tree of every opened codomain. -/
structure CheckedLocalSideT (Psi : EvalCtx)
    {Gamma : NLCtx} {tau : Ty} {k : Kind}
    (h : TValid Gamma tau k) : Type where
  descendants :
    @TValid.below
      (fun _ _ hs => checkedLocalSideSMotive Psi hs)
      (fun _ _ _ ht => checkedLocalSideTMotive Psi ht)
      (fun _ _ _ hsub => checkedLocalSideSubMotive Psi hsub)
      (fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he)
      Gamma tau k h

/-- Local-side tree rooted at a subtyping derivation.  It retains the FFS
witness term used by all four fundamental-subspace rules. -/
structure CheckedLocalSideSub (Psi : EvalCtx)
    {Gamma : NLCtx} {s0 s1 : Space}
    (h : SubType Gamma s0 s1) : Type where
  descendants :
    @SubType.below
      (fun _ _ hs => checkedLocalSideSMotive Psi hs)
      (fun _ _ _ ht => checkedLocalSideTMotive Psi ht)
      (fun _ _ _ hsub => checkedLocalSideSubMotive Psi hsub)
      (fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he)
      Gamma s0 s1 h

/-- The generated mutual `below` tree is exactly the recursive scope required
by the premise: it visits term subderivations reached through spaces, types,
subtyping, ordinary term constructors, promotion, and cofinite binders.  We
pair it with the root obligation because `HasType.below` contains strict
descendants only.

This is proof-relevant (`Type`) because source typing itself is proof-relevant;
it is nevertheless only an interface/record assembled by a caller, never an
axiom. -/
structure CheckedLocalSideBases (Psi : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) : Type where
  here : CheckedLocalTermSideBasis Psi h
  descendants :
    @HasType.below
      (fun _ _ hs => checkedLocalSideSMotive Psi hs)
      (fun _ _ _ ht => checkedLocalSideTMotive Psi ht)
      (fun _ _ _ hsub => checkedLocalSideSubMotive Psi hsub)
      (fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he)
      Delta Gamma e tau h

/-! The four wrappers above use the generated mutual `below` objects rather
than a hand-written shadow copy of the 34 source constructors.  A recursor
handler receives each immediate child as a pair `(child node, child below)`;
the following tiny constructors are the uniform way to repackage those
pairs for the recursive call. -/

def CheckedLocalSideS.ofBelowPair
    {Psi : EvalCtx} {Gamma : NLCtx} {s : Space} {h : SValid Gamma s}
    (p : PProd (checkedLocalSideSMotive Psi h)
      (SValid.below
        (motive_1 := fun _ _ hs => checkedLocalSideSMotive Psi hs)
        (motive_2 := fun _ _ _ ht => checkedLocalSideTMotive Psi ht)
        (motive_3 := fun _ _ _ hsub => checkedLocalSideSubMotive Psi hsub)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he) h)) :
    CheckedLocalSideS Psi h :=
  ⟨p.2⟩

def CheckedLocalSideT.ofBelowPair
    {Psi : EvalCtx} {Gamma : NLCtx} {tau : Ty} {k : Kind}
    {h : TValid Gamma tau k}
    (p : PProd (checkedLocalSideTMotive Psi h)
      (TValid.below
        (motive_1 := fun _ _ hs => checkedLocalSideSMotive Psi hs)
        (motive_2 := fun _ _ _ ht => checkedLocalSideTMotive Psi ht)
        (motive_3 := fun _ _ _ hsub => checkedLocalSideSubMotive Psi hsub)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he) h)) :
    CheckedLocalSideT Psi h :=
  ⟨p.2⟩

def CheckedLocalSideSub.ofBelowPair
    {Psi : EvalCtx} {Gamma : NLCtx} {s0 s1 : Space}
    {h : SubType Gamma s0 s1}
    (p : PProd (checkedLocalSideSubMotive Psi h)
      (SubType.below
        (motive_1 := fun _ _ hs => checkedLocalSideSMotive Psi hs)
        (motive_2 := fun _ _ _ ht => checkedLocalSideTMotive Psi ht)
        (motive_3 := fun _ _ _ hsub => checkedLocalSideSubMotive Psi hsub)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he) h)) :
    CheckedLocalSideSub Psi h :=
  ⟨p.2⟩

def CheckedLocalSideBases.ofBelowPair
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {tau : Ty} {h : HasType Delta Gamma e tau}
    (p : PProd (CheckedLocalTermSideBasis Psi h)
      (HasType.below
        (motive_1 := fun _ _ hs => checkedLocalSideSMotive Psi hs)
        (motive_2 := fun _ _ _ ht => checkedLocalSideTMotive Psi ht)
        (motive_3 := fun _ _ _ hsub => checkedLocalSideSubMotive Psi hsub)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he) h)) :
    CheckedLocalSideBases Psi h :=
  ⟨p.1, p.2⟩

/-- Promotion exposes the recursively certified premise at the smaller
nonlinear context `Gamma`.  No `NLCtxIncl` in the invalid shrinking direction
is requested or manufactured. -/
def CheckedLocalSideBases.promoteInner
    {Psi : EvalCtx} {Delta lin : LCtx} {Gamma : NLCtx}
    {e : Term} {tau : Ty}
    {hdisjDelta : Finmap.Disjoint lin Delta}
    {hdisjGamma : Finmap.Disjoint lin.toNL Gamma}
    {hfresh : PromoteFresh lin Delta Gamma}
    {hinner : HasType (lin ∪ Delta) Gamma e tau}
    (h : CheckedLocalSideBases Psi
      (.promote lin hdisjDelta hdisjGamma hfresh hinner)) :
    CheckedLocalSideBases Psi hinner :=
  ⟨h.descendants.1, h.descendants.2⟩

/-- Exact-basis checked type progress is the other member of the intended
mutual construction.  Its hypotheses are precisely current-context validity
and hereditary basis shape; in particular it does not ask for a creation
context to embed into the current one.  The space case is supplied by checked
`C.Space` progress and the frame case recurses under its own binder. -/
def CheckedExactBasisTyProgress : Prop :=
  forall (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> forall (Delta : LCtx), V2.CtxWF' Delta Gamma ->
    Basis.BasisValid Gamma b -> Basis.IsTyBasis b ->
    exists tauv, C.TyAt Gamma Psi b tauv

/-- A local side-basis certificate, exact-basis type progress, and the
hereditary store close the linear-variable arm.  The `VarsCovered` witness is
the literal key consumed by the rule; `CheckedLocalTermSideBasis` validates
that key at this exact node, and `CheckedExactBasisTyProgress` realizes its
type there. -/
theorem checked_var_lin_of_localSide
    (hexact : CheckedExactBasisTyProgress)
    {Psi : EvalCtx} (hstore : CheckedStdStore Psi)
    {Gamma : NLCtx} {x : VName} {s : Space}
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (Finmap.singleton x s) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (Finmap.singleton x s) Gamma)
    (hside : CheckedLocalSideBases Psi
      (HasType.var_lin : HasType (Finmap.singleton x s) Gamma (.var x)
        (.space s))) :
    exists w tauw,
      C.Term (Finmap.singleton x s) Gamma Psi (.var x)
        (Basis.std (.space s)) w tauw := by
  obtain ⟨b, hmem, htof⟩ := hcov.1 x s Finmap.lookup_singleton_eq
  obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
  have hbv : Basis.BasisValid Gamma b := hside.here b v hlookup htof
  have hty : Basis.IsTyBasis b := hstored x b hmem
  obtain ⟨tauv, htau⟩ := hexact Gamma Psi b hP hcov.drop_lin
    hstored (Finmap.singleton x s) hwf hbv hty
  exact checked_var_lin_of_store hstore hP hcov.drop_lin hstored
    hwf hlookup htof hbv htau

/-- Nonlinear-variable companion of `checked_var_lin_of_localSide`. -/
theorem checked_var_nlin_of_localSide
    (hexact : CheckedExactBasisTyProgress)
    {Psi : EvalCtx} (hstore : CheckedStdStore Psi)
    {Gamma : NLCtx} {x : VName} {tau : Ty}
    (hGamma : Gamma.lookup x = some tau)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hside : CheckedLocalSideBases Psi
      (HasType.var_nlin hGamma : HasType (∅ : LCtx) Gamma (.var x) tau)) :
    exists w tauw,
      C.Term (∅ : LCtx) Gamma Psi (.var x) (Basis.std tau) w tauw := by
  obtain ⟨b, hmem, htof⟩ := hcov.2 x tau hGamma
  obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
  have hbv : Basis.BasisValid Gamma b := hside.here b v hlookup htof
  have hty : Basis.IsTyBasis b := hstored x b hmem
  obtain ⟨tauv, htau⟩ := hexact Gamma Psi b hP hcov hstored
    (∅ : LCtx) hwf hbv hty
  exact checked_var_nlin_of_store hstore hP hcov hstored hwf
    hlookup hGamma htof hbv htau

/-! ## Root/future variable consumers -/

private theorem checked_root_or_standard_lin_valid
    {Psi0 Psi : EvalCtx} (hfuture : CheckedStdFuture Psi0 Psi)
    {Gamma : NLCtx} {x : VName} {s : Space} {b : Basis}
    (hmem : (x, b) ∈ Psi) (htof : Basis.tof b = .space s)
    (hwf : V2.CtxWF' (Finmap.singleton x s) Gamma)
    (hside : CheckedLocalSideBases Psi0
      (HasType.var_lin : HasType (Finmap.singleton x s) Gamma (.var x)
        (.space s))) :
    Basis.BasisValid Gamma b := by
  classical
  by_cases hbase : (x, b) ∈ Psi0
  · obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp hbase
    exact hside.here b v0 hlookup0 htof
  · have hbstd := hfuture.extra_standard x b hmem hbase
    obtain ⟨hs⟩ := hwf.lin_valid x s Finmap.lookup_singleton_eq
    rw [hbstd, htof]
    exact Basis.std_valid (.space s) (.space hs)

private theorem checked_root_or_standard_nlin_valid
    {Psi0 Psi : EvalCtx} (hfuture : CheckedStdFuture Psi0 Psi)
    {Gamma : NLCtx} {x : VName} {tau : Ty} {b : Basis}
    (hmem : (x, b) ∈ Psi) (htof : Basis.tof b = tau)
    (hGamma : Gamma.lookup x = some tau)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hside : CheckedLocalSideBases Psi0
      (HasType.var_nlin hGamma : HasType (∅ : LCtx) Gamma (.var x) tau)) :
    Basis.BasisValid Gamma b := by
  classical
  by_cases hbase : (x, b) ∈ Psi0
  · obtain ⟨v0, hlookup0⟩ := Finmap.mem_iff.mp hbase
    exact hside.here b v0 hlookup0 htof
  · have hbstd := hfuture.extra_standard x b hmem hbase
    obtain ⟨k, ⟨htau⟩⟩ := hwf.nl_valid x tau hGamma
    rw [hbstd, htof]
    exact Basis.std_valid tau htau

/-- Linear-variable progress in an arbitrary binder future of the root
store.  Arbitrary root keys are justified by the local side tree; every
non-root key is standard and is justified by `CtxWF'`. -/
theorem checked_var_lin_of_rootFuture
    (hexact : CheckedExactBasisTyProgress)
    {Psi0 Psi : EvalCtx} (hroot : CheckedStdStoreRoot Psi0)
    (hfuture : CheckedStdFuture Psi0 Psi)
    {Gamma : NLCtx} {x : VName} {s : Space}
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (Finmap.singleton x s) Gamma Psi)
    (hwf : V2.CtxWF' (Finmap.singleton x s) Gamma)
    (hside : CheckedLocalSideBases Psi0
      (HasType.var_lin : HasType (Finmap.singleton x s) Gamma (.var x)
        (.space s))) :
    exists w tauw,
      C.Term (Finmap.singleton x s) Gamma Psi (.var x)
        (Basis.std (.space s)) w tauw := by
  obtain ⟨b, hmem, htof⟩ := hcov.1 x s Finmap.lookup_singleton_eq
  obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
  have hstored := hfuture.storedWF hroot.storedWF
  have hbv := checked_root_or_standard_lin_valid hfuture hmem htof hwf hside
  have hty := hstored x b hmem
  obtain ⟨tauv, htau⟩ := hexact Gamma Psi b hP hcov.drop_lin
    hstored (Finmap.singleton x s) hwf hbv hty
  exact checked_var_lin_of_store (hfuture.checkedStore hroot.store)
    hP hcov.drop_lin hstored hwf hlookup htof hbv htau

/-- Nonlinear-variable companion of `checked_var_lin_of_rootFuture`. -/
theorem checked_var_nlin_of_rootFuture
    (hexact : CheckedExactBasisTyProgress)
    {Psi0 Psi : EvalCtx} (hroot : CheckedStdStoreRoot Psi0)
    (hfuture : CheckedStdFuture Psi0 Psi)
    {Gamma : NLCtx} {x : VName} {tau : Ty}
    (hGamma : Gamma.lookup x = some tau)
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hside : CheckedLocalSideBases Psi0
      (HasType.var_nlin hGamma : HasType (∅ : LCtx) Gamma (.var x) tau)) :
    exists w tauw,
      C.Term (∅ : LCtx) Gamma Psi (.var x) (Basis.std tau) w tauw := by
  obtain ⟨b, hmem, htof⟩ := hcov.2 x tau hGamma
  obtain ⟨v, hlookup⟩ := Finmap.mem_iff.mp hmem
  have hstored := hfuture.storedWF hroot.storedWF
  have hbv := checked_root_or_standard_nlin_valid
    hfuture hmem htof hGamma hwf hside
  have hty := hstored x b hmem
  obtain ⟨tauv, htau⟩ := hexact Gamma Psi b hP hcov hstored
    (∅ : LCtx) hwf hbv hty
  exact checked_var_nlin_of_store (hfuture.checkedStore hroot.store)
    hP hcov hstored hwf hlookup hGamma htof hbv htau

def PromoteStoredBasisRestriction : Prop :=
  forall (lin Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx),
    Finmap.Disjoint lin Delta -> Finmap.Disjoint lin.toNL Gamma ->
    PromoteFresh lin Delta Gamma ->
    V2.TypingImplyEval Delta (lin.toNL ∪ Gamma) Psi ->
    forall x b, (x, b) ∈ Psi -> Basis.BasisValid Gamma b

def AmbientCheckedVariableUse : Prop :=
  forall (Delta : LCtx) (GammaTerm GammaSide : NLCtx) (Psi : EvalCtx)
    (x : VName) (b : Basis) (v : ValExpr) (tauv : ValTy),
    NLCtxIncl GammaTerm GammaSide ->
    EvalCtx.lookup Psi (x, b) = some v ->
    Basis.BasisValid GammaSide b ->
    C.TyAt GammaSide Psi b tauv ->
    ((exists s, Delta = Finmap.singleton x s /\
        Basis.tof b = .space s) \/
      (Delta = ∅ /\ GammaTerm.lookup x = some (Basis.tof b))) ->
    exists DeltaSide,
      C.Term DeltaSide GammaSide Psi (.var x) b v tauv

end RawCertifiedHereditaryStore
end GLang
