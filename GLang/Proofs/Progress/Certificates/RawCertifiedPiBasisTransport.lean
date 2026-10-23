import GLang.Proofs.Progress.Certificates.RawCertifiedCobProgress
import GLang.Proofs.Progress.DependentApplication
import GLang.Proofs.Progress.Certificates.RawCertifiedRename
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLift
import GLang.Proofs.Progress.Certificates.Depth.RawCertifiedExactLower
import GLang.Proofs.Progress.Certificates.Context.RawCertifiedContextMono
import GLang.Proofs.Adequacy.Foundations.StrengthenedMono

set_option maxHeartbeats 3200000
set_option maxRecDepth 6000

namespace GLang
namespace RawCertifiedPiBasisTransport

open RawCertifiedOperational
open RawCertifiedProgressScratch

private theorem validBasis_tof_tvalid {Gamma : NLCtx} {b : Basis}
    (hb : Basis.BasisValid Gamma b) :
    exists k, Nonempty (TValid Gamma (Basis.tof b) k) := by
  cases b
  case frame b0 b1 =>
    obtain ⟨_, _, k0, k1, ht⟩ := hb.frame_inv
    exact ⟨.arrow k0 k1, ht⟩
  all_goals
    obtain ⟨hs⟩ := hb.sof_valid
    exact ⟨.base, ⟨.space hs⟩⟩

private theorem ctxWF_insert_nl
    {Delta : LCtx} {Gamma : NLCtx} {y : Name} {b : Basis}
    (hwf : V2.CtxWF' Delta Gamma)
    (hyDelta : y ∉ Delta) (hyGamma : y ∉ Gamma)
    (hb : Basis.BasisValid Gamma b) :
    V2.CtxWF' Delta (Finmap.insert y (Basis.tof b) Gamma) where
  disjoint := by
    intro x hxDelta hxGamma'
    rcases Finmap.mem_insert.mp hxGamma' with rfl | hxGamma
    · exact hyDelta hxDelta
    · exact hwf.disjoint x hxDelta hxGamma
  lin_fv := by
    intro x s hx z hz
    exact Finmap.mem_keys.mpr <| Finmap.mem_insert.mpr <| Or.inr <|
      Finmap.mem_keys.mp (hwf.lin_fv x s hx hz)
  nl_fv := by
    intro x tau hx z hz
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hx
      obtain rfl := Option.some.inj hx
      exact Finmap.mem_keys.mpr <| Finmap.mem_insert.mpr <| Or.inr <|
        Finmap.mem_keys.mp
          (((Basis.fv_tof_subset b).trans hb.fv_subset_keys) hz)
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      exact Finmap.mem_keys.mpr <| Finmap.mem_insert.mpr <| Or.inr <|
        Finmap.mem_keys.mp (hwf.nl_fv x tau hx hz)
  lin_valid := by
    intro x s hx
    obtain ⟨hs⟩ := hwf.lin_valid x s hx
    exact ⟨hs.weakenInsertNL y (Basis.tof b) hyGamma⟩
  nl_valid := by
    intro x tau hx
    by_cases hxy : x = y
    · subst x
      rw [Finmap.lookup_insert] at hx
      obtain rfl := Option.some.inj hx
      obtain ⟨k, ⟨ht⟩⟩ := validBasis_tof_tvalid hb
      exact ⟨k, ⟨ht.weakenInsertNL y (Basis.tof b) hyGamma⟩⟩
    · rw [Finmap.lookup_insert_of_ne _ hxy] at hx
      obtain ⟨k, ⟨ht⟩⟩ := hwf.nl_valid x tau hx
      exact ⟨k, ⟨ht.weakenInsertNL y (Basis.tof b) hyGamma⟩⟩

/-! ## Cofinite packaging at an arbitrary frame key -/

theorem checkedTyAt_arbitrary_cofinite_of_fresh
    (laws : CheckedRenameLaws)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName}
    {tau0 : Ty} {tauV0 tauV : ValTy} {b0 b1 : Basis}
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (htau0 : exists k, Nonempty (TValid Gamma tau0 k))
    (htof0 : Basis.tof b0 = tau0) (hb0 : Basis.BasisValid Gamma b0)
    (hxGamma : x ∉ Gamma)
    (h : C.TyAt (Finmap.insert x tau0 Gamma)
      (Psi.extend x b0 (.var x tauV0))
      (Basis.openVar x b1) tauV)
    (hxPsi : x ∉ EvalCtx.avoidB Psi)
    (hxb0 : x ∉ Basis.fv b0)
    (hxtauV0 : x ∉ ValTy.fv tauV0)
    (hxb1 : x ∉ Basis.fv b1)
    (hlctauV0 : ValTy.lc tauV0)
    (hlctauV : ValTy.lc tauV) :
    exists L : Finset VName, forall y, y ∉ L ->
      C.TyAt (Finmap.insert y tau0 Gamma)
        (Psi.extend y b0 (.var y tauV0))
        (Basis.openVar y b1)
        (ValTy.openVar y tauV0 (ValTy.closeRec 0 x tauV)) := by
  refine ⟨EvalCtx.avoidB Psi ∪ Gamma.keys ∪ {x}, ?_⟩
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨hyPsi, hyGammaKeys⟩, hyx⟩ := hy
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  have hes := ESubst.rename hxPsi hyPsi hxb0 hxtauV0 hlctauV0
  have hr := laws.tyAt_nl hwf htau0 htof0 hb0 hxGamma hyGamma
    (Ne.symm hyx) hes h
  have hsrc : Basis.subst x (.var y) (Basis.openVar x b1) =
      Basis.openVar y b1 :=
    (Basis.subst_intro x (.var y) b1 hxb1 0).symm
  rw [hsrc] at hr
  rw [ValTy.openVar_closeRec_of_lc x y tauV0 hlctauV]
  exact hr

theorem checkedTerm_arbitrary_frameEta_cofinite_of_fresh
    (laws : CheckedRenameLaws)
    {Gamma : NLCtx} {Psi : EvalCtx} {x : VName}
    {tau0 : Ty} {tauV0 tauV : ValTy} {b0 b1 : Basis}
    {n0 : Term} {v : ValExpr}
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (htau0 : exists k, Nonempty (TValid Gamma tau0 k))
    (htof0 : Basis.tof b0 = tau0) (hb0 : Basis.BasisValid Gamma b0)
    (hxGamma : x ∉ Gamma)
    (h : C.Term (∅ : LCtx) (Finmap.insert x tau0 Gamma)
      (Psi.extend x b0 (.var x tauV0))
      (.appN n0 (.var x)) (Basis.openVar x b1) v tauV)
    (hxPsi : x ∉ EvalCtx.avoidB Psi)
    (hxb0 : x ∉ Basis.fv b0)
    (hxtauV0 : x ∉ ValTy.fv tauV0)
    (hxn0 : x ∉ Term.fv n0)
    (hxb1 : x ∉ Basis.fv b1)
    (hlctauV0 : ValTy.lc tauV0)
    (hlcv : ValExpr.lc v)
    (hlctauV : ValTy.lc tauV) :
    exists L : Finset VName, forall y, y ∉ L ->
      C.Term (∅ : LCtx) (Finmap.insert y tau0 Gamma)
        (Psi.extend y b0 (.var y tauV0))
        (.appN n0 (.var y)) (Basis.openVar y b1)
        (ValExpr.openVar y tauV0 (ValExpr.closeRec 0 x v))
        (ValTy.openVar y tauV0 (ValTy.closeRec 0 x tauV)) := by
  refine ⟨EvalCtx.avoidB Psi ∪ Gamma.keys ∪ {x}, ?_⟩
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  obtain ⟨⟨hyPsi, hyGammaKeys⟩, hyx⟩ := hy
  have hyGamma : y ∉ Gamma := by
    intro hm
    exact hyGammaKeys (Finmap.mem_keys.mpr hm)
  have hes := ESubst.rename hxPsi hyPsi hxb0 hxtauV0 hlctauV0
  have hr := laws.term_nl hwf htau0 htof0 hb0 hxGamma hyGamma
    (Ne.symm hyx) hes h
  have hsrcT : Term.subst x (.var y) (.appN n0 (.var x)) =
      .appN n0 (.var y) := by
    simp [Term.subst, Term.subst_fresh x (.var y) n0 hxn0]
  have hsrcB : Basis.subst x (.var y) (Basis.openVar x b1) =
      Basis.openVar y b1 :=
    (Basis.subst_intro x (.var y) b1 hxb1 0).symm
  rw [hsrcT, hsrcB] at hr
  rw [ValExpr.openVar_closeRec_of_lc x y tauV0 hlcv,
    ValTy.openVar_closeRec_of_lc x y tauV0 hlctauV]
  exact hr

/-! ## Source and checked-certificate inversions -/

private theorem right_empty_of_union_empty {A : Type}
    {a b : Finmap (fun _ : Name => A)}
    (h : a ∪ b = (∅ : Finmap (fun _ : Name => A))) :
    b = (∅ : Finmap (fun _ : Name => A)) := by
  apply Finmap.ext_lookup
  intro x
  rw [Finmap.lookup_empty]
  cases hx : b.lookup x with
  | none => rfl
  | some v =>
      have hm : x ∈ a ∪ b := Finmap.mem_union.mpr
        (Or.inr (Finmap.mem_of_lookup_eq_some hx))
      rw [h] at hm
      exact False.elim (Finmap.notMem_empty hm)

/-- A source term of dependent-function type cannot retain a linear
assumption.  The only nontrivial case is promotion; its recursive linear
context is `lin union Delta`, so emptiness of that union implies emptiness of
the surviving right summand. -/
private def PiLinearMotive
    (Delta : LCtx) (_Gamma : NLCtx) (_e : Term) (tau : Ty)
    (_h : HasType Delta _Gamma _e tau) : Prop :=
  forall tau0 tau1, tau = .piTy tau0 tau1 -> Delta = ∅

theorem HasType.pi_linear_empty
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau0 tau1 : Ty}
    (h : HasType Delta Gamma e (.piTy tau0 tau1)) : Delta = ∅ := by
  have result := HasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := PiLinearMotive)
    ?svEmpty ?svReal ?svDual ?svDsum ?svTprod
    ?svKer ?svCoker ?svImg ?svCoimg
    ?tvSpace ?tvPi
    ?subKer ?subCoker ?subImg ?subCoimg
    ?termZero ?termSmul ?termAdd ?termInner ?termReal
    ?termAppL ?termAppI ?termAppN ?termVarL ?termVarN
    ?termPinvT ?termPinvD ?termPromote ?termDsum ?termTprod
    ?termLlamReal ?termLlamTensor ?termEmbed ?termNllam h
  case termPromote =>
    intro Delta Gamma e tau lin hdDelta hdGamma hfresh hinner ih
      cod0 cod1 htau
    exact right_empty_of_union_empty (ih cod0 cod1 htau)
  all_goals try simp [PiLinearMotive]
  exact result tau0 tau1 rfl

/-! Exact checked inversions used by dependent-basis conversion. -/

/-! ## Small checked structural helpers -/

/-- Exact certificates weaken along a genuinely fresh evaluator name without
changing any source, basis, value, or realized-type index. -/
theorem checkedTyAt_extend
    (h : C.TyAt Gamma Psi b tauV) (hx : x ∉ EvalCtx.avoidB Psi) :
    C.TyAt Gamma (Psi.extend x bx vx) b tauV := by
  have hxnames : x ∉ Psi.names := by
    intro hm
    obtain ⟨⟨z, bz⟩, hkey, hz⟩ := Finset.mem_image.mp hm
    simp only at hz
    subst z
    exact (EvalCtx.avoidB_spec hx).1 bz (Finmap.mem_keys.mp hkey)
  exact S.TyAt.toC
    (h.toS.mono (EvalCtx.Subctx.extend_right_of_name_fresh hxnames bx vx))

theorem checkedTerm_extend
    (h : C.Term Delta Gamma Psi e b v tauV)
    (hx : x ∉ EvalCtx.avoidB Psi) :
    C.Term Delta Gamma (Psi.extend x bx vx) e b v tauV := by
  have hxnames : x ∉ Psi.names := by
    intro hm
    obtain ⟨⟨z, bz⟩, hkey, hz⟩ := Finset.mem_image.mp hm
    simp only at hz
    subst z
    exact (EvalCtx.avoidB_spec hx).1 bz (Finmap.mem_keys.mp hkey)
  exact S.Term.toC
    (h.toS.mono (EvalCtx.Subctx.extend_right_of_name_fresh hxnames bx vx))

/-- Cut a checked frame codomain with an already checked argument.  The
argument is first retagged to the frame's exact domain realization; the
existing reviewed application-cut boundary then removes the fresh source
placeholder. -/
theorem checkedCodomainCut
    (happCut : CheckedTyAtAppCut)
    {Gamma : NLCtx} {Psi : EvalCtx} {b0 b1 : Basis}
    {tauV0 tauV1 tauVArg : ValTy} {n : Term} {arg : ValExpr}
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (harg : C.Term (∅ : LCtx) Gamma Psi n b0 arg tauVArg)
    (hdom : C.TyAt Gamma Psi b0 tauV0)
    (L : Finset Name)
    (hcod : forall z, z ∉ L ->
      C.TyAt (Finmap.insert z (Basis.tof b0) Gamma)
        (Psi.extend z b0 (.var z tauV0))
        (Basis.openVar z b1) (ValTy.openVar z tauV0 tauV1)) :
    exists arg' tauVOut,
      C.Term (∅ : LCtx) Gamma Psi n b0 arg' tauV0 /\
      C.TyAt Gamma Psi (Basis.instantiate n b1) tauVOut := by
  let arg' := ValExpr.reshap arg tauV0 tauVArg
  have harg' : C.Term (∅ : LCtx) Gamma Psi n b0 arg' tauV0 := by
    exact RawCertifiedProgressScratch.retag harg hdom
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
    (EvalCtx.avoidB Psi ∪ L ∪ Basis.fv b0 ∪
      Basis.fv b1 ∪ ValTy.fv tauV0)
  simp only [Finset.mem_union, not_or] at hz
  obtain ⟨⟨⟨⟨hzPsi, hzL⟩, hzb0⟩, hzb1⟩, _hztauV0⟩ := hz
  obtain ⟨hzfresh, hzvals, hzbases⟩ := EvalCtx.avoidB_spec hzPsi
  have hztauV0 : z ∉ ValTy.fv tauV0 := by
    intro hm
    have hkn : z ∈ Psi.keyNames := V2.evalT_fv hdom.erase hP.1 hm
    exact hzPsi (V2.keyNames_subset_avoidB Psi hkn)
  have hzGamma : z ∉ Gamma := by
    intro hm
    obtain ⟨tau, hlookup⟩ := Finmap.mem_iff.mp hm
    obtain ⟨b, hmem, _htof⟩ := hcov.2 z tau hlookup
    have hkey : z ∈ Psi.keyNames := by
      exact Finset.mem_image.mpr
        ⟨(z, b), Finmap.mem_keys.mpr hmem, rfl⟩
    exact hzPsi (V2.keyNames_subset_avoidB Psi hkey)
  have hlcarg : ValExpr.lc arg :=
    opStep_lc harg.erase hP.1.toEvalCtxLc
  have hlctauV0 : ValTy.lc tauV0 :=
    evalT_lc hdom.erase hP.1.toEvalCtxLc
  have hlctauVArg : ValTy.lc tauVArg :=
    evalT_lc harg.tyAt.erase hP.1.toEvalCtxLc
  have hes := V2.appN_esubst
    (Ψ₀ := Psi) (y := z) (b₀ := b0) (τv₀ := tauV0)
    (n₁ := n) (env₁ := arg') hzfresh hzb0
    (fun q b v hl => hzvals (q, b) v hl)
    (fun q b v hl => hzbases q b (Finmap.mem_of_lookup_eq_some hl))
    harg.hasType.some.lc (.reshap hlcarg hlctauV0 hlctauVArg)
    (by
      simp only [arg', ValExpr.inferSpace]
      exact (ValSpace.subst_fresh z _ _
        (fun hm => hztauV0 (ValSpace.fv_spaceOf_subset tauV0 hm))).symm)
    (by simpa only [arg', ValExpr.inferType] using (ValTy.subst_fresh z _ tauV0 hztauV0).symm)
    harg'.erase
  have hargCut : C.Term (∅ : LCtx) Gamma Psi n
      (Basis.subst z n b0) arg'
      (ValTy.subst z arg' tauV0) := by
    simpa only [Basis.subst_fresh z n b0 hzb0,
      ValTy.subst_fresh z arg' tauV0 hztauV0] using harg'
  obtain ⟨tauVOut, hout⟩ := happCut hwf hP.1.toEvalCtxLc hzGamma hzb0
    hes hargCut hzb1 (hcod z hzL)
  exact ⟨arg', tauVOut, harg', hout⟩

/-! ## WF-indexed fuel statements -/

/-- The only space-specific service used by the simultaneous higher-order
transport induction.  Factoring it with an explicit source-WF premise lets a
scoped COB development instantiate the induction without claiming COB for
unrelated or ill-formed source contexts. -/
def CheckedSpaceTermTransportWF : Prop :=
  forall {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx} {e : Term}
    {b1 b2 : Basis} {v1 : ValExpr} {sv : ValSpace},
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
    Basis.BasisValid Gamma b1 -> Basis.IsSpaceBasis b1 ->
    Basis.BasisValid Gamma b2 -> Basis.IsSpaceBasis b2 ->
    Basis.tof b2 = Basis.tof b1 ->
    C.Term Delta Gamma Psi e b1 v1 (.space sv) ->
    exists v2 tauV2, C.Term Delta Gamma Psi e b2 v2 tauV2

def CheckedTyAtTransportN (n : Nat) : Prop :=
  forall (Gamma : NLCtx) (Psi : EvalCtx) (b1 b2 : Basis) (tauV1 : ValTy),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
    Basis.BasisValid Gamma b1 -> Basis.IsTyBasis b1 ->
    Basis.BasisValid Gamma b2 -> Basis.IsTyBasis b2 ->
    Basis.tof b2 = Basis.tof b1 ->
    Ty.size (Basis.tof b1) <= n ->
    C.TyAt Gamma Psi b1 tauV1 ->
    exists tauV2, C.TyAt Gamma Psi b2 tauV2

def CheckedTermTransportN (n : Nat) : Prop :=
  forall (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (e : Term)
    (b1 b2 : Basis) (v1 : ValExpr) (tauV1 : ValTy),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
    Basis.BasisValid Gamma b1 -> Basis.IsTyBasis b1 ->
    Basis.BasisValid Gamma b2 -> Basis.IsTyBasis b2 ->
    Basis.tof b2 = Basis.tof b1 ->
    Ty.size (Basis.tof b1) <= n ->
    C.Term Delta Gamma Psi e b1 v1 tauV1 ->
    exists v2 tauV2, C.Term Delta Gamma Psi e b2 v2 tauV2

def CheckedTransportN (n : Nat) : Prop :=
  CheckedTermTransportN n /\ CheckedTyAtTransportN n

/-! ## Strong induction -/

/-- Simultaneous checked transport of terms and their exact basis-indexed
type certificates.  The only higher-order structural input is the explicitly
named arbitrary-key alpha law. -/
theorem checkedTransportN_of_spaceTransport
    (hspaceTransport : CheckedSpaceTermTransportWF)
    (hren : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut) : forall n, CheckedTransportN n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hTy : CheckedTyAtTransportN n := by
      intro Gamma Psi b1 b2 tauV1 hP hcov hstored hwf
        hb1 hity1 hb2 hity2 htofeq hsize hsourceAt
      cases hsource : Basis.tof b1 with
      | space s =>
          have htarget : Basis.tof b2 = .space s := htofeq.trans hsource
          obtain ⟨sv, rfl, hspace⟩ :=
            checkedTyAt_space_inv_full hsource hsourceAt
          have hsof : Basis.sof b2 = Basis.sof b1 := by
            rw [V2.sof_of_tof_eq_space htarget,
              V2.sof_of_tof_eq_space hsource]
          have hshape2 : Basis.tof b2 = .space (Basis.sof b2) := by
            rw [htarget, V2.sof_of_tof_eq_space htarget]
          exact ⟨.space sv, .space hshape2 hb2 (by rwa [hsof])⟩
      | piTy tau0 tau1 =>
          obtain ⟨b10, b11, rfl, htof10, htof11⟩ :=
            Basis.tof_piTy_inv hsource
          obtain ⟨b20, b21, rfl, htof20, htof21⟩ :=
            Basis.tof_piTy_inv (htofeq.trans hsource)
          rw [hsource] at hsize
          simp only [Ty.size] at hsize
          have hsmall0 : Ty.size tau0 < n := by omega
          have hsmall1 : Ty.size tau1 < n := by omega

          obtain ⟨hb10, ⟨Lv1, hb11⟩, _⟩ := hb1.frame_inv
          obtain ⟨hb20, ⟨Lv2, hb21⟩, k0, k1, ⟨hTpi⟩⟩ := hb2.frame_inv
          rw [htof20, htof21] at hTpi
          cases hTpi with
          | piTy LT hT0 hT1 =>
          obtain ⟨hi10, hi11⟩ := hity1
          obtain ⟨hi20, hi21⟩ := hity2
          obtain ⟨tauV10, tauV11, rfl, hdom10, Lsrc0, hcod10⟩ :=
            checkedTyAt_frame_inv_full hsourceAt
          obtain ⟨tauV20, hdom20⟩ :=
            (ih (Ty.size tau0) hsmall0).2 Gamma Psi b10 b20 tauV10
              hP hcov hstored hwf hb10 hi10 hb20 hi20
              (htof20.trans htof10.symm)
              (by rw [htof10]) hdom10

          obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
            (EvalCtx.avoidB Psi ∪ Gamma.keys ∪ Lv1 ∪ Lv2 ∪
              Basis.fv b20 ∪ Basis.fv b21 ∪ ValTy.fv tauV20)
          simp only [Finset.mem_union, not_or] at hx
          obtain ⟨⟨⟨⟨⟨⟨hxPsi, hxGammaKeys⟩, hxLv1⟩, hxLv2⟩,
            hxb20⟩, hxb21⟩, hxtauV20⟩ := hx
          have hxGamma : x ∉ Gamma := by
            intro hm
            exact hxGammaKeys (Finmap.mem_keys.mpr hm)
          have hfresh : (x, b20) ∉ Psi :=
            (EvalCtx.avoidB_spec hxPsi).1 b20
          obtain ⟨hPx, hcovx, hstoredx⟩ :=
            V2.pcarrier_extend_transport (V2.transportN (Ty.size tau0))
              hP hcov hstored hb20 hi20 hdom20.erase hfresh
              (by rw [htof20])
          rw [htof20] at hcovx
          have hwfx : V2.CtxWF' (∅ : LCtx)
              (Finmap.insert x tau0 Gamma) := by
            have h := ctxWF_insert_nl
              (b := b20) hwf Finmap.notMem_empty hxGamma hb20
            rwa [htof20] at h
          have hinc : NLCtxIncl Gamma (Finmap.insert x tau0 Gamma) :=
            (NLCtxIncl.refl Gamma).insert_right hxGamma tau0
          have hb20x : Basis.BasisValid (Finmap.insert x tau0 Gamma) b20 :=
            raw_basisValid_mono hb20 hinc
          have hb10x : Basis.BasisValid (Finmap.insert x tau0 Gamma) b10 :=
            raw_basisValid_mono hb10 hinc
          have hdom20x : C.TyAt (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) b20 tauV20 :=
            C.TyAt.weaken (checkedTyAt_extend hdom20 hxPsi) hinc
          have hvar20 : C.Term (∅ : LCtx) (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) (.var x) b20
              (.var x tauV20) tauV20 := by
            apply C.Term.var_nlin
            · rw [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]
            · rw [Finmap.lookup_insert, htof20]
            · exact hb20x
            · exact hdom20x
          obtain ⟨arg10, tauVArg, harg10⟩ :=
            (ih (Ty.size tau0) hsmall0).1 (∅ : LCtx)
              (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) (.var x)
              b20 b10 (.var x tauV20) tauV20 hPx hcovx hstoredx hwfx
              hb20x hi20 hb10x hi10 (htof10.trans htof20.symm)
              (by rw [htof20]) hvar20

          have hsourceAtX0 := checkedTyAt_extend
            (x := x) (bx := b20) (vx := .var x tauV20) hsourceAt hxPsi
          have hsourceAtX : C.TyAt (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) (.frame b10 b11)
              (.piTy tauV10 tauV11) := by
            exact C.TyAt.weaken hsourceAtX0 hinc
          obtain ⟨tauV10x, tauV11x, _hsrcV, hdom10x, Lsrc, hcodSrc⟩ :=
            checkedTyAt_frame_inv_full hsourceAtX
          obtain ⟨arg10', tauVCut, harg10', hcut⟩ :=
            checkedCodomainCut happCut hPx hcovx hwfx harg10 hdom10x Lsrc hcodSrc

          have hb11x : Basis.BasisValid (Finmap.insert x tau0 Gamma)
              (Basis.openVar x b11) := by
            have h := hb11 x hxLv1
            rwa [htof10] at h
          have hb21x : Basis.BasisValid (Finmap.insert x tau0 Gamma)
              (Basis.openVar x b21) := by
            have h := hb21 x hxLv2
            rwa [htof20] at h
          have htofcod : Basis.tof (Basis.openVar x b21) =
              Basis.tof (Basis.openVar x b11) := by
            show Basis.tof (Basis.openRec 0 (.var x) b21) =
              Basis.tof (Basis.openRec 0 (.var x) b11)
            rw [Basis.tof_openRec, Basis.tof_openRec, htof21, htof11]
          have hsizecod : Ty.size (Basis.tof (Basis.openVar x b11)) <=
              Ty.size tau1 := by
            show Ty.size (Basis.tof (Basis.openRec 0 (.var x) b11)) <=
              Ty.size tau1
            rw [Basis.tof_openRec, htof11]
            exact le_of_eq (Ty.size_openVar 0 x tau1)
          have hcut' : C.TyAt (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20))
              (Basis.openVar x b11) tauVCut := by
            simpa only [Basis.instantiate] using hcut
          obtain ⟨tauVOut, hout⟩ :=
            (ih (Ty.size tau1) hsmall1).2 (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20))
              (Basis.openVar x b11) (Basis.openVar x b21) tauVCut
              hPx hcovx hstoredx hwfx hb11x
              (Basis.IsTyBasis.openRec (.var x) 0 hi11) hb21x
              (Basis.IsTyBasis.openRec (.var x) 0 hi21) htofcod
              hsizecod hcut'
          have hlctauV20 : ValTy.lc tauV20 :=
            evalT_lc hdom20.erase hP.1.toEvalCtxLc
          have hlctauVOut : ValTy.lc tauVOut :=
            evalT_lc hout.erase hPx.1.toEvalCtxLc
          obtain ⟨Lout, hcodOut⟩ :=
            checkedTyAt_arbitrary_cofinite_of_fresh hren hwf
              ⟨k0, ⟨hT0⟩⟩ htof20 hb20 hxGamma hout hxPsi hxb20
              hxtauV20 hxb21 hlctauV20 hlctauVOut
          rw [← htof20] at hcodOut
          exact ⟨.piTy tauV20 (ValTy.closeRec 0 x tauVOut),
            .frame hb2 hdom20 Lout hcodOut⟩

    have hTerm : CheckedTermTransportN n := by
      intro Delta Gamma Psi e b1 b2 v1 tauV1 hP hcov hstored hwf
        hb1 hity1 hb2 hity2 htofeq hsize hterm
      cases hsource : Basis.tof b1 with
      | space s =>
          have hs1 : Basis.IsSpaceBasis b1 :=
            hity1.toIsSpaceBasis (Basis.ne_frame_of_tof_space hsource)
          have hs2 : Basis.IsSpaceBasis b2 :=
            hity2.toIsSpaceBasis
              (Basis.ne_frame_of_tof_space (htofeq.trans hsource))
          obtain ⟨sv, htauV1, _⟩ :=
            checkedTyAt_space_inv_full hsource hterm.tyAt
          subst tauV1
          exact hspaceTransport hP hcov hstored hwf
            hb1 hs1 hb2 hs2 htofeq hterm
      | piTy tau0 tau1 =>
          obtain ⟨hsourceTyping⟩ := hterm.hasType
          have hsourceTyping' : HasType Delta Gamma e (.piTy tau0 tau1) := by
            rwa [hsource] at hsourceTyping
          have hDelta : Delta = ∅ := HasType.pi_linear_empty hsourceTyping'
          subst Delta
          obtain ⟨b10, b11, rfl, htof10, htof11⟩ :=
            Basis.tof_piTy_inv hsource
          obtain ⟨b20, b21, rfl, htof20, htof21⟩ :=
            Basis.tof_piTy_inv (htofeq.trans hsource)
          rw [hsource] at hsize
          simp only [Ty.size] at hsize
          have hsmall0 : Ty.size tau0 < n := by omega
          have hsmall1 : Ty.size tau1 < n := by omega
          obtain ⟨hb10, ⟨Lv1, hb11⟩, _⟩ := hb1.frame_inv
          obtain ⟨hb20, ⟨Lv2, hb21⟩, k0, k1, ⟨hTpi⟩⟩ := hb2.frame_inv
          rw [htof20, htof21] at hTpi
          cases hTpi with
          | piTy LT hT0 hT1 =>
          obtain ⟨hi10, hi11⟩ := hity1
          obtain ⟨hi20, hi21⟩ := hity2
          obtain ⟨tauV2, htargetAt⟩ := hTy Gamma Psi
            (.frame b10 b11) (.frame b20 b21) tauV1 hP hcov hstored hwf
            hb1 ⟨hi10, hi11⟩ hb2 ⟨hi20, hi21⟩ htofeq
            (by simpa only [Basis.tof, Ty.size, htof10, htof11] using hsize)
            hterm.tyAt
          obtain ⟨tauV10, tauV11, rfl, hdom10, Lsrc, hcod10⟩ :=
            checkedTyAt_frame_inv_full hterm.tyAt
          obtain ⟨tauV20, tauV21, rfl, hdom20, Ltgt, hcod20⟩ :=
            checkedTyAt_frame_inv_full htargetAt

          obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset
            (EvalCtx.avoidB Psi ∪ Gamma.keys ∪ Lv1 ∪ Lv2 ∪ Lsrc ∪ Ltgt ∪
              Basis.fv b20 ∪ Basis.fv b21 ∪ Term.fv e ∪
              ValTy.fv tauV20)
          simp only [Finset.mem_union, not_or] at hx
          obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hxPsi, hxGammaKeys⟩, hxLv1⟩, hxLv2⟩,
            hxLsrc⟩, hxLtgt⟩, hxb20⟩, hxb21⟩, hxe⟩, hxtauV20⟩ := hx
          have hxGamma : x ∉ Gamma := by
            intro hm
            exact hxGammaKeys (Finmap.mem_keys.mpr hm)
          have hfresh : (x, b20) ∉ Psi :=
            (EvalCtx.avoidB_spec hxPsi).1 b20
          obtain ⟨hPx, hcovx, hstoredx⟩ :=
            V2.pcarrier_extend_transport (V2.transportN (Ty.size tau0))
              hP hcov hstored hb20 hi20 hdom20.erase hfresh
              (by rw [htof20])
          rw [htof20] at hcovx
          have hwfx : V2.CtxWF' (∅ : LCtx)
              (Finmap.insert x tau0 Gamma) := by
            have h := ctxWF_insert_nl
              (b := b20) hwf Finmap.notMem_empty hxGamma hb20
            rwa [htof20] at h
          have hinc : NLCtxIncl Gamma (Finmap.insert x tau0 Gamma) :=
            (NLCtxIncl.refl Gamma).insert_right hxGamma tau0
          have hb20x : Basis.BasisValid (Finmap.insert x tau0 Gamma) b20 :=
            raw_basisValid_mono hb20 hinc
          have hb10x : Basis.BasisValid (Finmap.insert x tau0 Gamma) b10 :=
            raw_basisValid_mono hb10 hinc
          have hdom20x : C.TyAt (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) b20 tauV20 :=
            C.TyAt.weaken (checkedTyAt_extend hdom20 hxPsi) hinc
          have hvar20 : C.Term (∅ : LCtx) (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) (.var x) b20
              (.var x tauV20) tauV20 := by
            apply C.Term.var_nlin
            · rw [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]
            · rw [Finmap.lookup_insert, htof20]
            · exact hb20x
            · exact hdom20x
          obtain ⟨arg10, tauVArg, harg10⟩ :=
            (ih (Ty.size tau0) hsmall0).1 (∅ : LCtx)
              (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) (.var x)
              b20 b10 (.var x tauV20) tauV20 hPx hcovx hstoredx hwfx
              hb20x hi20 hb10x hi10 (htof10.trans htof20.symm)
              (by rw [htof20]) hvar20

          have htypedX : Nonempty (HasType (∅ : LCtx)
              (Finmap.insert x tau0 Gamma) e (Basis.tof (.frame b10 b11))) :=
            hasType_mono_nl_checked hterm.hasType hinc
              (fun _ hm => False.elim (Finmap.notMem_empty hm))
          have hsourceAtX : C.TyAt (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) (.frame b10 b11)
              (.piTy tauV10 tauV11) :=
            C.TyAt.weaken (checkedTyAt_extend hterm.tyAt hxPsi) hinc
          have hfunX : C.Term (∅ : LCtx) (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) e (.frame b10 b11) v1
              (.piTy tauV10 tauV11) :=
            C.Term.weaken (checkedTerm_extend hterm hxPsi) hinc (Graded.CtxDisj.empty _)
          obtain ⟨tauV10x, tauV11x, _hsrcV, hdom10x, LsrcX, hcodSrcX⟩ :=
            checkedTyAt_frame_inv_full hfunX.tyAt
          obtain ⟨arg10', tauVCut, harg10', hcut⟩ :=
            checkedCodomainCut happCut hPx hcovx hwfx harg10 hdom10x LsrcX hcodSrcX
          have happTyped : Nonempty (HasType (∅ : LCtx)
              (Finmap.insert x tau0 Gamma) (.appN e (.var x))
              (Basis.tof (Basis.instantiate (.var x) b11))) := by
            obtain ⟨hf⟩ := hfunX.hasType
            obtain ⟨ha⟩ := harg10'.hasType
            refine ⟨?_⟩
            simpa only [Basis.tof, Basis.instantiate, Basis.tof_openRec,
              Ty.instantiate] using HasType.app_nonlinear hf ha
          have hb11x : Basis.BasisValid (Finmap.insert x tau0 Gamma)
              (Basis.openVar x b11) := by
            have h := hb11 x hxLv1
            rwa [htof10] at h
          have hb21x : Basis.BasisValid (Finmap.insert x tau0 Gamma)
              (Basis.openVar x b21) := by
            have h := hb21 x hxLv2
            rwa [htof20] at h
          have happ : C.Term (∅ : LCtx) (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) (.appN e (.var x))
              (Basis.openVar x b11) (.applyAt v1 arg10' tauVCut) tauVCut := by
            have happ0 := C.Term.appN_val happTyped hb11x hcut hfunX harg10'
            simpa only [Basis.instantiate] using happ0
          have htofcod : Basis.tof (Basis.openVar x b21) =
              Basis.tof (Basis.openVar x b11) := by
            show Basis.tof (Basis.openRec 0 (.var x) b21) =
              Basis.tof (Basis.openRec 0 (.var x) b11)
            rw [Basis.tof_openRec, Basis.tof_openRec, htof21, htof11]
          have hsizecod : Ty.size (Basis.tof (Basis.openVar x b11)) <=
              Ty.size tau1 := by
            show Ty.size (Basis.tof (Basis.openRec 0 (.var x) b11)) <=
              Ty.size tau1
            rw [Basis.tof_openRec, htof11]
            exact le_of_eq (Ty.size_openVar 0 x tau1)
          obtain ⟨w, tauVW, hw⟩ :=
            (ih (Ty.size tau1) hsmall1).1 (∅ : LCtx)
              (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) (.appN e (.var x))
              (Basis.openVar x b11) (Basis.openVar x b21)
              (.applyAt v1 arg10' tauVCut) tauVCut hPx hcovx hstoredx hwfx
              hb11x (Basis.IsTyBasis.openRec (.var x) 0 hi11)
              hb21x (Basis.IsTyBasis.openRec (.var x) 0 hi21)
              htofcod hsizecod happ
          have htargetCodX := hcod20 x hxLtgt
          rw [htof20] at htargetCodX
          have hw' : C.Term (∅ : LCtx) (Finmap.insert x tau0 Gamma)
              (Psi.extend x b20 (.var x tauV20)) (.appN e (.var x))
              (Basis.openVar x b21) _
              (ValTy.openVar x tauV20 tauV21) :=
            RawCertifiedProgressScratch.retag hw htargetCodX
          have hlctauV20 : ValTy.lc tauV20 :=
            evalT_lc hdom20.erase hP.1.toEvalCtxLc
          have hlcw : ValExpr.lc _ :=
            opStep_lc hw'.erase hPx.1.toEvalCtxLc
          have hlctauVW : ValTy.lc (ValTy.openVar x tauV20 tauV21) :=
            evalT_lc htargetCodX.erase hPx.1.toEvalCtxLc
          obtain ⟨Lbody, hbody⟩ :=
            checkedTerm_arbitrary_frameEta_cofinite_of_fresh hren hwf
              ⟨k0, ⟨hT0⟩⟩ htof20 hb20 hxGamma hw' hxPsi hxb20
              hxtauV20 hxe hxb21 hlctauV20 hlcw hlctauVW
          rw [← htof20] at hbody
          let tauVOut := ValTy.closeRec 0 x (ValTy.openVar x tauV20 tauV21)
          let bodyOut := ValExpr.closeRec 0 x
            (ValExpr.reshap w (ValTy.openVar x tauV20 tauV21) tauVW)
          have htargetAt' : C.TyAt Gamma Psi (.frame b20 b21)
              (.piTy tauV20 tauVOut) := by
            apply C.TyAt.frame hb2 hdom20 Lbody _
            intro y hy
            exact (hbody y hy).tyAt
          have htypedTarget : Nonempty (HasType (∅ : LCtx) Gamma e
              (Basis.tof (.frame b20 b21))) := by
            rw [htofeq]
            exact hterm.hasType
          exact ⟨.vlam tauV20 tauVOut (.reshap bodyOut tauVOut tauVOut),
            .piTy tauV20 tauVOut,
            C.Term.frame_eta htypedTarget hb2 htargetAt' hdom20 Lbody
              hbody (fun y hy => (hbody y hy).tyAt)⟩
    exact ⟨hTerm, hTy⟩

theorem checkedTransportN
    (hcob : CheckedCobToStd)
    (hren : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut) : forall n, CheckedTransportN n := by
  apply checkedTransportN_of_spaceTransport
  · intro Delta Gamma Psi e b1 b2 v1 sv hP hcov hstored _hwf
      hb1 hs1 hb2 hs2 htofeq hterm
    obtain ⟨_env, _hcob, htarget⟩ :=
      checkedSpaceTermTransport_of_toStd hcob hP hcov hstored
        hb1 hs1 hb2 hs2 htofeq hterm
    exact ⟨_, _, htarget⟩
  · exact hren
  · exact happCut

/-! ## Public WF-indexed interfaces -/

/-- The honest higher-order transport seam.  It is the existing
`CheckedPiBasisTransport` statement with the source context well-formedness
needed by checked alpha transport made explicit. -/
def CheckedPiBasisTransportWF : Prop :=
  forall (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (e : Term)
    (tau0 tau1 : Ty) (b1 b2 : Basis) (v1 : ValExpr) (tauV1 : ValTy),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
    Basis.BasisValid Gamma b1 -> Basis.IsTyBasis b1 ->
    Basis.BasisValid Gamma b2 -> Basis.IsTyBasis b2 ->
    Basis.tof b1 = .piTy tau0 tau1 ->
    Basis.tof b2 = Basis.tof b1 ->
    C.Term Delta Gamma Psi e b1 v1 tauV1 ->
    exists v2 tauV2, C.Term Delta Gamma Psi e b2 v2 tauV2

/-- The constructive higher-order result, conditional only on the exact
arbitrary-key checked alpha law and the already separated checked app-cut
interface. -/
theorem checkedPiBasisTransportWF_of_arbitraryRename
    (hcob : CheckedCobToStd)
    (hren : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut) : CheckedPiBasisTransportWF := by
  intro Delta Gamma Psi e tau0 tau1 b1 b2 v1 tauV1
    hP hcov hstored hwf hb1 hity1 hb2 hity2 _hpi htofeq hterm
  exact (checkedTransportN hcob hren happCut (Ty.size (Basis.tof b1))).1
    Delta Gamma Psi e b1 b2 v1 tauV1 hP hcov hstored hwf
    hb1 hity1 hb2 hity2 htofeq (le_refl _) hterm

/-- Full arbitrary-basis checked term transport with the same explicit
source-WF premise.  Its space branch is discharged by checked COB progress;
its Pi branch is the construction above. -/
def CheckedBasisTransportWF : Prop :=
  forall (Delta : LCtx) (Gamma : NLCtx) (Psi : EvalCtx) (e : Term)
    (b1 b2 : Basis) (v1 : ValExpr) (tauV1 : ValTy),
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' Delta Gamma ->
    Basis.BasisValid Gamma b1 -> Basis.IsTyBasis b1 ->
    Basis.BasisValid Gamma b2 -> Basis.IsTyBasis b2 ->
    Basis.tof b2 = Basis.tof b1 ->
    C.Term Delta Gamma Psi e b1 v1 tauV1 ->
    exists v2 tauV2, C.Term Delta Gamma Psi e b2 v2 tauV2

theorem checkedBasisTransportWF_of_arbitraryRename
    (hcob : CheckedCobToStd)
    (hren : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut) : CheckedBasisTransportWF := by
  intro Delta Gamma Psi e b1 b2 v1 tauV1
    hP hcov hstored hwf hb1 hity1 hb2 hity2 htofeq hterm
  exact (checkedTransportN hcob hren happCut (Ty.size (Basis.tof b1))).1
    Delta Gamma Psi e b1 b2 v1 tauV1 hP hcov hstored hwf
    hb1 hity1 hb2 hity2 htofeq (le_refl _) hterm

/-- Exact type anchors transport at the same fuel and under the same
arbitrary-key alpha premise.  This projection is useful to consumers that
need the target `C.TyAt` before constructing a target term. -/
theorem checkedTyAtTransportWF_of_arbitraryRename
    (hcob : CheckedCobToStd)
    (hren : CheckedRenameLaws)
    (happCut : CheckedTyAtAppCut)
    {Gamma : NLCtx} {Psi : EvalCtx} {b1 b2 : Basis} {tauV1 : ValTy}
    (hP : V2.PCarrier Psi)
    (hcov : V2.VarsCovered (∅ : LCtx) Gamma Psi)
    (hstored : V2.StoredWF Psi)
    (hwf : V2.CtxWF' (∅ : LCtx) Gamma)
    (hb1 : Basis.BasisValid Gamma b1) (hity1 : Basis.IsTyBasis b1)
    (hb2 : Basis.BasisValid Gamma b2) (hity2 : Basis.IsTyBasis b2)
    (htofeq : Basis.tof b2 = Basis.tof b1)
    (hsource : C.TyAt Gamma Psi b1 tauV1) :
    exists tauV2, C.TyAt Gamma Psi b2 tauV2 := by
  exact (checkedTransportN hcob hren happCut (Ty.size (Basis.tof b1))).2
    Gamma Psi b1 b2 tauV1 hP hcov hstored hwf
    hb1 hity1 hb2 hity2 htofeq (le_refl _) hsource

end RawCertifiedPiBasisTransport
end GLang
