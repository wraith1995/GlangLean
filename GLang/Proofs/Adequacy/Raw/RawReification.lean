import GLang.Proofs.Adequacy.Raw.RawNonBetaValueKernel
import GLang.Proofs.Adequacy.Foundations.OpenBridgeCore
import GLang.Proofs.Source.BasisSoundness
import GLang.Proofs.Source.Substitution

/-!
# Constructive non-vacuity for raw dimension agreement

`RawAgreeDimsAt` is the recursive equality proved by the adequacy mutual.  At
a dependent function it deliberately follows the application-facing shape of
`RawAgree`: its codomain premise is available for every *represented* source
argument.  Read alone, that implication could be vacuous.

This module proves constructively that a valid syntactic basis represents
every source element and that such a representation determines its source
element.  The canonical public `AgreeDimsAt` packages those two facts with the
raw dimension equality.  Internal adequacy proofs can continue to use the
lighter `RawAgreeDimsAt` relation.
-/

namespace GLang

/-- Semantic basis soundness in the exact recursive fibers used by
`RawAgree`.  At a dependent function this records both its domain basis and
the actual codomain basis at every source argument. -/
noncomputable def RawBasisAt (sigma : DEnv) :
    List DVal -> Ty -> BasisDenot -> Prop
  | Ds, .space s, B =>
      IsListBasis (denotSpaceAux sigma Ds s)
        (B.atSpace (denotSpaceAux sigma Ds s))
  | Ds, .piTy tau0 tau1, B =>
      let T0 := denotTyAux sigma Ds tau0
      RawBasisAt sigma Ds tau0 B.domainBasis /\
      forall x' : T0.El,
        RawBasisAt sigma (T0.embed x' :: Ds) tau1 (B.applyEl x')
  termination_by _ tau _ => Ty.size tau
  decreasing_by all_goals simp only [Ty.size]; omega

/-- Every source element has a raw representative at this exact basis. -/
def RawReifiableAt (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    (Ds : List DVal) (Gv : List ValTy) (Dv : List ValValSem)
    (tau : Ty) (tauv : ValTy) (B : BasisDenot) : Prop :=
  forall x' : (denotTyAux sigma Ds tau).El,
    exists raw : ValValSem,
      RawAgree orc sigma rho Ds Gv Dv tau tauv B
        ((denotTyAux sigma Ds tau).embed x') raw

/-- A raw representative at a sound basis determines at most one source
element.  This companion fact makes dependent-function reification independent
of the existential representative chosen for a decoded argument. -/
def RawSourceInjectiveAt (orc : FFSOracleSem) (sigma : DEnv)
    (rho : ValEnvSem) (Ds : List DVal) (Gv : List ValTy)
    (Dv : List ValValSem) (tau : Ty) (tauv : ValTy)
    (B : BasisDenot) : Prop :=
  forall (x0 x1 : (denotTyAux sigma Ds tau).El) (raw : ValValSem),
    RawAgree orc sigma rho Ds Gv Dv tau tauv B
        ((denotTyAux sigma Ds tau).embed x0) raw ->
    RawAgree orc sigma rho Ds Gv Dv tau tauv B
        ((denotTyAux sigma Ds tau).embed x1) raw ->
    x0 = x1

/-- Canonical, non-vacuous dimension agreement.  `raw` is the equality used
by the direct mutual proof.  `basis` retains recursive basis soundness, so the
domain and every reached codomain can be reified as well.  `reifiable` and
`sourceInjective` expose the constructive consequences at the current type. -/
structure AgreeDimsAt (orc : FFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    (Ds : List DVal) (Gv : List ValTy) (Dv : List ValValSem)
    (tau : Ty) (tauv : ValTy) (B : BasisDenot) : Prop where
  raw : RawAgreeDimsAt orc sigma rho Ds Gv Dv tau tauv B
  basis : RawBasisAt sigma Ds tau B
  reifiable : RawReifiableAt orc sigma rho Ds Gv Dv tau tauv B
  sourceInjective :
    RawSourceInjectiveAt orc sigma rho Ds Gv Dv tau tauv B

/-- The ordinary public dimension-agreement name remains basis-indexed. -/
abbrev AgreeDims := AgreeDimsAt

/-- The constructive reification package proved below. -/
def RawReificationClaim (orc : FFSOracleSem) : Prop :=
  forall {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot},
    RawBasisAt sigma Ds tau B ->
    RawAgreeDimsAt orc sigma rho Ds Gv Dv tau tauv B ->
    RawReifiableAt orc sigma rho Ds Gv Dv tau tauv B /\
      RawSourceInjectiveAt orc sigma rho Ds Gv Dv tau tauv B

private theorem rawReification_srcShp_foldr (sigma : DEnv)
    (Ds : List DVal) : forall s : Space,
      (srcShp sigma Ds s).foldr (· * ·) 1 =
        Module.finrank Real (denotSpaceAux sigma Ds s).carrier
  | .empty => by
      simp only [srcShp, List.foldr, denotSpaceAux]
      exact (Module.finrank_zero_of_subsingleton
        (R := Real) (M := PUnit)).symm
  | .real => by
      simp only [srcShp, List.foldr, denotSpaceAux]
      exact (Module.finrank_self Real).symm
  | .dual s => by
      have ih := rawReification_srcShp_foldr sigma Ds s
      simp only [srcShp, denotSpaceAux]
      rw [ih]
      exact (Subspace.dual_finrank_eq
        (K := Real) (V := (denotSpaceAux sigma Ds s).carrier)).symm
  | .dsum _ _ => by
      simp only [srcShp, List.foldr, denotSpaceAux, Nat.mul_one]
      exact (Module.finrank_prod (R := Real)).symm
  | .tprod _ _ => by
      simp only [srcShp, List.foldr, denotSpaceAux, Nat.mul_one]
      exact (Module.finrank_tensorProduct (R := Real)).symm
  | .ker _ _ _ => by simp [srcShp]
  | .coker _ _ _ => by simp [srcShp]
  | .img _ _ _ => by simp [srcShp]
  | .coimg _ _ _ => by simp [srcShp]

private theorem rawReification_dof_eq_finrank_of_shpOf
    {orc : FFSOracle} {sv : ValSpace} {sigma : DEnv}
    {Ds : List DVal} {s : Space}
    (h : ValSpace.shpOf orc sv = srcShp sigma Ds s) :
    ValSpace.dof orc sv =
      Module.finrank Real (denotSpaceAux sigma Ds s).carrier := by
  unfold ValSpace.dof
  rw [h]
  exact rawReification_srcShp_foldr sigma Ds s

/-- Finite coordinates of `x` in a list basis. -/
private noncomputable def basisCoordsArray {V : HSpace}
    {vs : List V.carrier} (hB : IsListBasis V vs) (x : V.carrier) :
    FlatArray :=
  FlatArray.ofFn vs.length fun i =>
    if hi : i < vs.length then hB.coords x ⟨i, hi⟩ else 0

private theorem basisCoordsArray_expands {V : HSpace}
    {vs : List V.carrier} (hB : IsListBasis V vs) (x : V.carrier) :
    x = ∑ i : Fin vs.length,
      (basisCoordsArray hB x).get i.val • vs.getD i.val 0 := by
  calc
    x = ∑ i : Fin vs.length, hB.coords x i • vs.get i :=
      (hB.sum_coords_smul x).symm
    _ = ∑ i : Fin vs.length,
        (basisCoordsArray hB x).get i.val • vs.getD i.val 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have hget : vs.getD i.val 0 = vs.get i := by
        rw [List.getD_eq_getElem vs 0 i.isLt, List.get_eq_getElem]
      rw [hget]
      simp only [basisCoordsArray, FlatArray.get_ofFn_lt _ _ _ i.isLt,
        dif_pos i.isLt]

/-- A sound semantic basis plus raw dimension agreement constructively
reifies every source element and makes representation source-injective.  The
proof is mutual: function reification consumes domain injectivity, while
function injectivity tests both callbacks using domain reification. -/
theorem rawReificationClaim_holds (orc : FFSOracleSem) :
    RawReificationClaim orc := by
  classical
  intro sigma rho Ds Gv Dv tau tauv B hB hd
  generalize hn : Ty.size tau + ValTy.kindSize tauv = n
  induction n using Nat.strong_induction_on generalizing
      Ds Gv Dv tau tauv B with
  | h n ih =>
      cases tau with
      | space s =>
          cases tauv with
          | piTy tauv0 tauv1 => simpa only [RawAgreeDimsAt] using hd
          | space sv =>
              simp only [RawBasisAt] at hB
              simp only [RawAgreeDimsAt] at hd
              let V := denotSpaceAux sigma Ds s
              let vs := B.atSpace V
              have hN : vs.length = ValSpace.dof (orc rho Gv Dv) sv := by
                exact hB.finrank_eq.symm.trans
                  (rawReification_dof_eq_finrank_of_shpOf hd).symm
              constructor
              · intro x'
                let a := basisCoordsArray hB x'
                refine ⟨.array a, ?_⟩
                simp only [RawAgree, LegacyAgree]
                change vs.length = ValSpace.dof (orc rho Gv Dv) sv /\
                  a.length = ValSpace.dof (orc rho Gv Dv) sv /\
                  ((denotTyAux sigma Ds (.space s)).embed x').atSpace V =
                    ∑ i : Fin (ValSpace.dof (orc rho Gv Dv) sv),
                      a.get i.val • vs.getD i.val 0
                refine ⟨hN, ?_, ?_⟩
                · change (basisCoordsArray hB x').length =
                    ValSpace.dof (orc rho Gv Dv) sv
                  simpa only [basisCoordsArray, FlatArray.length_ofFn] using hN
                · rw [← hN]
                  change (DVal.hil ⟨V, x'⟩).atSpace V =
                    ∑ i : Fin vs.length,
                      (basisCoordsArray hB x').get i.val • vs.getD i.val 0
                  rw [DVal.atSpace_hil_self]
                  change x' = ∑ i : Fin vs.length,
                    (basisCoordsArray hB x').get i.val • vs.getD i.val 0
                  exact basisCoordsArray_expands hB x'
              · intro x0 x1 raw hx0 hx1
                cases raw with
                | fn T f => simpa only [RawAgree] using hx0
                | array a =>
                    simp only [RawAgree] at hx0 hx1
                    simp only [LegacyAgree] at hx0 hx1
                    have h0 := hx0.2.2
                    have h1 := hx1.2.2
                    simpa only [denotTyAux, HType.embed,
                      DVal.atSpace_hil_self] using h0.trans h1.symm
      | piTy tau0 tau1 =>
          cases tauv with
          | space sv => simpa only [RawAgreeDimsAt] using hd
          | piTy tauv0 tauv1 =>
              simp only [RawBasisAt] at hB
              simp only [RawAgreeDimsAt] at hd
              let T0 := denotTyAux sigma Ds tau0
              let Tv0 := denotValTyS orc rho Gv Dv tauv0
              have hdomLt : Ty.size tau0 + ValTy.kindSize tauv0 < n := by
                simp only [Ty.size, ValTy.kindSize_piTy] at hn
                omega
              have ihDom :
                  RawReifiableAt orc sigma rho Ds Gv Dv tau0 tauv0
                      B.domainBasis /\
                    RawSourceInjectiveAt orc sigma rho Ds Gv Dv tau0 tauv0
                      B.domainBasis :=
                ih (Ty.size tau0 + ValTy.kindSize tauv0) hdomLt
                  hB.1 hd.1 rfl
              constructor
              · intro g
                let Good : Tv0.El -> Prop := fun arg =>
                  exists x' : T0.El,
                    exists raw : ValValSem,
                    ValValSem.toEl Tv0 raw = .ok arg /\
                    RawAgree orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis
                      (T0.embed x') raw
                let outRaw : forall (arg : Tv0.El), Good arg -> ValValSem :=
                  fun arg hg =>
                    let x' : T0.El := Classical.choose hg
                    let hx := Classical.choose_spec hg
                    let raw : ValValSem := Classical.choose hx
                    let hraw := Classical.choose_spec hx
                    let hdCod := hd.2 x' raw arg hraw.1 hraw.2
                    let ihCod := ih
                      (Ty.size tau1 + ValTy.kindSize tauv1)
                      (by
                        simp only [Ty.size, ValTy.kindSize_piTy] at hn
                        omega)
                      (hB.2 x') hdCod rfl
                    Classical.choose (ihCod.1 (g x'))
                let f : Tv0.El -> Except DimError ValValSem := fun arg =>
                  if hg : Good arg then .ok (outRaw arg hg)
                  else .error .mismatch
                refine ⟨.fn Tv0.El f, ?_⟩
                simp only [RawAgree]
                refine ⟨f, rfl, ?_⟩
                intro x' argVal arg hto harg
                have hgood : Good arg := by
                  exact ⟨x', argVal, hto, harg⟩
                let chosen : T0.El := Classical.choose hgood
                let hexists := Classical.choose_spec hgood
                let chosenRaw : ValValSem := Classical.choose hexists
                have hchosenTo :
                    ValValSem.toEl Tv0 chosenRaw = .ok arg :=
                  (Classical.choose_spec hexists).1
                have hchosenAgree : RawAgree orc sigma rho Ds Gv Dv
                    tau0 tauv0 B.domainBasis (T0.embed chosen)
                    chosenRaw :=
                  (Classical.choose_spec hexists).2
                obtain ⟨chosenEl, hchosenDecode, hchosenCanon⟩ :=
                  RawAgree.toEl_fromEl orc sigma rho hd.1 hchosenAgree
                have hchosenEl : chosenEl = arg :=
                  Except.ok.inj (hchosenDecode.symm.trans hchosenTo)
                subst chosenEl
                obtain ⟨currentEl, hcurrentDecode, hcurrentCanon⟩ :=
                  RawAgree.toEl_fromEl orc sigma rho hd.1 harg
                have hcurrentEl : currentEl = arg :=
                  Except.ok.inj (hcurrentDecode.symm.trans hto)
                subst currentEl
                have hchosenCanon' : RawAgree orc sigma rho Ds Gv Dv
                    tau0 tauv0 B.domainBasis (T0.embed chosen)
                    (ValValSem.fromEl Tv0 arg) := by
                  simpa only [Tv0] using hchosenCanon
                have hcurrentCanon' : RawAgree orc sigma rho Ds Gv Dv
                    tau0 tauv0 B.domainBasis (T0.embed x')
                    (ValValSem.fromEl Tv0 arg) := by
                  simpa only [T0, Tv0] using hcurrentCanon
                have hchosen : chosen = x' :=
                  ihDom.2 chosen x' (ValValSem.fromEl Tv0 arg)
                    hchosenCanon' hcurrentCanon'
                subst x'
                have hdChosen := hd.2 chosen chosenRaw arg
                  hchosenTo hchosenAgree
                have hcodLt : Ty.size tau1 + ValTy.kindSize tauv1 < n := by
                  simp only [Ty.size, ValTy.kindSize_piTy] at hn
                  omega
                have ihCod := ih
                  (Ty.size tau1 + ValTy.kindSize tauv1) hcodLt
                  (hB.2 chosen) hdChosen rfl
                have houtChosen : RawAgree orc sigma rho (T0.embed chosen :: Ds)
                    (tauv0 :: Gv) (chosenRaw :: Dv) tau1 tauv1
                    (B.applyEl chosen)
                    ((denotTyAux sigma Ds (.piTy tau0 tau1)).embed g
                      |>.applyEl chosen)
                    (outRaw arg hgood) := by
                  have hout := Classical.choose_spec (ihCod.1 (g chosen))
                  simpa only [T0, denotTyAux, HType.embed,
                    DVal.applyEl_pi, outRaw] using hout
                have hdRaw := hd.2 chosen argVal arg hto harg
                refine ⟨outRaw arg hgood, ?_, ?_⟩
                · simp only [f, dif_pos hgood]
                · exact RawAgree.realize_transport orc sigma rho
                    (ValSoundOfDenot.ValTy.SameShape.refl tauv1)
                    hdChosen hdRaw houtChosen
              · intro g0 g1 raw hg0 hg1
                simp only [RawAgree] at hg0 hg1
                obtain ⟨f0, hraw0, hf0⟩ := hg0
                obtain ⟨f1, hraw1, hf1⟩ := hg1
                have hfn : ValValSem.fn Tv0.El f0 =
                    ValValSem.fn Tv0.El f1 := hraw0.symm.trans hraw1
                have hfunctions : f0 = f1 := by
                  injection hfn
                funext x'
                obtain ⟨argVal, harg⟩ := ihDom.1 x'
                obtain ⟨arg, hto⟩ := harg.toEl
                obtain ⟨out0, hout0, houtAgree0⟩ :=
                  hf0 x' argVal arg hto harg
                obtain ⟨out1, hout1, houtAgree1⟩ :=
                  hf1 x' argVal arg hto harg
                have happ : f0 arg = f1 arg := by
                  exact congrFun hfunctions arg
                have houtEq : out0 = out1 :=
                  Except.ok.inj (hout0.symm.trans (happ.trans hout1))
                subst out1
                have hdCod := hd.2 x' argVal arg hto harg
                have hcodLt : Ty.size tau1 + ValTy.kindSize tauv1 < n := by
                  simp only [Ty.size, ValTy.kindSize_piTy] at hn
                  omega
                have ihCod := ih
                  (Ty.size tau1 + ValTy.kindSize tauv1) hcodLt
                  (hB.2 x') hdCod rfl
                apply ihCod.2 (g0 x') (g1 x') out0
                · simpa only [T0, denotTyAux, HType.embed,
                    DVal.applyEl_pi] using houtAgree0
                · simpa only [T0, denotTyAux, HType.embed,
                    DVal.applyEl_pi] using houtAgree1

/-- Basis soundness in the exact recursive form needed by reification. -/
def RawBasisAtValidClaim : Prop :=
  forall {sigma : DEnv} {Gamma : NLCtx} {b : Basis},
    Basis.BasisValid Gamma b -> CtxWF ∅ Gamma -> EnvWF sigma ∅ Gamma ->
      RawBasisAt sigma [] (Basis.tof b) (denotBasis sigma b)

/-- Opening a source binder and binding its selected source-stack entry is
invisible to recursive semantic basis soundness. -/
theorem RawBasisAt.openRec_bind_src {z : Name} (sigma : DEnv) :
    forall (tau : Ty) (Ds : List DVal) (k : Nat) (B : BasisDenot),
      z ∉ Ty.fv tau ->
      (RawBasisAt (sigma.bind z (Ds.getD k DVal.default)) Ds
          (Ty.openRec k (.var z) tau) B <->
        RawBasisAt sigma Ds tau B)
  | .space s, Ds, k, B, hz => by
      simp only [Ty.fv] at hz
      simp only [Ty.openRec, RawBasisAt]
      rw [denotSpaceAux_openRec_bind sigma Ds k s hz]
  | .piTy tau0 tau1, Ds, k, B, hz => by
      simp only [Ty.fv, Finset.mem_union, not_or] at hz
      have hT0 :
          denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
              (Ty.openRec k (.var z) tau0) = denotTyAux sigma Ds tau0 :=
        denotTyAux_openRec_bind sigma Ds k tau0 hz.1
      simp only [Ty.openRec, RawBasisAt]
      revert hT0
      generalize denotTyAux (sigma.bind z (Ds.getD k DVal.default)) Ds
          (Ty.openRec k (.var z) tau0) = T1
      generalize denotTyAux sigma Ds tau0 = T2
      intro hT0
      subst T2
      refine and_congr
        (RawBasisAt.openRec_bind_src sigma tau0 Ds k B.domainBasis hz.1) ?_
      refine forall_congr' fun x' => ?_
      have hcod := RawBasisAt.openRec_bind_src sigma tau1
        (T1.embed x' :: Ds) (k + 1) (B.applyEl x') hz.2
      simpa only [List.getD_cons_succ] using hcod
  termination_by tau _ _ _ => Ty.size tau
  decreasing_by all_goals simp only [Ty.size]; omega

/-- A locally closed source type is independent of its source De Bruijn
stack for the purpose of recursive semantic basis soundness. -/
theorem RawBasisAt.lc_irrel_src :
    forall {tau : Ty}, Ty.lc tau -> forall (sigma : DEnv)
      (Ds0 Ds1 : List DVal) (B : BasisDenot),
      RawBasisAt sigma Ds0 tau B <-> RawBasisAt sigma Ds1 tau B
  | _, .space hs => fun sigma Ds0 Ds1 B => by
      simp only [RawBasisAt]
      rw [denotSpaceAux_lc_irrel hs sigma Ds0 Ds1]
  | .piTy tau0 tau1, .piTy L htau0 hbody => fun sigma Ds0 Ds1 B => by
      have hT0 : denotTyAux sigma Ds0 tau0 = denotTyAux sigma Ds1 tau0 :=
        denotTyAux_lc_irrel htau0 sigma Ds0 Ds1
      simp only [RawBasisAt]
      revert hT0
      generalize denotTyAux sigma Ds0 tau0 = T0
      generalize denotTyAux sigma Ds1 tau0 = T1
      intro hT0
      subst T1
      refine and_congr
        (RawBasisAt.lc_irrel_src htau0 sigma Ds0 Ds1 B.domainBasis) ?_
      refine forall_congr' fun x' => ?_
      obtain ⟨w, hw⟩ := Infinite.exists_notMem_finset (L ∪ Ty.fv tau1)
      simp only [Finset.mem_union, not_or] at hw
      have h0 := RawBasisAt.openRec_bind_src (z := w) sigma tau1
        (T0.embed x' :: Ds0) 0 (B.applyEl x') hw.2
      have h1 := RawBasisAt.openRec_bind_src (z := w) sigma tau1
        (T0.embed x' :: Ds1) 0 (B.applyEl x') hw.2
      simp only [List.getD_cons_zero] at h0 h1
      rw [← h0, ← h1]
      exact RawBasisAt.lc_irrel_src (hbody w hw.1)
        (sigma.bind w (T0.embed x')) (T0.embed x' :: Ds0)
        (T0.embed x' :: Ds1) (B.applyEl x')

private theorem Basis.BasisValid.tof_lc_raw_reification
    {Gamma : NLCtx} {b : Basis} (h : Basis.BasisValid Gamma b) :
    Ty.lc (Basis.tof b) := by
  cases b with
  | frame b0 b1 =>
      obtain ⟨_hb0, _hbody, k0, k1, hty⟩ := h.frame_inv
      exact TValid.lc hty.some
  | empty | one | dual | dsum | tprod | proj | image | terms =>
      obtain ⟨hsof⟩ := h.sof_valid
      exact .space (SValid.lc hsof)

/-- Every valid syntactic basis denotes a recursively sound semantic basis.
The frame case recurses under a fresh named binder and transports the result
back to the actual source De Bruijn fiber. -/
theorem rawBasisAtValidClaim_holds : RawBasisAtValidClaim := by
  intro sigma Gamma b hb hctx henv
  generalize hn : Basis.size b = n
  induction n using Nat.strong_induction_on generalizing sigma Gamma b with
  | h n ih =>
      cases b with
      | empty | one | dual | dsum | tprod | proj | image | terms =>
          simp only [Basis.tof, RawBasisAt]
          exact denotBasis_atSpace_isListBasis sigma Gamma _ hb hctx henv
      | frame b0 b1 =>
          obtain ⟨hb0, ⟨L, hbody⟩, k0, k1, ⟨hpi⟩⟩ := hb.frame_inv
          cases hpi with
          | piTy Lty htau0 htau1 =>
              simp only [Basis.tof, RawBasisAt,
                denotBasis_frame_domainBasis]
              let T0 := denotTy sigma (Basis.tof b0)
              refine ⟨?_, ?_⟩
              · have hb0lt : Basis.size b0 < n := by
                  simp only [Basis.size] at hn
                  omega
                exact ih (Basis.size b0) hb0lt hb0 hctx henv rfl
              · intro x'
                obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
                  (L ∪ Gamma.keys ∪ Ty.fv (Basis.tof b0) ∪ Basis.fv b1)
                simp only [Finset.mem_union, not_or] at hz
                rcases hz with ⟨⟨⟨hzL, hzGammaKeys⟩, hztau0⟩, hzb1⟩
                have hzGamma : z ∉ Gamma := fun hzmem =>
                  hzGammaKeys (Finmap.mem_keys.mpr hzmem)
                have hctxz : CtxWF ∅
                    (Finmap.insert z (Basis.tof b0) Gamma) :=
                  hctx.insert_nl Finmap.notMem_empty hzGamma
                    htau0.fv_closure
                have henvz : EnvWF (sigma.bind z (T0.embed x')) ∅
                    (Finmap.insert z (Basis.tof b0) Gamma) :=
                  henv.bind_nl hctx Finmap.notMem_empty hzGamma hztau0 x'
                have hopenValid := hbody z hzL
                have hopenLt : Basis.size (Basis.openVar z b1) < n := by
                  simp only [Basis.size] at hn
                  simp only [Basis.openVar, Basis.size_openVar]
                  omega
                have hopen := ih (Basis.size (Basis.openVar z b1)) hopenLt
                  hopenValid hctxz henvz rfl
                have hlcOpen : Ty.lc (Basis.tof (Basis.openVar z b1)) :=
                  Basis.BasisValid.tof_lc_raw_reification hopenValid
                have hopenStack : RawBasisAt (sigma.bind z (T0.embed x'))
                    [T0.embed x'] (Basis.tof (Basis.openVar z b1))
                    (denotBasis (sigma.bind z (T0.embed x'))
                      (Basis.openVar z b1)) :=
                  (RawBasisAt.lc_irrel_src hlcOpen
                    (sigma.bind z (T0.embed x')) [] [T0.embed x'] _).mp hopen
                have hopenStack' : RawBasisAt (sigma.bind z (T0.embed x'))
                    [T0.embed x'] (Ty.openVar z (Basis.tof b1))
                    (denotBasis (sigma.bind z (T0.embed x'))
                      (Basis.openVar z b1)) := by
                  simpa only [Basis.openVar, Basis.tof_openRec] using hopenStack
                have hbridge := RawBasisAt.openRec_bind_src (z := z) sigma
                  (Basis.tof b1) [T0.embed x'] 0
                  (denotBasis (sigma.bind z (T0.embed x'))
                    (Basis.openVar z b1))
                  (fun hztof => hzb1 (Basis.fv_tof_subset b1 hztof))
                simp only [List.getD_cons_zero] at hbridge
                rw [denotBasis_frame_applyEl_openVar z hzb1 x']
                simpa only [T0] using hbridge.mp hopenStack'

/-- Build the canonical non-vacuous package from the two constructive
ingredients. -/
theorem AgreeDimsAt.ofRaw (orc : FFSOracleSem)
    {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot}
    (hB : RawBasisAt sigma Ds tau B)
    (hd : RawAgreeDimsAt orc sigma rho Ds Gv Dv tau tauv B) :
    AgreeDimsAt orc sigma rho Ds Gv Dv tau tauv B := by
  have htotal := rawReificationClaim_holds orc hB hd
  exact ⟨hd, hB, htotal.1, htotal.2⟩

/-- The domain of a canonical dependent-function agreement is itself a
canonical, non-vacuous agreement. -/
theorem AgreeDimsAt.domain {orc : FFSOracleSem}
    {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau0 tau1 : Ty} {tauv0 tauv1 : ValTy} {B : BasisDenot}
    (h : AgreeDimsAt orc sigma rho Ds Gv Dv
      (.piTy tau0 tau1) (.piTy tauv0 tauv1) B) :
    AgreeDimsAt orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis := by
  have hB := h.basis
  have hd := h.raw
  simp only [RawBasisAt] at hB
  simp only [RawAgreeDimsAt] at hd
  exact AgreeDimsAt.ofRaw orc hB.1 hd.1

/-- Every represented argument reaches a canonical, non-vacuous codomain
agreement.  Together with `domain.reifiable`, this rules out the vacuous
dependent-function reading of `RawAgreeDimsAt`. -/
theorem AgreeDimsAt.codomain {orc : FFSOracleSem}
    {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau0 tau1 : Ty} {tauv0 tauv1 : ValTy} {B : BasisDenot}
    (h : AgreeDimsAt orc sigma rho Ds Gv Dv
      (.piTy tau0 tau1) (.piTy tauv0 tauv1) B)
    (x' : (denotTyAux sigma Ds tau0).El)
    (argVal : ValValSem)
    (arg : (denotValTyS orc rho Gv Dv tauv0).El)
    (hto : ValValSem.toEl (denotValTyS orc rho Gv Dv tauv0) argVal =
      .ok arg)
    (harg : RawAgree orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis
      ((denotTyAux sigma Ds tau0).embed x') argVal) :
    AgreeDimsAt orc sigma rho
      ((denotTyAux sigma Ds tau0).embed x' :: Ds)
      (tauv0 :: Gv) (argVal :: Dv) tau1 tauv1 (B.applyEl x') := by
  have hB := h.basis
  have hd := h.raw
  simp only [RawBasisAt] at hB
  simp only [RawAgreeDimsAt] at hd
  exact AgreeDimsAt.ofRaw orc (hB.2 x') (hd.2 x' argVal arg hto harg)

end GLang
