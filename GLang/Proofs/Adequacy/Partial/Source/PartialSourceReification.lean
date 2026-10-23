import GLang.Proofs.Adequacy.Partial.Source.PartialSourceNormalization

namespace GLang.PartialAdequacy

/-- Every source element has a raw representative at this exact basis. -/
def ReifiableAt (orc : PartialFFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    (Ds : List DVal) (Gv : List ValTy) (Dv : List ValValSem)
    (tau : Ty) (tauv : ValTy) (B : BasisDenot) : Prop :=
  forall x' : (denotTyAux sigma Ds tau).El,
    exists raw : ValValSem,
      Agree orc sigma rho Ds Gv Dv tau tauv B
        ((denotTyAux sigma Ds tau).embed x') raw

/-- A raw representative at a sound basis determines at most one source
element.  This companion fact makes dependent-function reification independent
of the existential representative chosen for a decoded argument. -/
def SourceInjectiveAt (orc : PartialFFSOracleSem) (sigma : DEnv)
    (rho : ValEnvSem) (Ds : List DVal) (Gv : List ValTy)
    (Dv : List ValValSem) (tau : Ty) (tauv : ValTy)
    (B : BasisDenot) : Prop :=
  forall (x0 x1 : (denotTyAux sigma Ds tau).El) (raw : ValValSem),
    Agree orc sigma rho Ds Gv Dv tau tauv B
        ((denotTyAux sigma Ds tau).embed x0) raw ->
    Agree orc sigma rho Ds Gv Dv tau tauv B
        ((denotTyAux sigma Ds tau).embed x1) raw ->
    x0 = x1

/-- Canonical, non-vacuous dimension agreement.  `raw` is the equality used
by the direct mutual proof.  `basis` retains recursive basis soundness, so the
domain and every reached codomain can be reified as well.  `reifiable` and
`sourceInjective` expose the constructive consequences at the current type. -/
structure AgreeDimsAt (orc : PartialFFSOracleSem) (sigma : DEnv) (rho : ValEnvSem)
    (Ds : List DVal) (Gv : List ValTy) (Dv : List ValValSem)
    (tau : Ty) (tauv : ValTy) (B : BasisDenot) : Prop where
  raw : DimsAt orc sigma rho Ds Gv Dv tau tauv B
  basis : RawBasisAt sigma Ds tau B
  reifiable : ReifiableAt orc sigma rho Ds Gv Dv tau tauv B
  sourceInjective :
    SourceInjectiveAt orc sigma rho Ds Gv Dv tau tauv B

/-- The ordinary public dimension-agreement name remains basis-indexed. -/
abbrev AgreeDims := AgreeDimsAt

/-- The constructive reification package proved below. -/
def ReificationClaim (orc : PartialFFSOracleSem) : Prop :=
  forall {sigma : DEnv} {rho : ValEnvSem}
    {Ds : List DVal} {Gv : List ValTy} {Dv : List ValValSem}
    {tau : Ty} {tauv : ValTy} {B : BasisDenot},
    RawBasisAt sigma Ds tau B ->
    DimsAt orc sigma rho Ds Gv Dv tau tauv B ->
    ReifiableAt orc sigma rho Ds Gv Dv tau tauv B /\
      SourceInjectiveAt orc sigma rho Ds Gv Dv tau tauv B

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
theorem reificationClaim_holds (orc : PartialFFSOracleSem) :
    ReificationClaim orc := by
  classical
  intro sigma rho Ds Gv Dv tau tauv B hB hd
  generalize hn : Ty.size tau + ValTy.kindSize tauv = n
  induction n using Nat.strong_induction_on generalizing
      Ds Gv Dv tau tauv B with
  | h n ih =>
      cases tau with
      | space s =>
          cases tauv with
          | piTy tauv0 tauv1 => simpa only [DimsAt] using hd
          | space sv =>
              simp only [RawBasisAt] at hB
              simp only [DimsAt] at hd
              let V := denotSpaceAux sigma Ds s
              let vs := B.atSpace V
              have hN : vs.length = (srcShp sigma Ds s).foldr (· * ·) 1 := by
                exact hB.finrank_eq.symm.trans
                  (rawReification_srcShp_foldr sigma Ds s).symm
              have hp : sv.dofPartial (orc rho Gv Dv) = .ok ((srcShp sigma Ds s).foldr (· * ·) 1) := by
                simp only [ValSpace.dofPartial, hd, bind, Except.bind, pure, Except.pure]
              constructor
              · intro x'
                let a := basisCoordsArray hB x'
                refine ⟨.array a, ?_⟩
                simp only [Agree]
                refine ⟨_,hp,?_⟩
                change vs.length = (srcShp sigma Ds s).foldr (· * ·) 1 /\
                  a.length = (srcShp sigma Ds s).foldr (· * ·) 1 /\
                  ((denotTyAux sigma Ds (.space s)).embed x').atSpace V =
                    ∑ i : Fin ((srcShp sigma Ds s).foldr (· * ·) 1),
                      a.get i.val • vs.getD i.val 0
                refine ⟨hN, ?_, ?_⟩
                · change (basisCoordsArray hB x').length =
                    (srcShp sigma Ds s).foldr (· * ·) 1
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
                | fn T f => simpa only [Agree] using hx0
                | array a =>
                    simp only [Agree] at hx0 hx1
                    obtain ⟨n0,hn0,hx0⟩ := hx0
                    obtain ⟨n1,hn1,hx1⟩ := hx1
                    have he : n0 = n1 := Except.ok.inj (hn0.symm.trans hn1)
                    subst n1
                    have h0 := hx0.2.2
                    have h1 := hx1.2.2
                    simpa only [denotTyAux, HType.embed,
                      DVal.atSpace_hil_self] using h0.trans h1.symm
      | piTy tau0 tau1 =>
          cases tauv with
          | space sv => simpa only [DimsAt] using hd
          | piTy tauv0 tauv1 =>
              simp only [RawBasisAt] at hB
              simp only [DimsAt] at hd
              let T0 := denotTyAux sigma Ds tau0
              obtain ⟨D,hD⟩ := DimsAt.type_ok hd.1
              have hdomLt : Ty.size tau0 + ValTy.kindSize tauv0 < n := by
                simp only [Ty.size, ValTy.kindSize_piTy] at hn
                omega
              have ihDom :
                  ReifiableAt orc sigma rho Ds Gv Dv tau0 tauv0
                      B.domainBasis /\
                    SourceInjectiveAt orc sigma rho Ds Gv Dv tau0 tauv0
                      B.domainBasis :=
                ih (Ty.size tau0 + ValTy.kindSize tauv0) hdomLt
                  hB.1 hd.1 rfl
              constructor
              · intro g
                let Good : tauv0.carrierEl -> Prop := fun arg =>
                  exists x' : T0.El,
                    exists raw : ValValSem,
                    tauv0.carrierFromVal raw = .ok arg /\
                    Agree orc sigma rho Ds Gv Dv tau0 tauv0 B.domainBasis
                      (T0.embed x') raw
                let outRaw : forall (arg : tauv0.carrierEl), Good arg -> ValValSem :=
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
                let f : tauv0.carrierEl -> Except DimError ValValSem := fun arg =>
                  if hg : Good arg then .ok (outRaw arg hg)
                  else .error .mismatch
                refine ⟨.fn tauv0.carrierEl f, ?_⟩
                simp only [Agree]
                refine ⟨D,hD,f, rfl, ?_⟩
                intro x' argVal arg hto harg
                have hgood : Good arg := by
                  exact ⟨x', argVal, hto, harg⟩
                let chosen : T0.El := Classical.choose hgood
                let hexists := Classical.choose_spec hgood
                let chosenRaw : ValValSem := Classical.choose hexists
                have hchosenTo :
                    tauv0.carrierFromVal chosenRaw = .ok arg :=
                  (Classical.choose_spec hexists).1
                have hchosenAgree : Agree orc sigma rho Ds Gv Dv
                    tau0 tauv0 B.domainBasis (T0.embed chosen)
                    chosenRaw :=
                  (Classical.choose_spec hexists).2
                obtain ⟨chosenEl, hchosenDecode, hchosenCanon⟩ :=
                  Agree.normalize hchosenAgree
                have hchosenEl : chosenEl = arg :=
                  Except.ok.inj (hchosenDecode.symm.trans hchosenTo)
                subst chosenEl
                obtain ⟨currentEl, hcurrentDecode, hcurrentCanon⟩ :=
                  Agree.normalize harg
                have hcurrentEl : currentEl = arg :=
                  Except.ok.inj (hcurrentDecode.symm.trans hto)
                subst currentEl
                have hchosenCanon' : Agree orc sigma rho Ds Gv Dv
                    tau0 tauv0 B.domainBasis (T0.embed chosen)
                    (tauv0.carrierToVal arg) := by
                  exact hchosenCanon
                have hcurrentCanon' : Agree orc sigma rho Ds Gv Dv
                    tau0 tauv0 B.domainBasis (T0.embed x')
                    (tauv0.carrierToVal arg) := by
                  simpa only [T0] using hcurrentCanon
                have hchosen : chosen = x' :=
                  ihDom.2 chosen x' (tauv0.carrierToVal arg)
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
                have houtChosen : Agree orc sigma rho (T0.embed chosen :: Ds)
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
                · exact Agree.stack_transport
                    hdChosen hdRaw houtChosen
              · intro g0 g1 raw hg0 hg1
                simp only [Agree] at hg0 hg1
                obtain ⟨_,_,f0, hraw0, hf0⟩ := hg0
                obtain ⟨_,_,f1, hraw1, hf1⟩ := hg1
                have hfn : ValValSem.fn tauv0.carrierEl f0 =
                    ValValSem.fn tauv0.carrierEl f1 := hraw0.symm.trans hraw1
                have hfunctions : f0 = f1 := by
                  injection hfn
                funext x'
                obtain ⟨argVal, harg⟩ := ihDom.1 x'
                obtain ⟨arg, hto, _⟩ := harg.decode
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

theorem DimsAt.complete {orc : PartialFFSOracleSem} {σ : DEnv} {ρ : ValEnvSem}
    {Ds Γ Δ t tv B} (h : DimsAt orc σ ρ Ds Γ Δ t tv B)
    (hB : RawBasisAt σ Ds t B) : AgreeDimsAt orc σ ρ Ds Γ Δ t tv B := by
  obtain ⟨hr,hi⟩ := reificationClaim_holds orc hB h
  exact ⟨h,hB,hr,hi⟩

end GLang.PartialAdequacy
