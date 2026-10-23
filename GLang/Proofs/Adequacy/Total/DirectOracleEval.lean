import GLang.Proofs.Adequacy.Total.DirectOracleReshape

/-!
# Evaluator open/push transport from primitive oracle coherence

This is the structural evaluator half of the direct-oracle
construction.  The proof carries the named and de-Bruijn presentations in
parallel, exactly as `RawCertifiedRenameProof` carries its two renamed
worlds.  The only non-structural hypothesis below is the corresponding
paired higher-order reshape theorem; it is stated separately so that its
kind-recursive proof can be checked independently.
-/

namespace GLang.DirectOracleEval

open DirectOracleOpenPush

/-- Prefix-general evaluator presentation transport.  The public raw
adequacy boundary is its `G = D = []` specialization; the direct fixed-point
proof needs the general form while recursively traversing dependent types. -/
def ValueOpenPushEvalPrefix (orc : FFSOracleSem) : Prop :=
  forall {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
      {G : List ValTy} {D : List ValValSem} {e : ValExpr},
    G.length = D.length ->
    ValTy.lc sigmaV ->
    y ∉ ValTy.fv sigmaV ->
    (forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) ->
    y ∉ ValExpr.fv e ->
    denotValB_semS orc (rho.update y w)
        (ValTy.closePrefix (.var y sigmaV) G) D
        (ValExpr.openRec G.length (.var y sigmaV) e) =
      denotValB_semS orc rho (G ++ [sigmaV]) (D ++ [w]) e

/-- Leafwise oracle coherence entails prefix-general evaluator transport. -/
def EvalPrefixFromLeaf : Prop :=
  forall orc : FFSOracleSem,
    RawValueOpenPushOracleCoherent orc -> ValueOpenPushEvalPrefix orc

/-- The exact reshape instance needed by the evaluator induction. -/
def ReshapePrefixTransport (orc : FFSOracleSem) : Prop :=
  forall {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
      {G : List ValTy} {D : List ValValSem} {v : ValValSem}
      {target source : ValTy},
    G.length = D.length ->
    ValTy.lc sigmaV ->
    y ∉ ValTy.fv sigmaV ->
    (forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) ->
    y ∉ ValTy.fv target ->
    y ∉ ValTy.fv source ->
    reshapDenotSemS orc (rho.update y w)
        (ValTy.closePrefix (uOf y sigmaV) G) D v
        (ValTy.openRec G.length (uOf y sigmaV) target)
        (ValTy.openRec G.length (uOf y sigmaV) source) =
      reshapDenotSemS orc rho (G ++ [sigmaV]) (D ++ [w]) v target source

/-- The independent kind-recursive paired reshape proof discharges the sole
factored premise of the expression-size evaluator induction. -/
theorem reshapePrefixTransport_from_leaf
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc) :
    ReshapePrefixTransport orc := by
  intro rho y sigmaV w G D v target source hlen hlc hySigma hyG ht hs
  rw [reshapDenotSemS_eq_between, reshapDenotSemS_eq_between]
  exact DirectOracleReshape.reshapDenotSemBetweenS_valueOpenPush_local
    horacle (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
    v target source G D G D hlen hlen hlc hySigma hyG hyG ht hs

private theorem getD_append_singleton_self
    (D : List ValValSem) (w : ValValSem) :
    (D ++ [w]).getD D.length ValValSem.default = w := by
  rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

private theorem getD_append_singleton_ne
    (D : List ValValSem) (w : ValValSem) {n : Nat}
    (hn : n ≠ D.length) :
    (D ++ [w]).getD n ValValSem.default =
      D.getD n ValValSem.default := by
  rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_append_right _ _ _ _ (le_of_lt hgt),
      List.getD_eq_default _ _ (le_of_lt hgt)]
    exact List.getD_eq_default _ _ (by simp only [List.length_singleton]; omega)

private theorem fresh_append_singleton
    {y : VName} {sigmaV : ValTy} {G : List ValTy}
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall tauV, tauV ∈ G ++ [sigmaV] -> y ∉ ValTy.fv tauV := by
  intro tauV htau
  rw [List.mem_append] at htau
  rcases htau with htau | htau
  · exact hyG tauV htau
  · simp only [List.mem_singleton] at htau
    subst tauV
    exact hySigma

/-- Any observation which first checks that an inferred space is a tensor and
then uses only the two semantic dimensions transports across the paired
worlds.  This packages the repeated matrix-arm case split once. -/
theorem inferTprodDofs_valueOpenPush_from_leaf
    {Alpha : Sort _} {orc : FFSOracleSem}
    (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (hlc : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    (e : ValExpr) (hy : y ∉ ValExpr.fv e)
    (fallback : Alpha) (observe : Nat -> Nat -> Alpha) :
    (match ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G)
        (ValExpr.openRec G.length (uOf y sigmaV) e) with
      | .tprod s0 s1 => observe
          (ValSpace.dof
            (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) s0)
          (ValSpace.dof
            (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) s1)
      | _ => fallback) =
    (match ValExpr.inferSpaceCtx (G ++ [sigmaV]) e with
      | .tprod s0 s1 => observe
          (ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s0)
          (ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s1)
      | _ => fallback) := by
  rw [inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G e]
  have hyInf := ValExpr.notMem_fv_inferSpaceCtx y e (G ++ [sigmaV]) hy
    (fresh_append_singleton hySigma hyG)
  cases hp : ValExpr.inferSpaceCtx (G ++ [sigmaV]) e with
  | empty => rfl
  | real => rfl
  | dsum s0 s1 => rfl
  | tprod s0 s1 =>
      rw [hp] at hyInf
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hyInf
      simp only [hp, ValSpace.openRec]
      rw [dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s0 hyInf.1,
        dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s1 hyInf.2]
  | ffs p s witness => rfl

/-- Two-inferred-space version used by matrix composition, Kronecker, block,
and the generalized SVD family. -/
theorem inferTprodPairDofs_valueOpenPush_from_leaf
    {Alpha : Sort _} {orc : FFSOracleSem}
    (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (hlc : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    (e0 e1 : ValExpr) (hy0 : y ∉ ValExpr.fv e0)
    (hy1 : y ∉ ValExpr.fv e1)
    (fallback : Alpha) (observe : Nat -> Nat -> Nat -> Nat -> Alpha) :
    (match
        ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G)
          (ValExpr.openRec G.length (uOf y sigmaV) e0),
        ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G)
          (ValExpr.openRec G.length (uOf y sigmaV) e1) with
      | .tprod s00 s01, .tprod s10 s11 => observe
          (ValSpace.dof
            (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) s00)
          (ValSpace.dof
            (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) s01)
          (ValSpace.dof
            (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) s10)
          (ValSpace.dof
            (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) s11)
      | _, _ => fallback) =
    (match ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0,
        ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1 with
      | .tprod s00 s01, .tprod s10 s11 => observe
          (ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s00)
          (ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s01)
          (ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s10)
          (ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s11)
      | _, _ => fallback) := by
  rw [inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G e0,
    inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G e1]
  have hyInf0 := ValExpr.notMem_fv_inferSpaceCtx y e0 (G ++ [sigmaV]) hy0
    (fresh_append_singleton hySigma hyG)
  have hyInf1 := ValExpr.notMem_fv_inferSpaceCtx y e1 (G ++ [sigmaV]) hy1
    (fresh_append_singleton hySigma hyG)
  generalize hp0 : ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0 = q0 at hyInf0 ⊢
  generalize hp1 : ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1 = q1 at hyInf1 ⊢
  cases q0 <;> cases q1 <;> simp only [ValSpace.openRec] <;> try rfl
  case tprod.tprod s00 s01 s10 s11 =>
    simp only [ValSpace.fv, Finset.mem_union, not_or] at hyInf0 hyInf1
    rw [dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s00 hyInf0.1,
        dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s01 hyInf0.2,
        dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s10 hyInf1.1,
        dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s11 hyInf1.2]

/-- Observation used by pseudoinverse/inverse: tensor spaces expose both
factor dimensions; every other inferred space exposes its total dimension. -/
theorem inferTprodOrDof_valueOpenPush_from_leaf
    {Alpha : Sort _} {orc : FFSOracleSem}
    (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (hlc : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    (e : ValExpr) (hy : y ∉ ValExpr.fv e)
    (onOther : Nat -> Alpha) (onTensor : Nat -> Nat -> Alpha) :
    (match ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G)
        (ValExpr.openRec G.length (uOf y sigmaV) e) with
      | .tprod s0 s1 => onTensor
          (ValSpace.dof
            (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) s0)
          (ValSpace.dof
            (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) s1)
      | s => onOther (ValSpace.dof
          (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) s)) =
    (match ValExpr.inferSpaceCtx (G ++ [sigmaV]) e with
      | .tprod s0 s1 => onTensor
          (ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s0)
          (ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s1)
      | s => onOther
          (ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s)) := by
  rw [inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G e]
  have hyInf := ValExpr.notMem_fv_inferSpaceCtx y e (G ++ [sigmaV]) hy
    (fresh_append_singleton hySigma hyG)
  generalize hp : ValExpr.inferSpaceCtx (G ++ [sigmaV]) e = s at hyInf ⊢
  cases s with
  | empty =>
      have hd := dof_valueOpenPush_from_leaf horacle
        (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
        (G := G) (D := D) hlen hlc hySigma hyG .empty hyInf
      simpa only [ValSpace.openRec] using congrArg onOther hd
  | real =>
      have hd := dof_valueOpenPush_from_leaf horacle
        (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
        (G := G) (D := D) hlen hlc hySigma hyG .real hyInf
      simpa only [ValSpace.openRec] using congrArg onOther hd
  | dsum s0 s1 =>
      have hd := dof_valueOpenPush_from_leaf horacle
        (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
        (G := G) (D := D) hlen hlc hySigma hyG (.dsum s0 s1) hyInf
      simpa only [ValSpace.openRec] using congrArg onOther hd
  | tprod s0 s1 =>
      simp only [ValSpace.fv, Finset.mem_union, not_or] at hyInf
      simp only [ValSpace.openRec]
      rw [dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s0 hyInf.1,
        dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s1 hyInf.2]
  | ffs p parent witness =>
      have hd := dof_valueOpenPush_from_leaf horacle
        (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
        (G := G) (D := D) hlen hlc hySigma hyG
          (.ffs p parent witness) hyInf
      simpa only [ValSpace.openRec] using congrArg onOther hd

/-- Immediate-domain decoding transports across open/push worlds; the base
case uses dimension coherence, while the higher-order case retains carrier identity. -/
theorem toElDomainChecked_valueOpenPush_from_leaf
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (hlc : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    (tau : ValTy) (hy : y ∉ ValTy.fv tau) (v : ValValSem) :
    HEq (ValValSem.toElDomainChecked
      (denotValTyS orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D
        (ValTy.openRec G.length (uOf y sigmaV) tau)) v)
      (ValValSem.toElDomainChecked
        (denotValTyS orc rho (G ++ [sigmaV]) (D ++ [w]) tau) v) := by
  cases tau with
  | space s =>
      have hd := dof_valueOpenPush_from_leaf horacle
        (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
        (G := G) (D := D) hlen hlc hySigma hyG s hy
      cases v <;> simp only [ValTy.openRec, denotValTyS,
        ValValSem.toElDomainChecked, ValValSem.toElChecked, hd] <;> rfl
  | piTy domain codomain =>
      have hh := toEl_denotValTyS_sameShape_raw orc _ _
        (ValSoundOfDenot.ValTy.SameShape_openRec G.length (uOf y sigmaV)
          (.piTy domain codomain))
        (rho.update y w) rho (ValTy.closePrefix (uOf y sigmaV) G)
        (G ++ [sigmaV]) D (D ++ [w]) v
      simpa only [ValTy.openRec, denotValTyS, ValValSem.toElDomainChecked] using hh

/- Prefix-general evaluator transport, factored over higher-order reshape.
Every ordinary evaluator arm is proved directly from the primitive FFS leaf
law plus the exact inference square supplied by depth-aware lookup. -/
set_option maxHeartbeats 3200000 in
theorem denotValB_semS_valueOpenPush_from_leaf
    (orc : FFSOracleSem) (horacle : RawValueOpenPushOracleCoherent orc)
    (hreshape : ReshapePrefixTransport orc) :
    forall (rho : ValEnvSem) (y : VName) (sigmaV : ValTy) (w : ValValSem)
      (G : List ValTy) (D : List ValValSem) (e : ValExpr),
      G.length = D.length ->
      ValTy.lc sigmaV ->
      y ∉ ValTy.fv sigmaV ->
      (forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) ->
      y ∉ ValExpr.fv e ->
      denotValB_semS orc (rho.update y w)
          (ValTy.closePrefix (uOf y sigmaV) G) D
          (ValExpr.openRec G.length (uOf y sigmaV) e) =
        denotValB_semS orc rho (G ++ [sigmaV]) (D ++ [w]) e
  | rho, y, sigmaV, w, G, D, .bvar n =>
      fun hlen _ _ _ _ => by
        by_cases hn : n = G.length
        · subst n
          simp only [uOf, ValExpr.openRec, if_true, denotValB_semS,
            ValEnvSem.update_same]
          rw [hlen]
          simp [StrictValueAccess.lookup, List.getElem?_append_right (le_refl D.length)]
        · have hnD : n ≠ D.length := by simpa only [hlen] using hn
          simp only [uOf, ValExpr.openRec, if_neg hn, denotValB_semS]
          by_cases hlt : n < D.length
          · simp only [StrictValueAccess.lookup, List.getElem?_append_left hlt]
          · have hge : (D ++ [w]).length ≤ n := by simp only [List.length_append, List.length_singleton]; omega
            simp only [StrictValueAccess.lookup_of_ge _ _ hge,
              StrictValueAccess.lookup_of_ge _ _ (Nat.le_of_not_gt hlt)]
  | rho, y, sigmaV, w, G, D, .var z tau =>
      fun _ _ _ _ hy => by
        simp only [ValExpr.fv, Finset.mem_insert, not_or] at hy
        simp only [ValExpr.openRec, denotValB_semS]
        rw [ValEnvSem.update_other _ _ _ _ (Ne.symm hy.1)]
  | rho, y, sigmaV, w, G, D, .rlit r =>
      fun hlen hlc hySigma hyG _ => by
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.rlit r)
          (by simp only [ValExpr.fv]; exact Finset.notMem_empty y)
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_semS, denotValB_semS, hdim]
  | rho, y, sigmaV, w, G, D, .zero s =>
      fun hlen hlc hySigma hyG hy => by
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.zero s) hy
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_semS, denotValB_semS, hdim]
  | rho, y, sigmaV, w, G, D, .delta n s =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv] at hy
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.delta n s) hy
        have hs := dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hy
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_semS, denotValB_semS, hdim, hs]
  | rho, y, sigmaV, w, G, D, .idelta s =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv] at hy
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.idelta s) hy
        have hs := dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hy
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_semS, denotValB_semS, hdim, hs]
  | rho, y, sigmaV, w, G, D, .scale e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.scale e0 e1)
          (by simpa only [ValExpr.fv, Finset.mem_union, not_or] using hy)
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG hy.1
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG hy.2
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_semS, denotValB_semS, hdim, ih0, ih1]
        have hother := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e1 hy.2
        simp only [ValueShape.scale, hother]
  | rho, y, sigmaV, w, G, D, .vadd s e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨hs, h0⟩, h1⟩ := hy
        have hsd := dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hs
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec]
        rw [denotValB_semS, denotValB_semS, hsd, ih0, ih1]
  | rho, y, sigmaV, w, G, D, .tprodE e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.tprodE e0 e1)
          (by simpa only [ValExpr.fv, Finset.mem_union, not_or] using hy)
        have hsub := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e1 hy.2
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG hy.1
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG hy.2
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, hsub, ih0, ih1]
        have hother := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 hy.1
        simp only [ValueShape.pair, hother, hsub]
  | rho, y, sigmaV, w, G, D, .dsumE e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.dsumE e0 e1)
          (by simpa only [ValExpr.fv, Finset.mem_union, not_or] using hy)
        have hsub := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 hy.1
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG hy.1
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG hy.2
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, hsub, ih0, ih1]
        have hother := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e1 hy.2
        simp only [ValueShape.pair, hother, hsub]
  | rho, y, sigmaV, w, G, D, .vsum s es =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨hs, hes⟩ := hy
        have hsd := dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hs
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.vsum s es)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨hs, hes⟩)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hsd, hwhole]
        simp only [List.length_map]
        congr 1
        congr 1
        apply congrArg ValValSem.sequenceArrays
        simp only [List.attach_map_val, ← List.map_take, List.map_map,
          Function.comp_apply]
        apply List.map_congr_left
        intro e he
        have hmem : e ∈ es := List.mem_of_mem_take he
        have hye : y ∉ ValExpr.fv e := fun hc =>
          hes (ValExpr.mem_fvList.mpr ⟨e, hmem, hc⟩)
        exact denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG hye
  | rho, y, sigmaV, w, G, D, .reshap e target source =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨he, ht⟩, hs⟩ := hy
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        simp only [ValExpr.openRec]
        rw [denotValB_semS, denotValB_semS, ihe]
        generalize hv : denotValB_semS orc rho (G ++ [sigmaV]) (D ++ [w]) e = result
        cases result with
        | error err => rfl
        | ok v =>
            exact hreshape (rho := rho) (y := y) (sigmaV := sigmaV)
              (w := w) (G := G) (D := D) (v := v)
              (target := target) (source := source)
              hlen hlc hySigma hyG ht hs
  | rho, y, sigmaV, w, G, D, .vtrans e =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv] at hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.vtrans e) hy
        have hinfer := inferSpaceCtx_valueOpenPush
          (y := y) (sigmaV := sigmaV) hlc G e
        have hyInf := ValExpr.notMem_fv_inferSpaceCtx y e
          (G ++ [sigmaV]) hy (fresh_append_singleton hySigma hyG)
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG hy
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe]
        congr 1
        funext a
        have hguard : ValueShape.tensor (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e)) a =
            ValueShape.tensor (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e) a :=
          inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e hy False (fun d0 d1 => a.length = d0 * d1)
        simp only [hguard]
        congr 1
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        cases hp : ValExpr.inferSpaceCtx (G ++ [sigmaV]) e with
        | empty =>
            rw [hp] at hinfer
            simp only [ValSpace.openRec] at hinfer
            rw [hinfer]
        | real =>
            rw [hp] at hinfer
            simp only [ValSpace.openRec] at hinfer
            rw [hinfer]
        | dsum s0 s1 =>
            rw [hp] at hinfer
            simp only [ValSpace.openRec] at hinfer
            rw [hinfer]
        | tprod s0 s1 =>
            rw [hp] at hinfer hyInf
            simp only [ValSpace.openRec] at hinfer
            simp only [ValSpace.fv, Finset.mem_union, not_or] at hyInf
            have hd0 := dof_valueOpenPush_from_leaf horacle
              (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
              (G := G) (D := D) hlen hlc hySigma hyG s0 hyInf.1
            have hd1 := dof_valueOpenPush_from_leaf horacle
              (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
              (G := G) (D := D) hlen hlc hySigma hyG s1 hyInf.2
            rw [hinfer]
            simp only
            rw [hd0, hd1]
        | ffs p s witness =>
            rw [hp] at hinfer
            simp only [ValSpace.openRec] at hinfer
            rw [hinfer]
  | rho, y, sigmaV, w, G, D, .ttv s e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨hs, h0⟩, h1⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.ttv s e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨hs, h0⟩, h1⟩)
        have hcontract := dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hs
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, hcontract, ih0, ih1]
        congr 1
        funext a0 a1
        have hd0 := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 h0
        have hd1 := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e1 h1
        have hg := inferTprodOrDof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 h0
            (fun d => d = ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s ∧ ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) = ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s)
            (fun d _ => d = ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s ∧ ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) = ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s)
        have hguard : ValueShape.ttv (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValSpace.openRec G.length (uOf y sigmaV) s) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a0 a1 =
            ValueShape.ttv (orc rho (G ++ [sigmaV]) (D ++ [w])) s (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a0 a1 := by
          simp only [ValueShape.ttv, ValueShape.pair, hd0, hd1, hcontract]
          congr 1
          convert hg using 1
          · cases he : ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G)
                (ValExpr.openRec G.length (uOf y sigmaV) e0) <;>
              simp_all only []
          · cases he : ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0 <;> rfl
        simp only [hguard]
        congr 1
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        let dContract := ValSpace.dof
          (orc rho (G ++ [sigmaV]) (D ++ [w])) s
        exact inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 h0
          (if i = 0 then (Finset.range dContract).sum fun j =>
            a0.get j * a1.get j else 0)
          (fun _ dOut => if i ≥ dOut then 0 else
            (Finset.range dContract).sum fun j =>
              a0.get (dOut * j + i) * a1.get j)
  | rho, y, sigmaV, w, G, D, .mtm n0 n1 s0 s1 e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨⟨hs0, hs1⟩, h0⟩, h1⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG
          (.mtm n0 n1 s0 s1 e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨⟨hs0, hs1⟩, h0⟩, h1⟩)
        have hcontract := dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s0 hs0
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, hcontract, ih0, ih1]
        congr 1
        funext a0 a1
        have hg0 : ValueShape.tensor (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) a0 =
            ValueShape.tensor (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) a0 :=
          inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 h0 False (fun d0 d1 => a0.length = d0 * d1)
        have hg1 : ValueShape.tensor (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a1 =
            ValueShape.tensor (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a1 :=
          inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e1 h1 False (fun d0 d1 => a1.length = d0 * d1)
        have hg := inferTprodPairDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 e1 h0 h1 False
            (fun d00 _ _ d11 => d00 = ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s0 ∧ d11 = ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s0)
        have hguard : ValueShape.mtm (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValSpace.openRec G.length (uOf y sigmaV) s0) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a0 a1 =
            ValueShape.mtm (orc rho (G ++ [sigmaV]) (D ++ [w])) s0 (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a0 a1 := by
          simp only [ValueShape.mtm, ValueShape.matrices, hg0, hg1, hcontract]
          exact congrArg (fun p => (ValueShape.tensor (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) a0 ∧ ValueShape.tensor (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a1) ∧ p) hg
        simp only [hguard]
        congr 1
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        let dContract := ValSpace.dof
          (orc rho (G ++ [sigmaV]) (D ++ [w])) s0
        exact inferTprodPairDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 e1 h0 h1 0
          (fun _ d0 dTarget _ =>
            if i ≥ dTarget * d0 then 0 else
              (Finset.range dContract).sum fun k =>
                a0.get (d0 * k + i % d0) *
                  a1.get (dContract * (i / d0) + k))
  | rho, y, sigmaV, w, G, D, .vkrn e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨h0, h1⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.vkrn e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨h0, h1⟩)
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ih0, ih1]
        congr 1
        funext a0 a1
        have hg0 : ValueShape.tensor (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) a0 =
            ValueShape.tensor (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) a0 :=
          inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 h0 False (fun d0 d1 => a0.length = d0 * d1)
        have hg1 : ValueShape.tensor (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a1 =
            ValueShape.tensor (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a1 :=
          inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e1 h1 False (fun d0 d1 => a1.length = d0 * d1)
        simp only [ValueShape.matrices, hg0, hg1]
        congr 1
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        exact inferTprodPairDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 e1 h0 h1 0
          (fun _ d2 d1 d3 =>
            let dRightOut := d2 * d3
            let iLeft := i / dRightOut
            let iRight := i % dRightOut
            let i0 := iLeft / d1
            let i1 := iLeft % d1
            let j0 := iRight / d3
            let j1 := iRight % d3
            a0.get (d2 * i0 + j0) * a1.get (d3 * i1 + j1))
  | rho, y, sigmaV, w, G, D, .vblk e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨h0, h1⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.vblk e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨h0, h1⟩)
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ih0, ih1]
        congr 1
        funext a0 a1
        have hg0 : ValueShape.tensor (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) a0 =
            ValueShape.tensor (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) a0 :=
          inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 h0 False (fun d0 d1 => a0.length = d0 * d1)
        have hg1 : ValueShape.tensor (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a1 =
            ValueShape.tensor (orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a1 :=
          inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e1 h1 False (fun d0 d1 => a1.length = d0 * d1)
        simp only [ValueShape.matrices, hg0, hg1]
        congr 1
        apply congrArg Except.ok
        apply ValValSem.arrayOf_congr rfl
        intro i
        exact inferTprodPairDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 e1 h0 h1 0
          (fun d0 d2 _ d3 =>
            let dRightOut := d2 + d3
            let iLeft := i / dRightOut
            let iRight := i % dRightOut
            if iLeft < d0 then
              if iRight < d2 then a0.get (d2 * iLeft + iRight) else 0
            else if iRight < d2 then 0
            else a1.get (d3 * (iLeft - d0) + (iRight - d2)))
  | rho, y, sigmaV, w, G, D, .pinv e =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv] at hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.pinv e) hy
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG hy
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe]
        congr 1
        funext a
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.pinv e))
        exact inferTprodOrDof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e hy
          (fun d => (if a.length = d then
            Except.ok (.arrayOf outDim (fun i =>
              let M : Matrix (Fin d) (Fin 1) ℝ := fun j _ => a.get j.val
              matrixAsDenot (matrixSVDPinv M) i))
            else Except.error .mismatch : Except DimError ValValSem))
          (fun d0 d1 => (if a.length = d0 * d1 then
            Except.ok (.arrayOf outDim (fun i =>
              let M : Matrix (Fin d0) (Fin d1) ℝ :=
                denotAsMatrix d0 d1 a.get
              matrixAsDenot (matrixSVDPinv M) i))
            else Except.error .mismatch : Except DimError ValValSem))
  | rho, y, sigmaV, w, G, D, .gsvdS e a b =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨he, ha⟩, hb⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdS e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe, iha, ihb]
        congr 1
        funext ae aa ab
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdS e a b))
        exact inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e he
          (Except.error .mismatch)
          (fun d0 d1 =>
            match ValueCanonicalFSV.evalSigma d0 d1 ae aa ab with
            | .error err => .error err
            | .ok r => if r.rows * r.cols = outDim then
                .ok (ValValSem.array r.flatten) else .error .mismatch)
  | rho, y, sigmaV, w, G, D, .gsvdU e a b =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨he, ha⟩, hb⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdU e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe, iha, ihb]
        congr 1
        funext ae aa ab
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdU e a b))
        exact inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e he
          (Except.error .mismatch)
          (fun d0 d1 =>
            match ValueCanonicalFSV.eval .cokernel d0 d1 ae aa ab with
            | .error err => .error err
            | .ok r => if r.rows * r.cols = outDim then
                .ok (ValValSem.array r.flatten) else .error .mismatch)
  | rho, y, sigmaV, w, G, D, .gsvdUI e a b =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨he, ha⟩, hb⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdUI e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe, iha, ihb]
        congr 1
        funext ae aa ab
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdUI e a b))
        exact inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e he
          (Except.error .mismatch)
          (fun d0 d1 =>
            match ValueCanonicalFSV.eval .kernel d0 d1 ae aa ab with
            | .error err => .error err
            | .ok r => if r.rows * r.cols = outDim then
                .ok (ValValSem.array r.flatten) else .error .mismatch)
  | rho, y, sigmaV, w, G, D, .gsvdV e a b =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨he, ha⟩, hb⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdV e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe, iha, ihb]
        congr 1
        funext ae aa ab
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdV e a b))
        exact inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e he
          (Except.error .mismatch)
          (fun d0 d1 =>
            match ValueCanonicalFSV.eval .image d0 d1 ae aa ab with
            | .error err => .error err
            | .ok r => if r.rows * r.cols = outDim then
                .ok (ValValSem.array r.flatten) else .error .mismatch)
  | rho, y, sigmaV, w, G, D, .gsvdVI e a b =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨he, ha⟩, hb⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdVI e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe, iha, ihb]
        congr 1
        funext ae aa ab
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdVI e a b))
        exact inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e he
          (Except.error .mismatch)
          (fun d0 d1 =>
            match ValueCanonicalFSV.eval .coimage d0 d1 ae aa ab with
            | .error err => .error err
            | .ok r => if r.rows * r.cols = outDim then
                .ok (ValValSem.array r.flatten) else .error .mismatch)
  | rho, y, sigmaV, w, G, D, .gpinv e a b =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨he, ha⟩, hb⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gpinv e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe, iha, ihb]
        congr 1
        funext ae aa ab
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gpinv e a b))
        exact inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e he
          (Except.error .mismatch)
          (fun d0 d1 => (if GSVDInputsShape d0 d1 ae aa ab then
            Except.ok (.arrayOf outDim (fun i =>
              let M : Matrix (Fin d1) (Fin d0) ℝ :=
                (denotAsMatrix d0 d1 ae.get).transpose
              let MW : Matrix (Fin d0) (Fin d0) ℝ :=
                denotAsMatrix d0 d0 aa.get
              let MV : Matrix (Fin d1) (Fin d1) ℝ :=
                denotAsMatrix d1 d1 ab.get
              let P : Matrix (Fin d0) (Fin d1) ℝ := matrixGSVDPinv M MW MV
              matrixAsDenot (m := d1) (n := d0) P.transpose i))
            else Except.error .mismatch : Except DimError ValValSem))
  | rho, y, sigmaV, w, G, D, .rrefRep e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨h0, h1⟩ := hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.rrefRep e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨h0, h1⟩)
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ih0, ih1]
        congr 1
        funext a0 a1
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.rrefRep e0 e1))
        exact inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e1 h1
          (Except.error DimError.mismatch : Except DimError ValValSem)
          (fun dp0 dp1 => (
            let K := a0.length / dp0
            if dp0 = dp1 ∧ a0.length = K * dp0 ∧
                a1.length = dp0 * dp0 then
              Except.ok (ValValSem.arrayOf outDim
                (termsRREFRepDenot dp0 K a0.get a1.get))
            else Except.error DimError.mismatch : Except DimError ValValSem))
  | rho, y, sigmaV, w, G, D, .inv e =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv] at hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.inv e) hy
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG hy
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe]
        congr 1
        funext a
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.inv e))
        exact inferTprodOrDof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e hy
          (fun d => (if a.length = d then
            Except.ok (.arrayOf outDim (fun i =>
              let M : Matrix (Fin d) (Fin 1) ℝ := fun j _ => a.get j.val
              matrixAsDenot (matrixSVDPinv M) i))
            else Except.error .mismatch : Except DimError ValValSem))
          (fun d0 d1 => (if a.length = d0 * d1 then
            Except.ok (.arrayOf outDim (fun i =>
              let M : Matrix (Fin d0) (Fin d1) ℝ :=
                denotAsMatrix d0 d1 a.get
              matrixAsDenot (matrixSVDPinv M) i))
            else Except.error .mismatch : Except DimError ValValSem))
  | rho, y, sigmaV, w, G, D, .svds e =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv] at hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.svds e) hy
        have ihe := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e hlen hlc hySigma hyG hy
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_semS, denotValB_semS, hwhole, ihe]
        congr 1
        funext a
        let outDim := ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
          (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.svds e))
        exact inferTprodDofs_valueOpenPush_from_leaf horacle
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e hy
          (Except.error .mismatch)
          (fun d0 d1 => (if a.length = d0 * d1 then
            Except.ok (.arrayOf outDim (fun i =>
              let M : Matrix (Fin d1) (Fin d0) ℝ :=
                (denotAsMatrix d0 d1 a.get).transpose
              let g := ValueCanonicalFSV.standard M
              matrixAsDenot (m := g.r) (n := g.r) g.sMat i))
            else Except.error .mismatch : Except DimError ValValSem))
  | rho, y, sigmaV, w, G, D, .vlam tau0 tau1 body =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨hy0, _hy1⟩, hyBody⟩ := hy
        simp only [ValExpr.openRec, denotValB_semS]
        have hEl :
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) D
              (ValTy.openRec G.length (uOf y sigmaV) tau0)).El =
            (denotValTyS orc rho (G ++ [sigmaV]) (D ++ [w]) tau0).El := by
          rw [denotValTyS_El_eq_carrierEl_raw,
            denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
        apply congrArg Except.ok
        refine ValValSem.fn_congr _ _ hEl ?_
        intro a
        let namedCanon := ValValSem.fromEl
          (denotValTyS orc (rho.update y w)
            (ValTy.closePrefix (uOf y sigmaV) G) D
            (ValTy.openRec G.length (uOf y sigmaV) tau0)) a
        have hcanon := fromEl_valueOpenPush_from_leaf horacle hlen rfl hlc
          hySigma hyG tau0 hy0 (hEl ▸ a) a (cast_heq hEl a)
        have hlen' : (tau0 :: G).length = (namedCanon :: D).length := by
          simp only [List.length_cons, hlen]
        have hyG' : forall tauV, tauV ∈ tau0 :: G ->
            y ∉ ValTy.fv tauV := by
          intro tauV htau
          rcases List.mem_cons.mp htau with rfl | htau
          · exact hy0
          · exact hyG tauV htau
        have ih := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w (tau0 :: G) (namedCanon :: D) body
          hlen' hlc hySigma hyG' hyBody
        change
          denotValB_semS orc (rho.update y w)
              (ValTy.openRec G.length (uOf y sigmaV) tau0 ::
                ValTy.closePrefix (uOf y sigmaV) G)
              (namedCanon :: D)
              (ValExpr.openRec (G.length + 1) (uOf y sigmaV) body) =
            denotValB_semS orc rho (tau0 :: (G ++ [sigmaV]))
              (ValValSem.fromEl
                (denotValTyS orc rho (G ++ [sigmaV]) (D ++ [w]) tau0)
                (hEl ▸ a) :: (D ++ [w])) body
        rw [hcanon]
        simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
          Nat.succ_eq_add_one] using ih
  | rho, y, sigmaV, w, G, D, .appV e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨h0, h1⟩ := hy
        have ih0 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := denotValB_semS_valueOpenPush_from_leaf orc horacle hreshape
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        have hinfer := inferTypeCtxRaised_valueOpenPush
          (y := y) (sigmaV := sigmaV) hlc G e0
        have hshape : ValSoundOfDenot.ValTy.SameShape
            (ValExpr.inferTypeCtx
              (ValTy.closePrefix (uOf y sigmaV) G)
              (ValExpr.openRec G.length (uOf y sigmaV) e0)).domain
            (ValExpr.inferTypeCtx (G ++ [sigmaV]) e0).domain := by
          rw [hinfer, ValTy.domain_openRec]
          exact ValSoundOfDenot.ValTy.SameShape_openRec
            G.length (uOf y sigmaV)
              (ValExpr.inferTypeCtx (G ++ [sigmaV]) e0).domain
        have hEl :
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) D
              (ValExpr.inferTypeCtx
                (ValTy.closePrefix (uOf y sigmaV) G)
                (ValExpr.openRec G.length (uOf y sigmaV) e0)).domain).El =
            (denotValTyS orc rho (G ++ [sigmaV]) (D ++ [w])
              (ValExpr.inferTypeCtx (G ++ [sigmaV]) e0).domain).El := by
          rw [denotValTyS_El_eq_carrierEl_raw,
            denotValTyS_El_eq_carrierEl_raw,
            ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape]
        simp only [ValExpr.openRec]
        rw [denotValB_semS, denotValB_semS, ih0]
        generalize hfun : denotValB_semS orc rho
          (G ++ [sigmaV]) (D ++ [w]) e0 = funResult
        cases funResult with
        | error err => rfl
        | ok funVal =>
            cases funVal with
            | array a => rfl
            | fn T f =>
                rw [ih1]
                generalize harg : denotValB_semS orc rho
                  (G ++ [sigmaV]) (D ++ [w]) e1 = argResult
                cases argResult with
                | error err => rfl
                | ok arg =>
                    have htoEl : HEq
                        (ValValSem.toElDomainChecked
                          (denotValTyS orc (rho.update y w)
                            (ValTy.closePrefix (uOf y sigmaV) G) D
                            (ValExpr.inferTypeCtx
                              (ValTy.closePrefix (uOf y sigmaV) G)
                              (ValExpr.openRec G.length
                                (uOf y sigmaV) e0)).domain) arg)
                        (ValValSem.toElDomainChecked
                          (denotValTyS orc rho (G ++ [sigmaV]) (D ++ [w])
                            (ValExpr.inferTypeCtx
                              (G ++ [sigmaV]) e0).domain) arg) := by
                      have hfresh := ValTy.notMem_fv_domain
                        (ValExpr.notMem_fv_inferTypeCtx y e0 (G ++ [sigmaV]) h0
                          (fresh_append_singleton hySigma hyG))
                      rw [hinfer, ValTy.domain_openRec]
                      exact toElDomainChecked_valueOpenPush_from_leaf horacle
                          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
                          (G := G) (D := D) hlen hlc hySigma hyG
                          (ValExpr.inferTypeCtx (G ++ [sigmaV]) e0).domain hfresh arg
                    exact valSound_appV_match_congr_domainChecked (.fn T f) arg arg hEl htoEl
  termination_by rho y sigmaV w G D e => ValExpr.size e
  decreasing_by
    all_goals
      first
      | (simp only [ValExpr.size]; omega)
      | (simp only [ValExpr.size]
         have := ValExpr.size_le_sizeList hmem; omega)

theorem valueOpenPushEvalPrefix_from_leaf
    (orc : FFSOracleSem) (horacle : RawValueOpenPushOracleCoherent orc) :
    ValueOpenPushEvalPrefix orc := by
  intro rho y sigmaV w G D e hlen hlc hySigma hyG hy
  exact denotValB_semS_valueOpenPush_from_leaf orc horacle
    (reshapePrefixTransport_from_leaf horacle)
    rho y sigmaV w G D e hlen hlc hySigma hyG hy

theorem evalPrefixFromLeaf :
    EvalPrefixFromLeaf := by
  intro orc horacle
  exact valueOpenPushEvalPrefix_from_leaf orc horacle

/-- The adequacy-facing evaluator boundary is the empty-prefix instance of
the stronger telescope transport. -/
theorem ValueOpenPushEvalPrefix.to_public
    {orc : FFSOracleSem} (h : ValueOpenPushEvalPrefix orc) :
    RawValueOpenPushEvalCoherent orc := by
  intro rho y sigmaV w expression hlcSigma _hlcOpened
    hySigma hyExpression
  exact h (G := []) (D := []) (e := expression) rfl hlcSigma
    hySigma (by simp) hyExpression

/-- Primitive leaf coherence constructively entails the public evaluator
coherence law; no direct-oracle-specific assumption is used. -/
theorem valueOpenPushEvalCoherent_from_leaf
    {orc : FFSOracleSem} (h : RawValueOpenPushOracleCoherent orc) :
    RawValueOpenPushEvalCoherent orc :=
  ValueOpenPushEvalPrefix.to_public
    (valueOpenPushEvalPrefix_from_leaf orc h)

end GLang.DirectOracleEval
