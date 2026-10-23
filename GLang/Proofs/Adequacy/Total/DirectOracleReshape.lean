import GLang.Proofs.Adequacy.Total.DirectOracleOpenPush

namespace GLang.DirectOracleReshape

open DirectOracleOpenPush

/-! ## The paired open/push world -/

/-- All data which is invariant while the evaluator descends below binders.
`G/D` is the prefix inside the distinguished slot. -/
structure OpenPushWorld (orc : FFSOracleSem) where
  rho : ValEnvSem
  y : VName
  sigmaV : ValTy
  w : ValValSem
  G : List ValTy
  D : List ValValSem
  length_eq : G.length = D.length
  sigma_lc : ValTy.lc sigmaV
  y_sigma : y ∉ ValTy.fv sigmaV
  y_G : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV

namespace OpenPushWorld

def u (W : OpenPushWorld orc) : ValExpr := .var W.y W.sigmaV
def namedG (W : OpenPushWorld orc) : List ValTy := ValTy.closePrefix W.u W.G
def pushedG (W : OpenPushWorld orc) : List ValTy := W.G ++ [W.sigmaV]
def namedD (W : OpenPushWorld orc) : List ValValSem := W.D
def pushedD (W : OpenPushWorld orc) : List ValValSem := W.D ++ [W.w]
def namedRho (W : OpenPushWorld orc) : ValEnvSem := W.rho.update W.y W.w
def pushedRho (W : OpenPushWorld orc) : ValEnvSem := W.rho

def extend (W : OpenPushWorld orc) (tau : ValTy) (v : ValValSem)
    (hy : W.y ∉ ValTy.fv tau) : OpenPushWorld orc where
  rho := W.rho
  y := W.y
  sigmaV := W.sigmaV
  w := W.w
  G := tau :: W.G
  D := v :: W.D
  length_eq := by simp [W.length_eq]
  sigma_lc := W.sigma_lc
  y_sigma := W.y_sigma
  y_G := by
    intro tau' htau'
    rcases List.mem_cons.mp htau' with rfl | htau'
    · exact hy
    · exact W.y_G tau' htau'

@[simp] theorem extend_u (W : OpenPushWorld orc) (tau : ValTy)
    (v : ValValSem) (hy) : (W.extend tau v hy).u = W.u := rfl

@[simp] theorem extend_namedG (W : OpenPushWorld orc) (tau : ValTy)
    (v : ValValSem) (hy) :
    (W.extend tau v hy).namedG =
      ValTy.openRec W.G.length W.u tau :: W.namedG := by
  simp [extend, namedG, u, ValTy.closePrefix]

@[simp] theorem extend_pushedG (W : OpenPushWorld orc) (tau : ValTy)
    (v : ValValSem) (hy) :
    (W.extend tau v hy).pushedG = tau :: W.pushedG := by
  simp [extend, pushedG]

@[simp] theorem extend_namedD (W : OpenPushWorld orc) (tau : ValTy)
    (v : ValValSem) (hy) :
    (W.extend tau v hy).namedD = v :: W.namedD := rfl

@[simp] theorem extend_pushedD (W : OpenPushWorld orc) (tau : ValTy)
    (v : ValValSem) (hy) :
    (W.extend tau v hy).pushedD = v :: W.pushedD := by
  simp [extend, pushedD]

@[simp] theorem extend_depth (W : OpenPushWorld orc) (tau : ValTy)
    (v : ValValSem) (hy) : (W.extend tau v hy).G.length = W.G.length + 1 := by
  simp [extend]

end OpenPushWorld

/-! ## Leaf propagation through spaces -/

theorem shpOf_valueOpenPush_local
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    (W : OpenPushWorld orc) :
    forall (s : ValSpace), W.y ∉ ValSpace.fv s ->
      ValSpace.shpOf (orc W.namedRho W.namedG W.namedD)
          (ValSpace.openRec W.G.length W.u s) =
        ValSpace.shpOf (orc W.pushedRho W.pushedG W.pushedD) s :=
  shpOf_valueOpenPush_from_leaf horacle W.length_eq W.sigma_lc
    W.y_sigma W.y_G

theorem dof_valueOpenPush_local
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    (W : OpenPushWorld orc) (s : ValSpace) (hy : W.y ∉ ValSpace.fv s) :
    ValSpace.dof (orc W.namedRho W.namedG W.namedD)
        (ValSpace.openRec W.G.length W.u s) =
      ValSpace.dof (orc W.pushedRho W.pushedG W.pushedD) s := by
  simpa only [ValSpace.dof] using congrArg
    (fun xs => xs.foldr (fun a b => a * b) 1)
    (shpOf_valueOpenPush_local horacle W s hy)

/-! ## Checked reification -/

/-- Checked reification has the same open/push law as ordinary reification.
This is the extra ingredient needed by the higher-order reshape callback. -/
theorem fromElChecked_valueOpenPush_local
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {Dp Dc : List ValValSem}
    (hlen : G.length = Dp.length) (hD : Dp = Dc)
    (hlcSigma : ValTy.lc sigmaV) (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall (tau : ValTy), y ∉ ValTy.fv tau ->
      forall
        (a : (denotValTyS orc (rho.update y w)
          (ValTy.closePrefix (uOf y sigmaV) G) Dc
          (ValTy.openRec G.length (uOf y sigmaV) tau)).El)
        (a' : (denotValTyS orc rho
          (G ++ [sigmaV]) (Dp ++ [w]) tau).El),
        HEq a a' ->
        ValValSem.fromElChecked
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau)) a =
          ValValSem.fromElChecked
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau) a'
  | .space s, hy, a, a', ha => by
      simp only [ValTy.fv] at hy
      have haa : a = a' := eq_of_heq ha
      subst haa
      subst Dc
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromElChecked]
      rw [dof_valueOpenPush_from_leaf horacle hlen hlcSigma hySigma hyG s hy]
  | .piTy tau0 tau1, hy, a, a', ha => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      have hEl :
          (denotValTyS orc (rho.update y w)
            (ValTy.closePrefix (uOf y sigmaV) G) Dc
            (ValTy.openRec G.length (uOf y sigmaV) tau0)).El =
          (denotValTyS orc rho
            (G ++ [sigmaV]) (Dp ++ [w]) tau0).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      have hbeta : HEq
          (fun b : (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau0)).El =>
            Except DimError
              (denotValTyS orc (rho.update y w)
                (ValTy.openRec G.length (uOf y sigmaV) tau0 ::
                  ValTy.closePrefix (uOf y sigmaV) G)
                (ValValSem.fromEl
                  (denotValTyS orc (rho.update y w)
                    (ValTy.closePrefix (uOf y sigmaV) G) Dc
                    (ValTy.openRec G.length (uOf y sigmaV) tau0)) b :: Dc)
                (ValTy.openRec (G.length + 1) (uOf y sigmaV) tau1)).El)
          (fun b' : (denotValTyS orc rho
              (G ++ [sigmaV]) (Dp ++ [w]) tau0).El =>
            Except DimError
              (denotValTyS orc rho
                (tau0 :: (G ++ [sigmaV]))
                (ValValSem.fromEl
                  (denotValTyS orc rho
                    (G ++ [sigmaV]) (Dp ++ [w]) tau0) b' :: (Dp ++ [w]))
                tau1).El) := by
        refine Function.hfunext hEl ?_
        intro b b' _
        apply heq_of_eq
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromElChecked]
      apply congrArg Except.ok
      refine ValValSem.fn_congr _ _ hEl ?_
      intro b
      have hab : HEq (a b) (a' (hEl ▸ b)) :=
        heq_app_dep hEl hbeta ha (cast_heq hEl b).symm
      have hcanon := fromEl_valueOpenPush_from_leaf horacle hlen hD
        hlcSigma hySigma hyG tau0 hy.1 (hEl ▸ b) b
        (cast_heq hEl b)
      have hCod :
          (denotValTyS orc (rho.update y w)
            (ValTy.openRec G.length (uOf y sigmaV) tau0 ::
              ValTy.closePrefix (uOf y sigmaV) G)
            (ValValSem.fromEl
              (denotValTyS orc (rho.update y w)
                (ValTy.closePrefix (uOf y sigmaV) G) Dc
                (ValTy.openRec G.length (uOf y sigmaV) tau0)) b :: Dc)
            (ValTy.openRec (G.length + 1) (uOf y sigmaV) tau1)).El =
          (denotValTyS orc rho
            (tau0 :: (G ++ [sigmaV]))
            (ValValSem.fromEl
              (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0)
                (hEl ▸ b) :: (Dp ++ [w])) tau1).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      apply except_bind_heq_congr hCod (a b) (a' (hEl ▸ b)) hab
      intro z z' hzz
      have hlen' : (tau0 :: G).length =
          (ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0)
              (hEl ▸ b) :: Dp).length := by
        simp only [List.length_cons, hlen]
      have hD' :
          (ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0)
              (hEl ▸ b) :: Dp) =
          (ValValSem.fromEl
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau0)) b :: Dc) :=
        congrArg₂ List.cons hcanon hD
      have hyG' : forall tauV, tauV ∈ tau0 :: G ->
          y ∉ ValTy.fv tauV := by
        intro tauV htau
        rcases List.mem_cons.mp htau with rfl | htau
        · exact hy.1
        · exact hyG tauV htau
      have ih := fromElChecked_valueOpenPush_local horacle hlen' hD'
        hlcSigma hySigma hyG' tau1 hy.2 z z' hzz
      simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
        Nat.succ_eq_add_one] using ih
  termination_by tau _ _ _ _ => ValTy.kindSize tau
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-! ## Paired higher-order reshape -/

theorem applyTyped_heq_local {A B : Type} (hAB : A = B)
    (v : ValValSem) (a : A) (b : B) (hab : HEq a b) :
    v.applyTyped a = v.applyTyped b := by
  cases hAB
  exact congrArg (ValValSem.applyTyped v) (eq_of_heq hab)

theorem except_match_eq_bind_local {A : Type}
    (r : Except DimError A) (f : A -> Except DimError ValValSem) :
    (match r with
      | .error err => Except.error err
      | .ok a => f a) = r.bind f := by
  cases r with
  | error _ => rfl
  | ok _ => rfl

/-- Continuation form of the arbitrary-world `toEl` same-shape theorem.
Unlike a bare `HEq`, this statement can be rewritten directly into the
nested `match` generated by higher-order reshape. -/
theorem toEl_match_denotValTyS_sameShape_raw_local (orc : FFSOracleSem) :
    forall (d d' : ValTy), ValSoundOfDenot.ValTy.SameShape d d' ->
      forall (rho rho' : ValEnvSem) (G G' : List ValTy)
        (D D' : List ValValSem) (v : ValValSem)
        (f : (denotValTyS orc rho G D d).El -> Except DimError ValValSem)
        (g : (denotValTyS orc rho' G' D' d').El -> Except DimError ValValSem),
        (forall a a', HEq a a' -> f a = g a') ->
        (match ValValSem.toEl (denotValTyS orc rho G D d) v with
          | .error err => Except.error err
          | .ok a => f a) =
        (match ValValSem.toEl (denotValTyS orc rho' G' D' d') v with
          | .error err => Except.error err
          | .ok a' => g a')
  | .space _, .space _, _, rho, rho', G, G', D, D', v, f, g, hfg => by
      cases v with
      | array a => exact hfg a a HEq.rfl
      | fn _ _ => rfl
  | .piTy d0 d1, .piTy d0' d1', hshape,
      rho, rho', G, G', D, D', v, f, g, hfg => by
      obtain ⟨hshape0, hshape1⟩ := hshape
      cases v with
      | array _ => rfl
      | fn T' fam =>
          have hEl : (denotValTyS orc rho G D d0).El =
              (denotValTyS orc rho' G' D' d0').El := by
            rw [denotValTyS_El_eq_carrierEl_raw,
              denotValTyS_El_eq_carrierEl_raw,
              ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape0]
          simp only [denotValTyS, ValValSem.toEl]
          by_cases hT : (denotValTyS orc rho G D d0).El = T'
          · have hT' : (denotValTyS orc rho' G' D' d0').El = T' := hEl ▸ hT
            rw [dif_pos hT, dif_pos hT']
            apply hfg
            refine Function.hfunext hEl ?_
            intro a a' haa
            have hcast : fam (hT ▸ a) = fam (hT' ▸ a') := by
              congr 1
              apply eq_of_heq
              exact HEq.trans (cast_heq hT a)
                (HEq.trans haa (HEq.symm (cast_heq hT' a')))
            rw [hcast]
            have hCodEl :
                (denotValTyS orc rho (d0 :: G)
                  (ValValSem.fromEl (denotValTyS orc rho G D d0) a :: D)
                  d1).El =
                (denotValTyS orc rho' (d0' :: G')
                  (ValValSem.fromEl
                    (denotValTyS orc rho' G' D' d0') a' :: D') d1').El := by
              rw [denotValTyS_El_eq_carrierEl_raw,
                denotValTyS_El_eq_carrierEl_raw,
                ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape1]
            cases hfam : fam (hT' ▸ a') with
            | error err => exact except_error_heq hCodEl err
            | ok out =>
                exact toEl_denotValTyS_sameShape_raw orc d1 d1' hshape1
                  rho rho' (d0 :: G) (d0' :: G')
                  (ValValSem.fromEl (denotValTyS orc rho G D d0) a :: D)
                  (ValValSem.fromEl
                    (denotValTyS orc rho' G' D' d0') a' :: D') out
          · have hT' : ¬ ((denotValTyS orc rho' G' D' d0').El = T') :=
              fun h => hT (hEl ▸ h)
            rw [dif_neg hT, dif_neg hT']
  | .space _, .piTy _ _, hshape, _, _, _, _, _, _, _, _, _, _ =>
      hshape.elim
  | .piTy _ _, .space _, hshape, _, _, _, _, _, _, _, _, _, _ =>
      hshape.elim
  termination_by d _ _ _ _ _ _ _ _ _ _ _ _ => ValTy.kindSize d
  decreasing_by
    all_goals simp only [ValTy.kindSize_piTy]
    all_goals omega

/-- Prefix-general transport for paired-context reshape.  Target and source
prefixes are tracked independently because the Pi-domain recursive call swaps
them, while the Pi-codomain call extends each by its own reshaped argument. -/
theorem reshapDenotSemBetweenS_valueOpenPush_local
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem} :
    forall (v : ValValSem) (target source : ValTy)
      (Gt : List ValTy) (Dt : List ValValSem)
      (Gs : List ValTy) (Ds : List ValValSem),
      Gt.length = Dt.length -> Gs.length = Ds.length ->
      ValTy.lc sigmaV -> y ∉ ValTy.fv sigmaV ->
      (forall tauV, tauV ∈ Gt -> y ∉ ValTy.fv tauV) ->
      (forall tauV, tauV ∈ Gs -> y ∉ ValTy.fv tauV) ->
      y ∉ ValTy.fv target -> y ∉ ValTy.fv source ->
      reshapDenotSemBetweenS orc (rho.update y w)
          (ValTy.closePrefix (uOf y sigmaV) Gt) Dt
          (ValTy.closePrefix (uOf y sigmaV) Gs) Ds v
          (ValTy.openRec Gt.length (uOf y sigmaV) target)
          (ValTy.openRec Gs.length (uOf y sigmaV) source) =
        reshapDenotSemBetweenS orc rho
          (Gt ++ [sigmaV]) (Dt ++ [w])
          (Gs ++ [sigmaV]) (Ds ++ [w]) v target source
  | .array a, .space st, .space ss, Gt, Dt, Gs, Ds,
      htlen, hslen, hlcSigma, hySigma, hyGt, hyGs, hyt, hys => by
      simp only [ValTy.fv] at hyt hys
      simp only [ValTy.openRec, reshapDenotSemBetweenS,
        reshapArrayBetweenS]
      rw [dof_valueOpenPush_from_leaf horacle hslen hlcSigma hySigma
          hyGs ss hys,
        dof_valueOpenPush_from_leaf horacle htlen hlcSigma hySigma
          hyGt st hyt]
  | .array a, .space st, .piTy ss0 ss1, Gt, Dt, Gs, Ds,
      htlen, hslen, hlcSigma, hySigma, hyGt, hyGs, hyt, hys => by
      simp only [ValTy.openRec, reshapDenotSemBetweenS,
        reshapArrayBetweenS]
  | .fn T f, .space st, source, Gt, Dt, Gs, Ds,
      htlen, hslen, hlcSigma, hySigma, hyGt, hyGs, hyt, hys => by
      simp only [ValTy.openRec]
      rw [reshapDenotSemBetweenS.eq_2, reshapDenotSemBetweenS.eq_2]
  | v, .piTy tt0 tt1, .piTy ts0 ts1, Gt, Dt, Gs, Ds,
      htlen, hslen, hlcSigma, hySigma, hyGt, hyGs, hyt, hys => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hyt hys
      simp only [ValTy.openRec]
      rw [reshapDenotSemBetweenS.eq_3, reshapDenotSemBetweenS.eq_3]
      have hElT :
          (denotValTyS orc (rho.update y w)
            (ValTy.closePrefix (uOf y sigmaV) Gt) Dt
            (ValTy.openRec Gt.length (uOf y sigmaV) tt0)).El =
          (denotValTyS orc rho
            (Gt ++ [sigmaV]) (Dt ++ [w]) tt0).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      apply congrArg Except.ok
      refine ValValSem.fn_congr _ _ hElT ?_
      intro a
      dsimp only
      have hcheck := fromElChecked_valueOpenPush_local horacle
        (G := Gt) (Dp := Dt) (Dc := Dt) htlen rfl hlcSigma hySigma
        hyGt tt0 hyt.1 a (hElT ▸ a) (cast_heq hElT a).symm
      rw [hcheck]
      generalize hpcheck : ValValSem.fromElChecked
        (denotValTyS orc rho (Gt ++ [sigmaV]) (Dt ++ [w]) tt0)
          (hElT ▸ a) = checkResult
      cases checkResult with
      | error err => simp only [hpcheck]
      | ok argT =>
          simp only [hpcheck]
          have harg := reshapDenotSemBetweenS_valueOpenPush_local horacle
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            argT ts0 tt0 Gs Ds Gt Dt hslen htlen hlcSigma hySigma
            hyGs hyGt hys.1 hyt.1
          rw [harg]
          generalize hparg : reshapDenotSemBetweenS orc rho
            (Gs ++ [sigmaV]) (Ds ++ [w])
            (Gt ++ [sigmaV]) (Dt ++ [w]) argT ts0 tt0 = argResult
          cases argResult with
          | error err => simp only [hparg]
          | ok argS =>
              simp only [hparg]
              have hmatch := toEl_match_denotValTyS_sameShape_raw_local orc
                (ValTy.openRec Gs.length (uOf y sigmaV) ts0) ts0
                (ValSoundOfDenot.ValTy.SameShape_openRec
                  Gs.length (uOf y sigmaV) ts0)
                (rho.update y w) rho
                (ValTy.closePrefix (uOf y sigmaV) Gs) (Gs ++ [sigmaV])
                Ds (Ds ++ [w]) argS
                (fun argEl =>
                  match v.applyTyped argEl with
                  | .error err => Except.error err
                  | .ok res =>
                      reshapDenotSemBetweenS orc (rho.update y w)
                        (ValTy.openRec Gt.length (uOf y sigmaV) tt0 ::
                          ValTy.closePrefix (uOf y sigmaV) Gt) (argT :: Dt)
                        (ValTy.openRec Gs.length (uOf y sigmaV) ts0 ::
                          ValTy.closePrefix (uOf y sigmaV) Gs) (argS :: Ds)
                        res
                        (ValTy.openRec (Gt.length + 1) (uOf y sigmaV) tt1)
                        (ValTy.openRec (Gs.length + 1) (uOf y sigmaV) ts1))
                (fun argEl' =>
                  match v.applyTyped argEl' with
                  | .error err => Except.error err
                  | .ok res =>
                      reshapDenotSemBetweenS orc rho
                        (tt0 :: (Gt ++ [sigmaV])) (argT :: (Dt ++ [w]))
                        (ts0 :: (Gs ++ [sigmaV])) (argS :: (Ds ++ [w]))
                        res tt1 ts1) (by
                intro argEl argEl' hargEl
                have hElS :
                  (denotValTyS orc (rho.update y w)
                    (ValTy.closePrefix (uOf y sigmaV) Gs) Ds
                    (ValTy.openRec Gs.length (uOf y sigmaV) ts0)).El =
                  (denotValTyS orc rho
                    (Gs ++ [sigmaV]) (Ds ++ [w]) ts0).El := by
                  rw [denotValTyS_El_eq_carrierEl_raw,
                    denotValTyS_El_eq_carrierEl_raw,
                    ValTy.carrierEl_openRec]
                have happ := applyTyped_heq_local hElS v argEl argEl' hargEl
                simp only
                rw [happ]
                generalize hpapp : v.applyTyped argEl' = appResult
                cases appResult with
                | error err => simp only [hpapp]
                | ok res =>
                    simp only [hpapp]
                    have htlen' : (tt0 :: Gt).length = (argT :: Dt).length := by
                      simp only [List.length_cons, htlen]
                    have hslen' : (ts0 :: Gs).length = (argS :: Ds).length := by
                      simp only [List.length_cons, hslen]
                    have hyGt' : forall tauV, tauV ∈ tt0 :: Gt ->
                        y ∉ ValTy.fv tauV := by
                      intro tauV htau
                      rcases List.mem_cons.mp htau with rfl | htau
                      · exact hyt.1
                      · exact hyGt tauV htau
                    have hyGs' : forall tauV, tauV ∈ ts0 :: Gs ->
                        y ∉ ValTy.fv tauV := by
                      intro tauV htau
                      rcases List.mem_cons.mp htau with rfl | htau
                      · exact hys.1
                      · exact hyGs tauV htau
                    have hcod := reshapDenotSemBetweenS_valueOpenPush_local
                      horacle (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
                      res tt1 ts1 (tt0 :: Gt) (argT :: Dt)
                      (ts0 :: Gs) (argS :: Ds) htlen' hslen' hlcSigma
                      hySigma hyGt' hyGs' hyt.2 hys.2
                    simpa only [List.cons_append, ValTy.closePrefix,
                      List.length_cons, Nat.succ_eq_add_one] using hcod)
              generalize hnDecode : ValValSem.toEl
                (denotValTyS orc (rho.update y w)
                  (ValTy.closePrefix (uOf y sigmaV) Gs) Ds
                  (ValTy.openRec Gs.length (uOf y sigmaV) ts0)) argS =
                    namedDecode at hmatch ⊢
              generalize hpDecode : ValValSem.toEl
                (denotValTyS orc rho
                  (Gs ++ [sigmaV]) (Ds ++ [w]) ts0) argS =
                    pushedDecode at hmatch ⊢
              cases namedDecode <;> cases pushedDecode <;>
                simpa only using hmatch
  | v, .piTy tt0 tt1, .space ss, Gt, Dt, Gs, Ds,
      htlen, hslen, hlcSigma, hySigma, hyGt, hyGs, hyt, hys => by
      simp only [ValTy.openRec]
      rw [reshapDenotSemBetweenS.eq_4, reshapDenotSemBetweenS.eq_4]
  termination_by _v target source _ _ _ _ _ _ _ _ _ _ _ _ =>
    ValTy.kindSize target + ValTy.kindSize source
  decreasing_by
    all_goals simp only [ValTy.kindSize_piTy]
    all_goals omega

end GLang.DirectOracleReshape
