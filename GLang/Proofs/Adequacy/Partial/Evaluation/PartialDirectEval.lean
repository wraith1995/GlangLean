import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectReshape
import GLang.Proofs.Value.Partial.PartialValueRuntimeTransport
import GLang.Proofs.Adequacy.Total.DirectOracleEval

/-! All-constructor evaluator transport for the partial binder bridge. -/
namespace GLang.PartialDirectOpenPush
open DirectOracleOpenPush DirectOracleEval PartialValueTransport

abbrev numbersOrc (orc : PartialFFSOracleSem) : FFSOracleSem :=
  fun ρ Γ Δ => PartialValueEval.numbers (orc ρ Γ Δ)

theorem numbers_openPush {orc : PartialFFSOracleSem} (h : OracleOpenPush orc) :
    RawValueOpenPushOracleCoherent (numbersOrc orc) := by
  intro ρ y σ w G D p s e hlen hlc hσ hG hs he
  simp only [numbersOrc, PartialValueEval.numbers, h hlen hlc hσ hG hs he]

theorem dimensions_open {orc : PartialFFSOracleSem} (h : OracleOpenPush orc)
    (W : World orc) (ss : List ValSpace) (hs : ∀ s ∈ ss, W.y ∉ s.fv) :
    PartialValueEval.dimensions (orc W.namedRho W.namedG W.namedD)
      (ss.map (ValSpace.openRec W.G.length W.u)) =
    PartialValueEval.dimensions (orc W.pushedRho W.pushedG W.pushedD) ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      simp only [List.map_cons, PartialValueEval.dimensions,
        (observations h W s (hs s (by simp))).1,
        ih (fun t ht => hs t (by simp [ht]))]

theorem guarded_congr (q q' : PartialFFSOracle) (ss ss' : List ValSpace)
    (f g : FFSOracle → Except DimError ValValSem)
    (hs : PartialValueEval.dimensions q ss = PartialValueEval.dimensions q' ss')
    (hf : f (PartialValueEval.numbers q) = g (PartialValueEval.numbers q')) :
    PartialValueEval.withDimensions q ss f = PartialValueEval.withDimensions q' ss' g := by
  simp only [PartialValueEval.withDimensions, hs, hf]

theorem fresh_append {y : VName} {σ : ValTy} {G : List ValTy}
    (hσ : y ∉ σ.fv) (hG : ValTyCtxFresh y G) : ValTyCtxFresh y (G ++ [σ]) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact hG t ht
  · have he := List.mem_singleton.mp ht
    subst t
    exact hσ

theorem lam_eq (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (d c : ValTy) (body : ValExpr) :
    denotValB_partial orc ρ Γ Δ (.vlam d c body) =
      bindAcross (denotValTyPartial orc ρ Γ Δ d) (fun _ =>
        .ok (.fn d.carrierEl (fun a =>
          denotValB_partial orc ρ (d :: Γ) (d.carrierToVal a :: Δ) body))) := by
  rw [denotValB_partial]
  cases hd : denotValTyPartial orc ρ Γ Δ d <;> rfl

theorem app_eq (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (f a : ValExpr) :
    denotValB_partial orc ρ Γ Δ (.appV f a) =
      match ValExpr.inferTypeCtx Γ f with
      | .space _ => .error .mismatch
      | .piTy d _ => PartialValueEval.applyDomainChecked orc ρ Γ Δ d
          (denotValB_partial orc ρ Γ Δ f) (denotValB_partial orc ρ Γ Δ a) := by
  rw [denotValB_partial]
  cases ValExpr.inferTypeCtx Γ f <;> rfl

theorem decode_pi (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (d c : ValTy) (v : ValValSem) :
    PartialValueEval.decodeDomain orc ρ Γ Δ (.piTy d c) v =
      (denotValTyPartial orc ρ Γ Δ (.piTy d c)).bind (fun _ =>
        (ValTy.piTy d c).carrierFromVal v) := by
  unfold PartialValueEval.decodeDomain
  cases ht : denotValTyPartial orc ρ Γ Δ (.piTy d c) <;> rfl

theorem decode_heq {orc : PartialFFSOracleSem} (h : OracleOpenPush orc)
    (W : World orc) (d : ValTy) (hd : W.y ∉ d.fv) (v : ValValSem) :
    HEq (PartialValueEval.decodeDomain orc W.namedRho W.namedG W.namedD
        (ValTy.openRec W.G.length W.u d) v)
      (PartialValueEval.decodeDomain orc W.pushedRho W.pushedG W.pushedD d v) := by
  have ht := type_heq h d W hd
  cases d with
  | space s =>
      have he := eq_of_heq ht
      simp only [PartialValueEval.decodeDomain, he]
      cases hv : denotValTyPartial orc W.pushedRho W.pushedG W.pushedD (.space s) <;> cases v <;> rfl
  | piTy d c =>
      simp only [ValTy.openRec, decode_pi]
      have hs := ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u (.piTy d c)
      apply bind_heq (type_eq hs) (ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hs) _ _ ht
      intro _ _ _
      exact carrierFromVal_SameShape _ _ hs v

private theorem applyTyped_heq {A B : Type} (hAB : A = B) (v : ValValSem)
    (a : A) (b : B) (hab : HEq a b) : v.applyTyped a = v.applyTyped b := by
  cases hAB
  rw [eq_of_heq hab]

theorem reshape_prefix {orc : PartialFFSOracleSem} (h : OracleOpenPush orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem} {v : ValValSem} {target source : ValTy}
    (hlen : G.length = D.length) (hlc : sigmaV.lc) (hσ : y ∉ sigmaV.fv)
    (hG : ValTyCtxFresh y G) (ht : y ∉ target.fv) (hs : y ∉ source.fv) :
    PartialValueEval.reshapeBetween orc (rho.update y w)
      (ValTy.closePrefix (uOf y sigmaV) G) D (ValTy.closePrefix (uOf y sigmaV) G) D v
      (ValTy.openRec G.length (uOf y sigmaV) target)
      (ValTy.openRec G.length (uOf y sigmaV) source) =
    PartialValueEval.reshapeBetween orc rho (G ++ [sigmaV]) (D ++ [w])
      (G ++ [sigmaV]) (D ++ [w]) v target source :=
  reshape_eq h v target source ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hσ, hG⟩
    ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hσ, hG⟩ ⟨rfl, rfl, rfl, rfl⟩ ht hs

set_option maxHeartbeats 3200000 in
theorem eval_open
    (orc : PartialFFSOracleSem) (horacle : OracleOpenPush orc) :
    forall (rho : ValEnvSem) (y : VName) (sigmaV : ValTy) (w : ValValSem)
      (G : List ValTy) (D : List ValValSem) (e : ValExpr),
      G.length = D.length ->
      ValTy.lc sigmaV ->
      y ∉ ValTy.fv sigmaV ->
      (forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) ->
      y ∉ ValExpr.fv e ->
      denotValB_partial orc (rho.update y w)
          (ValTy.closePrefix (uOf y sigmaV) G) D
          (ValExpr.openRec G.length (uOf y sigmaV) e) =
        denotValB_partial orc rho (G ++ [sigmaV]) (D ++ [w]) e
  | rho, y, sigmaV, w, G, D, .bvar n =>
      fun hlen _ _ _ _ => by
        by_cases hn : n = G.length
        · subst n
          simp only [uOf, ValExpr.openRec, if_true, denotValB_partial,
            ValEnvSem.update_same]
          rw [hlen]
          simp [StrictValueAccess.lookup, List.getElem?_append_right (le_refl D.length)]
        · have hnD : n ≠ D.length := by simpa only [hlen] using hn
          simp only [uOf, ValExpr.openRec, if_neg hn, denotValB_partial]
          by_cases hlt : n < D.length
          · simp only [StrictValueAccess.lookup, List.getElem?_append_left hlt]
          · have hge : (D ++ [w]).length ≤ n := by simp only [List.length_append, List.length_singleton]; omega
            simp only [StrictValueAccess.lookup_of_ge _ _ hge,
              StrictValueAccess.lookup_of_ge _ _ (Nat.le_of_not_gt hlt)]
  | rho, y, sigmaV, w, G, D, .var z tau =>
      fun _ _ _ _ hy => by
        simp only [ValExpr.fv, Finset.mem_insert, not_or] at hy
        simp only [ValExpr.openRec, denotValB_partial]
        rw [ValEnvSem.update_other _ _ _ _ (Ne.symm hy.1)]
  | rho, y, sigmaV, w, G, D, .rlit r =>
      fun hlen hlc hySigma hyG _ => by
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.rlit r)
          (by simp only [ValExpr.fv]; exact Finset.notMem_empty y)
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.rlit r)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.rlit r)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hdim]
  | rho, y, sigmaV, w, G, D, .zero s =>
      fun hlen hlc hySigma hyG hy => by
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.zero s) hy
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.zero s)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.zero s)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hdim]
  | rho, y, sigmaV, w, G, D, .delta n s =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv] at hy
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.delta n s) hy
        have hs := dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hy
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.delta n s)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [s]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hdim, hs]
  | rho, y, sigmaV, w, G, D, .idelta s =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv] at hy
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.idelta s) hy
        have hs := dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hy
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.idelta s)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [s]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hdim, hs]
  | rho, y, sigmaV, w, G, D, .scale e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        have hdim := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.scale e0 e1)
          (by simpa only [ValExpr.fv, Finset.mem_union, not_or] using hy)
        have ih0 := eval_open orc horacle
          rho y sigmaV w G D e0 hlen hlc hySigma hyG hy.1
        have ih1 := eval_open orc horacle
          rho y sigmaV w G D e1 hlen hlc hySigma hyG hy.2
        simp only [ValExpr.openRec] at hdim ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.scale e0 e1)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hdim, ih0, ih1]
          have hother := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e1 hy.2
          simp only [ValueShape.scale, hother]
  | rho, y, sigmaV, w, G, D, .vadd s e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨hs, h0⟩, h1⟩ := hy
        have hsd := dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hs
        have ih0 := eval_open orc horacle
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := eval_open orc horacle
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec]
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.vadd s e0 e1)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [s]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hsd, ih0, ih1]
  | rho, y, sigmaV, w, G, D, .tprodE e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.tprodE e0 e1)
          (by simpa only [ValExpr.fv, Finset.mem_union, not_or] using hy)
        have hsub := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e1 hy.2
        have ih0 := eval_open orc horacle
          rho y sigmaV w G D e0 hlen hlc hySigma hyG hy.1
        have ih1 := eval_open orc horacle
          rho y sigmaV w G D e1 hlen hlc hySigma hyG hy.2
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.tprodE e0 e1)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0, ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, hsub, ih0, ih1]
          have hother := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e0 hy.1
          simp only [ValueShape.pair, hother, hsub]
  | rho, y, sigmaV, w, G, D, .dsumE e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.dsumE e0 e1)
          (by simpa only [ValExpr.fv, Finset.mem_union, not_or] using hy)
        have hsub := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG e0 hy.1
        have ih0 := eval_open orc horacle
          rho y sigmaV w G D e0 hlen hlc hySigma hyG hy.1
        have ih1 := eval_open orc horacle
          rho y sigmaV w G D e1 hlen hlc hySigma hyG hy.2
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.dsumE e0 e1)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0, ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, hsub, ih0, ih1]
          have hother := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e1 hy.2
          simp only [ValueShape.pair, hother, hsub]
  | rho, y, sigmaV, w, G, D, .vsum s es =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨hs, hes⟩ := hy
        have hsd := dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hs
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.vsum s es)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨hs, hes⟩)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.vsum s es)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [s, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.vsum s es)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hsd, hwhole]
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
          exact eval_open orc horacle
            rho y sigmaV w G D e hlen hlc hySigma hyG hye
  | rho, y, sigmaV, w, G, D, .reshap e target source =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨⟨he, ht⟩, hs⟩ := hy
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        simp only [ValExpr.openRec]
        rw [denotValB_partial, denotValB_partial, ihe]
        generalize hv : denotValB_partial orc rho (G ++ [sigmaV]) (D ++ [w]) e = result
        cases result with
        | error err => rfl
        | ok v =>
            have hinfer := inferTypeCtxRaised_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G e
            have hif := ValExpr.notMem_fv_inferTypeCtx y e (G ++ [sigmaV]) he
              (fresh_append hySigma hyG)
            cases source with
            | space s =>
                exact reshape_prefix horacle hlen hlc hySigma hyG ht hs
            | piTy d c =>
                simp only [ValTy.openRec, PartialValueEval.reshapeInferred, hinfer]
                cases hi : ValExpr.inferTypeCtx (G ++ [sigmaV]) e with
                | space s => rfl
                | piTy di ci =>
                    rw [hi] at hif
                    exact reshape_prefix horacle hlen hlc hySigma hyG ht hif
  | rho, y, sigmaV, w, G, D, .vtrans e =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv] at hy
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.vtrans e) hy
        have hinfer := inferSpaceCtx_valueOpenPush
          (y := y) (sigmaV := sigmaV) hlc G e
        have hyInf := ValExpr.notMem_fv_inferSpaceCtx y e
          (G ++ [sigmaV]) hy (fresh_append hySigma hyG)
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG hy
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.vtrans e)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.vtrans e)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe]
          congr 1
          funext a
          have hguard : ValueShape.tensor (numbersOrc orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e)) a =
              ValueShape.tensor (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e) a :=
            inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
              have hd0 := dof_valueOpenPush_from_leaf (numbers_openPush horacle)
                (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
                (G := G) (D := D) hlen hlc hySigma hyG s0 hyInf.1
              have hd1 := dof_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.ttv s e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨hs, h0⟩, h1⟩)
        have hcontract := dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s hs
        have ih0 := eval_open orc horacle
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := eval_open orc horacle
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.ttv s e0 e1)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [s, ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0, ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.ttv s e0 e1)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, hcontract, ih0, ih1]
          congr 1
          funext a0 a1
          have hd0 := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e0 h0
          have hd1 := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e1 h1
          have hg := inferTprodOrDof_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e0 h0
              (fun d => d = ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s ∧ ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) = ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s)
              (fun d _ => d = ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s ∧ ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) = ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s)
          have hguard : ValueShape.ttv (numbersOrc orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValSpace.openRec G.length (uOf y sigmaV) s) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a0 a1 =
              ValueShape.ttv (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a0 a1 := by
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
          let dContract := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s
          exact inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG
          (.mtm n0 n1 s0 s1 e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨⟨hs0, hs1⟩, h0⟩, h1⟩)
        have hcontract := dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG s0 hs0
        have ih0 := eval_open orc horacle
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := eval_open orc horacle
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.mtm n0 n1 s0 s1 e0 e1)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [s0, ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0, ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.mtm n0 n1 s0 s1 e0 e1)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, hcontract, ih0, ih1]
          congr 1
          funext a0 a1
          have hg0 : ValueShape.tensor (numbersOrc orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) a0 =
              ValueShape.tensor (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) a0 :=
            inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e0 h0 False (fun d0 d1 => a0.length = d0 * d1)
          have hg1 : ValueShape.tensor (numbersOrc orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a1 =
              ValueShape.tensor (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a1 :=
            inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e1 h1 False (fun d0 d1 => a1.length = d0 * d1)
          have hg := inferTprodPairDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e0 e1 h0 h1 False
              (fun d00 _ _ d11 => d00 = ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s0 ∧ d11 = ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s0)
          have hguard : ValueShape.mtm (numbersOrc orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValSpace.openRec G.length (uOf y sigmaV) s0) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a0 a1 =
              ValueShape.mtm (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s0 (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a0 a1 := by
            simp only [ValueShape.mtm, ValueShape.matrices, hg0, hg1, hcontract]
            exact congrArg (fun p => (ValueShape.tensor (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) a0 ∧ ValueShape.tensor (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a1) ∧ p) hg
          simp only [hguard]
          congr 1
          apply congrArg Except.ok
          apply ValValSem.arrayOf_congr rfl
          intro i
          let dContract := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) s0
          exact inferTprodPairDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.vkrn e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨h0, h1⟩)
        have ih0 := eval_open orc horacle
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := eval_open orc horacle
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.vkrn e0 e1)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0, ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.vkrn e0 e1)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ih0, ih1]
          congr 1
          funext a0 a1
          have hg0 : ValueShape.tensor (numbersOrc orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) a0 =
              ValueShape.tensor (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) a0 :=
            inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e0 h0 False (fun d0 d1 => a0.length = d0 * d1)
          have hg1 : ValueShape.tensor (numbersOrc orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a1 =
              ValueShape.tensor (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a1 :=
            inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e1 h1 False (fun d0 d1 => a1.length = d0 * d1)
          simp only [ValueShape.matrices, hg0, hg1]
          congr 1
          apply congrArg Except.ok
          apply ValValSem.arrayOf_congr rfl
          intro i
          exact inferTprodPairDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.vblk e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨h0, h1⟩)
        have ih0 := eval_open orc horacle
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := eval_open orc horacle
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.vblk e0 e1)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0, ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.vblk e0 e1)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ih0, ih1]
          congr 1
          funext a0 a1
          have hg0 : ValueShape.tensor (numbersOrc orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e0)) a0 =
              ValueShape.tensor (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e0) a0 :=
            inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e0 h0 False (fun d0 d1 => a0.length = d0 * d1)
          have hg1 : ValueShape.tensor (numbersOrc orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D) (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G) (ValExpr.openRec G.length (uOf y sigmaV) e1)) a1 =
              ValueShape.tensor (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w])) (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1) a1 :=
            inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
            (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
            (G := G) (D := D) hlen hlc hySigma hyG e1 h1 False (fun d0 d1 => a1.length = d0 * d1)
          simp only [ValueShape.matrices, hg0, hg1]
          congr 1
          apply congrArg Except.ok
          apply ValValSem.arrayOf_congr rfl
          intro i
          exact inferTprodPairDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.pinv e) hy
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG hy
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.pinv e)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.pinv e)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe]
          congr 1
          funext a
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.pinv e))
          exact inferTprodOrDof_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdS e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := eval_open orc horacle
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := eval_open orc horacle
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.gsvdS e a b)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) a, ValExpr.inferSpaceCtx (G ++ [sigmaV]) b, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdS e a b)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe, iha, ihb]
          congr 1
          funext ae aa ab
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdS e a b))
          exact inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdU e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := eval_open orc horacle
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := eval_open orc horacle
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.gsvdU e a b)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) a, ValExpr.inferSpaceCtx (G ++ [sigmaV]) b, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdU e a b)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe, iha, ihb]
          congr 1
          funext ae aa ab
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdU e a b))
          exact inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdUI e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := eval_open orc horacle
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := eval_open orc horacle
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.gsvdUI e a b)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) a, ValExpr.inferSpaceCtx (G ++ [sigmaV]) b, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdUI e a b)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe, iha, ihb]
          congr 1
          funext ae aa ab
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdUI e a b))
          exact inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdV e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := eval_open orc horacle
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := eval_open orc horacle
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.gsvdV e a b)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) a, ValExpr.inferSpaceCtx (G ++ [sigmaV]) b, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdV e a b)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe, iha, ihb]
          congr 1
          funext ae aa ab
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdV e a b))
          exact inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gsvdVI e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := eval_open orc horacle
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := eval_open orc horacle
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.gsvdVI e a b)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) a, ValExpr.inferSpaceCtx (G ++ [sigmaV]) b, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdVI e a b)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe, iha, ihb]
          congr 1
          funext ae aa ab
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gsvdVI e a b))
          exact inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.gpinv e a b)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨⟨he, ha⟩, hb⟩)
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG he
        have iha := eval_open orc horacle
          rho y sigmaV w G D a hlen hlc hySigma hyG ha
        have ihb := eval_open orc horacle
          rho y sigmaV w G D b hlen hlc hySigma hyG hb
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.gpinv e a b)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) a, ValExpr.inferSpaceCtx (G ++ [sigmaV]) b, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gpinv e a b)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl | rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe, iha, ihb]
          congr 1
          funext ae aa ab
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.gpinv e a b))
          exact inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.rrefRep e0 e1)
          (by
            simp only [ValExpr.fv, Finset.mem_union, not_or]
            exact ⟨h0, h1⟩)
        have ih0 := eval_open orc horacle
          rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := eval_open orc horacle
          rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.rrefRep e0 e1)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e1, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.rrefRep e0 e1)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ih0, ih1]
          congr 1
          funext a0 a1
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.rrefRep e0 e1))
          exact inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.inv e) hy
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG hy
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.inv e)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.inv e)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe]
          congr 1
          funext a
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.inv e))
          exact inferTprodOrDof_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        have hwhole := inferSpaceCtx_dof_valueOpenPush_from_leaf (numbers_openPush horacle)
          (rho := rho) (y := y) (sigmaV := sigmaV) (w := w)
          (G := G) (D := D) hlen hlc hySigma hyG (.svds e) hy
        have ihe := eval_open orc horacle
          rho y sigmaV w G D e hlen hlc hySigma hyG hy
        simp only [ValExpr.openRec] at hwhole ⊢
        rw [denotValB_partial, denotValB_partial]
        have hguardWhole := inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G (.svds e)
        simp only [ValExpr.openRec, ValExpr.openRecList_eq_map] at hguardWhole
        apply guarded_congr
        · try simp only [hguardWhole, inferSpaceCtx_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G]
          change PartialValueEval.dimensions _ (List.map (ValSpace.openRec G.length (uOf y sigmaV))
            [ValExpr.inferSpaceCtx (G ++ [sigmaV]) e, ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.svds e)]) = PartialValueEval.dimensions _ _
          apply dimensions_open horacle ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          intro sp hsp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hsp
          rcases hsp with rfl | rfl
          all_goals change y ∉ _
          all_goals first
            | assumption
            | (apply ValExpr.notMem_fv_inferSpaceCtx y _ (G ++ [sigmaV]) _ (fresh_append hySigma hyG)
               try simp only [ValExpr.fv, Finset.mem_union, not_or]
               tauto)
            | tauto
        · dsimp only
          rw [ hwhole, ihe]
          congr 1
          funext a
          let outDim := ValSpace.dof (numbersOrc orc rho (G ++ [sigmaV]) (D ++ [w]))
            (ValExpr.inferSpaceCtx (G ++ [sigmaV]) (.svds e))
          exact inferTprodDofs_valueOpenPush_from_leaf (numbers_openPush horacle)
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
        let W : World orc := ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
        have hshape := ValSoundOfDenot.ValTy.SameShape_openRec G.length (uOf y sigmaV) tau0
        have hEl := ValSoundOfDenot.ValTy.SameShape.carrierEl_eq hshape
        simp only [ValExpr.openRec, lam_eq]
        apply eq_of_heq
        apply bindAcross_heq (type_eq hshape) rfl _ _ (type_heq horacle tau0 W hy0)
        intro _ _ _
        apply heq_of_eq
        apply congrArg Except.ok
        apply ValValSem.fn_partial_congr _ _ hEl
        intro a
        have hcanon := carrierToVal_SameShape _ _ hshape a (hEl ▸ a) (cast_heq hEl a).symm
        rw [hcanon]
        have ih := eval_open orc horacle rho y sigmaV w (tau0 :: G)
          (tau0.carrierToVal (hEl ▸ a) :: D) body
          (by simp [hlen]) hlc hySigma (ValTyCtxFresh.cons hy0 hyG) hyBody
        simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
          Nat.succ_eq_add_one] using ih
  | rho, y, sigmaV, w, G, D, .appV e0 e1 =>
      fun hlen hlc hySigma hyG hy => by
        simp only [ValExpr.fv, Finset.mem_union, not_or] at hy
        obtain ⟨h0, h1⟩ := hy
        have ih0 := eval_open orc horacle rho y sigmaV w G D e0 hlen hlc hySigma hyG h0
        have ih1 := eval_open orc horacle rho y sigmaV w G D e1 hlen hlc hySigma hyG h1
        have hinfer := inferTypeCtxRaised_valueOpenPush (y := y) (sigmaV := sigmaV) hlc G e0
        have hff := ValExpr.notMem_fv_inferTypeCtx y e0 (G ++ [sigmaV]) h0 (fresh_append hySigma hyG)
        simp only [ValExpr.openRec, app_eq, ih0, ih1, hinfer]
        cases hft : ValExpr.inferTypeCtx (G ++ [sigmaV]) e0 with
        | space s => rfl
        | piTy d c =>
          rw [hft] at hff
          simp only [ValTy.fv, Finset.mem_union, not_or] at hff
          simp only [ValTy.openRec]
          let W : World orc := ⟨rho, y, sigmaV, w, G, D, hlen, hlc, hySigma, hyG⟩
          exact PartialValueEval.applyDomainChecked_congr _ _ _ _ _ _ _ _ _ _
            (ValSoundOfDenot.ValTy.SameShape_openRec G.length (uOf y sigmaV) d)
            (type_heq horacle d W hff.1) _ _

  termination_by rho y sigmaV w G D e => ValExpr.size e
  decreasing_by
    all_goals
      first
      | (simp only [ValExpr.size]; omega)
      | (simp only [ValExpr.size]
         have := ValExpr.size_le_sizeList hmem; omega)

end GLang.PartialDirectOpenPush
