import GLang.Proofs.Adequacy.Foundations.AgreeRealizeTransport
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceInferredDomain

namespace GLang.PartialAdequacy

/-- Inference retains the realized source kind even when its annotation differs. -/
theorem inferType_sameShape
    {Δ Γ Ψ e b v tv} (h : S.Term Δ Γ Ψ e b v tv)
    {orc : PartialFFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : History orc Δc Γc Ψ Γv σ ρ) :
    ValSoundOfDenot.ValTy.SameShape (ValExpr.inferTypeCtx [] v) tv := by
  have hp := V2.preservation_master.2.2.2 h.toOpStep Δ Γ Ψ.keyNames
    hc.evalCtxValidPlus hc.evalCtxValidPlus.rhoValid_keyNames (Finset.Subset.refl _)
    h.hasType.some h.tyAt.basisValid.sof_valid.some
  obtain ⟨⟨tv', heval, k, hi, ht⟩, _, _⟩ := hp
  rw [inferTypeCtx_of_lc [] (opStep_lc h.toOpStep hc.evalCtxLc)]
  have hshape := ValTValidC.sameShape_of_sameKind k hi.some ht.some
  have heq := heval.structuralKind_determined h.toEvalT
  exact hshape.trans (ValTValidC.sameShape_of_sameKind k ht.some
    (by
      have hk : k = tv.structuralKind := (ValTValidC.kind_eq_structural ht.some).trans heq
      rw [hk]
      exact (evalT_valid h.toEvalT).some))

/-- A base-space producer also has a base-space inferred type. -/
theorem inferType_isSpace
    {Δ Γ Ψ e b v sv} (h : S.Term Δ Γ Ψ e b v (.space sv))
    {orc : PartialFFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : History orc Δc Γc Ψ Γv σ ρ) :
    ∃ s, ValExpr.inferTypeCtx [] v = .space s := by
  have hs := inferType_sameShape h hc
  cases hi : ValExpr.inferTypeCtx [] v with
  | space s => exact ⟨s, rfl⟩
  | piTy d c => simp only [hi, ValSoundOfDenot.ValTy.SameShape] at hs

/-- Operational producers agree on their inferred type and array-space view. -/
theorem inferType_spaceOf_eq
    {Δ Γ Ψ e b v tv} (h : S.Term Δ Γ Ψ e b v tv)
    {orc : PartialFFSOracleSem} {Δc Γc Γv σ ρ}
    (hc : History orc Δc Γc Ψ Γv σ ρ) :
    ∀ s, ValExpr.inferTypeCtx [] v = .space s → ValExpr.inferSpaceCtx [] v = s := by
  refine S.Term.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ => True)
    (motive_5 := fun _ _ Ψ _ _ v _ _ =>
      ∀ {orc : PartialFFSOracleSem} {Δc Γc Γv σ ρ}, History orc Δc Γc Ψ Γv σ ρ →
        ∀ s, ValExpr.inferTypeCtx [] v = .space s → ValExpr.inferSpaceCtx [] v = s)
    ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
    ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
    ?tySpace ?tyPi ?tyAtSpace ?tyAtFrame
    ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
    ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
    ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
    ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
    ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
    ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
    ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
    ?termAppL ?termAppI ?termNllam ?termAppNVal
    ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
    ?termZero ?termRlit h hc
  case termVarLin =>
    intro Γ Ψ x b v sp tv hl _ _ _ _ orc Δc Γc Γv σ ρ hc s hi
    obtain ⟨v',tv',_,_,_,_,_,_,_,_,hs,_,heq,_,_⟩ :=
      hc.lookup (Finmap.mem_of_lookup_eq_some hl)
    have hv : v' = v := Option.some.inj (heq.symm.trans hl)
    subst v'
    have htv : tv' = .space s := by
      rw [inferTypeCtx_of_lc [] hs.hlc, hs.hinfer] at hi
      exact hi
    exact (htv ▸ hs.hinferSpaceBase).spaceEq
  case termVarNlin =>
    intro Γ Ψ x b v tv hl _ _ _ _ orc Δc Γc Γv σ ρ hc s hi
    obtain ⟨v',tv',_,_,_,_,_,_,_,_,hs,_,heq,_,_⟩ :=
      hc.lookup (Finmap.mem_of_lookup_eq_some hl)
    have hv : v' = v := Option.some.inj (heq.symm.trans hl)
    subst v'
    have htv : tv' = .space s := by
      rw [inferTypeCtx_of_lc [] hs.hlc, hs.hinfer] at hi
      exact hi
    exact (htv ▸ hs.hinferSpaceBase).spaceEq
  case termDsum =>
    intro Delta Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 htof0 htof1 ht hbv hTy he0 he1 ihTy ih0 ih1
      orc DC GC GV sig rh hc s hi
    obtain ⟨s0, h0⟩ := inferType_isSpace he0 hc
    obtain ⟨s1, h1⟩ := inferType_isSpace he1 hc
    simpa only [ValExpr.inferSpaceCtx, ih0 hc s0 h0, ih1 hc s1 h1] using
      (by simpa only [ValExpr.inferTypeCtx, h0, h1, ValTy.spaceOf, ValTy.space.injEq] using hi : s0.dsum s1 = s)
  case termTprod =>
    intro Delta0 Delta1 Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 hdisj htof0 htof1 ht hbv hTy he0 he1 ihTy ih0 ih1
      orc DC GC GV sig rh hc s hi
    obtain ⟨s0, h0⟩ := inferType_isSpace he0 hc
    obtain ⟨s1, h1⟩ := inferType_isSpace he1 hc
    simpa only [ValExpr.inferSpaceCtx, ih0 hc s0 h0, ih1 hc s1 h1] using
      (by simpa only [ValExpr.inferTypeCtx, h0, h1, ValTy.spaceOf, ValTy.space.injEq] using hi : s0.tprod s1 = s)
  case termPinvTStd =>
    intro Gamma Psi b0 b1 e v sv0 sv1 hb0 hb1 ht hbv hTy he ihTy ihE
      orc DC GC GV sig rh hc s hi
    obtain ⟨sv, hv⟩ := inferType_isSpace he hc
    have hs := ihE hc sv hv
    cases sv <;> simpa [ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, hv, hs] using hi
  case termPinvTGpinv =>
    intro Gamma Psi b0 b1 e v env0 env1 sv0 sv1 ht hbv hTy he hi0 hi1 ihTy ihE ihI0 ihI1
      orc DC GC GV sig rh hc s hi
    obtain ⟨sv, hv⟩ := inferType_isSpace he hc
    have hs := ihE hc sv hv
    cases sv <;> simpa [ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, hv, hs] using hi
  case termEmbedKer | termEmbedCoker | termEmbedImg | termEmbedCoimg =>
    intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv hTy hi0 hi1 he ihTy ihI0 ihI1 ihE
      orc DC GC GV sig rh hc s hi
    obtain ⟨sv, hv⟩ := inferType_isSpace he hc
    have hs := ihE hc sv hv
    cases sv <;> simpa [ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, hv, hs] using hi
  all_goals intros
  all_goals try dsimp only at *
  all_goals intros
  all_goals simp_all [ValExpr.applyAt, ValExpr.inferSpaceCtx, ValExpr.inferTypeCtx, ValExpr.reshapBase,
    ValExpr.sumAt, ValTy.spaceOf]
  all_goals solve_by_elim (maxDepth := 8)
end GLang.PartialAdequacy
