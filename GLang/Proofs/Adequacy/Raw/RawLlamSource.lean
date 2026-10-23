import GLang.Proofs.Adequacy.Raw.Context.RawSourceContextTransport
import GLang.Proofs.Source.InnerProduct

/-!
# Source linearity used by raw linear-lambda assembly

The source denotation represents a linear lambda with `LinearMap.ofFun`.
Assembly therefore needs the typing-derived fact that its body function is
linear, including through any number of source `promote` wrappers.
-/

namespace GLang

/-- A source typing at the tensor result of a linear lambda can only come
from the non-real introduction (possibly below `promote`). -/
def HasType.llam_tensor_codomain_ne_real
    {Delta : LCtx} {Gamma : NLCtx} {s0 s1 : Space} {body : Term}
    (d : HasType Delta Gamma (.llam s0 s1 body)
      (.space (.tprod (.dual s0) s1))) : s1 ≠ .real :=
  match d with
  | .llam_tensor _ hne _ _ _ => hne
  | .promote _ _ _ _ dinner => dinner.llam_tensor_codomain_ne_real

/-- The de-Bruijn body function of a well-typed real-codomain linear lambda
is linear at every well-formed semantic source world. -/
noncomputable def denot_llam_real_body_isLinear
    {Delta : LCtx} {Gamma : NLCtx} {s : Space} {body : Term}
    (d : HasType Delta Gamma (.llam s .real body) (.space (.dual s)))
    {sigma : DEnv} (ctx : CtxWF Delta Gamma)
    (wf : EnvWF sigma Delta Gamma) :
    IsLinearMap ℝ (fun x : (denotSpace sigma s).carrier =>
      (denotTermAux sigma [.hil ⟨denotSpace sigma s, x⟩] body).atSpace
        HSpace.real) :=
  match d with
  | .llam_real L hs hbody => by
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
        (L ∪ Delta.keys ∪ Gamma.keys ∪ Term.fv body)
      simp only [Finset.mem_union, not_or] at hy
      obtain ⟨⟨⟨hyL, hyDeltaK⟩, hyGammaK⟩, hyBody⟩ := hy
      have hyDelta : y ∉ Delta := fun hm =>
        hyDeltaK (Finmap.mem_keys.mpr hm)
      have hyGamma : y ∉ Gamma := fun hm =>
        hyGammaK (Finmap.mem_keys.mpr hm)
      have hctxExt : CtxWF (Finmap.insert y s Delta) Gamma :=
        ctx.extend_lin hyGamma hs
      let V := denotSpace sigma s
      let sigma0 := sigma.bind y (.hil ⟨V, (0 : V.carrier)⟩)
      have hwfExt : EnvWF sigma0 (Finmap.insert y s Delta) Gamma := by
        simpa only [sigma0, V] using wf.extend_lin ctx hyGamma hs
          (0 : (denotSpace sigma s).carrier)
      have hlin := (soundness (hbody y hyL) hctxExt hwfExt).2 y s
        (Finmap.lookup_insert Delta)
      simp only [LinearAtVar] at hlin
      have hyfv : y ∉ Space.fv s := fun hm =>
        hyGamma (Finmap.mem_keys.mp (SValid.fv_closure hs hm))
      have hspace0 : denotSpace sigma0 s = denotSpace sigma s :=
        denotSpace_agree s
          (DEnv.AgreeOn.bind_left_of_not_mem hyfv)
      rw [hspace0] at hlin
      refine IsLinearMap.congr hlin ?_
      intro x
      have hoverwrite : sigma0.bind y
          (.hil ⟨denotSpace sigma s, x⟩) =
          sigma.bind y (.hil ⟨denotSpace sigma s, x⟩) := by
        show (DEnv.mk _ : DEnv) = DEnv.mk _
        congr 1
        exact Finmap.insert_insert sigma.vars
      rw [hoverwrite]
      exact congrArg (DVal.atSpace HSpace.real)
        (denotTerm_openVar_bind (HasType.lc (hbody y hyL)) hyBody)
  | @HasType.promote DeltaOuter GammaInner _ _ lin hdisjDelta
      hdisjGamma hfresh dinner => by
      have ctxInner : CtxWF (lin ∪ DeltaOuter) GammaInner := {
        disjoint := fun x hxIn hxGamma => by
          rcases Finmap.mem_union.mp hxIn with hxLin | hxDelta
          · have hxToNL : x ∈ lin.toNL :=
              (LCtx.mem_toNL_iff lin x).mpr hxLin
            exact @hdisjGamma x hxToNL hxGamma
          · exact ctx.disjoint x hxDelta
              (Finmap.mem_union.mpr (Or.inr hxGamma))
        lin_fv_in_ε := fun x sx hx z hz => by
          by_cases hxLin : x ∈ lin
          · have hLin : lin.lookup x = some sx := by
              rw [Finmap.lookup_union_left hxLin] at hx
              exact hx
            have hOuter : (lin.toNL ∪ GammaInner).lookup x =
                some (.space sx) := by
              rw [Finmap.lookup_union_left
                ((LCtx.mem_toNL_iff lin x).mpr hxLin)]
              exact LCtx.toNL_lookup lin x sx hLin
            have hzOuter := ctx.nl_fv_in_ε x (.space sx) hOuter z
              (by simpa only [Ty.fv] using hz)
            rcases Finmap.mem_union.mp hzOuter with hzLin | hzGamma
            · have hzInLin : z ∈ lin :=
                (LCtx.mem_toNL_iff lin z).mp hzLin
              exact absurd hz
                (hfresh.fresh_lin z hzInLin x sx hLin)
            · exact hzGamma
          · have hDelta : DeltaOuter.lookup x = some sx := by
              rw [Finmap.lookup_union_right hxLin] at hx
              exact hx
            have hzOuter := ctx.lin_fv_in_ε x sx hDelta z hz
            rcases Finmap.mem_union.mp hzOuter with hzLin | hzGamma
            · have hzInLin : z ∈ lin :=
                (LCtx.mem_toNL_iff lin z).mp hzLin
              exact absurd hz
                (hfresh.fresh_Δ z hzInLin x sx hDelta)
            · exact hzGamma
        nl_fv_in_ε := fun x tau hx z hz => by
          have hxNotLin : x ∉ lin.toNL := fun hm =>
            @hdisjGamma x hm (Finmap.mem_of_lookup_eq_some hx)
          have hOuter : (lin.toNL ∪ GammaInner).lookup x = some tau := by
            rw [Finmap.lookup_union_right hxNotLin]
            exact hx
          have hzOuter := ctx.nl_fv_in_ε x tau hOuter z hz
          rcases Finmap.mem_union.mp hzOuter with hzLin | hzGamma
          · have hzInLin : z ∈ lin :=
              (LCtx.mem_toNL_iff lin z).mp hzLin
            exact absurd hz
              (hfresh.fresh_ε z hzInLin x tau hx)
          · exact hzGamma
      }
      have wfInner : EnvWF sigma (lin ∪ DeltaOuter) GammaInner := {
        lin_match := fun x sx hx => by
          by_cases hxLin : x ∈ lin
          · have hLin : lin.lookup x = some sx := by
              rw [Finmap.lookup_union_left hxLin] at hx
              exact hx
            have hOuter : (lin.toNL ∪ GammaInner).lookup x =
                some (.space sx) := by
              rw [Finmap.lookup_union_left
                ((LCtx.mem_toNL_iff lin x).mpr hxLin)]
              exact LCtx.toNL_lookup lin x sx hLin
            exact wf.nl_match x (.space sx) hOuter
          · have hDelta : DeltaOuter.lookup x = some sx := by
              rw [Finmap.lookup_union_right hxLin] at hx
              exact hx
            exact wf.lin_match x sx hDelta
        nl_match := fun x tau hx => by
          have hxNotLin : x ∉ lin.toNL := fun hm =>
            @hdisjGamma x hm (Finmap.mem_of_lookup_eq_some hx)
          have hOuter : (lin.toNL ∪ GammaInner).lookup x = some tau := by
            rw [Finmap.lookup_union_right hxNotLin]
            exact hx
          exact wf.nl_match x tau hOuter
      }
      exact denot_llam_real_body_isLinear dinner ctxInner wfInner

/-- The de-Bruijn body function of a well-typed tensor-codomain linear
lambda is linear at every well-formed semantic source world.  As in the
real-codomain specialization above, this follows the source `promote`
wrappers until it reaches the actual `llam_tensor` introduction. -/
noncomputable def denot_llam_tensor_body_isLinear
    {Delta : LCtx} {Gamma : NLCtx} {s0 s1 : Space} {body : Term}
    (d : HasType Delta Gamma (.llam s0 s1 body)
      (.space (.tprod (.dual s0) s1)))
    {sigma : DEnv} (ctx : CtxWF Delta Gamma)
    (wf : EnvWF sigma Delta Gamma) :
    IsLinearMap ℝ (fun x : (denotSpace sigma s0).carrier =>
      (denotTermAux sigma [.hil ⟨denotSpace sigma s0, x⟩] body).atSpace
        (denotSpace sigma s1)) :=
  match d with
  | .llam_tensor L _hne hs0 hs1 hbody => by
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
        (L ∪ Delta.keys ∪ Gamma.keys ∪ Term.fv body)
      simp only [Finset.mem_union, not_or] at hy
      obtain ⟨⟨⟨hyL, hyDeltaK⟩, hyGammaK⟩, hyBody⟩ := hy
      have hyDelta : y ∉ Delta := fun hm =>
        hyDeltaK (Finmap.mem_keys.mpr hm)
      have hyGamma : y ∉ Gamma := fun hm =>
        hyGammaK (Finmap.mem_keys.mpr hm)
      have hctxExt : CtxWF (Finmap.insert y s0 Delta) Gamma :=
        ctx.extend_lin hyGamma hs0
      let V := denotSpace sigma s0
      let sigma0 := sigma.bind y (.hil ⟨V, (0 : V.carrier)⟩)
      have hwfExt : EnvWF sigma0 (Finmap.insert y s0 Delta) Gamma := by
        simpa only [sigma0, V] using wf.extend_lin ctx hyGamma hs0
          (0 : (denotSpace sigma s0).carrier)
      have hlin := (soundness (hbody y hyL) hctxExt hwfExt).2 y s0
        (Finmap.lookup_insert Delta)
      simp only [LinearAtVar] at hlin
      have hyfv0 : y ∉ Space.fv s0 := fun hm =>
        hyGamma (Finmap.mem_keys.mp (SValid.fv_closure hs0 hm))
      have hyfv1 : y ∉ Space.fv s1 := fun hm =>
        hyGamma (Finmap.mem_keys.mp (SValid.fv_closure hs1 hm))
      have hspace0 : denotSpace sigma0 s0 = denotSpace sigma s0 :=
        denotSpace_agree s0
          (DEnv.AgreeOn.bind_left_of_not_mem hyfv0)
      have hspace1 : denotSpace sigma0 s1 = denotSpace sigma s1 :=
        denotSpace_agree s1
          (DEnv.AgreeOn.bind_left_of_not_mem hyfv1)
      rw [hspace0, hspace1] at hlin
      refine IsLinearMap.congr hlin ?_
      intro x
      have hoverwrite : sigma0.bind y
          (.hil ⟨denotSpace sigma s0, x⟩) =
          sigma.bind y (.hil ⟨denotSpace sigma s0, x⟩) := by
        show (DEnv.mk _ : DEnv) = DEnv.mk _
        congr 1
        exact Finmap.insert_insert sigma.vars
      rw [hoverwrite]
      exact congrArg (DVal.atSpace (denotSpace sigma s1))
        (denotTerm_openVar_bind (HasType.lc (hbody y hyL)) hyBody)
  | @HasType.promote DeltaOuter GammaInner _ _ lin hdisjDelta
      hdisjGamma hfresh dinner => by
      have ctxInner : CtxWF (lin ∪ DeltaOuter) GammaInner := {
        disjoint := fun x hxIn hxGamma => by
          rcases Finmap.mem_union.mp hxIn with hxLin | hxDelta
          · have hxToNL : x ∈ lin.toNL :=
              (LCtx.mem_toNL_iff lin x).mpr hxLin
            exact @hdisjGamma x hxToNL hxGamma
          · exact ctx.disjoint x hxDelta
              (Finmap.mem_union.mpr (Or.inr hxGamma))
        lin_fv_in_ε := fun x sx hx z hz => by
          by_cases hxLin : x ∈ lin
          · have hLin : lin.lookup x = some sx := by
              rw [Finmap.lookup_union_left hxLin] at hx
              exact hx
            have hOuter : (lin.toNL ∪ GammaInner).lookup x =
                some (.space sx) := by
              rw [Finmap.lookup_union_left
                ((LCtx.mem_toNL_iff lin x).mpr hxLin)]
              exact LCtx.toNL_lookup lin x sx hLin
            have hzOuter := ctx.nl_fv_in_ε x (.space sx) hOuter z
              (by simpa only [Ty.fv] using hz)
            rcases Finmap.mem_union.mp hzOuter with hzLin | hzGamma
            · have hzInLin : z ∈ lin :=
                (LCtx.mem_toNL_iff lin z).mp hzLin
              exact absurd hz
                (hfresh.fresh_lin z hzInLin x sx hLin)
            · exact hzGamma
          · have hDelta : DeltaOuter.lookup x = some sx := by
              rw [Finmap.lookup_union_right hxLin] at hx
              exact hx
            have hzOuter := ctx.lin_fv_in_ε x sx hDelta z hz
            rcases Finmap.mem_union.mp hzOuter with hzLin | hzGamma
            · have hzInLin : z ∈ lin :=
                (LCtx.mem_toNL_iff lin z).mp hzLin
              exact absurd hz
                (hfresh.fresh_Δ z hzInLin x sx hDelta)
            · exact hzGamma
        nl_fv_in_ε := fun x tau hx z hz => by
          have hxNotLin : x ∉ lin.toNL := fun hm =>
            @hdisjGamma x hm (Finmap.mem_of_lookup_eq_some hx)
          have hOuter : (lin.toNL ∪ GammaInner).lookup x = some tau := by
            rw [Finmap.lookup_union_right hxNotLin]
            exact hx
          have hzOuter := ctx.nl_fv_in_ε x tau hOuter z hz
          rcases Finmap.mem_union.mp hzOuter with hzLin | hzGamma
          · have hzInLin : z ∈ lin :=
              (LCtx.mem_toNL_iff lin z).mp hzLin
            exact absurd hz
              (hfresh.fresh_ε z hzInLin x tau hx)
          · exact hzGamma
      }
      have wfInner : EnvWF sigma (lin ∪ DeltaOuter) GammaInner := {
        lin_match := fun x sx hx => by
          by_cases hxLin : x ∈ lin
          · have hLin : lin.lookup x = some sx := by
              rw [Finmap.lookup_union_left hxLin] at hx
              exact hx
            have hOuter : (lin.toNL ∪ GammaInner).lookup x =
                some (.space sx) := by
              rw [Finmap.lookup_union_left
                ((LCtx.mem_toNL_iff lin x).mpr hxLin)]
              exact LCtx.toNL_lookup lin x sx hLin
            exact wf.nl_match x (.space sx) hOuter
          · have hDelta : DeltaOuter.lookup x = some sx := by
              rw [Finmap.lookup_union_right hxLin] at hx
              exact hx
            exact wf.lin_match x sx hDelta
        nl_match := fun x tau hx => by
          have hxNotLin : x ∉ lin.toNL := fun hm =>
            @hdisjGamma x hm (Finmap.mem_of_lookup_eq_some hx)
          have hOuter : (lin.toNL ∪ GammaInner).lookup x = some tau := by
            rw [Finmap.lookup_union_right hxNotLin]
            exact hx
          exact wf.nl_match x tau hOuter
      }
      exact denot_llam_tensor_body_isLinear dinner ctxInner wfInner

end GLang
