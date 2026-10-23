import GLang.Proofs.Value.Binding.ValueScope
import GLang.Proofs.Value.Binding.ValueBeta
import GLang.Proofs.Adequacy.Raw.RawNonBetaValueKernel
import GLang.Proofs.Adequacy.Foundations.FvIrrel

namespace GLang.DirectOracleOpenPush

@[simp] theorem inferTypeCtxRaised_bvar (Gamma : List ValTy) (k : Nat) :
    ValExpr.inferTypeCtx Gamma (.bvar k) = ValTyCtx.lookupUse Gamma k := rfl

/-! ## First exact endpoint facts -/

theorem raise_uOf_eq (n : Nat) {y : VName} {sigmaV : ValTy}
    (hsc : RaiseStableTy sigmaV) :
    ValExpr.raise n 0 (uOf y sigmaV) = uOf y sigmaV := by
  simp [uOf, ValExpr.raise, hsc n]

theorem lookupUse_singleton_zero {sigmaV : ValTy} (hsc : RaiseStableTy sigmaV) :
    ValTyCtx.lookupUse [sigmaV] 0 = sigmaV := by
  simp [ValTyCtx.lookupUse, hsc 1]

theorem inferTypeCtxRaised_bvar0_singleton {sigmaV : ValTy}
    (hsc : RaiseStableTy sigmaV) :
    ValExpr.inferTypeCtx [sigmaV] (.bvar 0) = sigmaV := by
  rw [inferTypeCtxRaised_bvar]
  exact lookupUse_singleton_zero hsc

/-! ## The exact dependent-prefix lookup square -/

/-- Entry `i` of `closePrefix u G` is entry `i` of `G`, opened at the
number of declarations outside it. -/
theorem getD_closePrefix_of_lt (u : ValExpr) : forall (G : List ValTy)
    (i : Nat), i < G.length ->
    (ValTy.closePrefix u G).getD i default =
      ValTy.openRec (G.length - (i + 1)) u (G.getD i default)
  | [], i, hi => by simp at hi
  | t :: G, 0, _ => by simp [ValTy.closePrefix]
  | t :: G, i + 1, hi => by
      simp only [ValTy.closePrefix, List.getD_cons_succ,
        List.length_cons] at hi ⊢
      have hit : i < G.length := by omega
      rw [getD_closePrefix_of_lt u G i hit]
      rw [show G.length + 1 - (i + 1 + 1) =
        G.length - (i + 1) by omega]

theorem lookupUse_closePrefix_open_of_lt
    {y : VName} {sigmaV : ValTy} (hsigma : ValTy.lc sigmaV)
    (G : List ValTy) {i : Nat} (hi : i < G.length) :
    ValTyCtx.lookupUse (ValTy.closePrefix (uOf y sigmaV) G) i =
      ValTy.openRec G.length (uOf y sigmaV)
        (ValTyCtx.lookupUse (G ++ [sigmaV]) i) := by
  let u := uOf y sigmaV
  have hu : RaiseStableExpr u := raiseStable_uOf_of_lc hsigma
  rw [ValTyCtx.lookupUse, ValTyCtx.lookupUse, getD_closePrefix_of_lt u G i hi,
    List.getD_append G [sigmaV] default i hi]
  have hopen := raiseTy_openRec (i + 1) 0 (G.length - (i + 1))
    u hu (Nat.zero_le _) (G.getD i default)
  rw [hopen]
  congr 2
  omega

/-- At the distinguished slot, the pushed lookup reduces to the locally
closed binder annotation. -/
theorem lookupUse_append_at_length
    {y : VName} {sigmaV : ValTy} (hsigma : ValTy.lc sigmaV)
    (G : List ValTy) :
    ValTy.openRec G.length (uOf y sigmaV)
        (ValTyCtx.lookupUse (G ++ [sigmaV]) G.length) = sigmaV := by
  rw [ValTyCtx.lookupUse, List.getD_append_right G [sigmaV] default G.length
    (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getD_cons_zero]
  rw [raiseTy_lc hsigma (G.length + 1) 0,
    ValTy.openRec_lc hsigma]

/-- Past the whole pushed telescope both sides return the common default. -/
theorem lookupUse_closePrefix_open_of_gt
    {y : VName} {sigmaV : ValTy} (G : List ValTy) {i : Nat}
    (hi : G.length < i) :
    ValTyCtx.lookupUse (ValTy.closePrefix (uOf y sigmaV) G) i =
      ValTy.openRec G.length (uOf y sigmaV)
        (ValTyCtx.lookupUse (G ++ [sigmaV]) i) := by
  have hlenClose : (ValTy.closePrefix (uOf y sigmaV) G).length = G.length := by
    clear hi
    induction G with
    | nil => rfl
    | cons t G ih => simp [ValTy.closePrefix, ih]
  have hiLeft : (ValTy.closePrefix (uOf y sigmaV) G).length <= i := by
    omega
  have hiRight : (G ++ [sigmaV]).length <= i := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [ValTyCtx.lookupUse, ValTyCtx.lookupUse]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  rfl

/-! ## Inference is structural once bound-variable lookup is correct -/

/-- The only non-structural premise required by inference/opening
commutation.  It says that lookup itself presents the same type on the named
and pushed sides. -/
def InferBVarOpenBridge (named pushed : List ValTy) (k : Nat)
    (u : ValExpr) : Prop :=
  forall i,
    ValExpr.inferTypeCtx named (ValExpr.openRec k u (.bvar i)) =
      ValTy.openRec k u (ValExpr.inferTypeCtx pushed (.bvar i))

/-- `closePrefix` versus append supplies the lookup premise exactly after the
depth-aware repair.  No property of the expression being inferred is used. -/
theorem inferBVarOpenBridge_closePrefix_append
    {y : VName} {sigmaV : ValTy} (hsigma : ValTy.lc sigmaV)
    (G : List ValTy) :
    InferBVarOpenBridge
      (ValTy.closePrefix (uOf y sigmaV) G) (G ++ [sigmaV]) G.length
      (uOf y sigmaV) := by
  intro i
  by_cases hlt : i < G.length
  · have hne : i ≠ G.length := by omega
    simp only [ValExpr.openRec, if_neg hne,
      inferTypeCtxRaised_bvar]
    exact lookupUse_closePrefix_open_of_lt hsigma G hlt
  · by_cases heq : i = G.length
    · subst i
      rw [show ValExpr.openRec G.length (uOf y sigmaV)
        (.bvar G.length) = uOf y sigmaV by
          simp [ValExpr.openRec]]
      rw [inferTypeCtxRaised_bvar]
      change sigmaV = ValTy.openRec G.length (uOf y sigmaV)
        (ValTyCtx.lookupUse (G ++ [sigmaV]) G.length)
      exact (lookupUse_append_at_length (y := y) hsigma G).symm
    · have hgt : G.length < i := by omega
      simp only [ValExpr.openRec, if_neg heq,
        inferTypeCtxRaised_bvar]
      exact lookupUse_closePrefix_open_of_gt G hgt

/-- Exact type inference commutes with opening, provided the two contexts
agree at bound-variable lookup.  This is independent of typing and of the
oracle. -/
theorem inferTypeCtxRaised_openRec_of_bvar_bridge
    {named pushed : List ValTy} {k : Nat} {u : ValExpr}
    (hu : ValExpr.lc u) (hbvar : InferBVarOpenBridge named pushed k u) :
    forall e : ValExpr,
      ValExpr.inferTypeCtx named (ValExpr.openRec k u e) =
        ValTy.openRec k u (ValExpr.inferTypeCtx pushed e)
  | .bvar i => hbvar i
  | .var x t => rfl
  | .vlam t0 t1 body => rfl
  | .zero s => rfl
  | .rlit r => rfl
  | .scale e0 e1 =>
      inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e1
  | .vadd s e0 e1 => rfl
  | .dsumE e0 e1 => by
      have ih0 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e0
      have ih1 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e1
      simp only [ValExpr.inferTypeCtx] at ih0 ih1
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx,
        ValExpr.inferTypeCtx]
      rw [ih0, ih1]
      simp only [ValTy.openRec, ValSpace.openRec, ValTy.spaceOf_openRec]
  | .tprodE e0 e1 => by
      have ih0 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e0
      have ih1 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e1
      simp only [ValExpr.inferTypeCtx] at ih0 ih1
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx,
        ValExpr.inferTypeCtx]
      rw [ih0, ih1]
      simp only [ValTy.openRec, ValSpace.openRec, ValTy.spaceOf_openRec]
  | .delta i s => rfl
  | .idelta s => rfl
  | .vsum s es => by
      cases es with
      | nil => rfl
      | cons e es =>
          simpa [ValExpr.inferTypeCtx, ValExpr.openRec,
            ValExpr.openRecList, ValExpr.inferTypeCtx] using
            inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
  | .ttv s e0 e1 => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e0
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e0 = t at ih ⊢
      cases t with
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
  | .mtm i j s0 s1 e0 e1 => by
      have ih0 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e0
      have ih1 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e1
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih0 ih1 ⊢
      generalize ht0 : ValExpr.inferTypeCtx pushed e0 = t0 at ih0 ⊢
      generalize ht1 : ValExpr.inferTypeCtx pushed e1 = t1 at ih1 ⊢
      cases t0 with
      | piTy => cases t1 <;> simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp0 =>
          cases sp0 <;> cases t1 with
          | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
          | space sp1 => cases sp1 <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .appV e0 e1 => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e0
      simp only [ValExpr.openRec, ValExpr.inferTypeCtx, ih]
      cases ht : ValExpr.inferTypeCtx pushed e0 with
      | space s => rfl
      | piTy d c =>
          exact (ValTy.openRec_applyCodomain u hu c e1 k).symm
  | .vkrn e0 e1 => by
      have ih0 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e0
      have ih1 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e1
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih0 ih1 ⊢
      generalize ht0 : ValExpr.inferTypeCtx pushed e0 = t0 at ih0 ⊢
      generalize ht1 : ValExpr.inferTypeCtx pushed e1 = t1 at ih1 ⊢
      cases t0 with
      | piTy => cases t1 <;> simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp0 =>
          cases sp0 <;> cases t1 with
          | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
          | space sp1 => cases sp1 <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .vblk e0 e1 => by
      have ih0 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e0
      have ih1 := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e1
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih0 ih1 ⊢
      generalize ht0 : ValExpr.inferTypeCtx pushed e0 = t0 at ih0 ⊢
      generalize ht1 : ValExpr.inferTypeCtx pushed e1 = t1 at ih1 ⊢
      cases t0 with
      | piTy => cases t1 <;> simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp0 =>
          cases sp0 <;> cases t1 with
          | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
          | space sp1 => cases sp1 <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .reshap e t t0 => rfl
  | .vtrans e => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .gsvdS e a b => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .gsvdU e a b => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .gsvdUI e a b => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .gsvdV e a b => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .gsvdVI e a b => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .pinv e => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .gpinv e a b => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .rrefRep e0 e1 => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e1
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e1 = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .inv e => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]
  | .svds e => by
      have ih := inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e
      simp only [ValExpr.inferTypeCtx, ValExpr.openRec, ValExpr.inferTypeCtx] at ih ⊢
      generalize ht : ValExpr.inferTypeCtx pushed e = t at ih ⊢
      cases t with
      | piTy => simp_all [ValTy.openRec, ValSpace.openRec]
      | space sp => cases sp <;> simp_all [ValTy.openRec, ValSpace.openRec]

/-! The evaluator also consults the independent space inferer.  On malformed
syntax it is not definitionally `spaceOf ∘ inferTypeCtx`, so it gets its own
lookup premise and structural proof. -/

def InferSpaceBVarOpenBridge (named pushed : List ValTy) (k : Nat)
    (u : ValExpr) : Prop :=
  forall i,
    ValExpr.inferSpaceCtx named (ValExpr.openRec k u (.bvar i)) =
      ValSpace.openRec k u (ValExpr.inferSpaceCtx pushed (.bvar i))

theorem inferSpaceBVarOpenBridge_closePrefix_append
    {y : VName} {sigmaV : ValTy} (hsigma : ValTy.lc sigmaV)
    (G : List ValTy) :
    InferSpaceBVarOpenBridge
      (ValTy.closePrefix (uOf y sigmaV) G) (G ++ [sigmaV]) G.length
      (uOf y sigmaV) := by
  intro i
  by_cases hlt : i < G.length
  · have hne : i ≠ G.length := by omega
    simp only [ValExpr.openRec, if_neg hne, ValExpr.inferSpaceCtx]
    rw [← ValTy.spaceOf_openRec]
    exact congrArg ValTy.spaceOf
      (lookupUse_closePrefix_open_of_lt hsigma G hlt)
  · by_cases heq : i = G.length
    · subst i
      simp only [ValExpr.openRec, if_pos rfl, if_true, uOf,
        ValExpr.inferSpaceCtx]
      rw [← ValTy.spaceOf_openRec]
      change ValTy.spaceOf sigmaV = ValTy.spaceOf
        (ValTy.openRec G.length (uOf y sigmaV)
          (ValTyCtx.lookupUse (G ++ [sigmaV]) G.length))
      exact congrArg ValTy.spaceOf
        (lookupUse_append_at_length (y := y) hsigma G).symm
    · have hgt : G.length < i := by omega
      simp only [ValExpr.openRec, if_neg heq, ValExpr.inferSpaceCtx]
      rw [← ValTy.spaceOf_openRec]
      exact congrArg ValTy.spaceOf
        (lookupUse_closePrefix_open_of_gt G hgt)

theorem inferSpaceCtx_openRec_of_bvar_bridge
    {named pushed : List ValTy} {k : Nat} {u : ValExpr}
    (hu : ValExpr.lc u) (htype : InferBVarOpenBridge named pushed k u)
    (hbvar : InferSpaceBVarOpenBridge named pushed k u) :
    forall e : ValExpr,
      ValExpr.inferSpaceCtx named (ValExpr.openRec k u e) =
        ValSpace.openRec k u (ValExpr.inferSpaceCtx pushed e)
  | .bvar i => hbvar i
  | .var x t => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx,
        ValTy.spaceOf_openRec]
  | .vlam t0 t1 body => rfl
  | .zero s => rfl
  | .rlit r => rfl
  | .scale e0 e1 => inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e1
  | .vadd s e0 e1 => rfl
  | .dsumE e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.openRec]
      rw [inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e0,
        inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e1]
  | .tprodE e0 e1 => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.openRec]
      rw [inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e0,
        inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e1]
  | .delta i s => rfl
  | .idelta s => rfl
  | .vsum s es => by
      cases es with
      | nil => rfl
      | cons e es =>
          simpa [ValExpr.openRec, ValExpr.openRecList,
            ValExpr.inferSpaceCtx] using
            inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
  | .ttv s e0 e1 => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e0
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e0 = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .mtm i j s0 s1 e0 e1 => by
      have ih0 := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e0
      have ih1 := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e1
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih0 ih1 ⊢
      generalize hs0 : ValExpr.inferSpaceCtx pushed e0 = sp0 at ih0 ⊢
      generalize hs1 : ValExpr.inferSpaceCtx pushed e1 = sp1 at ih1 ⊢
      cases sp0 <;> cases sp1 <;> simp_all [ValSpace.openRec]
  | .appV e0 e1 => by
      have h := inferTypeCtxRaised_openRec_of_bvar_bridge hu htype (.appV e0 e1)
      simpa only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValTy.spaceOf_openRec] using
        congrArg ValTy.spaceOf h
  | .vkrn e0 e1 => by
      have ih0 := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e0
      have ih1 := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e1
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih0 ih1 ⊢
      generalize hs0 : ValExpr.inferSpaceCtx pushed e0 = sp0 at ih0 ⊢
      generalize hs1 : ValExpr.inferSpaceCtx pushed e1 = sp1 at ih1 ⊢
      cases sp0 <;> cases sp1 <;> simp_all [ValSpace.openRec]
  | .vblk e0 e1 => by
      have ih0 := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e0
      have ih1 := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e1
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih0 ih1 ⊢
      generalize hs0 : ValExpr.inferSpaceCtx pushed e0 = sp0 at ih0 ⊢
      generalize hs1 : ValExpr.inferSpaceCtx pushed e1 = sp1 at ih1 ⊢
      cases sp0 <;> cases sp1 <;> simp_all [ValSpace.openRec]
  | .reshap e t t0 => by
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx,
        ValTy.spaceOf_openRec]
  | .vtrans e => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .gsvdS e a b => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.openRec]
      rw [ih]
  | .gsvdU e a b => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .gsvdUI e a b => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .gsvdV e a b => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .gsvdVI e a b => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .pinv e => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .gpinv e a b => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .rrefRep e0 e1 => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e1
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e1 = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .inv e => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx] at ih ⊢
      generalize hs : ValExpr.inferSpaceCtx pushed e = sp at ih ⊢
      cases sp <;> simp_all [ValSpace.openRec]
  | .svds e => by
      have ih := inferSpaceCtx_openRec_of_bvar_bridge hu htype hbvar e
      simp only [ValExpr.openRec, ValExpr.inferSpaceCtx, ValSpace.openRec]
      rw [ih]

/-- Space inference is the base-space projection of the exact type equation. -/
def inferSpaceViaRaisedType (Gamma : List ValTy) (e : ValExpr) : ValSpace :=
  ValTy.spaceOf (ValExpr.inferTypeCtx Gamma e)

theorem inferSpaceViaRaisedType_openRec_of_bvar_bridge
    {named pushed : List ValTy} {k : Nat} {u : ValExpr}
    (hu : ValExpr.lc u) (hbvar : InferBVarOpenBridge named pushed k u) (e : ValExpr) :
    inferSpaceViaRaisedType named (ValExpr.openRec k u e) =
      ValSpace.openRec k u (inferSpaceViaRaisedType pushed e) := by
  simp only [inferSpaceViaRaisedType,
    inferTypeCtxRaised_openRec_of_bvar_bridge hu hbvar e,
    ValTy.spaceOf_openRec]

/-- Full dependent-prefix inference square.  This is the exact syntactic
fact needed by evaluator `.appV` after the lookup repair. -/
theorem inferTypeCtxRaised_valueOpenPush
    {y : VName} {sigmaV : ValTy} (hsigma : ValTy.lc sigmaV)
    (G : List ValTy) (e : ValExpr) :
    ValExpr.inferTypeCtx (ValTy.closePrefix (uOf y sigmaV) G)
        (ValExpr.openRec G.length (uOf y sigmaV) e) =
      ValTy.openRec G.length (uOf y sigmaV)
        (ValExpr.inferTypeCtx (G ++ [sigmaV]) e) :=
  inferTypeCtxRaised_openRec_of_bvar_bridge (.var hsigma)
    (inferBVarOpenBridge_closePrefix_append hsigma G) e

/-- Full dependent-prefix square for the current space inferer. -/
theorem inferSpaceCtx_valueOpenPush
    {y : VName} {sigmaV : ValTy} (hsigma : ValTy.lc sigmaV)
    (G : List ValTy) (e : ValExpr) :
    ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G)
        (ValExpr.openRec G.length (uOf y sigmaV) e) =
      ValSpace.openRec G.length (uOf y sigmaV)
        (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e) :=
  inferSpaceCtx_openRec_of_bvar_bridge (.var hsigma)
    (inferBVarOpenBridge_closePrefix_append hsigma G)
    (inferSpaceBVarOpenBridge_closePrefix_append hsigma G) e

/-- Corresponding space projection for every inference-consuming matrix
constructor. -/
theorem inferSpaceViaRaisedType_valueOpenPush
    {y : VName} {sigmaV : ValTy} (hsigma : ValTy.lc sigmaV)
    (G : List ValTy) (e : ValExpr) :
    inferSpaceViaRaisedType (ValTy.closePrefix (uOf y sigmaV) G)
        (ValExpr.openRec G.length (uOf y sigmaV) e) =
      ValSpace.openRec G.length (uOf y sigmaV)
        (inferSpaceViaRaisedType (G ++ [sigmaV]) e) :=
  inferSpaceViaRaisedType_openRec_of_bvar_bridge (.var hsigma)
    (inferBVarOpenBridge_closePrefix_append hsigma G) e

/-! ## Primitive leaf coherence gives every space observation -/

/-- Derived form of the leaf-to-shape traversal.  It imports no
adequacy relation and is the semantic analogue of the lookup square above. -/
theorem shpOf_valueOpenPush_from_leaf
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (hlcSigma : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall (s : ValSpace), y ∉ ValSpace.fv s ->
      ValSpace.shpOf
          (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D)
          (ValSpace.openRec G.length (uOf y sigmaV) s) =
        ValSpace.shpOf (orc rho (G ++ [sigmaV]) (D ++ [w])) s := by
  intro s hyS
  generalize hn : ValSpace.size s = n
  induction n using Nat.strong_induction_on generalizing s with
  | h n ih =>
      cases s with
      | empty => simp only [ValSpace.openRec, ValSpace.shpOf]
      | real => simp only [ValSpace.openRec, ValSpace.shpOf]
      | dsum s0 s1 =>
          simp only [ValSpace.fv, Finset.mem_union, not_or] at hyS
          have ih0 := ih (ValSpace.size s0) (by
            simp only [ValSpace.size] at hn
            omega) s0 hyS.1 rfl
          have ih1 := ih (ValSpace.size s1) (by
            simp only [ValSpace.size] at hn
            omega) s1 hyS.2 rfl
          have hd0 := congrArg (fun xs => xs.foldr (fun a b => a * b) 1) ih0
          have hd1 := congrArg (fun xs => xs.foldr (fun a b => a * b) 1) ih1
          simp only [ValSpace.openRec, ValSpace.shpOf_dsum, ValSpace.dof,
            hd0, hd1]
      | tprod s0 s1 =>
          simp only [ValSpace.fv, Finset.mem_union, not_or] at hyS
          have ih0 := ih (ValSpace.size s0) (by
            simp only [ValSpace.size] at hn
            omega) s0 hyS.1 rfl
          have ih1 := ih (ValSpace.size s1) (by
            simp only [ValSpace.size] at hn
            omega) s1 hyS.2 rfl
          have hd0 := congrArg (fun xs => xs.foldr (fun a b => a * b) 1) ih0
          have hd1 := congrArg (fun xs => xs.foldr (fun a b => a * b) 1) ih1
          simp only [ValSpace.openRec, ValSpace.shpOf_tprod, ValSpace.dof,
            hd0, hd1]
      | ffs p parent witness =>
          simp only [ValSpace.fv, Finset.mem_union, not_or] at hyS
          simp only [ValSpace.openRec, ValSpace.shpOf_ffs]
          exact congrArg List.singleton
            (horacle hlen hlcSigma hySigma hyG hyS.1 hyS.2)

theorem dof_valueOpenPush_from_leaf
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (hlcSigma : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    (s : ValSpace) (hyS : y ∉ ValSpace.fv s) :
    ValSpace.dof
        (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D)
        (ValSpace.openRec G.length (uOf y sigmaV) s) =
      ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w])) s := by
  simpa only [ValSpace.dof] using congrArg
    (fun xs => xs.foldr (fun a b => a * b) 1)
    (shpOf_valueOpenPush_from_leaf horacle hlen hlcSigma hySigma hyG s hyS)

/-- Reification transport needed when the evaluator crosses a literal
function value.  The induction pushes the same semantic argument into the
dependent prefix after proving the two reifications equal. -/
theorem fromEl_valueOpenPush_from_leaf
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {Dp Dc : List ValValSem}
    (hlen : G.length = Dp.length) (hD : Dp = Dc)
    (hlcSigma : ValTy.lc sigmaV) (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall (tau : ValTy), y ∉ ValTy.fv tau ->
      forall
        (v : (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau).El)
        (v' : (denotValTyS orc (rho.update y w)
          (ValTy.closePrefix (uOf y sigmaV) G) Dc
          (ValTy.openRec G.length (uOf y sigmaV) tau)).El),
        HEq v v' ->
        ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau) v =
          ValValSem.fromEl
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau)) v'
  | .space s, hy, v, v', hv => by
      simp only [ValTy.fv] at hy
      have hvv : v = v' := eq_of_heq hv
      subst hvv
      subst Dc
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromEl]
      rw [dof_valueOpenPush_from_leaf horacle hlen hlcSigma hySigma hyG s hy]
  | .piTy tau0 tau1, hy, v, v', hv => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      have hEl :
          (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0).El =
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau0)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      have hbeta : HEq
          (fun a : (denotValTyS orc rho
              (G ++ [sigmaV]) (Dp ++ [w]) tau0).El =>
            Except DimError
              (denotValTyS orc rho
                (tau0 :: (G ++ [sigmaV]))
                (ValValSem.fromEl
                  (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a ::
                    (Dp ++ [w])) tau1).El)
          (fun a' : (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau0)).El =>
            Except DimError
              (denotValTyS orc (rho.update y w)
                (ValTy.openRec G.length (uOf y sigmaV) tau0 ::
                  ValTy.closePrefix (uOf y sigmaV) G)
                (ValValSem.fromEl
                  (denotValTyS orc (rho.update y w)
                    (ValTy.closePrefix (uOf y sigmaV) G) Dc
                    (ValTy.openRec G.length (uOf y sigmaV) tau0)) a' :: Dc)
                (ValTy.openRec (G.length + 1) (uOf y sigmaV) tau1)).El) := by
        refine Function.hfunext hEl ?_
        intro a a' _
        apply heq_of_eq
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromEl]
      refine ValValSem.fn_congr _ _ hEl ?_
      intro a
      have hva : HEq (v a) (v' (hEl ▸ a)) :=
        heq_app_dep hEl hbeta hv (cast_heq hEl a).symm
      have hcanon := fromEl_valueOpenPush_from_leaf horacle hlen hD hlcSigma
        hySigma hyG tau0 hy.1 a (hEl ▸ a) (cast_heq hEl a).symm
      have hCod :
          (denotValTyS orc rho
            (tau0 :: (G ++ [sigmaV]))
            (ValValSem.fromEl
              (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a ::
                (Dp ++ [w])) tau1).El =
          (denotValTyS orc (rho.update y w)
            (ValTy.openRec G.length (uOf y sigmaV) tau0 ::
              ValTy.closePrefix (uOf y sigmaV) G)
            (ValValSem.fromEl
              (denotValTyS orc (rho.update y w)
                (ValTy.closePrefix (uOf y sigmaV) G) Dc
                (ValTy.openRec G.length (uOf y sigmaV) tau0)) (hEl ▸ a) :: Dc)
            (ValTy.openRec (G.length + 1) (uOf y sigmaV) tau1)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      apply except_map_heq_congr hCod (v a) (v' (hEl ▸ a)) hva
      intro z z' hzz
      have hlen' : (tau0 :: G).length =
          (ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a :: Dp).length := by
        simp only [List.length_cons, hlen]
      have hD' :
          (ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a :: Dp) =
          (ValValSem.fromEl
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau0)) (hEl ▸ a) :: Dc) :=
        congrArg₂ List.cons hcanon hD
      have hyG' : forall tauV, tauV ∈ tau0 :: G ->
          y ∉ ValTy.fv tauV := by
        intro tauV htau
        rcases List.mem_cons.mp htau with rfl | htau
        · exact hy.1
        · exact hyG tauV htau
      have ih := fromEl_valueOpenPush_from_leaf horacle hlen' hD' hlcSigma
        hySigma hyG' tau1 hy.2 z z' hzz
      simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
        Nat.succ_eq_add_one] using ih
  termination_by tau _ _ _ _ => ValTy.kindSize tau
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-- No-resize reification obeys the same prefix transport.  This is the
extra boundary used by higher-order reshape before it accepts a callback
argument. -/
theorem fromElChecked_valueOpenPush_from_leaf
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {Dp Dc : List ValValSem}
    (hlen : G.length = Dp.length) (hD : Dp = Dc)
    (hlcSigma : ValTy.lc sigmaV) (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV) :
    forall (tau : ValTy), y ∉ ValTy.fv tau ->
      forall
        (v : (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau).El)
        (v' : (denotValTyS orc (rho.update y w)
          (ValTy.closePrefix (uOf y sigmaV) G) Dc
          (ValTy.openRec G.length (uOf y sigmaV) tau)).El),
        HEq v v' ->
        ValValSem.fromElChecked
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau) v =
          ValValSem.fromElChecked
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau)) v'
  | .space s, hy, v, v', hv => by
      simp only [ValTy.fv] at hy
      have hvv : v = v' := eq_of_heq hv
      subst hvv
      subst Dc
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromElChecked]
      rw [dof_valueOpenPush_from_leaf horacle hlen hlcSigma hySigma hyG s hy]
  | .piTy tau0 tau1, hy, v, v', hv => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      have hEl :
          (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0).El =
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau0)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      have hbeta : HEq
          (fun a : (denotValTyS orc rho
              (G ++ [sigmaV]) (Dp ++ [w]) tau0).El =>
            Except DimError
              (denotValTyS orc rho
                (tau0 :: (G ++ [sigmaV]))
                (ValValSem.fromEl
                  (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a ::
                    (Dp ++ [w])) tau1).El)
          (fun a' : (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau0)).El =>
            Except DimError
              (denotValTyS orc (rho.update y w)
                (ValTy.openRec G.length (uOf y sigmaV) tau0 ::
                  ValTy.closePrefix (uOf y sigmaV) G)
                (ValValSem.fromEl
                  (denotValTyS orc (rho.update y w)
                    (ValTy.closePrefix (uOf y sigmaV) G) Dc
                    (ValTy.openRec G.length (uOf y sigmaV) tau0)) a' :: Dc)
                (ValTy.openRec (G.length + 1) (uOf y sigmaV) tau1)).El) := by
        refine Function.hfunext hEl ?_
        intro a a' _
        apply heq_of_eq
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      simp only [ValTy.openRec, denotValTyS, ValValSem.fromElChecked]
      apply congrArg Except.ok
      refine ValValSem.fn_partial_congr _ _ hEl ?_
      intro a
      have hva : HEq (v a) (v' (hEl ▸ a)) :=
        heq_app_dep hEl hbeta hv (cast_heq hEl a).symm
      have hcanon := fromEl_valueOpenPush_from_leaf horacle hlen hD hlcSigma
        hySigma hyG tau0 hy.1 a (hEl ▸ a) (cast_heq hEl a).symm
      have hCod :
          (denotValTyS orc rho
            (tau0 :: (G ++ [sigmaV]))
            (ValValSem.fromEl
              (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a ::
                (Dp ++ [w])) tau1).El =
          (denotValTyS orc (rho.update y w)
            (ValTy.openRec G.length (uOf y sigmaV) tau0 ::
              ValTy.closePrefix (uOf y sigmaV) G)
            (ValValSem.fromEl
              (denotValTyS orc (rho.update y w)
                (ValTy.closePrefix (uOf y sigmaV) G) Dc
                (ValTy.openRec G.length (uOf y sigmaV) tau0)) (hEl ▸ a) :: Dc)
            (ValTy.openRec (G.length + 1) (uOf y sigmaV) tau1)).El := by
        rw [denotValTyS_El_eq_carrierEl_raw,
          denotValTyS_El_eq_carrierEl_raw, ValTy.carrierEl_openRec]
      apply except_bind_heq_congr hCod (v a) (v' (hEl ▸ a)) hva
      intro z z' hzz
      have hlen' : (tau0 :: G).length =
          (ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a :: Dp).length := by
        simp only [List.length_cons, hlen]
      have hD' :
          (ValValSem.fromEl
            (denotValTyS orc rho (G ++ [sigmaV]) (Dp ++ [w]) tau0) a :: Dp) =
          (ValValSem.fromEl
            (denotValTyS orc (rho.update y w)
              (ValTy.closePrefix (uOf y sigmaV) G) Dc
              (ValTy.openRec G.length (uOf y sigmaV) tau0)) (hEl ▸ a) :: Dc) :=
        congrArg₂ List.cons hcanon hD
      have hyG' : forall tauV, tauV ∈ tau0 :: G ->
          y ∉ ValTy.fv tauV := by
        intro tauV htau
        rcases List.mem_cons.mp htau with rfl | htau
        · exact hy.1
        · exact hyG tauV htau
      have ih := fromElChecked_valueOpenPush_from_leaf horacle hlen' hD'
        hlcSigma hySigma hyG' tau1 hy.2 z z' hzz
      simpa only [List.cons_append, ValTy.closePrefix, List.length_cons,
        Nat.succ_eq_add_one] using ih
  termination_by tau _ _ _ _ => ValTy.kindSize tau
  decreasing_by
    all_goals simp_wf
    all_goals omega

theorem inferSpaceCtx_dof_valueOpenPush_from_leaf
    {orc : FFSOracleSem} (horacle : RawValueOpenPushOracleCoherent orc)
    {rho : ValEnvSem} {y : VName} {sigmaV : ValTy} {w : ValValSem}
    {G : List ValTy} {D : List ValValSem}
    (hlen : G.length = D.length) (hlcSigma : ValTy.lc sigmaV)
    (hySigma : y ∉ ValTy.fv sigmaV)
    (hyG : forall tauV, tauV ∈ G -> y ∉ ValTy.fv tauV)
    (e : ValExpr) (hyE : y ∉ ValExpr.fv e) :
    ValSpace.dof
        (orc (rho.update y w) (ValTy.closePrefix (uOf y sigmaV) G) D)
        (ValExpr.inferSpaceCtx (ValTy.closePrefix (uOf y sigmaV) G)
          (ValExpr.openRec G.length (uOf y sigmaV) e)) =
      ValSpace.dof (orc rho (G ++ [sigmaV]) (D ++ [w]))
        (ValExpr.inferSpaceCtx (G ++ [sigmaV]) e) := by
  rw [inferSpaceCtx_valueOpenPush hlcSigma G e]
  apply dof_valueOpenPush_from_leaf horacle hlen hlcSigma hySigma hyG
  apply ValExpr.notMem_fv_inferSpaceCtx y e (G ++ [sigmaV]) hyE
  intro tau htau
  rw [List.mem_append] at htau
  rcases htau with htau | htau
  · exact hyG tau htau
  · simp only [List.mem_singleton] at htau
    subst tau
    exact hySigma

end GLang.DirectOracleOpenPush
