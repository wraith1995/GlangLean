/- GLang.ValueInfer: theorem API for the canonical inference functions in ValueDenot. -/
import GLang.Value.Inference
import GLang.Value.Typing
import GLang.Value.Supporting.StrictTyping

namespace GLang.RuntimeValue

/-- For a well-typed value, canonical context-aware type inference recovers its type. -/
theorem ValExpr.inferTypeCtx_eq_of_typed {epsilon : ValCtx}
    {Gamma : List ValTy} {e : ValExpr} {tau : ValTy} (h : ValHasType epsilon e tau) :
    ValExpr.inferTypeCtx Gamma e = tau := by
  refine @ValHasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ e tau _ => ValExpr.inferTypeCtx Gamma e = tau)
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_ ?_
    ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_ ?_
    ?_
    ?_ ?_
    ?_ ?_
    ?_ ?_
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_
    ?_
    ?_ ?_ ?_
    _ _ _ h
  case refine_20 =>
    intro epsilon' s0 s es hsv hbody hsvr hdet ihsv ihbody ihsvr
    cases es with
    | nil => simp [ValExpr.inferTypeCtx, hdet rfl]
    | cons e es => exact ihbody e (List.mem_cons_self)
  all_goals intros <;> simp_all [ValExpr.inferTypeCtx]

/-- For a well-typed value, canonical context-aware type inference recovers its type. -/
theorem ValHasType.inferType_eq_of_typed {epsilon : ValCtx}
    {e : ValExpr} {tau : ValTy} (h : ValHasType epsilon e tau) :
    ValExpr.inferType e = tau := by
  refine @ValHasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ e tau _ => ValExpr.inferType e = tau)
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_ ?_
    ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_ ?_
    ?_
    ?_ ?_
    ?_ ?_
    ?_ ?_
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_
    ?_
    ?_ ?_ ?_
    _ _ _ h
  case refine_20 =>
    intro epsilon' s0 s es hsv hbody hsvr hdet ihsv ihbody ihsvr
    cases es with
    | nil => simp [ValExpr.inferType, hdet rfl]
    | cons e es => exact ihbody e (List.mem_cons_self)
  all_goals intros <;> simp_all [ValExpr.inferType]

/-- Canonical space inference agrees with a well-typed base-kind conclusion. -/
theorem ValExpr.inferSpaceCtx_eq_of_typed {epsilon : ValCtx}
    {Gamma : List ValTy} {e : ValExpr} {s : ValSpace}
    (h : ValHasType epsilon e (.space s)) :
    ValExpr.inferSpaceCtx Gamma e = s := by
  refine @ValHasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ e tau _ => ValExpr.inferSpaceCtx Gamma e = tau.spaceOf)
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_ ?_
    ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_ ?_
    ?_
    ?_ ?_
    ?_ ?_
    ?_ ?_
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_
    ?_
    ?_ ?_ ?_
    _ _ _ h
  case refine_20 =>
    intro epsilon' s0 s' es hsv hbody hsvr hdet ihsv ihbody ihsvr
    cases es with
    | nil => simp [ValExpr.inferSpaceCtx, hdet rfl]
    | cons e es => exact ihbody e (List.mem_cons_self)
  case refine_22 =>
    intro epsilon' e0 e1 tau0 tau1 tauOut k h0 h1 heq ht ih0 ih1 iht
    have hf := ValExpr.inferTypeCtx_eq_of_typed (Gamma := Gamma) h0
    simp [GLang.ValExpr.inferSpaceCtx, GLang.ValExpr.inferTypeCtx, hf, heq]
  all_goals intros <;> simp_all [ValExpr.inferSpaceCtx, GLang.ValExpr.inferTypeCtx, ValTy.spaceOf]

/-- Canonical space inference agrees with a well-typed base-kind conclusion. -/
theorem ValExpr.inferSpaceCtx_eq_spaceOf {epsilon : ValCtx}
    {Gamma : List ValTy} {e : ValExpr} {tau : ValTy}
    (h : ValHasType epsilon e tau) :
    ValExpr.inferSpaceCtx Gamma e = tau.spaceOf := by
  refine @ValHasType.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ e tau _ => ValExpr.inferSpaceCtx Gamma e = tau.spaceOf)
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_ ?_
    ?_ ?_ ?_ ?_
    ?_ ?_
    ?_ ?_ ?_
    ?_
    ?_ ?_
    ?_ ?_
    ?_ ?_
    ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_
    ?_
    ?_ ?_ ?_
    _ _ _ h
  case refine_20 =>
    intro epsilon' s0 s' es hsv hbody hsvr hdet ihsv ihbody ihsvr
    cases es with
    | nil => simp [ValExpr.inferSpaceCtx, hdet rfl]
    | cons e es => exact ihbody e (List.mem_cons_self)
  case refine_22 =>
    intro epsilon' e0 e1 tau0 tau1 tauOut k h0 h1 heq ht ih0 ih1 iht
    have hf := ValExpr.inferTypeCtx_eq_of_typed (Gamma := Gamma) h0
    simp [GLang.ValExpr.inferSpaceCtx, GLang.ValExpr.inferTypeCtx, hf, heq]
  all_goals intros <;> simp_all [ValExpr.inferSpaceCtx, GLang.ValExpr.inferTypeCtx, ValTy.spaceOf]

theorem ValHasType.unique {ε e t t'} (h : ValHasType ε e t) (h' : ValHasType ε e t') : t = t' :=
  (ValExpr.inferTypeCtx_eq_of_typed (Gamma := []) h).symm.trans (ValExpr.inferTypeCtx_eq_of_typed h')

end GLang.RuntimeValue
