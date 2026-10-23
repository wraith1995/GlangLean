import GLang.Value.Inference
import GLang.Value.Supporting.StrictTyping

namespace GLang

/-- A finite sum's empty source annotation is derived from its actual syntax. -/
def ValHasType.sumAt {ε : ValCtx} {index target : ValSpace} {es : List ValExpr}
    (hi : ValSValid ε index) (ht : ValSValid ε target)
    (he : ∀ e ∈ es, ValHasType ε e (.space target)) :
    ValHasType ε (ValExpr.sumAt index es target) (.space target) := by
  cases es with
  | nil =>
    exact .reshap (.vsum hi (fun _ h => False.elim (List.not_mem_nil h))
      .empty (fun _ => rfl)) (.space .empty) (.space ht)
  | cons head tail =>
    exact .reshap (.vsum hi he ht (fun h => by cases h)) (.space ht) (.space ht)

/-- The assembly wrapper preserves local closure in both family cases. -/
theorem ValExpr.lc.sumAt {index target : ValSpace} {es : List ValExpr}
    (he : ValExpr.lc (.vsum index es)) (ht : ValSpace.lc target) :
    ValExpr.lc (ValExpr.sumAt index es target) := by
  cases es with
  | nil => exact .reshap he (.space ht) (.space .empty)
  | cons head tail => exact .reshap he (.space ht) (.space ht)

@[simp] theorem ValExpr.subst_sumAt (x : VName) (u : ValExpr)
    (index : ValSpace) (es : List ValExpr) (target : ValSpace) :
    ValExpr.subst x u (ValExpr.sumAt index es target) =
      ValExpr.sumAt (ValSpace.subst x u index) (es.map (ValExpr.subst x u))
        (ValSpace.subst x u target) := by
  cases es <;> simp [ValExpr.sumAt, ValExpr.subst, ValExpr.substList_eq_map,
    ValTy.subst, ValSpace.subst]

@[simp] theorem ValExpr.openRec_sumAt (k : Nat) (u : ValExpr)
    (index : ValSpace) (es : List ValExpr) (target : ValSpace) :
    ValExpr.openRec k u (ValExpr.sumAt index es target) =
      ValExpr.sumAt (ValSpace.openRec k u index) (es.map (ValExpr.openRec k u))
        (ValSpace.openRec k u target) := by
  cases es <;> simp [ValExpr.sumAt, ValExpr.openRec, ValExpr.openRecList_eq_map,
    ValTy.openRec, ValSpace.openRec]

@[simp] theorem ValExpr.closeRec_sumAt (k : Nat) (x : VName)
    (index : ValSpace) (es : List ValExpr) (target : ValSpace) :
    ValExpr.closeRec k x (ValExpr.sumAt index es target) =
      ValExpr.sumAt (ValSpace.closeRec k x index) (es.map (ValExpr.closeRec k x))
        (ValSpace.closeRec k x target) := by
  cases es <;> simp [ValExpr.sumAt, ValExpr.closeRec, ValExpr.closeRecList_eq_map,
    ValTy.closeRec, ValSpace.closeRec]

@[simp] theorem ValExpr.fv_sumAt (index : ValSpace) (es : List ValExpr)
    (target : ValSpace) :
    ValExpr.fv (ValExpr.sumAt index es target) =
      ValExpr.fv (ValExpr.reshapBase (.vsum index es) target) := by
  cases es <;> simp [ValExpr.sumAt, ValExpr.reshapBase, ValExpr.fv,
    ValTy.fv, ValSpace.fv, Finset.union_assoc]

end GLang
