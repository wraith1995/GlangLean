import GLang.Value.Inference

/-! Coordinate conversion between the image of the canonical cokernel basis
and the paired canonical image basis.  This is a composition
of existing value operations, not an additional numerical primitive. -/

namespace GLang

/-- In standard ambient coordinates, compute `Uᵀ Aᵀ V`, where `U` and `V`
are the paired canonical domain and image columns.  Value
matrices store the source index first, hence this is the transpose of the
usual coordinate matrix `Vᵀ A U`.  The explicit space annotation makes the
construction commute with substitution without inferring types of open terms. -/
def ValExpr.imageCoords (s : ValSpace) (e : ValExpr) : ValExpr :=
  match s with
  | .tprod s0 s1 =>
      let v := ValExpr.reshapBase e s
      let u := ValExpr.gsvdU v (.idelta s0) (.idelta s1)
      let w := ValExpr.gsvdV v (.idelta s0) (.idelta s1)
      .mtm 0 0 s1 s1 w (.mtm 0 0 s0 s0 v (.vtrans u))
  | _ => .zero .empty

@[simp] theorem ValExpr.imageCoords_subst (x : VName) (arg e : ValExpr)
    (s : ValSpace) :
    ValExpr.subst x arg (imageCoords s e) =
      imageCoords (ValSpace.subst x arg s) (ValExpr.subst x arg e) := by
  cases s <;> rfl

@[simp] theorem ValExpr.imageCoords_inferSpaceCtx (G : List ValTy)
    (s0 s1 : ValSpace) (e : ValExpr) :
    inferSpaceCtx G (imageCoords (.tprod s0 s1) e) =
      .tprod (.ffs .cokernel (.tprod s0 s1) (reshapBase e (.tprod s0 s1)))
        (.ffs .image (.tprod s0 s1) (reshapBase e (.tprod s0 s1))) := rfl

@[simp] theorem ValExpr.imageCoords_inferSpaceCtx_subst (x : VName)
    (arg e : ValExpr) (s : ValSpace) :
    inferSpaceCtx [] (imageCoords (ValSpace.subst x arg s) (subst x arg e)) =
      ValSpace.subst x arg (inferSpaceCtx [] (imageCoords s e)) := by
  cases s <;> rfl

theorem ValExpr.imageCoords_fv (s : ValSpace) (e : ValExpr) :
    (imageCoords s e).fv ⊆ s.fv ∪ e.fv := by
  cases s <;> simp [imageCoords, reshapBase, ValExpr.fv, ValTy.fv, ValSpace.fv]
  all_goals intro x hx; simp_all only [Finset.mem_union]; tauto

end GLang
