import GLang.Surface.Context
import GLang.Elaboration.JudgmentErasure
import GLang.Proofs.Source.SourceContextInductive

/-! Erasing a well-formed annotated context. -/

namespace GLang

theorem InductiveCtxWF.toSurface {Δ ε} (h : InductiveCtxWF Δ ε) :
    Surface.InductiveCtxWF Δ.erase ε.erase := by
  induction h with
  | empty => exact .empty
  | linear ctx hx hy hs hv ih =>
      simpa only [LCtx.erase, sourceMap_insert] using
        Surface.InductiveCtxWF.linear ih
          (by simpa using hx) (by simpa using hy)
          (fun y hy => (sourceMap_mem _ _ _).mpr (hs y (Space.erase_fv_subset _ hy)))
          hv.toSurface
  | nonlinear ctx hx hy hs hv ih =>
      simpa only [NLCtx.erase, sourceMap_insert] using
        Surface.InductiveCtxWF.nonlinear ih
          (by simpa using hx) (by simpa using hy)
          (fun y hy => (sourceMap_mem _ _ _).mpr (hs y (Ty.erase_fv_subset _ hy)))
          hv.toSurface

end GLang
