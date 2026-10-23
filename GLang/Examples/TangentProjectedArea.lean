import GLang.Examples.TangentCoordinates

namespace GLang.Examples.TangentCoordinates

abbrev squareBasis (b : Basis) : Basis := .tprod b b
abbrev linearBasis (b : Basis) : Basis := .tprod (.dual (squareBasis b)) (squareBasis b)
abbrev curriedBasis (b : Basis) : Basis := .tprod (.dual b) (.tprod (.dual b) (squareBasis b))
abbrev squareSV (sv : ValSpace) : ValSpace := .tprod sv sv
abbrev linearSV (sv : ValSpace) : ValSpace := .tprod (squareSV sv) (squareSV sv)
abbrev curriedSV (sv : ValSpace) : ValSpace := .tprod sv (.tprod sv (squareSV sv))

def curryCode (sv : ValSpace) : ValExpr :=
  tensorColumns (linearSV sv) (curriedSV sv) fun i =>
    tensorColumns sv (.tprod sv (squareSV sv)) fun j =>
      tensorColumns sv (squareSV sv) fun k =>
        .reshapBase (.ttv (squareSV sv) (.delta i.val (linearSV sv))
          (.tprodE (.delta j.val sv) (.delta k.val sv))) (squareSV sv)

/-- Derive curry itself; no uncurrying/permutation primitive is assumed. -/
theorem curry_op {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    (ht : b.tof = .space b.sof) (hlc : Space.lc b.sof)
    (hs : ValSpace.EvalS Ψ b.sof sv) :
    ValExpr.OpStep Ψ (Term.curry2NonReal b.sof b.sof (.tprod b.sof b.sof))
      (.tprod (.dual (linearBasis b)) (curriedBasis b)) (curryCode sv) := by
  unfold Term.curry2NonReal curryCode tensorColumns
  refine ValExpr.OpStep.llam_assemble (b' := linearBasis b) (b := curriedBasis b)
    rfl (.tprod (.dual (.tprod hs hs)) (.tprod hs hs))
    (.tprod (.dual hs) (.tprod (.dual hs) (.tprod hs hs))) Ψ.avoid (fun g hg i => ?_)
  have fg := (EvalCtx.avoid_spec hg).1 (linearBasis b)
  let Ψg := Ψ.extend g (linearBasis b) (.delta i.val (linearSV sv))
  have hsg : ValSpace.EvalS Ψg b.sof sv := evalS_wk hs fg
  have hvg : ValExpr.OpStep Ψg (.var g) (linearBasis b) (.delta i.val (linearSV sv)) :=
    .var (Finmap.lookup_insert _)
  simp [Term.openVar, Term.openRec, Space.openRec, Space.openRec_lc hlc]
  refine ValExpr.OpStep.llam_assemble (b' := b) (b := .tprod (.dual b) (squareBasis b))
    ht hsg (.tprod (.dual hsg) (.tprod hsg hsg)) Ψg.avoid (fun y hy j => ?_)
  have fy := (EvalCtx.avoid_spec hy).1 b
  let Ψy := Ψg.extend y b (.delta j.val sv)
  have hsy : ValSpace.EvalS Ψy b.sof sv := evalS_wk hsg fy
  have hvgy : ValExpr.OpStep Ψy (.var g) (linearBasis b) (.delta i.val (linearSV sv)) :=
    opStep_wk hvg fy
  have hvy : ValExpr.OpStep Ψy (.var y) b (.delta j.val sv) :=
    .var (Finmap.lookup_insert _)
  simp [Term.openVar, Term.openRec, Space.openRec, Space.openRec_lc hlc]
  refine ValExpr.OpStep.llam_assemble (b' := b) (b := squareBasis b)
    ht hsy (.tprod hsy hsy) Ψy.avoid (fun z hz k => ?_)
  have fz := (EvalCtx.avoid_spec hz).1 b
  let Ψz := Ψy.extend z b (.delta k.val sv)
  have hsz : ValSpace.EvalS Ψz b.sof sv := evalS_wk hsy fz
  have hvgz : ValExpr.OpStep Ψz (.var g) (linearBasis b) (.delta i.val (linearSV sv)) :=
    opStep_wk hvgy fz
  have hvyz : ValExpr.OpStep Ψz (.var y) b (.delta j.val sv) := opStep_wk hvy fz
  simp [Term.openVar, Term.openRec, Space.openRec, Space.openRec_lc hlc]
  exact ValExpr.OpStep.appL_lin hvgz (.tprod hsz hsz)
    (.tprodE hvyz (.var (Finmap.lookup_insert _)) ht ht) (.tprod hsz hsz) rfl

noncomputable def antiSymLinear (s : Space) : Term :=
  Term.applyUncurry2NonReal s s (.tprod s s) (antiSym s)

/-- Applying the pseudoinverse of curry is the literal source definition of uncurry. -/
noncomputable def antiSymLinearCode (sv : ValSpace) : ValExpr :=
  .reshapBase (.ttv (curriedSV sv) (.pinv (curryCode sv)) (antiSymOperatorCode sv))
    (linearSV sv)

/-- Uncurried antisymmetrizer in standard coordinates, built from the actual
curry, pseudoinverse, application, and linear-lambda rules. -/
theorem antiSymLinear_op {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    (ht : b.tof = .space b.sof) (hlc : Space.lc b.sof)
    (hstd : Basis.isStd b) (hs : ValSpace.EvalS Ψ b.sof sv) :
    ValExpr.OpStep Ψ (antiSymLinear b.sof) (linearBasis b) (antiSymLinearCode sv) := by
  apply ValExpr.OpStep.appL_lin (b₀ := curriedBasis b) (b₁ := linearBasis b)
  · exact .pinvT_std (curry_op ht hlc hs)
      ⟨hstd, hstd, hstd, hstd⟩ ⟨⟨hstd, hstd⟩, hstd, hstd⟩
  · exact .tprod (.dual hs) (.tprod (.dual hs) (.tprod hs hs))
  · exact antiSym_op ht hlc hs
  · exact .tprod (.dual (.tprod hs hs)) (.tprod hs hs)
  · rfl

/-- The image space of the normalized antisymmetrizer. -/
noncomputable def areaSpace (s : Space) : Space :=
  .img (.tprod s s) (.tprod s s) (antiSymLinear s)

/-- A valid standard fallback, whenever `b` is a valid standard basis of `s`. -/
noncomputable def areaFallback (b : Basis) : Basis :=
  .proj (areaSpace b.sof) (squareBasis b) (squareBasis b)

/-- The actual image dimension expression emitted by the space rule. -/
noncomputable def areaSV (sv : ValSpace) : ValSpace :=
  .ffs .image (linearSV sv)
    (.reshap (antiSymLinearCode sv) (.space (linearSV sv)) (.space (linearSV sv)))

/-- Literal `proj_Img(v ⊗ w)` from the moving-area example. -/
noncomputable def projectedArea (s : Space) (v w : Term) : Term :=
  .appL (.tprod s s) (areaSpace s)
    (Term.lproj (areaSpace s) (.tprod s s)) (.tprodE v w)

/-- Projection matrix before multiplication by the input tensor coordinates. -/
noncomputable def projectionCode (sv : ValSpace) : ValExpr :=
  .pinv (.vtrans (.gsvdV (antiSymLinearCode sv)
    (.idelta (squareSV sv)) (.idelta (squareSV sv))))

/-- Exact compiled projected area in the standard fallback. -/
noncomputable def projectedAreaCode (sv : ValSpace) (v w : ValExpr) : ValExpr :=
  .reshapBase (.ttv (squareSV sv) (projectionCode sv) (.tprodE v w)) (areaSV sv)

theorem areaSpace_eval {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    (ht : b.tof = .space b.sof) (hlc : Space.lc b.sof)
    (hstd : Basis.isStd b) (hs : ValSpace.EvalS Ψ b.sof sv) :
    ValSpace.EvalS Ψ (areaSpace b.sof) (areaSV sv) :=
  .img (antiSymLinear_op ht hlc hstd hs) rfl ⟨squareBasis b, squareBasis b, rfl⟩
    (.tprod (.dual (.tprod hs hs)) (.tprod hs hs))

theorem projectedArea_op {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    {v w : Term} {vv wv : ValExpr}
    (ht : b.tof = .space b.sof) (hlc : Space.lc b.sof)
    (hstd : Basis.isStd b) (hs : ValSpace.EvalS Ψ b.sof sv)
    (hv : ValExpr.OpStep Ψ v b vv) (hw : ValExpr.OpStep Ψ w b wv) :
    ValExpr.OpStep Ψ (projectedArea b.sof v w) (areaFallback b)
      (projectedAreaCode sv vv wv) := by
  apply ValExpr.OpStep.appL_lin (b₀ := squareBasis b) (b₁ := areaFallback b)
  · apply ValExpr.OpStep.pinvT_std (b₀ := squareBasis b) (b₁ := areaFallback b)
    · exact .embed_img rfl rfl
        (.inner_std ⟨hstd, hstd⟩ (.tprod hs hs) rfl)
        (.inner_std ⟨hstd, hstd⟩ (.tprod hs hs) rfl)
        (antiSymLinear_op ht hlc hstd hs)
    · exact ⟨hstd, hstd⟩
    · exact ⟨⟨hstd, hstd⟩, hstd, hstd⟩
  · exact .tprod hs hs
  · exact .tprodE hv hw ht ht
  · exact areaSpace_eval ht hlc hstd hs
  · rfl

/-- Ordered projection of all four tensor products, with the supplied fallback.
LexInd/RREF skips the zero diagonal projections and dependent reverse pair. -/
noncomputable def projectedAreaBasis (b : Basis) (u₀ u₁ : Term) : Basis :=
  .terms (areaSpace b.sof)
    [projectedArea b.sof u₀ u₀, projectedArea b.sof u₀ u₁,
      projectedArea b.sof u₁ u₀, projectedArea b.sof u₁ u₁] (areaFallback b)

/-- Exact four-column RREF completion input, in the same order as the basis. -/
noncomputable def projectedGeneratorsCode (sv : ValSpace) (u₀ u₁ : ValExpr) : ValExpr :=
  .dsumE (.dsumE (.dsumE (projectedAreaCode sv u₀ u₀) (projectedAreaCode sv u₀ u₁))
    (projectedAreaCode sv u₁ u₀)) (projectedAreaCode sv u₁ u₁)

/-- The RREF coordinate conversion retained by the literal semantics. -/
noncomputable def projectedBasisChangeCode (sv : ValSpace) (u₀ u₁ : ValExpr) : ValExpr :=
  let a := areaSV sv
  let aa := ValSpace.tprod a a
  .reshap (.rrefRep (projectedGeneratorsCode sv u₀ u₁)
    (.reshapBase (.reshap (.idelta a) (.space aa) (.space aa)) aa))
    (.space aa) (.space aa)

/-- Exact generated value for the area measured in the projected moving basis. -/
noncomputable def measuredAreaCode (sv : ValSpace) (u₀ u₁ v w : ValExpr) : ValExpr :=
  let a := areaSV sv
  .ttv a (.reshapBase (projectedBasisChangeCode sv u₀ u₁) (.tprod a a))
    (.reshapBase (projectedAreaCode sv v w) a)

/-- Full literal projected-area derivation into the completed projected basis.
The only term premises are coordinates of the four input vectors. -/
theorem measuredArea_op {Ψ : EvalCtx} {b : Basis} {sv : ValSpace}
    {u₀ u₁ v w : Term} {u₀v u₁v vv wv : ValExpr}
    (ht : b.tof = .space b.sof) (hlc : Space.lc b.sof)
    (hstd : Basis.isStd b) (hs : ValSpace.EvalS Ψ b.sof sv)
    (hu₀ : ValExpr.OpStep Ψ u₀ b u₀v) (hu₁ : ValExpr.OpStep Ψ u₁ b u₁v)
    (hv : ValExpr.OpStep Ψ v b vv) (hw : ValExpr.OpStep Ψ w b wv) :
    ValExpr.OpStep Ψ (projectedArea b.sof v w) (projectedAreaBasis b u₀ u₁)
      (measuredAreaCode sv u₀v u₁v vv wv) := by
  have hd := areaSpace_eval ht hlc hstd hs
  have hp00 := projectedArea_op ht hlc hstd hs hu₀ hu₀
  have hp01 := projectedArea_op ht hlc hstd hs hu₀ hu₁
  have hp10 := projectedArea_op ht hlc hstd hs hu₁ hu₀
  have hp11 := projectedArea_op ht hlc hstd hs hu₁ hu₁
  apply ValExpr.OpStep.cob (b₀ := projectedAreaBasis b u₀ u₁) (b₁ := areaFallback b) rfl rfl
    (projectedArea_op ht hlc hstd hs hv hw) _ hd
  apply Basis.EvalBB.terms_rref (b' := areaFallback b) (.refl rfl hd) _ hd
  exact .dsumE (.dsumE (.dsumE hp00 hp01 rfl rfl) hp10 rfl rfl) hp11 rfl rfl

/-! Source formation and validity, independent of the operational trace. -/

noncomputable def antiSym_hasType {Γ : NLCtx} {s : Space} (hs : SValid Γ s) :
    HasType ∅ Γ (antiSym s)
      (.space (.tprod (.dual s) (.tprod (.dual s) (.tprod s s)))) := by
  unfold antiSym
  refine HasType.llam_tensor ∅ (by intro h; cases h) hs
    (.tprod (.dual hs) (.tprod hs hs)) (fun y _ => ?_)
  simp only [Nat.reduceAdd, Nat.reduceEqDiff, ↓reduceIte, Term.openVar, Term.openRec,
    Space.openRec, Space.openRec_lc (SValid.lc hs), antiSymBody]
  refine HasType.llam_tensor {y} (by intro h; cases h) hs (.tprod hs hs) (fun z hz => ?_)
  simp only [Finset.mem_singleton] at hz
  simp only [↓reduceIte, Term.openVar, Term.openRec]
  rw [Examples.Paper.pair_ctx y z s s (Ne.symm hz)]
  exact Examples.Paper.smul_const (1/2) (.tprod hs hs)
    (.add (.tprod hs hs)
      (Examples.Paper.tprodE_vars y z (Ne.symm hz) hs hs)
      (Examples.Paper.smul_const (-1) (.tprod hs hs)
        (Examples.Paper.castΔ (Examples.Paper.tprodE_vars z y hz hs hs)
          (Finmap.union_comm_of_disjoint (Examples.Paper.pair_disjoint hz)))))

noncomputable def antiSymLinear_hasType {Γ : NLCtx} {s : Space} (hs : SValid Γ s) :
    HasType ∅ Γ (antiSymLinear s)
      (.space (.tprod (.dual (.tprod s s)) (.tprod s s))) :=
  Term.applyUncurry2NonReal_hasType (by intro h; cases h) hs hs (.tprod hs hs)
    (antiSym_hasType hs)

noncomputable def areaSpace_valid {Γ : NLCtx} {s : Space} (hs : SValid Γ s) :
    SValid Γ (areaSpace s) :=
  .img (.tprod hs hs) (.tprod hs hs) (antiSymLinear_hasType hs)

noncomputable def projectedArea_hasType {Γ : NLCtx} {s : Space}
    {Δv Δw : LCtx} {v w : Term} (hs : SValid Γ s)
    (hd : Finmap.Disjoint Δv Δw)
    (hv : HasType Δv Γ v (.space s)) (hw : HasType Δw Γ w (.space s)) :
    HasType (Δv ∪ Δw) Γ (projectedArea s v w) (.space (areaSpace s)) :=
  Examples.Paper.castΔ
    (HasType.app_linear (.tprod hs hs) (areaSpace_valid hs) (Finmap.disjoint_empty _)
      (HasType.lproj (areaSpace_valid hs) (.tprod hs hs)
        (.sub_img (.tprod hs hs) (.tprod hs hs) (antiSymLinear_hasType hs)))
      (.tprodE hs hs hd hv hw)) Finmap.empty_union

theorem areaFallback_valid {Γ : NLCtx} {b : Basis}
    (hb : Basis.BasisValid Γ b) (ht : b.tof = .space b.sof) (hs : SValid Γ b.sof) :
    Basis.BasisValid Γ (areaFallback b) :=
  .proj_img (.tprod hb hb ht ht) (.tprod hb hb ht ht) rfl rfl
    ⟨antiSymLinear_hasType hs⟩

theorem projectedAreaBasis_valid {Γ : NLCtx} {b : Basis} {u₀ u₁ : Term}
    (hb : Basis.BasisValid Γ b) (ht : b.tof = .space b.sof) (hs : SValid Γ b.sof)
    (hu₀ : HasType ∅ Γ u₀ (.space b.sof)) (hu₁ : HasType ∅ Γ u₁ (.space b.sof)) :
    Basis.BasisValid Γ (projectedAreaBasis b u₀ u₁) := by
  refine .terms (areaFallback_valid hb ht hs) rfl ⟨areaSpace_valid hs⟩ ?_ (by simp)
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  all_goals exact ⟨Examples.Paper.castΔ
    (projectedArea_hasType hs (Finmap.disjoint_empty _) (by assumption) (by assumption))
    Finmap.empty_union⟩

end GLang.Examples.TangentCoordinates
