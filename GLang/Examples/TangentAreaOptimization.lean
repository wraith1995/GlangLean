import GLang.Examples.TangentAreaSource
import GLang.Examples.TangentAreaPolynomial

/-! Verified specialization of the literal measured projected-area source.
The replacement is an explicit fixed polynomial. Correctness compares the
live partial evaluator on both programs; it is restricted to genuine rank-two
frames with matching input coordinates. -/
namespace GLang.Examples.TangentCoordinates
open scoped TensorProduct

/-- Correctness of the specialization for any checked compilation of the
literal source into its requested projected basis. -/
theorem measuredArea_optimization_correct
    {σ : DEnv} {ρ : ValEnvSem} {Γ : NLCtx} {Ψ : EvalCtx} {Γv : ValCtx}
    {base : Basis} {u₀ u₁ v w : Term} {original vv wv : ValExpr} {sv av : ValSpace}
    (fresh : IofFresh Γ) (hs : SValid Γ base.sof)
    (hc : Adequacy.PartialDirect.Consistent ∅ Γ Ψ Γv σ ρ)
    (compiled : Operational.Term ∅ Γ Ψ
      (projectedArea base.sof v w) (projectedAreaBasis base u₀ u₁) original (.space av))
    (frame : Module.Basis (Fin 2) ℝ (denotSpace σ base.sof).carrier)
    (h₀ : denotTerm σ u₀ = .hil ⟨denotSpace σ base.sof, frame 0⟩)
    (h₁ : denotTerm σ u₁ = .hil ⟨denotSpace σ base.sof, frame 1⟩)
    (a b : FlatArray)
    (ha : a.length = 2) (hb : b.length = 2)
    (hv : denotTerm σ v = .hil ⟨denotSpace σ base.sof,
      a.get 0 • frame 0 + a.get 1 • frame 1⟩)
    (hw : denotTerm σ w = .hil ⟨denotSpace σ base.sof,
      b.get 0 • frame 0 + b.get 1 • frame 1⟩)
    (hd : sv.dofPartial (PartialDirectOracle.oracle ρ [] []) = .ok 2)
    (hvv : Adequacy.PartialDirect.evalVal ρ [] [] vv = .ok (.array a))
    (hwv : Adequacy.PartialDirect.evalVal ρ [] [] wv = .ok (.array b)) :
    Adequacy.PartialDirect.evalVal ρ [] [] original =
      Adequacy.PartialDirect.evalVal ρ [] [] (optimizedAreaCode sv av vv wv) := by
  have hctx := hc.history.ctxWF_nl
  have henv := hc.history.envWF_nl
  have hsource := projectedArea_denot fresh hs hctx henv hv hw
  have hbasis := projectedAreaBasis_denot fresh hs hctx henv frame h₀ h₁
  have hspace := areaSpace_denot fresh hs hctx henv
  obtain ⟨raw, hraw, hcoords⟩ := (Metatheory.termAdequacy compiled σ Γv hc).1
  change PartialAdequacy.Agree PartialDirectOracle.oracle σ ρ [] [] []
    (.space (areaSpace base.sof)) (.space av)
    (denotBasis σ (projectedAreaBasis base u₀ u₁))
    (denotTerm σ (projectedArea base.sof v w)) raw at hcoords
  rw [hsource, hbasis] at hcoords
  cases raw with
  | fn T f => simp only [PartialAdequacy.Agree] at hcoords
  | array c =>
      simp only [PartialAdequacy.Agree] at hcoords
      change ∃ n, av.dofPartial (PartialDirectOracle.oracle ρ [] []) = .ok n ∧
        ((BasisDenot.vecs (areaHSpace (denotSpace σ base.sof))
          [areaGenerator (denotSpace σ base.sof) frame]).atSpace
          (denotSpace σ (areaSpace base.sof))).length = n ∧ c.length = n ∧
        (DVal.hil ⟨areaHSpace (denotSpace σ base.sof),
          (antisymMap (denotSpace σ base.sof)).rangeRestrict
            ((a.get 0 • frame 0 + a.get 1 • frame 1) ⊗ₜ[ℝ]
              (b.get 0 • frame 0 + b.get 1 • frame 1))⟩).atSpace
          (denotSpace σ (areaSpace base.sof)) =
          ∑ i : Fin n, c.get i.val •
            ((BasisDenot.vecs (areaHSpace (denotSpace σ base.sof))
              [areaGenerator (denotSpace σ base.sof) frame]).atSpace
              (denotSpace σ (areaSpace base.sof))).getD i.val 0 at hcoords
      rw [hspace] at hcoords
      simp only [BasisDenot.atSpace_vecs_self, List.length_cons, List.length_nil,
        atSpace_hil_self] at hcoords
      obtain ⟨n, hdout, hn, hclen, hcoord⟩ := hcoords
      have hn1 : n = 1 := hn.symm
      subst n
      have hexpand : (antisymMap (denotSpace σ base.sof)).rangeRestrict
          ((a.get 0 • frame 0 + a.get 1 • frame 1) ⊗ₜ[ℝ]
            (b.get 0 • frame 0 + b.get 1 • frame 1)) =
          (a.get 0 * b.get 1 - a.get 1 * b.get 0) •
            areaGenerator (denotSpace σ base.sof) frame := by
        apply Subtype.ext
        exact normalized_tensor_area _ _ _ _ _ _
      rw [hexpand] at hcoord
      have hscalar : c.get 0 = a.get 0 * b.get 1 - a.get 1 * b.get 0 :=
        (smul_left_injective ℝ (areaGenerator_ne_zero _ frame) hcoord).symm
      have hcarray : c = FlatArray.ofFn 1
          (fun _ => a.get 0 * b.get 1 - a.get 1 * b.get 0) := by
        refine FlatArray.ext_get hclen ?_
        intro i
        by_cases hi : i < 1
        · have hi0 : i = 0 := by omega
          subst i
          simpa using hscalar
        · have hci : c.get i = 0 := by simp [FlatArray.get, hclen, hi]
          simp [hci, FlatArray.get_ofFn, hi]
      rw [hraw, hcarray]
      exact (optimizedAreaCode_eval hd hdout hvv hwv ha hb).symm

/-- A checked source compiler followed by the proved area specialization.
Only operand coordinates, source typing, and a genuine frame are supplied;
the original area trace is constructed internally. The replacement program
is the explicit `optimizedAreaCode`, not an existentially selected program. -/
theorem measuredArea_optimizedCompilation
    {σ : DEnv} {ρ : ValEnvSem} {Γ : NLCtx} {Ψ : EvalCtx} {Γv : ValCtx}
    {base : Basis} {u₀ u₁ v w : Term} {vv wv : ValExpr} {sv : ValSpace}
    (fresh : IofFresh Γ) (hs : SValid Γ base.sof)
    (hc : Adequacy.PartialDirect.Consistent ∅ Γ Ψ Γv σ ρ)
    (hbase : Basis.BasisValid Γ base) (hbaseTy : base.tof = .space base.sof)
    (hu₀ : HasType ∅ Γ u₀ (.space base.sof))
    (hu₁ : HasType ∅ Γ u₁ (.space base.sof))
    (hvt : HasType ∅ Γ v (.space base.sof))
    (hwt : HasType ∅ Γ w (.space base.sof))
    (frame : Module.Basis (Fin 2) ℝ (denotSpace σ base.sof).carrier)
    (h₀ : denotTerm σ u₀ = .hil ⟨denotSpace σ base.sof, frame 0⟩)
    (h₁ : denotTerm σ u₁ = .hil ⟨denotSpace σ base.sof, frame 1⟩)
    (a b : FlatArray) (ha : a.length = 2) (hb : b.length = 2)
    (hv : denotTerm σ v = .hil ⟨denotSpace σ base.sof,
      a.get 0 • frame 0 + a.get 1 • frame 1⟩)
    (hw : denotTerm σ w = .hil ⟨denotSpace σ base.sof,
      b.get 0 • frame 0 + b.get 1 • frame 1⟩)
    (hd : sv.dofPartial (PartialDirectOracle.oracle ρ [] []) = .ok 2)
    (hvv : Adequacy.PartialDirect.evalVal ρ [] [] vv = .ok (.array a))
    (hwv : Adequacy.PartialDirect.evalVal ρ [] [] wv = .ok (.array b)) :
    ∃ original av,
      Operational.Term ∅ Γ Ψ
        (projectedArea base.sof v w) (projectedAreaBasis base u₀ u₁)
        original (.space av) ∧
      Adequacy.PartialDirect.evalVal ρ [] [] original =
        Adequacy.PartialDirect.evalVal ρ [] [] (optimizedAreaCode sv av vv wv) := by
  have ht := Examples.Paper.castΔ
    (projectedArea_hasType hs (Finmap.disjoint_empty _) hvt hwt) Finmap.empty_union
  have hbvalid := projectedAreaBasis_valid hbase hbaseTy hs hu₀ hu₁
  obtain ⟨original, tv, compiled, _, _, _, hdims⟩ :=
    Metatheory.checkedProgressAdequacy hc ht hbvalid
  cases tv with
  | piTy d c =>
      simp only [Adequacy.PartialDirect.AgreeDims, PartialAdequacy.DimsAt,
        projectedAreaBasis, Basis.tof] at hdims
  | space av =>
      exact ⟨original, av, compiled,
        measuredArea_optimization_correct fresh hs hc compiled frame h₀ h₁
          a b ha hb hv hw hd hvv hwv⟩

/-- Extract coordinates from an actual checked operand compilation in an
explicit rank-two frame. This is an operand agreement lemma, not an assumed
area/projection calculation. -/
theorem rankTwo_operand_denot
    {σ : DEnv} {ρ : ValEnvSem} {Γ : NLCtx} {Ψ : EvalCtx} {Γv : ValCtx}
    {base : Basis} {e : Term} {value : ValExpr} {sv : ValSpace}
    (hc : Adequacy.PartialDirect.Consistent ∅ Γ Ψ Γv σ ρ)
    (ht : base.tof = .space base.sof)
    (he : HasType ∅ Γ e (.space base.sof))
    (compiled : Operational.Term ∅ Γ Ψ e base value (.space sv))
    (frame : Module.Basis (Fin 2) ℝ (denotSpace σ base.sof).carrier)
    (hframe : denotBasis σ base = .vecs (denotSpace σ base.sof) [frame 0, frame 1])
    {a : FlatArray}
    (heval : Adequacy.PartialDirect.evalVal ρ [] [] value = .ok (.array a)) :
    a.length = 2 ∧ denotTerm σ e = .hil ⟨denotSpace σ base.sof,
      a.get 0 • frame 0 + a.get 1 • frame 1⟩ := by
  obtain ⟨raw, hraw, hagree⟩ := (Metatheory.termAdequacy compiled σ Γv hc).1
  rw [heval] at hraw
  cases hraw
  rw [ht, hframe] at hagree
  simp only [PartialAdequacy.Agree] at hagree
  simp only [BasisDenot.atSpace_vecs_self, List.length_cons, List.length_nil] at hagree
  obtain ⟨n, _, hn, ha, hcoord⟩ := hagree
  have hn2 : n = 2 := hn.symm
  subst n
  obtain ⟨x, hx⟩ := DVal.matchesShape_hil_eq
    (soundness he hc.history.ctxWF_nl hc.history.envWF_nl).1
  rw [hx, atSpace_hil_self] at hcoord
  refine ⟨ha, ?_⟩
  rw [hx]
  congr 1
  simpa [Fin.sum_univ_two] using hcoord

/-- Pointwise tangent-area specialization with actual moving-frame inputs.
The image-of-cokernel basis is matched explicitly to a genuine rank-two basis;
the four operand traces certify its generators and the input coordinates.
The original area trace is built internally, while the new program contains
only the two input variables and fixed determinant arithmetic. -/
theorem tangentMeasuredArea_optimizedCompilation
    {σ : DEnv} {ρ : ValEnvSem} {Γ : NLCtx} {Ψ : EvalCtx} {Γv : ValCtx}
    {f : Term} {fv : ValExpr} {u₀ u₁ v w vx wx : Name}
    (fresh : IofFresh Γ)
    (hc : Adequacy.PartialDirect.Consistent ∅ Γ Ψ Γv σ ρ)
    (hft : HasType ∅ Γ f (.space (.tprod (.dual Examples.Paper.R2) Examples.Paper.R3)))
    (hu₀ : Γ.lookup u₀ = some (.space (tangentSpace f)))
    (hu₁ : Γ.lookup u₁ = some (.space (tangentSpace f)))
    (hvt : Γ.lookup v = some (.space (tangentSpace f)))
    (hwt : Γ.lookup w = some (.space (tangentSpace f)))
    (frame : Module.Basis (Fin 2) ℝ (denotSpace σ (tangentSpace f)).carrier)
    (hframe : denotBasis σ (tangentBasis f) =
      .vecs (denotSpace σ (tangentSpace f)) [frame 0, frame 1])
    (cu₀ : Operational.Term ∅ Γ Ψ (.var u₀) (tangentBasis f)
      (.delta 0 (tangentSV fv)) (.space (tangentSV fv)))
    (cu₁ : Operational.Term ∅ Γ Ψ (.var u₁) (tangentBasis f)
      (.delta 1 (tangentSV fv)) (.space (tangentSV fv)))
    (cv : Operational.Term ∅ Γ Ψ (.var v) (tangentBasis f)
      (.var vx (.space (tangentSV fv))) (.space (tangentSV fv)))
    (cw : Operational.Term ∅ Γ Ψ (.var w) (tangentBasis f)
      (.var wx (.space (tangentSV fv))) (.space (tangentSV fv)))
    (hd : (tangentSV fv).dofPartial (PartialDirectOracle.oracle ρ [] []) = .ok 2)
    {a b : FlatArray}
    (hvv : Adequacy.PartialDirect.evalVal ρ [] [] (.var vx (.space (tangentSV fv))) =
      .ok (.array a))
    (hwv : Adequacy.PartialDirect.evalVal ρ [] [] (.var wx (.space (tangentSV fv))) =
      .ok (.array b)) :
    ∃ original av,
      Operational.Term ∅ Γ Ψ
        (projectedArea (tangentSpace f) (.var v) (.var w))
        (projectedAreaBasis (tangentStandard f) (.var u₀) (.var u₁))
        original (.space av) ∧
      Adequacy.PartialDirect.evalVal ρ [] [] original =
        Adequacy.PartialDirect.evalVal ρ [] []
          (optimizedAreaCode (tangentSV fv) av
            (.var vx (.space (tangentSV fv))) (.var wx (.space (tangentSV fv)))) := by
  have h₀ := (rankTwo_operand_denot hc rfl (.var_nlin hu₀) cu₀ frame hframe
    (PartialAdequacy.delta_ok hd 0)).2
  have h₁ := (rankTwo_operand_denot hc rfl (.var_nlin hu₁) cu₁ frame hframe
    (PartialAdequacy.delta_ok hd 1)).2
  simp only [FlatArray.get_ofFn] at h₀ h₁
  norm_num at h₀ h₁
  obtain ⟨ha, hv⟩ := rankTwo_operand_denot hc rfl (.var_nlin hvt) cv frame hframe hvv
  obtain ⟨hb, hw⟩ := rankTwo_operand_denot hc rfl (.var_nlin hwt) cw frame hframe hwv
  exact measuredArea_optimizedCompilation (base := tangentStandard f)
    fresh (.img Examples.Paper.svR2 Examples.Paper.svR3 hft) hc
    (tangentStandard_valid hft) rfl
    (.var_nlin hu₀) (.var_nlin hu₁) (.var_nlin hvt) (.var_nlin hwt)
    frame h₀ h₁ a b ha hb hv hw hd hvv hwv

end GLang.Examples.TangentCoordinates
