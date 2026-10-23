import GLang.Proofs.Adequacy.Partial.Source.PartialSourceHistory
import GLang.Proofs.Source.SourceContextInductive
import GLang.Proofs.Value.Runtime.RuntimeValueMatchedClosure

namespace GLang.PaperContextResults

open Basis (BasisValid)

structure Entry (Ψ : EvalCtx) (x : VName) (b : Basis) (v : ValExpr) : Prop where
  typeRealized : ValTy.EvalT Ψ (Basis.tof b) (ValExpr.inferType v)
  valueScoped : ValExpr.fv v ⊆ Ψ.keyNames ∪ {x}
  frameAnchored : V2.EvalFrameAnchored Ψ b v

/-- Value typing supplies the base-inference evidence stored by consistency. -/
theorem inferSpaceMatchesBase (hv : RuntimeValue.ValHasType Γv v Tv) :
    ValExpr.InferSpaceMatchesBase v Tv :=
  .ofSpaceOfEq (RuntimeValue.ValExpr.inferSpaceCtx_eq_spaceOf hv)

theorem Entry.creation (he : Entry Ψ x b v)
    (hc : RuntimeValue.ValCtxValid Γv)
    (hv : RuntimeValue.ValHasType Γv v (ValExpr.inferType v)) :
    V2.EvalEntryCreation Ψ x b v := by
  refine ⟨⟨he.typeRealized, ?_, (RuntimeValue.validExpr_lc hc hv).1⟩,
    he.frameAnchored⟩
  simpa only [EvalCtx.keyNames_extend_core, Finset.union_singleton] using he.valueScoped

/-- Erasing implementation evidence recovers precisely the printed entry. -/
theorem entry_of_creation (he : V2.EvalEntryCreation Ψ x b v) :
    Entry Ψ x b v := by
  refine ⟨he.valid.typeRealized, ?_, he.frameAnchored⟩
  simpa only [EvalCtx.keyNames_extend_core, Finset.union_singleton] using he.valid.valueScoped

/-- Indexed operational formation already implies source-context formation. -/
theorem sourceContext (hc : Operational.TypedContext Δ ε Γv Ψ) :
    InductiveCtxWF Δ ε := by
  induction hc with
  | empty => exact .empty
  | extend_nlin _ hf _ hb _ _ ih =>
      exact .nonlinear ih hf.freshLinear hf.freshNonlinear
        (fun y hy => Finmap.mem_keys.mp
          (hb.fv_subset_keys_for_progress ((Basis.fv_tof_subset _) hy)))
        hb.tof_valid_structural.some
  | @extend_lin Δ ε Γv Ψ x b v s k _ hf _ hb hs _ _ ih =>
      have ht := hb.tof_valid_structural.some
      rw [hs] at ht
      cases ht with
      | space ht =>
        apply InductiveCtxWF.linear ih hf.freshLinear hf.freshNonlinear _ ht
        intro y hy
        apply Finmap.mem_keys.mp
        apply hb.fv_subset_keys_for_progress
        apply Basis.fv_tof_subset b
        simpa only [hs, Ty.fv] using hy
  | extend_rep _ _ _ _ _ _ ih => exact ih

/-- Introduce a nonlinear source name using only the printed entry conditions. -/
theorem contextNonlinear (hc : Operational.TypedContext Δ ε Γv Ψ)
    (hx : V2.SourceEntryValid Δ ε x) (hb : BasisValid ε b)
    (he : Entry Ψ x b v)
    (hk : RuntimeValue.ValTValid Γv (ValExpr.inferType v) k)
    (hv : RuntimeValue.ValHasType (Finmap.insert x (ValExpr.inferType v) Γv)
      v (ValExpr.inferType v)) :
    Operational.TypedContext Δ (Finmap.insert x (Basis.tof b) ε)
      (Finmap.insert x (ValExpr.inferType v) Γv) (Ψ.extend x b v) := by
  have hf : x ∉ Γv := fun hm => ((hc.mem_iff x).mp hm).elim hx.freshLinear hx.freshNonlinear
  exact .extend_nlin hc hx (he.creation (hc.valueContextValid.some.insert hf hk) hv)
    hb ⟨hk⟩ ⟨hv⟩

/-- Introduce a linear source name; its basis must have a space type. -/
theorem contextLinear (hc : Operational.TypedContext Δ ε Γv Ψ)
    (hx : V2.SourceEntryValid Δ ε x) (hb : BasisValid ε b)
    (hs : Basis.tof b = .space s) (he : Entry Ψ x b v)
    (hk : RuntimeValue.ValTValid Γv (ValExpr.inferType v) k)
    (hv : RuntimeValue.ValHasType (Finmap.insert x (ValExpr.inferType v) Γv)
      v (ValExpr.inferType v)) :
    Operational.TypedContext (Finmap.insert x s Δ) ε
      (Finmap.insert x (ValExpr.inferType v) Γv) (Ψ.extend x b v) := by
  have hf : x ∉ Γv := fun hm => ((hc.mem_iff x).mp hm).elim hx.freshLinear hx.freshNonlinear
  exact .extend_lin hc hx (he.creation (hc.valueContextValid.some.insert hf hk) hv)
    hb hs ⟨hk⟩ ⟨hv⟩

theorem contextRepresentation (hc : Operational.TypedContext Δ ε Γv Ψ)
    (hx : V2.SourceEntryLinked Δ ε x b) (hkey : (x,b) ∉ Ψ)
    (hb : BasisValid ε b) (he : Entry Ψ x b v)
    (hv : RuntimeValue.ValHasType Γv v (ValExpr.inferType v)) :
    Operational.TypedContext Δ ε Γv (Ψ.extend x b v) :=
  .extend_rep hc hx hkey (he.creation hc.valueContextValid.some hv) hb ⟨hv⟩

private theorem sourceShapeNonlinear {σ : DEnv} {a : DVal}
    (hb : BasisValid ε b) (hx : x ∉ ε)
    (hσ : EnvWF (σ.bind x a) Δ (Finmap.insert x (Basis.tof b) ε)) :
    a.matchesShape (denotTy σ (Basis.tof b)) := by
  obtain ⟨a', ha', hshape⟩ := hσ.nl_match x (Basis.tof b) (by simp)
  have haa : a = a' := by simpa [DEnv.bind] using ha'
  subst a'
  have hf : x ∉ Ty.fv (Basis.tof b) := fun hm => hx (Finmap.mem_keys.mp
    (hb.fv_subset_keys_for_progress ((Basis.fv_tof_subset _) hm)))
  rwa [denotTy_agree _ (DEnv.AgreeOn.bind_left_of_not_mem hf)] at hshape

private theorem sourceShapeLinear {σ : DEnv} {a : DVal}
    (hb : BasisValid ε b) (hx : x ∉ ε)
    (hs : Basis.tof b = .space s)
    (hσ : EnvWF (σ.bind x a) (Finmap.insert x s Δ) ε) :
    a.matchesShape (denotTy σ (Basis.tof b)) := by
  obtain ⟨a', ha', hshape⟩ := hσ.lin_match x s (by simp)
  have haa : a = a' := by simpa [DEnv.bind] using ha'
  subst a'
  have hf : x ∉ Ty.fv (Basis.tof b) := fun hm => hx (Finmap.mem_keys.mp
    (hb.fv_subset_keys_for_progress ((Basis.fv_tof_subset _) hm)))
  have ht : a.matchesShape (denotTy (σ.bind x a) (Basis.tof b)) := by
    simpa only [hs, denotTy_space] using hshape
  rwa [denotTy_agree _ (DEnv.AgreeOn.bind_left_of_not_mem hf)] at ht

private theorem sourceShapeRepresentation (hσ : EnvWF σ Δ ε)
    (hx : V2.SourceEntryLinked Δ ε x b) (ha : σ.vars.lookup x = some a) :
    a.matchesShape (denotTy σ (Basis.tof b)) := by
  rcases hx with ⟨s, hx, hs⟩ | hx
  · obtain ⟨a', ha', hshape⟩ := hσ.lin_match x s hx
    have haa : a = a' := Option.some.inj (ha.symm.trans ha')
    subst a'
    simpa only [hs, denotTy_space] using hshape
  · obtain ⟨a', ha', hshape⟩ := hσ.nl_match x (Basis.tof b) hx
    have haa : a = a' := Option.some.inj (ha.symm.trans ha')
    exact haa ▸ hshape

theorem consistentNonlinear
    (hc : PartialAdequacy.Consistent orc Δ ε Ψ Γv σ ρ)
    (hx : V2.SourceEntryValid Δ ε x) (hb : BasisValid ε b)
    (he : Entry Ψ x b v)
    (hk : RuntimeValue.ValTValid Γv (ValExpr.inferType v) k)
    (hv : RuntimeValue.ValHasType (Finmap.insert x (ValExpr.inferType v) Γv)
      v (ValExpr.inferType v))
    (hσ : EnvWF (σ.bind x a) Δ (Finmap.insert x (Basis.tof b) ε))
    (hρ : RuntimeValue.PartialEnvWF orc (Finmap.insert x (ValExpr.inferType v) Γv)
      (ρ.update x w))
    (hnr : x ∉ ValExpr.fv v ∨ v = .var x (ValExpr.inferType v))
    (hden : denotValB_partial orc ρ [] [] v = .ok w)
    (hagree : PartialAdequacy.Agree orc σ ρ [] [] [] (Basis.tof b)
      (ValExpr.inferType v) (denotBasis σ b) a w)
    (hdims : PartialAdequacy.DimsAt orc σ ρ [] [] [] (Basis.tof b)
      (ValExpr.inferType v) (denotBasis σ b)) :
    PartialAdequacy.Consistent orc Δ (Finmap.insert x (Basis.tof b) ε)
      (Ψ.extend x b v) (Finmap.insert x (ValExpr.inferType v) Γv)
      (σ.bind x a) (ρ.update x w) := by
  have hf : x ∉ Γv := fun hm => ((hc.context.mem_iff x).mp hm).elim hx.freshLinear hx.freshNonlinear
  have hentry := he.creation (hc.context.valueContextValid.some.insert hf hk) hv
  refine ⟨?_, contextNonlinear hc.context hx hb he hk hv, hρ⟩
  exact .extend_nl hc.history ⟨hx.freshLinear, hx.freshNonlinear⟩ hb
    he.typeRealized rfl (inferSpaceMatchesBase hv) hentry.valid.valueScoped
    hentry.valid.locallyClosed (hnr.imp_right (fun h => ⟨_,h⟩))
    (sourceShapeNonlinear hb hx.freshNonlinear hσ) hden hagree hdims hentry

theorem consistentLinear
    (hc : PartialAdequacy.Consistent orc Δ ε Ψ Γv σ ρ)
    (hx : V2.SourceEntryValid Δ ε x) (hb : BasisValid ε b)
    (hs : Basis.tof b = .space s) (he : Entry Ψ x b v)
    (hk : RuntimeValue.ValTValid Γv (ValExpr.inferType v) k)
    (hv : RuntimeValue.ValHasType (Finmap.insert x (ValExpr.inferType v) Γv)
      v (ValExpr.inferType v))
    (hσ : EnvWF (σ.bind x a) (Finmap.insert x s Δ) ε)
    (hρ : RuntimeValue.PartialEnvWF orc (Finmap.insert x (ValExpr.inferType v) Γv)
      (ρ.update x w))
    (hnr : x ∉ ValExpr.fv v ∨ v = .var x (ValExpr.inferType v))
    (hden : denotValB_partial orc ρ [] [] v = .ok w)
    (hagree : PartialAdequacy.Agree orc σ ρ [] [] [] (Basis.tof b)
      (ValExpr.inferType v) (denotBasis σ b) a w)
    (hdims : PartialAdequacy.DimsAt orc σ ρ [] [] [] (Basis.tof b)
      (ValExpr.inferType v) (denotBasis σ b)) :
    PartialAdequacy.Consistent orc (Finmap.insert x s Δ) ε
      (Ψ.extend x b v) (Finmap.insert x (ValExpr.inferType v) Γv)
      (σ.bind x a) (ρ.update x w) := by
  have hf : x ∉ Γv := fun hm => ((hc.context.mem_iff x).mp hm).elim hx.freshLinear hx.freshNonlinear
  have hentry := he.creation (hc.context.valueContextValid.some.insert hf hk) hv
  refine ⟨?_, contextLinear hc.context hx hb hs he hk hv, hρ⟩
  exact .extend_lin hc.history ⟨hx.freshLinear, hx.freshNonlinear⟩ hs hb
    he.typeRealized rfl (inferSpaceMatchesBase hv) hentry.valid.valueScoped
    hentry.valid.locallyClosed (hnr.imp_right (fun h => ⟨_,h⟩))
    (sourceShapeLinear hb hx.freshNonlinear hs hσ) hden hagree hdims

/-- A second representation can have its own inferred type and denoted value.
Only the evaluator map changes; the source and canonical value bindings stay fixed. -/
theorem consistentRepresentation
    (hc : PartialAdequacy.Consistent orc Δ ε Ψ Γv σ ρ)
    (hσ : EnvWF σ Δ ε)
    (hx : V2.SourceEntryLinked Δ ε x b) (hkey : (x,b) ∉ Ψ)
    (ha : σ.vars.lookup x = some a) (hb : BasisValid ε b)
    (he : Entry Ψ x b v)
    (hv : RuntimeValue.ValHasType Γv v (ValExpr.inferType v))
    (hden : denotValB_partial orc ρ [] [] v = .ok w)
    (hagree : PartialAdequacy.Agree orc σ ρ [] [] [] (Basis.tof b)
      (ValExpr.inferType v) (denotBasis σ b) a w)
    (hdims : PartialAdequacy.DimsAt orc σ ρ [] [] [] (Basis.tof b)
      (ValExpr.inferType v) (denotBasis σ b)) :
    PartialAdequacy.Consistent orc Δ ε (Ψ.extend x b v) Γv σ ρ := by
  have hentry := he.creation hc.context.valueContextValid.some hv
  refine ⟨?_, contextRepresentation hc.context hx hkey hb he hv, hc.valueEnv⟩
  exact .extend_rep hc.history hkey hx ha hb he.typeRealized rfl
    (inferSpaceMatchesBase hv) hentry.valid.valueScoped hentry.valid.locallyClosed
    (sourceShapeRepresentation hσ hx ha) hden hagree hdims hentry

end GLang.PaperContextResults
