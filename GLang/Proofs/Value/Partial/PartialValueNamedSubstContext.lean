import GLang.Proofs.Value.Binding.ValueSubstitutionValidity
import GLang.Proofs.Value.Partial.PartialValueRawPresentation
import GLang.Proofs.Value.Partial.PartialValueSubstitutionSpaces
import GLang.Proofs.Value.Presentation.PaperValueTypedSubstitution
import GLang.Proofs.Value.Presentation.PaperValueLocalClosure

namespace GLang.PartialValueSubstitution
open PaperValueDomains

structure NamedSubstCtx (x : VName) (u : ValExpr) (ε : ValCtx) (τx : ValTy)
    (ρ : ValEnvSem) (v : ValValSem) where
  sd : ValSubstData x u ε τx
  argEval : denotValB_partial PartialDirectOracle.oracle ρ [] [] u = .ok v
  lc : ContextLocallyClosed ε
  valid : Nonempty (ValCtxValid ε)
  declarations : ∀ y τ, ε.lookup y = some τ →
    RawPresentation PartialDirectOracle.oracle τ (ValTy.subst x u τ)
      ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩
  baseDeclarations : ∀ y s, ε.lookup y = some (.space s) →
    SpaceAgreement (PartialDirectOracle.oracle (ρ.update x v) [] [])
      (PartialDirectOracle.oracle ρ [] []) x u s

private theorem update_comm (ρ : ValEnvSem) (x y : VName) (v z : ValValSem)
    (hyx : y ≠ x) : (ρ.update x v).update y z = (ρ.update y z).update x v := by
  funext a
  by_cases hx : a = x <;> by_cases hy : a = y <;> simp_all [ValEnvSem.update]

private theorem subst_fresh {x y : VName} {u : ValExpr} {τ : ValTy}
    (ht : y ∉ ValTy.fv τ) (hu : y ∉ ValExpr.fv u) :
    y ∉ ValTy.fv (ValTy.subst x u τ) := by
  intro hm
  rcases Finset.mem_union.mp (ValTy.fv_subst_mem hm) with hm | hm
  · exact ht hm
  · exact hu hm

private theorem declaration_update {x y : VName} {u : ValExpr} {τ : ValTy}
    {ρ : ValEnvSem} {v z : ValValSem} (hyx : y ≠ x)
    (ht : y ∉ ValTy.fv τ) (hu : y ∉ ValExpr.fv u)
    (h : RawPresentation PartialDirectOracle.oracle τ (ValTy.subst x u τ)
      ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩) :
    RawPresentation PartialDirectOracle.oracle τ (ValTy.subst x u τ)
      ⟨(ρ.update y z).update x v,[],[]⟩ ⟨ρ.update y z,[],[]⟩ := by
  have hl := RawPresentation.fresh PartialDirectFv.oracle_fresh τ
    (⟨ρ.update x v,[],[]⟩ : World) y z (by simp [ValTyCtxFresh]) ht
  have hr := RawPresentation.fresh PartialDirectFv.oracle_fresh (ValTy.subst x u τ)
    (⟨ρ,[],[]⟩ : World) y z (by simp [ValTyCtxFresh]) (subst_fresh ht hu)
  have hh := RawPresentation.trans PartialDirectOracle.oracle τ τ (ValTy.subst x u τ) _ _ _
    (RawPresentation.symm PartialDirectOracle.oracle τ τ _ _ hl) h
  have hh' := RawPresentation.trans PartialDirectOracle.oracle τ (ValTy.subst x u τ)
    (ValTy.subst x u τ) _ _ _ hh hr
  simpa only [World.update,update_comm ρ x y v z hyx] using hh'

private theorem base_update {x y : VName} {u : ValExpr} {s : ValSpace}
    {ρ : ValEnvSem} {v z : ValValSem} (hyx : y ≠ x)
    (ht : y ∉ ValSpace.fv s) (hu : y ∉ ValExpr.fv u)
    (h : SpaceAgreement (PartialDirectOracle.oracle (ρ.update x v) [] [])
      (PartialDirectOracle.oracle ρ [] []) x u s) :
    SpaceAgreement (PartialDirectOracle.oracle ((ρ.update y z).update x v) [] [])
      (PartialDirectOracle.oracle (ρ.update y z) [] []) x u s := by
  have hl := LeafAgreement.fresh PartialDirectFv.oracle_fresh
    (⟨ρ.update x v,[],[]⟩ : World) y z (by simp [ValTyCtxFresh]) s ht
  have hr := LeafAgreement.fresh PartialDirectFv.oracle_fresh
    (⟨ρ,[],[]⟩ : World) y z (by simp [ValTyCtxFresh]) (ValSpace.subst x u s)
    (by
      intro hm
      rcases Finset.mem_union.mp (ValSpace.fv_subst_mem hm) with hm | hm
      · exact ht hm
      · exact hu hm)
  simpa only [World.update,update_comm ρ x y v z hyx] using h.transport hl hr

noncomputable def NamedSubstCtx.extend {x : VName} {u : ValExpr} {ε : ValCtx}
    {τx : ValTy} {ρ : ValEnvSem} {v : ValValSem}
    (h : NamedSubstCtx x u ε τx ρ v) (y : VName) (d : ValTy) (z : ValValSem)
    (hdvalid : ValTValid ε d k)
    (hyx : y ≠ x) (hyε : y ∉ ε) (hys : y ∉ ε.fvSupport)
    (hyu : y ∉ ValExpr.fv u) (hyd : y ∉ ValTy.fv d) (hdlc : ValTy.lc d)
    (hd : RawPresentation PartialDirectOracle.oracle d (ValTy.subst x u d)
      ⟨ρ.update x v,[],[]⟩ ⟨ρ,[],[]⟩)
    (hdb : ∀ s, d = .space s → SpaceAgreement
      (PartialDirectOracle.oracle (ρ.update x v) [] []) (PartialDirectOracle.oracle ρ [] []) x u s) :
    NamedSubstCtx x u (Finmap.insert y d ε) τx (ρ.update y z) v where
  sd := h.sd.extend d hyx hyε
  argEval := (PartialDirectFv.eval_eq PartialDirectFv.oracle_fresh
    ρ y z u [] [] hyu (by simp)).trans h.argEval
  lc := h.lc.insert y d hdlc
  valid := ⟨h.valid.some.insert hyε hdvalid⟩
  declarations := by
    intro a τ ha
    by_cases hay : a = y
    · subst a
      simp only [Finmap.lookup_insert,Option.some.injEq] at ha
      subst τ
      exact declaration_update hyx hyd hyu hd
    · rw [Finmap.lookup_insert_of_ne _ hay] at ha
      exact declaration_update hyx (ValCtx.not_mem_fv_of_not_mem_support hys ha) hyu
        (h.declarations a τ ha)
  baseDeclarations := by
    intro a s ha
    by_cases hay : a = y
    · subst a
      simp only [Finmap.lookup_insert,Option.some.injEq] at ha
      subst d
      exact base_update hyx hyd hyu (hdb s rfl)
    · rw [Finmap.lookup_insert_of_ne _ hay] at ha
      exact base_update hyx (ValCtx.not_mem_fv_of_not_mem_support hys ha) hyu
        (h.baseDeclarations a s ha)

theorem SpaceAgreement.of_fresh {q q' : PartialFFSOracle} {x : VName} {u : ValExpr}
    {s : ValSpace} (h : LeafAgreement q q' s) (hx : x ∉ ValSpace.fv s) :
    SpaceAgreement q q' x u s := by
  cases s with
  | empty | real => trivial
  | dsum s t | tprod s t =>
      simp only [ValSpace.fv,Finset.mem_union,not_or] at hx
      exact ⟨SpaceAgreement.of_fresh h.1 hx.1,SpaceAgreement.of_fresh h.2 hx.2⟩
  | ffs p s e =>
      simp only [ValSpace.fv,Finset.mem_union,not_or] at hx
      simpa only [SpaceAgreement,ValSpace.subst_fresh x u s hx.1,
        ValExpr.subst_fresh x u e hx.2] using h
termination_by sizeOf s

/-- A fresh typed substitution starts in the original context without assuming
any evaluator or oracle substitution theorem. -/
noncomputable def NamedSubstCtx.of_fresh {x : VName} {u : ValExpr} {ε : ValCtx}
    {d : ValTy} {ρ : ValEnvSem} {v : ValValSem}
    (hu : ValHasType ε u d) (hulc : ValExpr.lc u) (hc : ContextLocallyClosed ε)
    (hv : ValCtxValid ε) (hdvalid : ValTValid ε d k)
    (hdlc : ValTy.lc d) (hx : x ∉ ε) (hxs : x ∉ ε.fvSupport)
    (hxd : x ∉ ValTy.fv d)
    (he : denotValB_partial PartialDirectOracle.oracle ρ [] [] u = .ok v) :
    NamedSubstCtx x u (Finmap.insert x d ε) d ρ v where
  sd := ValSubstData.of_fresh hu hulc hx hxd
    (fun _ _ ht => ValCtx.not_mem_fv_of_not_mem_support hxs ht)
  argEval := he
  lc := hc.insert x d hdlc
  valid := ⟨hv.insert hx hdvalid⟩
  declarations := by
    intro y τ hy
    have hf : x ∉ ValTy.fv τ := by
      by_cases hyx : y = x
      · subst y
        simp only [Finmap.lookup_insert,Option.some.injEq] at hy
        simpa only [← hy] using hxd
      · rw [Finmap.lookup_insert_of_ne _ hyx] at hy
        exact ValCtx.not_mem_fv_of_not_mem_support hxs hy
    rw [ValTy.subst_fresh x u τ hf]
    exact RawPresentation.symm PartialDirectOracle.oracle τ τ _ _
      (RawPresentation.fresh PartialDirectFv.oracle_fresh τ
        ⟨ρ,[],[]⟩ x v (by simp [ValTyCtxFresh]) hf)
  baseDeclarations := by
    intro y s hy
    have hf : x ∉ ValSpace.fv s := by
      by_cases hyx : y = x
      · subst y
        simp only [Finmap.lookup_insert,Option.some.injEq] at hy
        simpa only [hy,ValTy.fv] using hxd
      · rw [Finmap.lookup_insert_of_ne _ hyx] at hy
        exact ValCtx.not_mem_fv_of_not_mem_support hxs hy
    exact SpaceAgreement.of_fresh
      (LeafAgreement.symm _ _ s
        (LeafAgreement.fresh PartialDirectFv.oracle_fresh
          ⟨ρ,[],[]⟩ x v (by simp [ValTyCtxFresh]) s hf)) hf

end GLang.PartialValueSubstitution
