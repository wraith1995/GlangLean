import GLang.Proofs.Value.Partial.PartialValueTypeCoherence
import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectAssembly

/-! Fresh-variable and open/push transport for the formation-coherence motive
of the partial value-language fundamental theorem. -/
namespace GLang.PartialValueDomains
open PaperValueDomains PartialDirectOpenPush

private theorem space_fresh {orc : PartialFFSOracleSem} (hf : PartialDirectFv.OracleFresh orc)
    (s : ValSpace) (w w' : PaperValueDomains.World) (x : VName) (v v' : ValValSem)
    (hΓ : ValTyCtxFresh x w.types) (hΓ' : ValTyCtxFresh x w'.types) (hx : x ∉ s.fv)
    (h : PartialSpaceAgreement (orc w.env w.types w.values) (orc w'.env w'.types w'.values) s) :
    PartialSpaceAgreement (orc (w.env.update x v) w.types w.values)
      (orc (w'.env.update x v') w'.types w'.values) s := by
  cases s with
  | empty | real => trivial
  | dsum s t | tprod s t =>
    simp only [ValSpace.fv,Finset.mem_union,not_or] at hx
    exact ⟨space_fresh hf s w w' x v v' hΓ hΓ' hx.1 h.1,
      space_fresh hf t w w' x v v' hΓ hΓ' hx.2 h.2⟩
  | ffs p s e =>
    simp only [ValSpace.fv,Finset.mem_union,not_or] at hx
    simp only [PartialSpaceAgreement,hf _ _ _ _ _ _ _ _ hΓ hx.1 hx.2,
      hf _ _ _ _ _ _ _ _ hΓ' hx.1 hx.2]
    exact h
termination_by sizeOf s

/-- Updating an unused named binding preserves raw formation coherence. -/
theorem PartialRawTypeCoherent.fresh {orc : PartialFFSOracleSem}
    (hf : PartialDirectFv.OracleFresh orc) (t : ValTy)
    (w w' : PaperValueDomains.World) (x : VName) (v v' : ValValSem)
    (hΓ : ValTyCtxFresh x w.types) (hΓ' : ValTyCtxFresh x w'.types) (hx : x ∉ t.fv)
    (h : PartialRawTypeCoherent orc t w w') :
    PartialRawTypeCoherent orc t ⟨w.env.update x v,w.types,w.values⟩
      ⟨w'.env.update x v',w'.types,w'.values⟩ := by
  cases t with
  | space s => exact space_fresh hf s w w' x v v' hΓ hΓ' hx h
  | piTy d c =>
    simp only [ValTy.fv,Finset.mem_union,not_or] at hx
    refine ⟨h.1.fresh hf d w w' x v v' hΓ hΓ' hx.1,?_⟩
    intro a b hab
    have hab0 : PartialRuntimeRelated d (PartialWorldType orc w d)
        (PartialWorldType orc w' d) a b := by
      simpa only [PartialWorldType,PartialDirectFv.type_eq hf _ _ _ _ _ _ hΓ hx.1,
        PartialDirectFv.type_eq hf _ _ _ _ _ _ hΓ' hx.1] using hab
    exact (h.2 a b hab0).fresh hf c _ _ x v v' (hΓ.cons hx.1) (hΓ'.cons hx.1) hx.2
termination_by sizeOf t

private theorem space_openPush (s : ValSpace) (W W' : World PartialDirectOracle.oracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u)
    (hy : W.y ∉ s.fv) (hy' : W'.y ∉ s.fv)
    (h : PartialSpaceAgreement
      (PartialDirectOracle.oracle W.namedRho W.namedG W.namedD)
      (PartialDirectOracle.oracle W'.namedRho W'.namedG W'.namedD)
      (ValSpace.openRec W.G.length W.u s)) :
    PartialSpaceAgreement
      (PartialDirectOracle.oracle W.pushedRho W.pushedG W.pushedD)
      (PartialDirectOracle.oracle W'.pushedRho W'.pushedG W'.pushedD) s := by
  cases s with
  | empty | real => trivial
  | dsum s t | tprod s t =>
    simp only [ValSpace.fv,Finset.mem_union,not_or] at hy hy'
    exact ⟨space_openPush s W W' hG hu hy.1 hy'.1 h.1,
      space_openPush t W W' hG hu hy.2 hy'.2 h.2⟩
  | ffs p s e =>
    simp only [ValSpace.fv,Finset.mem_union,not_or] at hy hy'
    change PartialDirectOracle.oracle W.namedRho W.namedG W.namedD p
      (ValSpace.openRec W.G.length W.u s) (ValExpr.openRec W.G.length W.u e) =
      PartialDirectOracle.oracle W'.namedRho W'.namedG W'.namedD p
      (ValSpace.openRec W.G.length W.u s) (ValExpr.openRec W.G.length W.u e) at h
    have hleft := oracle_openPush (rho := W.rho) (w := W.w) (p := p) W.length_eq W.sigma_lc W.y_sigma W.y_G hy.1 hy.2
    have hright := oracle_openPush (rho := W'.rho) (w := W'.w) (p := p) W'.length_eq W'.sigma_lc W'.y_sigma W'.y_G hy'.1 hy'.2
    change PartialDirectOracle.oracle W.pushedRho W.pushedG W.pushedD p s e =
      PartialDirectOracle.oracle W'.pushedRho W'.pushedG W'.pushedD p s e
    change PartialDirectOracle.oracle W.namedRho W.namedG W.namedD p
      (ValSpace.openRec W.G.length W.u s) (ValExpr.openRec W.G.length W.u e) = _ at hleft
    change PartialDirectOracle.oracle W'.namedRho W'.namedG W'.namedD p
      (ValSpace.openRec W'.G.length W'.u s) (ValExpr.openRec W'.G.length W'.u e) = _ at hright
    have hright' : PartialDirectOracle.oracle W'.namedRho W'.namedG W'.namedD p
        (ValSpace.openRec W.G.length W.u s) (ValExpr.openRec W.G.length W.u e) =
        PartialDirectOracle.oracle W'.pushedRho W'.pushedG W'.pushedD p s e := by
      simpa only [hG,hu] using hright
    exact hleft.symm.trans (h.trans hright')
termination_by sizeOf s

/-- Binder opening preserves the stronger raw-fibre type coherence, including
failed dimensions and arbitrary function-valued raw arguments. -/
theorem PartialRawTypeCoherent.openPush (t : ValTy) (W W' : World PartialDirectOracle.oracle)
    (hG : W.G = W'.G) (hu : W.u = W'.u)
    (hy : W.y ∉ t.fv) (hy' : W'.y ∉ t.fv)
    (h : PartialRawTypeCoherent PartialDirectOracle.oracle (ValTy.openRec W.G.length W.u t)
      ⟨W.namedRho,W.namedG,W.namedD⟩ ⟨W'.namedRho,W'.namedG,W'.namedD⟩) :
    PartialRawTypeCoherent PartialDirectOracle.oracle t
      ⟨W.pushedRho,W.pushedG,W.pushedD⟩ ⟨W'.pushedRho,W'.pushedG,W'.pushedD⟩ := by
  cases t with
  | space s => exact space_openPush s W W' hG hu hy hy' h
  | piTy d c =>
    simp only [ValTy.fv,Finset.mem_union,not_or] at hy hy'
    refine ⟨h.1.openPush d W W' hG hu hy.1 hy'.1,?_⟩
    intro v v' hv
    have ht := type_heq oracle_openPush d W hy.1
    have ht' := type_heq oracle_openPush d W' hy'.1
    rw [← hG,← hu] at ht'
    have hn := (partialRuntimeRelated_heq
      (ValSoundOfDenot.ValTy.SameShape_openRec W.G.length W.u d) _ _ _ _ ht ht' v v').2 hv
    let E := W.extend d v hy.1
    let E' := W'.extend d v' hy'.1
    have he : E.namedG = ValTy.openRec W.G.length W.u d :: W.namedG := by simp [E]
    have he' : E'.namedG = ValTy.openRec W.G.length W.u d :: W'.namedG := by
      simp only [E',World.extend_namedG,← hG,← hu]
    have hh : PartialRawTypeCoherent PartialDirectOracle.oracle
        (ValTy.openRec E.G.length E.u c)
        ⟨E.namedRho,E.namedG,E.namedD⟩ ⟨E'.namedRho,E'.namedG,E'.namedD⟩ := by
      rw [show E.G.length = W.G.length + 1 by simp [E,World.extend],
        show E.u = W.u from rfl, he, he']
      exact h.2 v v' hn
    have ho := hh.openPush c E E'
      (by simp only [E,E',World.extend,hG]) (by simpa only [E,E',World.extend_u] using hu)
      hy.2 hy'.2
    simpa only [E,E',World.extend_pushedG,World.extend_pushedD,World.pushedRho,World.extend]
      using ho
termination_by sizeOf t

end GLang.PartialValueDomains
