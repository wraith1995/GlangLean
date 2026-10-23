import GLang.Graded.StrengtheningCtx

/-!
# Graded coordinate erasure

Mutual strengthening for the promote-free graded judgments.  Formation and
subtyping erase a fresh coordinate from their type view; term typing erases it
from the resource context.  `GHasType.result_fresh` supplies hidden intermediate
type freshness in dependent application.
-/

namespace GLang.Graded

open GLang

mutual

noncomputable def gsvalid_eraseName : {f : Name → Option Ty} → {s : Space} →
    GSValid f s → ∀ {x : Name}, TypeViewFreshAt f x → x ∉ Space.fv s →
      GSValid (Function.update f x none) s
  | _, _, .empty, _, _, _ => .empty
  | _, _, .real, _, _, _ => .real
  | _, _, .dual hs, x, hf, hx => by
      simp only [Space.fv] at hx
      exact .dual (gsvalid_eraseName hs hf hx)
  | _, _, .dsum hs₀ hs₁, x, hf, hx => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx
      exact .dsum (gsvalid_eraseName hs₀ hf hx.1) (gsvalid_eraseName hs₁ hf hx.2)
  | _, _, .tprod hs₀ hs₁, x, hf, hx => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx
      exact .tprod (gsvalid_eraseName hs₀ hf hx.1) (gsvalid_eraseName hs₁ hf hx.2)
  | _, _, .ker hs₀ hs₁ he, x, hf, hx => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx
      refine .ker (gsvalid_eraseName hs₀ hf hx.1.1)
        (gsvalid_eraseName hs₁ hf hx.1.2) ?_
      rw [resurrect_erase]
      exact ghastype_eraseName he hf.resurrect hx.2
        (by simpa [Ty.fv, Space.fv] using ⟨hx.1.1, hx.1.2⟩)
  | _, _, .coker hs₀ hs₁ he, x, hf, hx => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx
      refine .coker (gsvalid_eraseName hs₀ hf hx.1.1)
        (gsvalid_eraseName hs₁ hf hx.1.2) ?_
      rw [resurrect_erase]
      exact ghastype_eraseName he hf.resurrect hx.2
        (by simpa [Ty.fv, Space.fv] using ⟨hx.1.1, hx.1.2⟩)
  | _, _, .img hs₀ hs₁ he, x, hf, hx => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx
      refine .img (gsvalid_eraseName hs₀ hf hx.1.1)
        (gsvalid_eraseName hs₁ hf hx.1.2) ?_
      rw [resurrect_erase]
      exact ghastype_eraseName he hf.resurrect hx.2
        (by simpa [Ty.fv, Space.fv] using ⟨hx.1.1, hx.1.2⟩)
  | _, _, .coimg hs₀ hs₁ he, x, hf, hx => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx
      refine .coimg (gsvalid_eraseName hs₀ hf hx.1.1)
        (gsvalid_eraseName hs₁ hf hx.1.2) ?_
      rw [resurrect_erase]
      exact ghastype_eraseName he hf.resurrect hx.2
        (by simpa [Ty.fv, Space.fv] using ⟨hx.1.1, hx.1.2⟩)

noncomputable def gtvalid_eraseName : {f : Name → Option Ty} → {τ : Ty} → {k : Kind} →
    GTValid f τ k → ∀ {x : Name}, TypeViewFreshAt f x → x ∉ Ty.fv τ →
      GTValid (Function.update f x none) τ k
  | _, _, _, .space hs, _, hf, hx => by
      simp only [Ty.fv] at hx
      exact .space (gsvalid_eraseName hs hf hx)
  | _, _, _, .piTy L hdom hbody, x, hf, hx => by
      rename_i f τdom τcod kdom kcod
      simp only [Ty.fv, Finset.mem_union, not_or] at hx
      refine .piTy (L ∪ {x}) (gtvalid_eraseName hdom hf hx.1) ?_
      intro y hy
      have hyL : y ∉ L := fun hm => hy (Finset.mem_union_left _ hm)
      have hyx : y ≠ x := by
        intro h; subst y
        exact hy (Finset.mem_union_right _ (Finset.mem_singleton_self x))
      have hopen : x ∉ Ty.fv (Ty.openVar y τcod) := by
        intro hm
        have hm' := Ty.fv_openRec_subset 0 (.var y) τcod hm
        rcases Finset.mem_union.mp hm' with hm' | hm'
        · exact hx.2 hm'
        · have hxy : x = y := by simpa [Term.fv] using hm'
          exact hyx hxy.symm
      have hb := gtvalid_eraseName (hbody y hyL) (hf.update hyx hx.1) hopen
      simpa only [Function.update_comm hyx] using hb

noncomputable def gsubtype_eraseName : {f : Name → Option Ty} → {s₀ s₁ : Space} →
    GSubType f s₀ s₁ → ∀ {x : Name}, TypeViewFreshAt f x →
      x ∉ Space.fv s₀ → x ∉ Space.fv s₁ →
      GSubType (Function.update f x none) s₀ s₁
  | _, _, _, .sub_ker hs₀ hs₁ he, x, hf, hx₀, hx₁ => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx₀
      refine .sub_ker (gsvalid_eraseName hs₀ hf hx₀.1.1)
        (gsvalid_eraseName hs₁ hf hx₀.1.2) ?_
      rw [resurrect_erase]
      exact ghastype_eraseName he hf.resurrect hx₀.2
        (by simpa [Ty.fv, Space.fv] using ⟨hx₀.1.1, hx₀.1.2⟩)
  | _, _, _, .sub_coker hs₀ hs₁ he, x, hf, hx₀, hx₁ => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx₀
      refine .sub_coker (gsvalid_eraseName hs₀ hf hx₀.1.1)
        (gsvalid_eraseName hs₁ hf hx₀.1.2) ?_
      rw [resurrect_erase]
      exact ghastype_eraseName he hf.resurrect hx₀.2
        (by simpa [Ty.fv, Space.fv] using ⟨hx₀.1.1, hx₀.1.2⟩)
  | _, _, _, .sub_img hs₀ hs₁ he, x, hf, hx₀, hx₁ => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx₀
      refine .sub_img (gsvalid_eraseName hs₀ hf hx₀.1.1)
        (gsvalid_eraseName hs₁ hf hx₀.1.2) ?_
      rw [resurrect_erase]
      exact ghastype_eraseName he hf.resurrect hx₀.2
        (by simpa [Ty.fv, Space.fv] using ⟨hx₀.1.1, hx₀.1.2⟩)
  | _, _, _, .sub_coimg hs₀ hs₁ he, x, hf, hx₀, hx₁ => by
      simp only [Space.fv, Finset.mem_union, not_or] at hx₀
      refine .sub_coimg (gsvalid_eraseName hs₀ hf hx₀.1.1)
        (gsvalid_eraseName hs₁ hf hx₀.1.2) ?_
      rw [resurrect_erase]
      exact ghastype_eraseName he hf.resurrect hx₀.2
        (by simpa [Ty.fv, Space.fv] using ⟨hx₀.1.1, hx₀.1.2⟩)

noncomputable def ghastype_eraseName : {Γ : GCtx} → {e : Term} → {τ : Ty} →
    GHasType Γ e τ → ∀ {x : Name}, TypeFreshAt Γ x →
      x ∉ Term.fv e → x ∉ Ty.fv τ → GHasType (eraseName Γ x) e τ
  | _, _, _, .gzero hs, x, hf, he, _ => by
      simp only [Term.fv] at he
      refine .gzero ?_
      rw [typeCtxOmega_eraseName]
      exact gsvalid_eraseName hs hf.typeCtxOmega he
  | _, _, _, .gsmul hs hsp hta h₀ h₁, x, hf, he, hτ => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      refine .gsmul ?_ (split_eraseName x hsp) (typeAgree_eraseName x hta)
        (ghastype_eraseName h₀ (hf.of_split_left hsp hta) he.1
          (by simp [Ty.fv, Space.fv]))
        (ghastype_eraseName h₁ (hf.of_split_right hsp hta) he.2 hτ)
      rw [typeCtxOmega_eraseName]
      exact gsvalid_eraseName hs hf.typeCtxOmega (by simpa [Ty.fv] using hτ)
  | _, _, _, .gadd hs h₀ h₁, x, hf, he, hτ => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      refine .gadd ?_ (ghastype_eraseName h₀ hf he.1 hτ)
        (ghastype_eraseName h₁ hf he.2 hτ)
      rw [typeCtxOmega_eraseName]
      exact gsvalid_eraseName hs hf.typeCtxOmega (by simpa [Ty.fv] using hτ)
  | _, _, _, .ginner hs hnl, x, hf, he, _ => by
      simp only [Term.fv] at he
      refine .ginner ?_ (hnl.eraseName x)
      rw [typeCtxOmega_eraseName]
      exact gsvalid_eraseName hs hf.typeCtxOmega he
  | _, _, _, .greal_lit r hnl, x, _, _, _ => .greal_lit r (hnl.eraseName x)
  | _, _, _, .gapp_linear hs₀ hs₁ hsp hta h₀ h₁, x, hf, he, hτ => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      refine .gapp_linear ?_ ?_ (split_eraseName x hsp) (typeAgree_eraseName x hta)
        (ghastype_eraseName h₀ (hf.of_split_left hsp hta) he.1.2
          (by simpa [Ty.fv, Space.fv] using ⟨he.1.1.1, hτ⟩))
        (ghastype_eraseName h₁ (hf.of_split_right hsp hta) he.2
          (by simpa [Ty.fv] using he.1.1.1))
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs₀ hf.typeCtxOmega he.1.1.1
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs₁ hf.typeCtxOmega (by simpa [Ty.fv] using hτ)
  | _, _, _, .gapp_inner hs hsp hta h₀ h₁, x, hf, he, _ => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      refine .gapp_inner ?_ (split_eraseName x hsp) (typeAgree_eraseName x hta)
        (ghastype_eraseName h₀ (hf.of_split_left hsp hta) he.1.2
          (by simpa [Ty.fv, Space.fv] using he.1.1))
        (ghastype_eraseName h₁ (hf.of_split_right hsp hta) he.2
          (by simpa [Ty.fv] using he.1.1))
      rw [typeCtxOmega_eraseName]
      exact gsvalid_eraseName hs hf.typeCtxOmega he.1.1
  | _, _, _, .gapp_nonlinear hnl h₀ h₁, x, hf, he, hτ => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      have hfpi := GHasType.result_fresh h₀ hf he.1
      simp only [Ty.fv, Finset.mem_union, not_or] at hfpi
      have hfarg := GHasType.result_fresh h₁ hf he.2
      exact .gapp_nonlinear (hnl.eraseName x)
        (ghastype_eraseName h₀ hf he.1 (by simpa [Ty.fv] using hfpi))
        (ghastype_eraseName h₁ hf he.2 hfarg)
  | _, _, _, @GHasType.gvar Γ z g τ hz hg hlin, x, hf, he, _ => by
      have hzx : z ≠ x := by
        intro h; subst z
        exact he (by simp [Term.fv])
      exact .gvar (by rw [eraseName_of_ne Γ hzx]; exact hz) hg (by
        intro y hy τy hlookup
        rcases eq_or_ne y x with rfl | hyx
        · rw [eraseName_self] at hlookup; simp at hlookup
        · rw [eraseName_of_ne Γ hyx] at hlookup
          exact hlin y hy τy hlookup)
  | _, _, _, .gpinv_tensor hs₀ hs₁ hnl he', x, hf, he, _ => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      refine .gpinv_tensor ?_ ?_ (hnl.eraseName x)
        (ghastype_eraseName he' hf he.2
          (by simpa [Ty.fv, Space.fv] using ⟨he.1.1, he.1.2⟩))
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs₀ hf.typeCtxOmega he.1.1
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs₁ hf.typeCtxOmega he.1.2
  | _, _, _, .gpinv_dual hs hnl he', x, hf, he, _ => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      refine .gpinv_dual ?_ (hnl.eraseName x)
        (ghastype_eraseName he' hf he.2 (by simpa [Ty.fv, Space.fv] using he.1))
      rw [typeCtxOmega_eraseName]
      exact gsvalid_eraseName hs hf.typeCtxOmega he.1
  | _, _, _, .gdsumE hs₀ hs₁ h₀ h₁, x, hf, he, hτ => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      simp only [Ty.fv, Space.fv, Finset.mem_union, not_or] at hτ
      refine .gdsumE ?_ ?_ (ghastype_eraseName h₀ hf he.1 (by simpa [Ty.fv] using hτ.1))
        (ghastype_eraseName h₁ hf he.2 (by simpa [Ty.fv] using hτ.2))
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs₀ hf.typeCtxOmega hτ.1
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs₁ hf.typeCtxOmega hτ.2
  | _, _, _, .gtprodE hs₀ hs₁ hsp hta h₀ h₁, x, hf, he, hτ => by
      simp only [Term.fv, Finset.mem_union, not_or] at he
      simp only [Ty.fv, Space.fv, Finset.mem_union, not_or] at hτ
      refine .gtprodE ?_ ?_ (split_eraseName x hsp) (typeAgree_eraseName x hta)
        (ghastype_eraseName h₀ (hf.of_split_left hsp hta) he.1 (by simpa [Ty.fv] using hτ.1))
        (ghastype_eraseName h₁ (hf.of_split_right hsp hta) he.2 (by simpa [Ty.fv] using hτ.2))
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs₀ hf.typeCtxOmega hτ.1
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs₁ hf.typeCtxOmega hτ.2
  | _, _, _, .gllam_real L hs hbody, x, hf, he, _ => by
      rename_i Γ s body
      simp only [Term.fv, Finset.mem_union, not_or] at he
      refine .gllam_real (L ∪ {x}) ?_ ?_
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs hf.typeCtxOmega he.1.1
      · intro y hy
        have hyL : y ∉ L := fun hm => hy (Finset.mem_union_left _ hm)
        have hyx : y ≠ x := by
          intro h; subst y
          exact hy (Finset.mem_union_right _ (Finset.mem_singleton_self x))
        have hopen : x ∉ Term.fv (Term.openVar y s) := by
          intro hm
          have hm' := Term.fv_openRec_subset 0 (.var y) s hm
          rcases Finset.mem_union.mp hm' with hm' | hm'
          · exact he.2 hm'
          · have hxy : x = y := by simpa [Term.fv] using hm'
            exact hyx hxy.symm
        have hb := ghastype_eraseName (hbody y hyL)
          (hf.update (g := .one) hyx (by simpa [Ty.fv] using he.1.1)) hopen
          (by simp [Ty.fv, Space.fv])
        simpa only [eraseName_update_comm _ _ (Ne.symm hyx)] using hb
  | _, _, _, .gllam_tensor L hne hs₀ hs hbody, x, hf, he, hτ => by
      rename_i Γ sdom scod body
      simp only [Term.fv, Finset.mem_union, not_or] at he
      change x ∉ Space.fv sdom ∪ Space.fv scod at hτ
      simp only [Finset.mem_union, not_or] at hτ
      refine .gllam_tensor (L ∪ {x}) hne ?_ ?_ ?_
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs₀ hf.typeCtxOmega he.1.1
      · rw [typeCtxOmega_eraseName]
        exact gsvalid_eraseName hs hf.typeCtxOmega hτ.2
      · intro y hy
        have hyL : y ∉ L := fun hm => hy (Finset.mem_union_left _ hm)
        have hyx : y ≠ x := by
          intro h; subst y
          exact hy (Finset.mem_union_right _ (Finset.mem_singleton_self x))
        have hopen : x ∉ Term.fv (Term.openVar y body) := by
          intro hm
          have hm' := Term.fv_openRec_subset 0 (.var y) body hm
          rcases Finset.mem_union.mp hm' with hm' | hm'
          · exact he.2 hm'
          · have hxy : x = y := by simpa [Term.fv] using hm'
            exact hyx hxy.symm
        have hb := ghastype_eraseName (hbody y hyL)
          (hf.update (g := .one) hyx (by simpa [Ty.fv] using he.1.1)) hopen
          (by simpa [Ty.fv] using hτ.2)
        simpa only [eraseName_update_comm _ _ (Ne.symm hyx)] using hb
  | _, _, _, .gembed hsub hnl, x, hf, he, hτ => by
      simp only [Term.fv] at he
      simp only [Ty.fv, Space.fv, Finset.mem_union, not_or] at hτ
      refine .gembed ?_ (hnl.eraseName x)
      rw [typeCtxOmega_eraseName]
      exact gsubtype_eraseName hsub hf.typeCtxOmega he hτ.2
  | _, _, _, .gnllam L htv hnl hbody, x, hf, he, hτ => by
      rename_i Γ τdom τcod kdom kcod e
      simp only [Term.fv, Finset.mem_union, not_or] at he
      change x ∉ Ty.fv τdom ∪ Ty.fv τcod at hτ
      simp only [Finset.mem_union, not_or] at hτ
      have htv' : GTValid (typeCtxOmega (eraseName Γ x)) (.piTy τdom τcod)
          (.arrow kdom kcod) := by
        rw [typeCtxOmega_eraseName]
        exact gtvalid_eraseName htv hf.typeCtxOmega (by simpa [Ty.fv] using hτ)
      have hbody' : ∀ y, y ∉ L ∪ {x} →
          GHasType (Function.update (eraseName Γ x) y (some (.omega, τdom)))
            (Term.openVar y e) (Ty.openVar y τcod) := by
        intro y hy
        have hyL : y ∉ L := fun hm => hy (Finset.mem_union_left _ hm)
        have hyx : y ≠ x := by
          intro h; subst y
          exact hy (Finset.mem_union_right _ (Finset.mem_singleton_self x))
        have heopen : x ∉ Term.fv (Term.openVar y e) := by
          intro hm
          have hm' := Term.fv_openRec_subset 0 (.var y) e hm
          rcases Finset.mem_union.mp hm' with hm' | hm'
          · exact he.2 hm'
          · have hxy : x = y := by simpa [Term.fv] using hm'
            exact hyx hxy.symm
        have htopen : x ∉ Ty.fv (Ty.openVar y τcod) := by
          intro hm
          have hm' := Ty.fv_openRec_subset 0 (.var y) τcod hm
          rcases Finset.mem_union.mp hm' with hm' | hm'
          · exact hτ.2 hm'
          · have hxy : x = y := by simpa [Term.fv] using hm'
            exact hyx hxy.symm
        have hb := ghastype_eraseName (hbody y hyL)
          (hf.update (g := .omega) hyx hτ.1) heopen htopen
        simpa only [eraseName_update_comm _ _ (Ne.symm hyx)] using hb
      exact .gnllam (L ∪ {x}) htv' (hnl.eraseName x) hbody'

end

end GLang.Graded
