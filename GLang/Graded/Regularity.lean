import GLang.Graded.BridgeBwd
import GLang.Graded.Subst
import GLang.Proofs.Source.Regularity
import GLang.Proofs.Source.NLCtxFv

namespace GLang.Graded

open GLang

/-! ## Context validity carrier (for `gvar`). -/

def CtxValid (Γ : GCtx) : Type :=
  ∀ {x : Name} {g : GGrade} {τ : Ty}, Γ x = some (g, τ) → Σ k, GTValid (typeCtxOmega Γ) τ k

/-! ## The graded type-instantiation interface (the sole substitution residual). -/

def GTVInst : Type :=
  ∀ {ε : NLCtx} {τ₀ τ₁ : Ty} {k₀ k₁ : Kind} {e₁ : Term},
    GTValid (asTypeCtx ε) (.piTy τ₀ τ₁) (.arrow k₀ k₁) →
    GHasType (tr (∅ : LCtx) ε) e₁ τ₀ →
    GTValid (asTypeCtx ε) (Ty.instantiate e₁ τ₁) k₁

/-! ## Inversion helper. -/

/-- A subspace derivation validates both of its spaces (the sub-* constructors carry
    the ambient `SValid` premises; the source space is reconstructed). -/
def gsubtype_svalid {f : Name → Option Ty} {s₀ s₁ : Space} :
    GSubType f s₀ s₁ → GSValid f s₀ × GSValid f s₁
  | .sub_ker h₀ h₁ he => ⟨.ker h₀ h₁ he, h₀⟩
  | .sub_coker h₀ h₁ he => ⟨.coker h₀ h₁ he, h₀⟩
  | .sub_img h₀ h₁ he => ⟨.img h₀ h₁ he, h₁⟩
  | .sub_coimg h₀ h₁ he => ⟨.coimg h₀ h₁ he, h₁⟩

/-! ## Graded regularity. -/

/-- **Graded regularity.** A well-typed term's type is valid (at some kind), over the
    ω-view `typeCtxOmega Γ`. Structural recursion on the derivation; NO promote case
    (there is no promote constructor). All cases but `gapp_nonlinear` are read-offs;
    `gvar` reads the `CtxValid` carrier; `gapp_nonlinear` consumes `GTVInst`.

    The `Γ = tr Δ ε` / `CtxDisj Δ ε` hypotheses are only touched by `gapp_nonlinear`
    (to bridge its ∅-linear argument); every recursion keeps the SAME context, so they
    thread unchanged. -/
def GHasType.regular : {Γ : GCtx} → {Δ : LCtx} → {ε : NLCtx} → {e : Term} → {τ : Ty} →
    GHasType Γ e τ → GTVInst → Γ = tr Δ ε → CtxDisj Δ ε → CtxValid Γ →
    Σ k, GTValid (typeCtxOmega Γ) τ k
  | _, _, _, _, _, .gzero hs, _, _, _, _ => ⟨.base, .space hs⟩
  | _, _, _, _, _, .gsmul hs _ _ _ _, _, _, _, _ => ⟨.base, .space hs⟩
  | _, _, _, _, _, .gadd hs _ _, _, _, _, _ => ⟨.base, .space hs⟩
  | _, _, _, _, _, .ginner hs _, _, _, _, _ =>
      ⟨.base, .space (.tprod (.dual hs) (.dual hs))⟩
  | _, _, _, _, _, .greal_lit _ _, _, _, _, _ => ⟨.base, .space .real⟩
  | _, _, _, _, _, .gapp_linear _ hs₁ _ _ _ _, _, _, _, _ => ⟨.base, .space hs₁⟩
  | _, _, _, _, _, .gapp_inner _ _ _ _ _, _, _, _, _ => ⟨.base, .space .real⟩
  | _, _, _, _, _, .gvar hx _ _, _, _, _, hctx => hctx hx
  | _, _, _, _, _, .gpinv_tensor hs₀ hs₁ _ _, _, _, _, _ =>
      ⟨.base, .space (.tprod (.dual hs₁) hs₀)⟩
  | _, _, _, _, _, .gpinv_dual hs _ _, _, _, _, _ =>
      ⟨.base, .space (.tprod (.dual .real) hs)⟩
  | _, _, _, _, _, .gdsumE hs₀ hs₁ _ _, _, _, _, _ =>
      ⟨.base, .space (.dsum hs₀ hs₁)⟩
  | _, _, _, _, _, .gtprodE hs₀ hs₁ _ _ _ _, _, _, _, _ =>
      ⟨.base, .space (.tprod hs₀ hs₁)⟩
  | _, _, _, _, _, .gllam_real _ hs _, _, _, _, _ => ⟨.base, .space (.dual hs)⟩
  | _, _, _, _, _, .gllam_tensor _ _ hs₀ hs _, _, _, _, _ =>
      ⟨.base, .space (.tprod (.dual hs₀) hs)⟩
  | _, _, _, _, _, .gembed hsub _, _, _, _, _ =>
      let ⟨hv0, hv1⟩ := gsubtype_svalid hsub
      ⟨.base, .space (.tprod (.dual hv0) hv1)⟩
  | _, _, _, _, _, .gnllam _ htv _ _, _, _, _, _ => ⟨_, htv⟩
  | Γ, Δ, ε, _, _, .gapp_nonlinear hnl h₀ h₁, hinst, hΓ, hcd, hctx => by
      -- Recurse on the functor operand (SAME context) to get the pi-type's validity.
      obtain ⟨k, hpik⟩ := GHasType.regular h₀ hinst hΓ hcd hctx
      -- The ω-view of a `tr`-image is `asTypeCtx ε` (needs only `CtxDisj`).
      have heqΓ : typeCtxOmega Γ = asTypeCtx ε := by rw [hΓ]; exact typeCtxOmega_tr hcd
      -- `NoLin` forces the linear context empty, so the argument lives at `tr ∅ ε`.
      have hΔ : Δ = (∅ : LCtx) := noLin_trge_empty hnl (by rw [hΓ]; exact TrGe.refl_tr Δ ε)
      have hΓ' : Γ = tr (∅ : LCtx) ε := by rw [hΓ, hΔ]
      have h₁' := hΓ' ▸ h₁
      have hpik' := heqΓ ▸ hpik
      cases hpik' with
      | @piTy _ _ _ k₀' k₁' L hh0 hbody =>
          exact ⟨k₁', heqΓ.symm ▸ hinst (.piTy L hh0 hbody) h₁'⟩

noncomputable def hasType_regular_via_graded {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (hinst : GTVInst) (hcd : CtxDisj Δ ε) (hctx : CtxValid (tr Δ ε))
    (h : HasType Δ ε e τ) : Σ k, TValid ε τ k := by
  have hg : GHasType (tr Δ ε) e τ := hasTypeBridge hcd h
  obtain ⟨k, hgt⟩ := GHasType.regular hg hinst rfl hcd hctx
  rw [typeCtxOmega_tr hcd] at hgt
  exact ⟨k, tvalidBwd hgt (fun _ _ hh => hh)⟩

def ctxValid_tr {Δ : LCtx} {ε : NLCtx} (hcd : CtxDisj Δ ε)
    (hlin : ∀ x s, Δ.lookup x = some s → SValid ε s)
    (hnl : ∀ x τ, ε.lookup x = some τ → Σ k, TValid ε τ k) :
    CtxValid (tr Δ ε) := by
  intro x g τ hx
  have hom : typeCtxOmega (tr Δ ε) = asTypeCtx ε := typeCtxOmega_tr hcd
  rw [hom]
  -- Decode the `tr` lookup.
  simp only [tr] at hx
  cases hlk : Δ.lookup x with
  | some s =>
      rw [hlk] at hx
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨_, hτ⟩ := hx; subst hτ
      exact ⟨.base, .space (svalidBridge (hlin x s hlk))⟩
  | none =>
      rw [hlk] at hx
      cases hlkε : ε.lookup x with
      | none => rw [hlkε] at hx; simp at hx
      | some τ' =>
          rw [hlkε] at hx
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨_, hτ⟩ := hx; subst hτ
          obtain ⟨k, htv⟩ := hnl x τ' hlkε
          exact ⟨k, tvalidBridge htv⟩

/-! ## Discharging `GTVInst` via the graded substitution (U2.2) — regularity UNCONDITIONAL. -/

/-- Graded type instantiation, derived from graded substitution. -/
noncomputable def gtvInst : GTVInst := by
  intro ε τ₀ τ₁ k₀ k₁ e₁ hpi harg
  have hlc : Term.lc e₁ := HasType.lc (hasTypeBridgeBwd (CtxDisj.empty ε) harg)
  cases hpi with
  | @piTy _ _ _ _ _ L h0 hcod =>
      have hex := Infinite.exists_notMem_finset
        (L ∪ ε.keys ∪ NLCtx.fv ε ∪ Ty.fv τ₀ ∪ Ty.fv τ₁)
      set y := hex.choose with hydef
      have hy : y ∉ (L ∪ ε.keys ∪ NLCtx.fv ε ∪ Ty.fv τ₀ ∪ Ty.fv τ₁) := hex.choose_spec
      simp only [Finset.mem_union, not_or] at hy
      obtain ⟨⟨⟨⟨hyL, hykeys⟩, hyfvε⟩, hyτ0⟩, hyτ1⟩ := hy
      have hynε : ε.lookup y = none := lookup_eq_none_of_notMem_keys hykeys
      have hεfresh : ∀ z τ, ε.lookup z = some τ → y ∉ Ty.fv τ :=
        fun z τ hz hc => hyfvε (NLCtx.mem_fv_of_lookup hz hc)
      have htinv : TInv y τ₀ ε (Function.update (asTypeCtx ε) y (some τ₀)) := by
        refine ⟨?_, ?_⟩
        · intro z τ hz τ' hf
          rcases eq_or_ne z y with rfl | hzy
          · rw [hynε] at hz; exact absurd hz (by simp)
          · rw [Function.update_of_ne hzy] at hf
            simp only [asTypeCtx] at hf
            rw [hz] at hf; simp only [Option.some.injEq] at hf; exact hf
        · intro τ hf
          rw [Function.update_self] at hf
          simp only [Option.some.injEq] at hf; exact hf.symm
      have sd : GSubstData y e₁ ε τ₀ := ⟨hlc, harg, hyτ0, hynε, hεfresh⟩
      have hres := gtvalid_subst sd htinv (hcod y hyL)
      rw [tsubstCtx_update_asTypeCtx hynε hεfresh, ty_subst_intro y e₁ τ₁ hlc hyτ1] at hres
      exact hres

/-- **Graded regularity, UNCONDITIONAL.** `GHasType.regular` with `GTVInst` discharged. -/
noncomputable def GHasType.regular_uncond {Γ : GCtx} {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (h : GHasType Γ e τ) (hΓ : Γ = tr Δ ε) (hcd : CtxDisj Δ ε) (hctx : CtxValid Γ) :
    Σ k, GTValid (typeCtxOmega Γ) τ k :=
  GHasType.regular h gtvInst hΓ hcd hctx

noncomputable def hasType_regular {Δ : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (hcd : CtxDisj Δ ε) (hctx : CtxValid (tr Δ ε)) (h : HasType Δ ε e τ) :
    Σ k, TValid ε τ k :=
  hasType_regular_via_graded gtvInst hcd hctx h

end GLang.Graded
