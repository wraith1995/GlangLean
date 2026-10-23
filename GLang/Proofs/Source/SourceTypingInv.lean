

import GLang.Annotated.Judgments

namespace GLang

/-- Data from inverting a `smul` source typing. `Δ` splits into `Δ₀ ∪ Δ₁`. -/
structure SmulInvData (e₀ e₁ : Term) (τ : Ty) : Type where
  Δ₀ : LCtx
  Δ₁ : LCtx
  Γ' : NLCtx
  s  : Space
  hτ : τ = .space s
  hsv : SValid Γ' s
  h₀ : HasType Δ₀ Γ' e₀ (.space .real)
  h₁ : HasType Δ₁ Γ' e₁ (.space s)

/-- Promote-aware `smul` source-typing inversion. -/
def hasType_smul_inv {Δ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {τ : Ty}
    (h : HasType Δ Γ (.smul e₀ e₁) τ) : SmulInvData e₀ e₁ τ :=
  match h with
  | .smul hsv _ h₀ h₁ => ⟨_, _, _, _, rfl, hsv, h₀, h₁⟩
  | .promote _ _ _ _ h' => hasType_smul_inv h'

/-- Data from inverting an `add` source typing (both operands share `Δ'`/`Γ'`/`s`). -/
structure AddInvData (e₀ e₁ : Term) (τ : Ty) : Type where
  Δ' : LCtx
  Γ' : NLCtx
  s  : Space
  hτ : τ = .space s
  hsv : SValid Γ' s
  h₀ : HasType Δ' Γ' e₀ (.space s)
  h₁ : HasType Δ' Γ' e₁ (.space s)

/-- Promote-aware `add` source-typing inversion. -/
def hasType_add_inv {Δ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {τ : Ty}
    (h : HasType Δ Γ (.add e₀ e₁) τ) : AddInvData e₀ e₁ τ :=
  match h with
  | .add hsv h₀ h₁ => ⟨_, _, _, rfl, hsv, h₀, h₁⟩
  | .promote _ _ _ _ h' => hasType_add_inv h'

/-- Inversion data for a `dsumE` source typing (operands share `Δ'`/`Γ'`). -/
structure DsumEInvData (e₀ e₁ : Term) (τ : Ty) : Type where
  Δ' : LCtx
  Γ' : NLCtx
  s₀ : Space
  s₁ : Space
  hτ : τ = .space (.dsum s₀ s₁)
  hsv0 : SValid Γ' s₀
  hsv1 : SValid Γ' s₁
  h₀ : HasType Δ' Γ' e₀ (.space s₀)
  h₁ : HasType Δ' Γ' e₁ (.space s₁)

/-- Promote-aware `dsumE` source-typing inversion. -/
def hasType_dsumE_inv {Δ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {τ : Ty}
    (h : HasType Δ Γ (.dsumE e₀ e₁) τ) : DsumEInvData e₀ e₁ τ :=
  match h with
  | .dsumE hsv0 hsv1 h₀ h₁ => ⟨_, _, _, _, rfl, hsv0, hsv1, h₀, h₁⟩
  | .promote _ _ _ _ h' => hasType_dsumE_inv h'

/-- Inversion data for a `tprodE` source typing (operands use disjoint `Δ₀`/`Δ₁`). -/
structure TprodEInvData (e₀ e₁ : Term) (τ : Ty) : Type where
  Δ₀ : LCtx
  Δ₁ : LCtx
  Γ' : NLCtx
  s₀ : Space
  s₁ : Space
  hτ : τ = .space (.tprod s₀ s₁)
  hsv0 : SValid Γ' s₀
  hsv1 : SValid Γ' s₁
  h₀ : HasType Δ₀ Γ' e₀ (.space s₀)
  h₁ : HasType Δ₁ Γ' e₁ (.space s₁)

/-- Promote-aware `tprodE` source-typing inversion. -/
def hasType_tprodE_inv {Δ : LCtx} {Γ : NLCtx} {e₀ e₁ : Term} {τ : Ty}
    (h : HasType Δ Γ (.tprodE e₀ e₁) τ) : TprodEInvData e₀ e₁ τ :=
  match h with
  | .tprodE hsv0 hsv1 _ h₀ h₁ => ⟨_, _, _, _, _, rfl, hsv0, hsv1, h₀, h₁⟩
  | .promote _ _ _ _ h' => hasType_tprodE_inv h'

/-- `LCtx.toNL` preserves membership (names). -/
theorem mem_toNL {lin : LCtx} {x : Name} (h : x ∈ lin) : x ∈ lin.toNL := by
  obtain ⟨s, hs⟩ := Finmap.mem_iff.mp h
  exact Finmap.mem_of_lookup_eq_some (lin.toNL_lookup x s hs)

/-- A `var` source typing places the variable in the combined context
    `Δ ∪ Γ` (promote-aware: a promoted linear name lands in the non-linear side). -/
def hasType_var_mem {Δ : LCtx} {Γ : NLCtx} {x : Name} {τ : Ty}
    (h : HasType Δ Γ (.var x) τ) : x ∈ Δ ∨ x ∈ Γ :=
  match h with
  | .var_lin => Or.inl (Finmap.mem_of_lookup_eq_some Finmap.lookup_singleton_eq)
  | .var_nlin hl => Or.inr (Finmap.mem_of_lookup_eq_some hl)
  | .promote _ _ _ _ h' =>
      match hasType_var_mem h' with
      | Or.inl hd =>
          (Finmap.mem_union.mp hd).elim
            (fun hlin => Or.inr (Finmap.mem_union.mpr (Or.inl (mem_toNL hlin))))
            (fun hΔ => Or.inl hΔ)
      | Or.inr hε => Or.inr (Finmap.mem_union.mpr (Or.inr hε))

/-- Data from inverting an `nllam` source typing (promote may reclassify the
    non-linear context, so `Γ'` and the codomain `τ₁` are existential).
    LN/cofinite: no binder name; the body premise is the cofinite `∀ y ∉ L`. -/
structure NllamInvData (τ₀ : Ty) (e : Term) (τ : Ty) : Type where
  Γ' : NLCtx
  τ₁ : Ty
  k₀ : Kind
  k₁ : Kind
  L : Finset Name
  hτ : τ = .piTy τ₀ τ₁
  htval : TValid Γ' (.piTy τ₀ τ₁) (.arrow k₀ k₁)
  hbody : ∀ y, y ∉ L →
    HasType ∅ (Finmap.insert y τ₀ Γ') (Term.openVar y e) (Ty.openVar y τ₁)

/-- Promote-aware `nllam` source-typing inversion. -/
def hasType_nllam_inv {Δ : LCtx} {Γ : NLCtx} {τ₀ : Ty} {e : Term} {τ : Ty}
    (h : HasType Δ Γ (.nllam τ₀ e) τ) : NllamInvData τ₀ e τ :=
  match h with
  | .nllam L htval hbody => ⟨_, _, _, _, L, rfl, htval, hbody⟩
  | .promote _ _ _ _ h' => hasType_nllam_inv h'

/-- Data from inverting a `pinvT` source typing (`pinv_tensor` types under `Δ = ∅`,
    so only `Γ'` is existential through `promote`). -/
structure PinvTInvData (s₀ s₁ : Space) (e : Term) (τ : Ty) : Type where
  Γ' : NLCtx
  hτ : τ = .space (.tprod (.dual s₁) s₀)
  hsv₀ : SValid Γ' s₀
  hsv₁ : SValid Γ' s₁
  h : HasType ∅ Γ' e (.space (.tprod (.dual s₀) s₁))

/-- Promote-aware `pinvT` source-typing inversion. -/
def hasType_pinvT_inv {Δ : LCtx} {Γ : NLCtx} {s₀ s₁ : Space} {e : Term} {τ : Ty}
    (h : HasType Δ Γ (.pinvT s₀ s₁ e) τ) : PinvTInvData s₀ s₁ e τ :=
  match h with
  | .pinv_tensor hsv₀ hsv₁ h' => ⟨_, rfl, hsv₀, hsv₁, h'⟩
  | .promote _ _ _ _ h' => hasType_pinvT_inv h'

/-- Data from inverting an `appL` source typing (`app_linear`; the linear context
    splits, both annotations are syntactic). -/
structure AppLInvData (s₀ s₁ : Space) (e₀ e₁ : Term) (τ : Ty) : Type where
  Δ₀ : LCtx
  Δ₁ : LCtx
  Γ' : NLCtx
  hτ : τ = .space s₁
  hsv₀ : SValid Γ' s₀
  hsv₁ : SValid Γ' s₁
  h₀ : HasType Δ₀ Γ' e₀ (.space (.tprod (.dual s₀) s₁))
  h₁ : HasType Δ₁ Γ' e₁ (.space s₀)

/-- Promote-aware `appL` source-typing inversion. -/
def hasType_appL_inv {Δ : LCtx} {Γ : NLCtx} {s₀ s₁ : Space} {e₀ e₁ : Term} {τ : Ty}
    (h : HasType Δ Γ (.appL s₀ s₁ e₀ e₁) τ) : AppLInvData s₀ s₁ e₀ e₁ τ :=
  match h with
  | .app_linear hsv₀ hsv₁ _ h₀ h₁ => ⟨_, _, _, rfl, hsv₀, hsv₁, h₀, h₁⟩
  | .promote _ _ _ _ h' => hasType_appL_inv h'

/-- Data from inverting an `appI` source typing (`app_inner`). -/
structure AppIInvData (s : Space) (e₀ e₁ : Term) (τ : Ty) : Type where
  Δ₀ : LCtx
  Δ₁ : LCtx
  Γ' : NLCtx
  hτ : τ = .space .real
  hsv : SValid Γ' s
  h₀ : HasType Δ₀ Γ' e₀ (.space (.dual s))
  h₁ : HasType Δ₁ Γ' e₁ (.space s)

/-- Promote-aware `appI` source-typing inversion. -/
def hasType_appI_inv {Δ : LCtx} {Γ : NLCtx} {s : Space} {e₀ e₁ : Term} {τ : Ty}
    (h : HasType Δ Γ (.appI s e₀ e₁) τ) : AppIInvData s e₀ e₁ τ :=
  match h with
  | .app_inner hsv _ h₀ h₁ => ⟨_, _, _, rfl, hsv, h₀, h₁⟩
  | .promote _ _ _ _ h' => hasType_appI_inv h'

/-- Data from inverting a `pinvD` source typing. -/
structure PinvDInvData (s : Space) (e : Term) (τ : Ty) : Type where
  Γ' : NLCtx
  hτ : τ = .space (.tprod (.dual .real) s)
  hsv : SValid Γ' s
  h : HasType ∅ Γ' e (.space (.dual s))

/-- Promote-aware `pinvD` source-typing inversion. -/
def hasType_pinvD_inv {Δ : LCtx} {Γ : NLCtx} {s : Space} {e : Term} {τ : Ty}
    (h : HasType Δ Γ (.pinvD s e) τ) : PinvDInvData s e τ :=
  match h with
  | .pinv_dual hsv h' => ⟨_, rfl, hsv, h'⟩
  | .promote _ _ _ _ h' => hasType_pinvD_inv h'

end GLang

