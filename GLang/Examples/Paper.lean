import GLang.Proofs.Source.InnerProduct
import GLang.Metatheory

/-! Typing and operational derivations for parallelogram area and
point-dependent tangent spaces. -/

namespace GLang
namespace Examples.Paper

open Basis (BasisValid)
open RawCertifiedOperational

/-! ## Linear-context bookkeeping

The typing rules produce syntactic unions `Δ₀ ∪ Δ₁`, while `var_lin` needs a
`Finmap.singleton` and the binder rules open into `Finmap.insert`.  These helpers
transport derivations along the (propositional) equalities between those forms. -/

/-- Transport a typing derivation along an equality of linear contexts. -/
def castΔ {Δ Δ' : LCtx} {ε : NLCtx} {e : Term} {τ : Ty}
    (h : HasType Δ ε e τ) (heq : Δ = Δ') : HasType Δ' ε e τ := heq ▸ h

/-- Transport a typing derivation along an equality of types. -/
def castTy {Δ : LCtx} {ε : NLCtx} {e : Term} {τ τ' : Ty}
    (h : HasType Δ ε e τ) (heq : τ = τ') : HasType Δ ε e τ' := heq ▸ h

theorem pair_disjoint {a b : Name} {sa sb : Space} (h : a ≠ b) :
    Finmap.Disjoint (Finmap.singleton a sa : LCtx) (Finmap.singleton b sb) := by
  intro x hxa hxb
  rw [Finmap.mem_singleton] at hxa hxb
  exact h (hxa.symm.trans hxb)

/-- Two nested binder openings form the union of two singletons. -/
theorem pair_ctx (a b : Name) (sa sb : Space) (h : a ≠ b) :
    (Finmap.insert b sb (Finmap.insert a sa ∅) : LCtx) =
      Finmap.singleton a sa ∪ Finmap.singleton b sb := by
  apply Finmap.ext_lookup
  intro k
  by_cases hkb : k = b
  · rw [hkb]
    have hb : b ∉ (Finmap.singleton a sa : LCtx) := by
      rw [Finmap.mem_singleton]; exact h.symm
    rw [Finmap.lookup_insert, Finmap.lookup_union_right hb, Finmap.lookup_singleton_eq]
  · rw [Finmap.lookup_insert_of_ne _ hkb]
    by_cases hka : k = a
    · rw [hka]
      have ha : a ∈ (Finmap.singleton a sa : LCtx) := by rw [Finmap.mem_singleton]
      rw [Finmap.lookup_insert, Finmap.lookup_union_left ha, Finmap.lookup_singleton_eq]
    · have ha : k ∉ (Finmap.singleton a sa : LCtx) := by rw [Finmap.mem_singleton]; exact hka
      have hb : k ∉ (Finmap.singleton b sb : LCtx) := by rw [Finmap.mem_singleton]; exact hkb
      rw [Finmap.lookup_insert_of_ne _ hka, Finmap.lookup_empty, Finmap.lookup_union_right ha]
      exact (Finmap.lookup_eq_none.mpr hb).symm

/-- Apply a closed linear map to a linear variable. -/
noncomputable def appL_var {ε : NLCtx} {s₀ s₁ : Space} {f : Term} (x : Name)
    (sv₀ : SValid ε s₀) (sv₁ : SValid ε s₁)
    (hf : HasType ∅ ε f (.space (.tprod (.dual s₀) s₁))) :
    HasType (Finmap.singleton x s₀) ε (.appL s₀ s₁ f (.var x)) (.space s₁) :=
  castΔ (HasType.app_linear sv₀ sv₁ (Finmap.disjoint_empty _) hf HasType.var_lin)
    Finmap.empty_union

/-- Scale by a real literal: the literal is closed, so `Δ` is unchanged. -/
noncomputable def smul_const {Δ : LCtx} {ε : NLCtx} {s : Space} {e : Term} (r : ℝ)
    (sv : SValid ε s) (h : HasType Δ ε e (.space s)) :
    HasType Δ ε (.smul (.real r) e) (.space s) :=
  castΔ (HasType.smul sv (Finmap.disjoint_empty _) (HasType.real_lit r) h)
    Finmap.empty_union

/-- The tensor of two distinct linear variables. -/
noncomputable def tprodE_vars {ε : NLCtx} {sa sb : Space} (a b : Name) (h : a ≠ b)
    (sva : SValid ε sa) (svb : SValid ε sb) :
    HasType (Finmap.singleton a sa ∪ Finmap.singleton b sb) ε
      (.tprodE (.var a) (.var b)) (.space (.tprod sa sb)) :=
  HasType.tprodE sva svb (pair_disjoint h) HasType.var_lin HasType.var_lin

/-! ## Spaces -/

/-- `ℝ² := ℝ ⊕ ℝ`. -/
def R2 : Space := .dsum .real .real
/-- `ℝ³ := (ℝ ⊕ ℝ) ⊕ ℝ`. -/
def R3 : Space := .dsum R2 .real

noncomputable def svR2 {ε : NLCtx} : SValid ε R2 := .dsum .real .real
noncomputable def svR3 {ε : NLCtx} : SValid ε R3 := .dsum svR2 .real

/-! ## Example 1 — the area of a parallelogram -/

def pi0 : Term := Term.kproj0 .real .real
/-- `π₁ : (ℝ ⊕ ℝ)* ⊗ ℝ`. -/
def pi1 : Term := Term.kproj1 .real .real

noncomputable def pi0_hasType {ε : NLCtx} :
    HasType ∅ ε pi0 (.space (.tprod (.dual R2) .real)) :=
  Term.kproj0_hasType SValid.real SValid.real

noncomputable def pi1_hasType {ε : NLCtx} :
    HasType ∅ ε pi1 (.space (.tprod (.dual R2) .real)) :=
  Term.kproj1_hasType SValid.real SValid.real

theorem pi0_lc : Term.lc pi0 := HasType.lc (pi0_hasType (ε := ∅))
theorem pi1_lc : Term.lc pi1 := HasType.lc (pi1_hasType (ε := ∅))

/-- The projections are closed, so binder opening leaves them alone. -/
@[simp] theorem pi0_openRec (k : Nat) (u : Term) : Term.openRec k u pi0 = pi0 :=
  Term.openRec_lc pi0_lc k u
@[simp] theorem pi1_openRec (k : Nat) (u : Term) : Term.openRec k u pi1 = pi1 :=
  Term.openRec_lc pi1_lc k u

/-- Body of `area`, LN: `v₀ = bvar 1` (outer binder), `v₁ = bvar 0` (inner):
    `π₀(v₀)·π₁(v₁) − π₁(v₀)·π₀(v₁)`.  Subtraction is `add e (smul (-1) e')`. -/
noncomputable def areaBody : Term :=
  .add (.smul (.appL R2 .real pi0 (.bvar 1)) (.appL R2 .real pi1 (.bvar 0)))
    (.smul (.real (-1))
      (.smul (.appL R2 .real pi1 (.bvar 1)) (.appL R2 .real pi0 (.bvar 0))))

noncomputable def area : Term := .llam R2 (.dual R2) (.llam R2 .real areaBody)

/-- `(ℝ²)* ⊗ (ℝ²)*`. -/
def areaTy : Ty := .space (.tprod (.dual R2) (.dual R2))

/-- The fully opened body at two distinct linear vector names. -/
noncomputable def areaBody_open_hasType {ε : NLCtx} (v₀ v₁ : Name) (h : v₀ ≠ v₁) :
    HasType (Finmap.singleton v₀ R2 ∪ Finmap.singleton v₁ R2) ε
      (.add (.smul (.appL R2 .real pi0 (.var v₀)) (.appL R2 .real pi1 (.var v₁)))
        (.smul (.real (-1))
          (.smul (.appL R2 .real pi1 (.var v₀)) (.appL R2 .real pi0 (.var v₁)))))
      (.space .real) :=
  HasType.add SValid.real
    (HasType.smul SValid.real (pair_disjoint h)
      (appL_var v₀ svR2 SValid.real pi0_hasType)
      (appL_var v₁ svR2 SValid.real pi1_hasType))
    (smul_const (-1) SValid.real
      (HasType.smul SValid.real (pair_disjoint h)
        (appL_var v₀ svR2 SValid.real pi1_hasType)
        (appL_var v₁ svR2 SValid.real pi0_hasType)))

noncomputable def area_hasType {ε : NLCtx} : HasType ∅ ε area areaTy := by
  unfold area areaTy
  refine HasType.llam_tensor ∅ (by intro h; cases h) svR2 (SValid.dual svR2)
    (fun v₀ _ => ?_)
  simp only [Term.openVar, Term.openRec, Space.openRec, areaBody, pi0_openRec, pi1_openRec,
    Space.openRec_lc (SValid.lc (svR2 (ε := ∅)))]
  refine HasType.llam_real {v₀} svR2 (fun v₁ hv₁ => ?_)
  rw [Finset.mem_singleton] at hv₁
  simp only [Term.openVar, Term.openRec, Space.openRec, pi0_openRec, pi1_openRec,
    Space.openRec_lc (SValid.lc (svR2 (ε := ∅)))]
  rw [pair_ctx v₀ v₁ R2 R2 (Ne.symm hv₁)]
  exact areaBody_open_hasType v₀ v₁ (Ne.symm hv₁)

/-- Body of `antiSymMap`, LN: `x₀ = bvar 1`, `x₁ = bvar 0`:
    `½·(x₀ ⊗ x₁ − x₁ ⊗ x₀)`. -/
noncomputable def antiSymBody : Term :=
  .smul (.real (1/2))
    (.add (.tprodE (.bvar 1) (.bvar 0))
      (.smul (.real (-1)) (.tprodE (.bvar 0) (.bvar 1))))

noncomputable def antiSymMap : Term :=
  .llam R2 (.tprod (.dual R2) (.tprod R2 R2)) (.llam R2 (.tprod R2 R2) antiSymBody)

/-- `(ℝ²)* ⊗ (ℝ²)* ⊗ (ℝ² ⊗ ℝ²)`. -/
def antiSymMapTy : Ty :=
  .space (.tprod (.dual R2) (.tprod (.dual R2) (.tprod R2 R2)))

noncomputable def antiSymBody_open_hasType {ε : NLCtx} (x₀ x₁ : Name) (h : x₀ ≠ x₁) :
    HasType (Finmap.singleton x₀ R2 ∪ Finmap.singleton x₁ R2) ε
      (.smul (.real (1/2))
        (.add (.tprodE (.var x₀) (.var x₁))
          (.smul (.real (-1)) (.tprodE (.var x₁) (.var x₀)))))
      (.space (.tprod R2 R2)) :=
  smul_const (1/2) (SValid.tprod svR2 svR2)
    (HasType.add (SValid.tprod svR2 svR2)
      (tprodE_vars x₀ x₁ h svR2 svR2)
      (smul_const (-1) (SValid.tprod svR2 svR2)
        (castΔ (tprodE_vars x₁ x₀ h.symm svR2 svR2)
          (Finmap.union_comm_of_disjoint (pair_disjoint h.symm)))))

/-- **`antiSymMap : (ℝ²)* ⊗ (ℝ²)* ⊗ (ℝ² ⊗ ℝ²)`**. -/
noncomputable def antiSymMap_hasType {ε : NLCtx} : HasType ∅ ε antiSymMap antiSymMapTy := by
  unfold antiSymMap antiSymMapTy
  refine HasType.llam_tensor ∅ (by intro h; cases h) svR2
    (SValid.tprod (SValid.dual svR2) (SValid.tprod svR2 svR2)) (fun x₀ _ => ?_)
  simp only [Term.openVar, Term.openRec, Space.openRec, antiSymBody,
    Space.openRec_lc (SValid.lc (svR2 (ε := ∅)))]
  refine HasType.llam_tensor {x₀} (by intro h; cases h) svR2 (SValid.tprod svR2 svR2)
    (fun x₁ hx₁ => ?_)
  rw [Finset.mem_singleton] at hx₁
  simp only [Term.openVar, Term.openRec]
  rw [pair_ctx x₀ x₁ R2 R2 (Ne.symm hx₁)]
  exact antiSymBody_open_hasType x₀ x₁ (Ne.symm hx₁)

noncomputable def antiSymMapL : Term := Term.applyUncurry2NonReal R2 R2 (.tprod R2 R2) antiSymMap

/-- `(ℝ² ⊗ ℝ²)* ⊗ (ℝ² ⊗ ℝ²)`. -/
def antiSymMapLTy : Ty := .space (.tprod (.dual (.tprod R2 R2)) (.tprod R2 R2))

/-- **`antiSymMapL : (ℝ² ⊗ ℝ²)* ⊗ (ℝ² ⊗ ℝ²)`**. -/
noncomputable def antiSymMapL_hasType {ε : NLCtx} : HasType ∅ ε antiSymMapL antiSymMapLTy :=
  Term.applyUncurry2NonReal_hasType (by intro h; cases h) svR2 svR2 (SValid.tprod svR2 svR2)
    antiSymMap_hasType

noncomputable def Img : Space := .img (.tprod R2 R2) (.tprod R2 R2) antiSymMapL

/-- **`Img` is a well-formed space** (its witness is typed at `(ℝ²⊗ℝ²)*⊗(ℝ²⊗ℝ²)`). -/
noncomputable def svImg {ε : NLCtx} : SValid ε Img :=
  SValid.img (SValid.tprod svR2 svR2) (SValid.tprod svR2 svR2) antiSymMapL_hasType

/-- `Img ≤ ℝ² ⊗ ℝ²`. -/
noncomputable def subImg {ε : NLCtx} : SubType ε Img (.tprod R2 R2) :=
  SubType.sub_img (SValid.tprod svR2 svR2) (SValid.tprod svR2 svR2) antiSymMapL_hasType

noncomputable def projImg : Term := Term.lproj Img (.tprod R2 R2)

noncomputable def projImg_hasType {ε : NLCtx} :
    HasType ∅ ε projImg (.space (.tprod (.dual (.tprod R2 R2)) Img)) :=
  HasType.lproj svImg (SValid.tprod svR2 svR2) subImg

noncomputable def pTerm (v₀ v₁ : Name) : Term :=
  .appL (.tprod R2 R2) Img projImg (.tprodE (.var v₀) (.var v₁))

/-- **`{v₀ : ℝ², v₁ : ℝ²} ⊢ p : Img`**. -/
noncomputable def pTerm_hasType {ε : NLCtx} (v₀ v₁ : Name) (h : v₀ ≠ v₁) :
    HasType (Finmap.singleton v₀ R2 ∪ Finmap.singleton v₁ R2) ε (pTerm v₀ v₁) (.space Img) :=
  castΔ (HasType.app_linear (SValid.tprod svR2 svR2) svImg (Finmap.disjoint_empty _)
      projImg_hasType (tprodE_vars v₀ v₁ h svR2 svR2))
    Finmap.empty_union

/-- The vector `1 ⊕ 0 : ℝ²` (literally `e₀`). -/
def e10 : Term := .dsumE (.real 1) (.real 0)

noncomputable def e10_hasType {ε : NLCtx} : HasType ∅ ε e10 (.space R2) :=
  HasType.dsumE SValid.real SValid.real (HasType.real_lit 1) (HasType.real_lit 0)

/-- `proj((1⊕0) ⊗ (1⊕0)) : Img`, the explicit basis vector of `b₀`. -/
noncomputable def projE10 : Term := .appL (.tprod R2 R2) Img projImg (.tprodE e10 e10)

noncomputable def projE10_hasType {ε : NLCtx} : HasType ∅ ε projE10 (.space Img) :=
  castΔ (HasType.app_linear (SValid.tprod svR2 svR2) svImg (Finmap.disjoint_empty _)
      projImg_hasType
      (castΔ (HasType.tprodE svR2 svR2 (Finmap.disjoint_empty _) e10_hasType e10_hasType)
        Finmap.empty_union))
    Finmap.empty_union

noncomputable def b0 : Basis := .terms Img [projE10] (Basis.std (.space Img))

/-- **`b₀` is a valid basis** (of `Img`, in any source context). -/
theorem b0_valid {ε : NLCtx} : BasisValid ε b0 :=
  BasisValid.terms (Basis.stdSpace_valid Img svImg) (Basis.tof_std (.space Img)) ⟨svImg⟩
    (fun e he => by
      simp only [List.mem_singleton] at he
      subst he
      exact ⟨projE10_hasType⟩)
    (by simp)

/-! ## Example 2 — the tangent space at a point -/

/-- The parametrization's type: `(x:ℝ²) → (ℝ²)* ⊗ ℝ³` (non-dependent codomain). -/
def fTy : Ty := .piTy (.space R2) (.space (.tprod (.dual R2) R3))

/-- The source context holding the free non-linear parametrization `f`. -/
def εf : NLCtx := Finmap.singleton "f" fTy

/-- `Img(f(x))` with the point at de Bruijn index `n`. -/
def fTAt (n : Nat) : Space := .img R2 R3 (.appN (.var "f") (.bvar n))

/-- `Img(f(y))` at a named point. -/
def fTyAt (y : Name) : Space := .img R2 R3 (.appN (.var "f") (.var y))

def fT : Ty := .piTy (.space R2) (.space (fTAt 0))

@[simp] theorem fTAt_openVar (n : Nat) (y : Name) :
    Space.openRec n (.var y) (fTAt n) = fTyAt y := by
  simp [fTAt, fTyAt, Space.openRec, Term.openRec,
    Space.openRec_lc (SValid.lc (svR2 (ε := ∅))), Space.openRec_lc (SValid.lc (svR3 (ε := ∅)))]

@[simp] theorem fTyAt_openRec (k : Nat) (u : Term) (y : Name) :
    Space.openRec k u (fTyAt y) = fTyAt y := by
  simp [fTyAt, Space.openRec, Term.openRec,
    Space.openRec_lc (SValid.lc (svR2 (ε := ∅))), Space.openRec_lc (SValid.lc (svR3 (ε := ∅)))]

/-- The codomain of `f` is closed, so instantiation is the identity on it. -/
theorem fTy_cod_instantiate (u : Term) :
    Ty.instantiate u (.space (.tprod (.dual R2) R3)) = .space (.tprod (.dual R2) R3) := by
  simp [Ty.instantiate, Ty.openRec, Space.openRec,
    Space.openRec_lc (SValid.lc (svR2 (ε := ∅))), Space.openRec_lc (SValid.lc (svR3 (ε := ∅)))]

/-- `Img(f(y))` is a well-formed space whenever `f` and the point `y` are in scope. -/
noncomputable def fTyAt_svalid {ε : NLCtx} {y : Name}
    (hf : ε.lookup "f" = some fTy) (hy : ε.lookup y = some (.space R2)) :
    SValid ε (fTyAt y) :=
  SValid.img svR2 svR3
    (castTy (HasType.app_nonlinear (HasType.var_nlin hf) (HasType.var_nlin hy))
      (fTy_cod_instantiate (.var y)))

/-- **`fT : * → *`** — the tangent-space dependent type is well-kinded. -/
noncomputable def fT_tvalid {ε : NLCtx} (hf : ε.lookup "f" = some fTy) :
    TValid ε fT (.arrow .base .base) := by
  unfold fT
  refine TValid.piTy {"f"} (TValid.space svR2) (fun y hy => ?_)
  rw [Finset.mem_singleton] at hy
  simp only [Ty.openVar, Ty.openRec, fTAt_openVar]
  exact TValid.space (fTyAt_svalid
    (by rw [Finmap.lookup_insert_of_ne _ (Ne.symm hy)]; exact hf)
    (Finmap.lookup_insert _))

/-- Codomain of `ev` at the bound point: `fT(x)** ⊗ fT(x)*` with `x = bvar 0`. -/
def evCod : Ty := .space (.tprod (.dual (.dual (fTAt 0))) (.dual (fTAt 0)))

/-- The same codomain at a named point. -/
def evCodAt (y : Name) : Ty := .space (.tprod (.dual (.dual (fTyAt y))) (.dual (fTyAt y)))

def evTy : Ty := .piTy (.space R2) evCod

theorem evCod_openVar (y : Name) : Ty.openVar y evCod = evCodAt y := by
  simp [evCod, evCodAt, Ty.openVar, Ty.openRec, Space.openRec, fTAt_openVar]

noncomputable def evTy_tvalid {ε : NLCtx} (hf : ε.lookup "f" = some fTy) :
    TValid ε evTy (.arrow .base .base) := by
  unfold evTy
  refine TValid.piTy {"f"} (TValid.space svR2) (fun y hy => ?_)
  rw [Finset.mem_singleton] at hy
  rw [evCod_openVar]
  have sv : SValid (Finmap.insert y (.space R2) ε) (fTyAt y) :=
    fTyAt_svalid (by rw [Finmap.lookup_insert_of_ne _ (Ne.symm hy)]; exact hf)
      (Finmap.lookup_insert _)
  exact TValid.space (SValid.tprod (SValid.dual (SValid.dual sv)) (SValid.dual sv))

/-- Innermost `λ(z : fT(x)) ⊸ y(z)`; here `x = bvar 2`, `y = bvar 1`, `z = bvar 0`
    (the `llam` annotation sits one level out, so it sees `x` as `bvar 1`). -/
def evInner : Term := .llam (fTAt 1) .real (.appI (fTAt 2) (.bvar 1) (.bvar 0))

/-- `λ(y : fT(x)*) ⊸ λ(z : fT(x)) ⊸ y(z)` with `x = bvar 0` in the annotations. -/
def evOuter : Term := .llam (.dual (fTAt 0)) (.dual (fTAt 0)) evInner

def ev : Term := .nllam (.space R2) evOuter

theorem evOuter_openVar (yx : Name) :
    Term.openVar yx evOuter =
      .llam (.dual (fTyAt yx)) (.dual (fTyAt yx))
        (.llam (fTyAt yx) .real (.appI (fTyAt yx) (.bvar 1) (.bvar 0))) := by
  simp [evOuter, evInner, Term.openVar, Term.openRec, Space.openRec, fTAt_openVar]

/-- **`ev : (x:ℝ²) → fT(x)** ⊗ fT(x)*`**, in any context that binds `f`. -/
noncomputable def ev_hasType {ε : NLCtx} (hf : ε.lookup "f" = some fTy) :
    HasType ∅ ε ev evTy := by
  unfold ev evTy
  refine HasType.nllam {"f"} (evTy_tvalid hf) (fun yx hyx => ?_)
  rw [Finset.mem_singleton] at hyx
  rw [evOuter_openVar, evCod_openVar]
  have hf' : (Finmap.insert yx (.space R2) ε).lookup "f" = some fTy := by
    rw [Finmap.lookup_insert_of_ne _ (Ne.symm hyx)]; exact hf
  have sv : SValid (Finmap.insert yx (.space R2) ε) (fTyAt yx) :=
    fTyAt_svalid hf' (Finmap.lookup_insert _)
  unfold evCodAt
  refine HasType.llam_tensor {"f", yx} (by intro h; cases h) (SValid.dual sv) (SValid.dual sv)
    (fun yy _ => ?_)
  simp only [Term.openVar, Term.openRec, Space.openRec, fTyAt_openRec]
  refine HasType.llam_real {"f", yx, yy} sv (fun yz hyz => ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyz
  simp only [Term.openVar, Term.openRec, fTyAt_openRec]
  rw [pair_ctx yy yz (.dual (fTyAt yx)) (fTyAt yx) (Ne.symm hyz.2.2)]
  exact HasType.app_inner sv (pair_disjoint (Ne.symm hyz.2.2)) HasType.var_lin HasType.var_lin

/-! ### The tangent space at a LINEARLY-given point (source level, via `T-Promote`) -/

/-- The point `p`, supplied linearly: `Δ = {p : ℝ²}`. -/
def pLin : LCtx := Finmap.singleton "p" R2

theorem p_ne_f : ("p" : Name) ≠ "f" := by decide
theorem z_ne_f : ("z" : Name) ≠ "f" := by decide
theorem p_ne_z : ("p" : Name) ≠ "z" := by decide

theorem pLin_toNL_lookup : pLin.toNL.lookup "p" = some (.space R2) :=
  LCtx.toNL_lookup pLin "p" R2 Finmap.lookup_singleton_eq

theorem mem_pLin_toNL {x : Name} (h : x ∈ pLin.toNL) : x = "p" := by
  simpa [pLin, LCtx.mem_toNL_iff, Finmap.mem_singleton] using h

theorem f_not_mem_pLin_toNL : ("f" : Name) ∉ pLin.toNL :=
  fun h => p_ne_f (mem_pLin_toNL h).symm

/-- `T-Promote`'s freshness for `{p}`: `p` names nothing in `∅`, in its own space
    `ℝ²`, or in the (closed) type of `f`. -/
theorem promoteFresh_p : PromoteFresh pLin ∅ εf := by
  refine ⟨?_, ?_, ?_⟩
  · intro y _ x s hx
    rw [Finmap.lookup_empty] at hx
    cases hx
  · intro y _ x s hx
    have hxp : x = "p" := by
      simpa [pLin, Finmap.mem_singleton] using Finmap.mem_of_lookup_eq_some hx
    subst hxp
    have hs : R2 = s := by simpa [pLin, Finmap.lookup_singleton_eq] using hx
    subst hs
    simp [R2, Space.fv]
  · intro y _ x τ hx
    have hxf : x = "f" := by
      simpa [εf, Finmap.mem_singleton] using Finmap.mem_of_lookup_eq_some hx
    subst hxf
    have hτ : fTy = τ := by simpa [εf, Finmap.lookup_singleton_eq] using hx
    subst hτ
    simp [fTy, R2, R3, Ty.fv, Space.fv]

theorem disj_pLin_empty : Finmap.Disjoint pLin (∅ : LCtx) :=
  Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty _)

theorem disj_pLin_εf : Finmap.Disjoint pLin.toNL εf := by
  intro x hx hx'
  have h1 : x = "p" := mem_pLin_toNL hx
  have h2 : x = "f" := by simpa [εf, Finmap.mem_singleton] using hx'
  exact p_ne_f (h1.symm.trans h2)

/-- **`T-Promote` moves the linearly supplied point to the non-linear side.**
    Premise: `{p : ℝ²} ; f ⊢ p : ℝ²` (linear variable); conclusion:
    `∅ ; {p : ℝ²}.toNL ∪ {f} ⊢ p : ℝ²`. -/
noncomputable def p_promoted : HasType ∅ (pLin.toNL ∪ εf) (.var "p") (.space R2) :=
  HasType.promote pLin disj_pLin_empty disj_pLin_εf promoteFresh_p
    (castΔ HasType.var_lin (Finmap.union_empty (s₁ := pLin)).symm)

theorem hf_union : (pLin.toNL ∪ εf).lookup "f" = some fTy := by
  rw [Finmap.lookup_union_right f_not_mem_pLin_toNL]
  exact Finmap.lookup_singleton_eq

/-- **The tangent space at a linearly-given point.**
    `∅ ; {p}.toNL ∪ {f} ⊢ ev(p) : (fT(x)** ⊗ fT(x)*)[x := p]`.
    `app_nonlinear` needs `Δ = ∅` on both sides, so the promoted `p_promoted`
    is the only way to consume the linear point: the derivation MUST go through
    `T-Promote`. -/
noncomputable def tangentAtLinearPoint :
    HasType ∅ (pLin.toNL ∪ εf) (.appN ev (.var "p")) (Ty.instantiate (.var "p") evCod) :=
  HasType.app_nonlinear (ev_hasType hf_union) p_promoted

/-- The instantiated codomain is literally `fT(p)** ⊗ fT(p)*`. -/
theorem instantiate_p_evCod : Ty.instantiate (.var "p") evCod = evCodAt "p" :=
  evCod_openVar "p"

noncomputable def tangentAtLinearPoint' :
    HasType ∅ (pLin.toNL ∪ εf) (.appN ev (.var "p")) (evCodAt "p") :=
  castTy tangentAtLinearPoint instantiate_p_evCod

/-! ### (a) Checked progress on the closed `area` program -/

theorem area_std_valid : BasisValid ∅ (Basis.std areaTy) := by
  unfold areaTy
  exact Basis.stdSpace_valid _ (SValid.tprod (SValid.dual svR2) (SValid.dual svR2))

/-- **`Metatheory.progress` on `area`** at its standard basis, with the trivial
    creation history `ContextHistory.empty`: an end-to-end checked evaluation exists,
    and the selected value's inferers recover its exact realized type. -/
theorem area_progress :
    ∃ v τv, Operational.Term ∅ ∅ ∅ area (Basis.std areaTy) v τv ∧
      ValExpr.inferType v = τv ∧ ValExpr.inferSpaceCtx [] v = ValTy.spaceOf τv :=
  Metatheory.progress Operational.TypedContext.empty
    (castTy area_hasType (Basis.tof_std areaTy).symm) area_std_valid

/-! ### (b) The generalized checked `promote` node with a point-dependent extension -/

/-- The standard basis of `ℝ²`: `⌊1⌋ ⊕ ⌊1⌋`. -/
def bStd : Basis := Basis.stdSpace R2
/-- Its exact realization. -/
def τvR2 : ValTy := .space (.dsum .real .real)
/-- The runtime entry stored for `p`. -/
def vP : ValExpr := .var "p" τvR2
/-- An evaluator holding exactly the promoted point. -/
noncomputable def ΨP : EvalCtx := EvalCtx.extend ∅ "p" bStd vP

/-- **A binding whose TYPE mentions the promoted point**: `z : Img(f(p))`. -/
def zTy : Ty := .space (fTyAt "p")
/-- The post-promotion world extended by that point-dependent binding. -/
def Γext : NLCtx := Finmap.insert "z" zTy εf

theorem tof_bStd : Basis.tof bStd = .space R2 := Basis.tof_stdSpace R2
theorem bStd_valid {Γ : NLCtx} : BasisValid Γ bStd := Basis.stdSpace_valid R2 svR2
theorem bStd_isTyBasis : Basis.IsTyBasis bStd := (Basis.isSpaceBasis_stdSpace R2).toIsTyBasis

/-- Exact realization certificate of `bStd`, in any source context. -/
theorem tyAt_bStd (Γ : NLCtx) (Ψ : EvalCtx) : Operational.TyAt Γ Ψ bStd τvR2 :=
  C.TyAt.space (by simp [bStd, Basis.stdSpace, Basis.tof, Basis.sof, R2]) bStd_valid
    (C.Space.dsum ⟨svR2⟩ .real .real)

theorem lookup_ΨP : EvalCtx.lookup ΨP ("p", bStd) = some vP := by
  simp [ΨP, EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]

/-- The premise: the checked LINEAR variable `p`, in the pre-promotion world `εf`. -/
theorem premise_p : Operational.Term (pLin ∪ ∅) εf ΨP (.var "p") bStd vP τvR2 := by
  rw [Finmap.union_empty]
  exact C.Term.var_lin lookup_ΨP tof_bStd bStd_valid (tyAt_bStd εf ΨP)

theorem hle_ext : NLCtxIncl εf Γext :=
  (NLCtxIncl.refl εf).insert_right
    (show ("z" : Name) ∉ Finmap.singleton "f" fTy by rw [Finmap.mem_singleton]; exact z_ne_f)
    zTy

theorem disj_pLin_Γext : Finmap.Disjoint pLin.toNL Γext := by
  intro x hx hx'
  have h1 : x = "p" := mem_pLin_toNL hx
  subst h1
  simp only [Γext, Finmap.mem_insert, εf, Finmap.mem_singleton] at hx'
  rcases hx' with h | h
  · exact p_ne_z h
  · exact p_ne_f h

theorem lookup_p_ext : (pLin.toNL ∪ Γext).lookup "p" = some (.space R2) := by
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some pLin_toNL_lookup)]
  exact pLin_toNL_lookup

theorem ht_ext : Nonempty (HasType ∅ (pLin.toNL ∪ Γext) (.var "p") (Basis.tof bStd)) :=
  ⟨castTy (HasType.var_nlin lookup_p_ext) tof_bStd.symm⟩

/-- **The generalized checked `promote` node**, concluding in a world that ADDS
    `z : Img(f(p))` — a binding whose type mentions the promoted `p`.  Its
    `PromoteFresh` obligation is against the PREMISE world `εf` only
    (`promoteFresh_p`); nothing about `Γext` has to be fresh for `p`. -/
theorem tangentPromoteNode :
    Operational.Term ∅ (pLin.toNL ∪ Γext) ΨP (.var "p") bStd vP τvR2 :=
  C.Term.promote pLin disj_pLin_empty disj_pLin_Γext promoteFresh_p hle_ext
    ht_ext bStd_valid (tyAt_bStd _ ΨP) premise_p

theorem lookup_p_old : (pLin.toNL ∪ εf).lookup "p" = some (.space R2) := by
  rw [Finmap.lookup_union_left (Finmap.mem_of_lookup_eq_some pLin_toNL_lookup)]
  exact pLin_toNL_lookup

theorem tangentPromoteNode_old :
    Operational.Term ∅ (pLin.toNL ∪ εf) ΨP (.var "p") bStd vP τvR2 :=
  C.Term.promote pLin disj_pLin_empty disj_pLin_εf promoteFresh_p (NLCtxIncl.refl εf)
    ⟨castTy (HasType.var_nlin lookup_p_old) tof_bStd.symm⟩ bStd_valid
    (tyAt_bStd _ ΨP) premise_p

end Examples.Paper
end GLang
