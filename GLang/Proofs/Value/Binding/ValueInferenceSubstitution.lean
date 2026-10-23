import GLang.Value.Inference
import GLang.Proofs.Value.Binding.ValueBeta

set_option maxHeartbeats 3000000
namespace GLang

def InferTypeSubstAt (x : VName) (u e : ValExpr) : Prop :=
  ValExpr.inferType (ValExpr.subst x u e) = ValTy.subst x u (ValExpr.inferType e)

private theorem spaceOf_subst_type (x : VName) (u : ValExpr) (t : ValTy) :
    (ValTy.subst x u t).spaceOf = ValSpace.subst x u t.spaceOf := by
  cases t <;> rfl

theorem inferType_subst_bvar {x : VName} {u : ValExpr} (hu : u.lc) {i : Nat}
    : InferTypeSubstAt x u (.bvar i) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_vlam {x : VName} {u : ValExpr} (hu : u.lc) {t0 : ValTy} {t1 : ValTy} {e : ValExpr}
    : InferTypeSubstAt x u (.vlam t0 t1 e) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_zero {x : VName} {u : ValExpr} (hu : u.lc) {s : ValSpace}
    : InferTypeSubstAt x u (.zero s) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_rlit {x : VName} {u : ValExpr} (hu : u.lc) {r : ℝ}
    : InferTypeSubstAt x u (.rlit r) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_scale {x : VName} {u : ValExpr} (hu : u.lc) {e0 : ValExpr} {e1 : ValExpr}
    (h_e1 : InferTypeSubstAt x u e1)
    : InferTypeSubstAt x u (.scale e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e1, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_dsumE {x : VName} {u : ValExpr} (hu : u.lc) {e0 : ValExpr} {e1 : ValExpr}
    (h_e0 : InferTypeSubstAt x u e0)
    (h_e1 : InferTypeSubstAt x u e1)
    : InferTypeSubstAt x u (.dsumE e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e0, h_e1, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_tprodE {x : VName} {u : ValExpr} (hu : u.lc) {e0 : ValExpr} {e1 : ValExpr}
    (h_e0 : InferTypeSubstAt x u e0)
    (h_e1 : InferTypeSubstAt x u e1)
    : InferTypeSubstAt x u (.tprodE e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e0, h_e1, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_appV {x : VName} {u : ValExpr} (hu : u.lc) {e0 : ValExpr} {e1 : ValExpr}
    (h_e0 : InferTypeSubstAt x u e0)
    : InferTypeSubstAt x u (.appV e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e0, spaceOf_subst_type]
  cases hf : ValExpr.inferType e0 <;>
    simp only [ValTy.subst, ValSpace.subst, GLang.ValTy.subst_applyCodomain x u hu]

theorem inferType_subst_vkrn {x : VName} {u : ValExpr} (hu : u.lc) {e0 : ValExpr} {e1 : ValExpr}
    (h_e0 : InferTypeSubstAt x u e0)
    (h_e1 : InferTypeSubstAt x u e1)
    : InferTypeSubstAt x u (.vkrn e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e0, h_e1, spaceOf_subst_type]
  all_goals cases he_e0 : ValExpr.inferType e0 with
  | space ss =>
    cases ss
    all_goals cases he_e1 : ValExpr.inferType e1 with
    | space ss =>
      cases ss
      all_goals simp_all only [ValTy.subst, ValSpace.subst]
    | piTy dd cc =>
      all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals cases he_e1 : ValExpr.inferType e1 with
    | space ss =>
      cases ss
      all_goals simp_all only [ValTy.subst, ValSpace.subst]
    | piTy dd cc =>
      all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_vblk {x : VName} {u : ValExpr} (hu : u.lc) {e0 : ValExpr} {e1 : ValExpr}
    (h_e0 : InferTypeSubstAt x u e0)
    (h_e1 : InferTypeSubstAt x u e1)
    : InferTypeSubstAt x u (.vblk e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e0, h_e1, spaceOf_subst_type]
  all_goals cases he_e0 : ValExpr.inferType e0 with
  | space ss =>
    cases ss
    all_goals cases he_e1 : ValExpr.inferType e1 with
    | space ss =>
      cases ss
      all_goals simp_all only [ValTy.subst, ValSpace.subst]
    | piTy dd cc =>
      all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals cases he_e1 : ValExpr.inferType e1 with
    | space ss =>
      cases ss
      all_goals simp_all only [ValTy.subst, ValSpace.subst]
    | piTy dd cc =>
      all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_rrefRep {x : VName} {u : ValExpr} (hu : u.lc) {e0 : ValExpr} {e1 : ValExpr}
    (h_e1 : InferTypeSubstAt x u e1)
    : InferTypeSubstAt x u (.rrefRep e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e1, spaceOf_subst_type]
  all_goals cases he_e1 : ValExpr.inferType e1 with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_vadd {x : VName} {u : ValExpr} (hu : u.lc) {s : ValSpace} {e0 : ValExpr} {e1 : ValExpr}
    : InferTypeSubstAt x u (.vadd s e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_delta {x : VName} {u : ValExpr} (hu : u.lc) {i : Nat} {s : ValSpace}
    : InferTypeSubstAt x u (.delta i s) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_idelta {x : VName} {u : ValExpr} (hu : u.lc) {s : ValSpace}
    : InferTypeSubstAt x u (.idelta s) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_vsum (x : VName) (u : ValExpr) (hu : u.lc) (s : ValSpace) (es : List ValExpr)
    (hes : ∀ e ∈ es, InferTypeSubstAt x u e) :
    InferTypeSubstAt x u (.vsum s es) := by
  cases es with
  | nil => rfl
  | cons e es => exact hes e (by simp)

theorem inferType_subst_ttv {x : VName} {u : ValExpr} (hu : u.lc) {s : ValSpace} {e0 : ValExpr} {e1 : ValExpr}
    (h_e0 : InferTypeSubstAt x u e0)
    : InferTypeSubstAt x u (.ttv s e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e0, spaceOf_subst_type]
  all_goals cases he_e0 : ValExpr.inferType e0 with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_mtm {x : VName} {u : ValExpr} (hu : u.lc) {i : Nat} {j : Nat} {s0 : ValSpace} {s1 : ValSpace} {e0 : ValExpr} {e1 : ValExpr}
    (h_e0 : InferTypeSubstAt x u e0)
    (h_e1 : InferTypeSubstAt x u e1)
    : InferTypeSubstAt x u (.mtm i j s0 s1 e0 e1) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e0, h_e1, spaceOf_subst_type]
  all_goals cases he_e0 : ValExpr.inferType e0 with
  | space ss =>
    cases ss
    all_goals cases he_e1 : ValExpr.inferType e1 with
    | space ss =>
      cases ss
      all_goals simp_all only [ValTy.subst, ValSpace.subst]
    | piTy dd cc =>
      all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals cases he_e1 : ValExpr.inferType e1 with
    | space ss =>
      cases ss
      all_goals simp_all only [ValTy.subst, ValSpace.subst]
    | piTy dd cc =>
      all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_reshap {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr} {t : ValTy} {t0 : ValTy}
    : InferTypeSubstAt x u (.reshap e t t0) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, spaceOf_subst_type]
  all_goals try rfl
  all_goals repeat' first
    | (split <;> simp_all only [ValTy.subst, ValSpace.subst])
    | (simp_all only [ValTy.subst, ValSpace.subst])
  all_goals try rfl

theorem inferType_subst_vtrans {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.vtrans e) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_pinv {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.pinv e) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_inv {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.inv e) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_svds {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.svds e) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_gsvdS {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr} {a : ValExpr} {b : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.gsvdS e a b) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_gsvdU {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr} {a : ValExpr} {b : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.gsvdU e a b) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_gsvdUI {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr} {a : ValExpr} {b : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.gsvdUI e a b) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_gsvdV {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr} {a : ValExpr} {b : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.gsvdV e a b) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_gsvdVI {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr} {a : ValExpr} {b : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.gsvdVI e a b) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

theorem inferType_subst_gpinv {x : VName} {u : ValExpr} (hu : u.lc) {e : ValExpr} {a : ValExpr} {b : ValExpr}
    (h_e : InferTypeSubstAt x u e)
    : InferTypeSubstAt x u (.gpinv e a b) := by
  unfold InferTypeSubstAt at *
  simp only [ValExpr.subst, ValExpr.inferType, h_e, spaceOf_subst_type]
  all_goals cases he_e : ValExpr.inferType e with
  | space ss =>
    cases ss
    all_goals simp_all only [ValTy.subst, ValSpace.subst]
  | piTy dd cc =>
    all_goals simp_all only [ValTy.subst, ValSpace.subst]

/-- Compile-time argument conversion commutes with substitution when the
inferred operand types do. -/
theorem ValExpr.subst_applyValue {x : VName} {u f a : ValExpr}
    (hf : InferTypeSubstAt x u f) (ha : InferTypeSubstAt x u a) :
    ValExpr.subst x u (ValExpr.applyValue f a) =
      ValExpr.applyValue (ValExpr.subst x u f) (ValExpr.subst x u a) := by
  unfold InferTypeSubstAt at hf ha
  have hd : (ValTy.subst x u f.inferType).domain = ValTy.subst x u f.inferType.domain := by
    cases f.inferType <;> rfl
  simp only [ValExpr.applyValue, ValExpr.subst, hf, ha, hd]

/-- A compiler-selected result conversion commutes with substitution. -/
theorem ValExpr.subst_applyAt {x : VName} {u f a : ValExpr} {t : ValTy}
    (hu : u.lc) (hf : InferTypeSubstAt x u f) (ha : InferTypeSubstAt x u a) :
    ValExpr.subst x u (.applyAt f a t) =
      .applyAt (ValExpr.subst x u f) (ValExpr.subst x u a) (ValTy.subst x u t) := by
  have hi : InferTypeSubstAt x u (.applyValue f a) := inferType_subst_appV hu hf
  unfold InferTypeSubstAt at hi
  rw [ValExpr.subst_applyValue hf ha] at hi
  simp only [ValExpr.applyAt, ValExpr.subst, ValExpr.subst_applyValue hf ha]
  rw [hi]

end GLang
