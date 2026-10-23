import GLang.Proofs.Value.Queries.ValueQueryDependencies
import GLang.Proofs.Adequacy.Total.DirectOracleOpenPush

namespace GLang.ValueQueryDependencies
open DirectOracleOpenPush

def pushLast (σ : ValTy) : Node → Node
  | .space Γ s => .space (Γ ++ [σ]) s
  | .type Γ t => .type (Γ ++ [σ]) t
  | .expr Γ e => .expr (Γ ++ [σ]) e

def openLast (x : VName) (σ : ValTy) : Node → Node
  | .space Γ s => .space (ValTy.closePrefix (.var x σ) Γ)
      (ValSpace.openRec Γ.length (.var x σ) s)
  | .type Γ t => .type (ValTy.closePrefix (.var x σ) Γ)
      (ValTy.openRec Γ.length (.var x σ) t)
  | .expr Γ e => .expr (ValTy.closePrefix (.var x σ) Γ)
      (ValExpr.openRec Γ.length (.var x σ) e)

/-- Closing a fresh named parameter into the bound telescope preserves a
finite dependency bound. This supports the cofinite typing rules. -/
theorem Bounded.of_openLast {σ : ValTy} (hσ : ValTy.lc σ) (x : VName)
    {n : Nat} (root : Node) (h : Bounded n (openLast x σ root)) :
    Bounded n (pushLast σ root) := by
  induction n generalizing root with
  | zero => exact False.elim h
  | succ n ih =>
    cases root with
    | space Γ s =>
      cases s <;>
        simp only [openLast, pushLast, ValSpace.openRec, Bounded, children,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, IsEmpty.forall_iff, implies_true, and_true] at h ⊢
      case dsum a b => exact ⟨ih (.space Γ a) h.1, ih (.space Γ b) h.2⟩
      case tprod a b => exact ⟨ih (.space Γ a) h.1, ih (.space Γ b) h.2⟩
      case ffs p s e => exact ⟨ih (.space Γ s) h.1, ih (.expr Γ e) h.2⟩
    | type Γ t =>
      cases t with
      | space s =>
        simp only [openLast, pushLast, ValTy.openRec, Bounded, children,
          List.mem_singleton, forall_eq] at h ⊢
        exact ih (.space Γ s) h
      | piTy d c =>
        simp only [openLast, pushLast, ValTy.openRec, Bounded, children,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at h ⊢
        refine ⟨ih (.type Γ d) h.1, ?_⟩
        exact ih (.type (d :: Γ) c) h.2
    | expr Γ e =>
      have hi := inferTypeCtxRaised_valueOpenPush (y := x) hσ Γ e
      have hs := inferSpaceCtx_valueOpenPush (y := x) hσ Γ e
      change _ at hi hs
      simp only [openLast, pushLast, Bounded, children,
        List.mem_cons, forall_eq_or_imp] at h ⊢
      rw [hi, hs] at h
      refine ⟨ih (.type Γ (ValExpr.inferTypeCtx (Γ ++ [σ]) e)) h.1,
        ih (.space Γ (ValExpr.inferSpaceCtx (Γ ++ [σ]) e)) h.2.1, ?_⟩
      have hc := h.2.2
      cases e <;>
        simp only [ValExpr.openRec, exprChildren, List.mem_cons,
          List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          IsEmpty.forall_iff, implies_true, and_true] at hc ⊢
      case vlam d c body =>
        exact ⟨ih (.type Γ d) hc.1, ih (.type (d :: Γ) c) hc.2.1,
          ih (.expr (d :: Γ) body) hc.2.2⟩
      case vsum s es =>
        refine ⟨ih (.space Γ s) hc.1, ?_⟩
        intro child hm
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        apply ih (.expr Γ e)
        apply hc.2
        exact List.mem_map.mpr ⟨ValExpr.openRec Γ.length (.var x σ) e,
          by simpa only [ValExpr.openRecList_eq_map] using List.mem_map.mpr ⟨e, he, rfl⟩, rfl⟩
      all_goals first
        | exact ih (.space Γ _) hc
        | exact ih (.expr Γ _) hc
        | exact ⟨ih (.expr Γ _) hc.1, ih (.expr Γ _) hc.2⟩
        | exact ⟨ih (.space Γ _) hc.1,
            ih (.expr Γ _) hc.2.1, ih (.expr Γ _) hc.2.2⟩
        | exact ⟨ih (.space Γ _) hc.1, ih (.space Γ _) hc.2.1,
            ih (.expr Γ _) hc.2.2.1, ih (.expr Γ _) hc.2.2.2⟩
        | exact ⟨ih (.expr Γ _) hc.1,
            ih (.type Γ _) hc.2.1, ih (.type Γ _) hc.2.2⟩
        | exact ⟨ih (.expr Γ _) hc.1,
            ih (.expr Γ _) hc.2.1, ih (.expr Γ _) hc.2.2⟩

theorem Bounded.to_openLast {σ : ValTy} (hσ : ValTy.lc σ) (x : VName)
    {n : Nat} (root : Node) (h : Bounded n (pushLast σ root)) :
    Bounded n (openLast x σ root) := by
  induction n generalizing root with
  | zero => exact False.elim h
  | succ n ih =>
    cases root with
    | space Γ s =>
      cases s <;>
        simp only [openLast, pushLast, ValSpace.openRec, Bounded, children,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq, IsEmpty.forall_iff, implies_true, and_true] at h ⊢
      case dsum a b => exact ⟨ih (.space Γ a) h.1, ih (.space Γ b) h.2⟩
      case tprod a b => exact ⟨ih (.space Γ a) h.1, ih (.space Γ b) h.2⟩
      case ffs p s e => exact ⟨ih (.space Γ s) h.1, ih (.expr Γ e) h.2⟩
    | type Γ t =>
      cases t with
      | space s =>
        simp only [openLast, pushLast, ValTy.openRec, Bounded, children,
          List.mem_singleton, forall_eq] at h ⊢
        exact ih (.space Γ s) h
      | piTy d c =>
        simp only [openLast, pushLast, ValTy.openRec, Bounded, children,
          List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at h ⊢
        refine ⟨ih (.type Γ d) h.1, ?_⟩
        exact ih (.type (d :: Γ) c) h.2
    | expr Γ e =>
      have hi := inferTypeCtxRaised_valueOpenPush (y := x) hσ Γ e
      have hs := inferSpaceCtx_valueOpenPush (y := x) hσ Γ e
      change _ at hi hs
      simp only [openLast, pushLast, Bounded, children,
        List.mem_cons, forall_eq_or_imp] at h ⊢
      rw [hi, hs]
      refine ⟨ih (.type Γ (ValExpr.inferTypeCtx (Γ ++ [σ]) e)) h.1,
        ih (.space Γ (ValExpr.inferSpaceCtx (Γ ++ [σ]) e)) h.2.1, ?_⟩
      have hc := h.2.2
      cases e <;>
        simp only [ValExpr.openRec, exprChildren, List.mem_cons,
          List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          IsEmpty.forall_iff, implies_true, and_true] at hc ⊢
      case vlam d c body =>
        exact ⟨ih (.type Γ d) hc.1, ih (.type (d :: Γ) c) hc.2.1,
          ih (.expr (d :: Γ) body) hc.2.2⟩
      case bvar i => by_cases hi : i = Γ.length <;> simp [hi, exprChildren]
      case vsum s es =>
        refine ⟨ih (.space Γ s) hc.1, ?_⟩
        intro child hm
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
        rw [ValExpr.openRecList_eq_map] at he
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
        exact ih (.expr Γ a) (hc.2 _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
      all_goals first
        | exact ih (.space Γ _) hc
        | exact ih (.expr Γ _) hc
        | exact ⟨ih (.expr Γ _) hc.1, ih (.expr Γ _) hc.2⟩
        | exact ⟨ih (.space Γ _) hc.1,
            ih (.expr Γ _) hc.2.1, ih (.expr Γ _) hc.2.2⟩
        | exact ⟨ih (.space Γ _) hc.1, ih (.space Γ _) hc.2.1,
            ih (.expr Γ _) hc.2.2.1, ih (.expr Γ _) hc.2.2.2⟩
        | exact ⟨ih (.expr Γ _) hc.1,
            ih (.type Γ _) hc.2.1, ih (.type Γ _) hc.2.2⟩
        | exact ⟨ih (.expr Γ _) hc.1,
            ih (.expr Γ _) hc.2.1, ih (.expr Γ _) hc.2.2⟩

theorem Finite.of_openLast {σ : ValTy} (hσ : ValTy.lc σ) (x : VName)
    (root : Node) (h : Finite (openLast x σ root)) : Finite (pushLast σ root) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.of_openLast hσ x root⟩

/-- Opening a bound parameter at a variable preserves the exact least
finite dependency bound, including rejection of uncertified raw syntax. -/
theorem rank_openLast {σ : ValTy} (hσ : ValTy.lc σ) (x : VName) (root : Node) :
    rank (openLast x σ root) = rank (pushLast σ root) := by
  classical
  by_cases ho : Finite (openLast x σ root)
  · have hp := ho.of_openLast hσ x root
    apply Nat.le_antisymm
    · exact rank_le ((rank_spec hp).to_openLast hσ x root)
    · exact rank_le ((rank_spec ho).of_openLast hσ x root)
  · have hp : ¬ Finite (pushLast σ root) := by
      rintro ⟨n, hn⟩
      exact ho ⟨n, hn.to_openLast hσ x root⟩
    simp only [rank, dif_neg ho, dif_neg hp]

end GLang.ValueQueryDependencies
