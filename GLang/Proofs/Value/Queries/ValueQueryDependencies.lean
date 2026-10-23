import GLang.Value.Inference

/-! Syntax-directed dependencies of value evaluation, including the types
computed by inference. Unlike a size measure on raw syntax, this graph does
not assume that substitution preserves an expression's syntactic depth.
Finite dependency bounds are certificates to be derived from typing.
-/

namespace GLang.ValueQueryDependencies

inductive Node where
  | space : List ValTy → ValSpace → Node
  | type : List ValTy → ValTy → Node
  | expr : List ValTy → ValExpr → Node

/-- Explicit annotations and operand evaluations; inference dependencies are
added separately by `children`. The bound-type telescope follows binders. -/
def exprChildren (Γ : List ValTy) : ValExpr → List Node
  | .bvar _ | .var _ _ | .rlit _ => []
  | .zero s | .delta _ s | .idelta s => [.space Γ s]
  | .scale a b | .dsumE a b | .tprodE a b | .vkrn a b | .vblk a b |
      .rrefRep a b | .appV a b => [.expr Γ a, .expr Γ b]
  | .vadd s a b | .ttv s a b => [.space Γ s, .expr Γ a, .expr Γ b]
  | .mtm _ _ s t a b => [.space Γ s, .space Γ t, .expr Γ a, .expr Γ b]
  | .vsum s es => .space Γ s :: es.map (.expr Γ)
  | .vlam d c e => [.type Γ d, .type (d :: Γ) c, .expr (d :: Γ) e]
  | .reshap e t s => [.expr Γ e, .type Γ t, .type Γ s]
  | .vtrans e | .pinv e | .inv e | .svds e => [.expr Γ e]
  | .gsvdS e a b | .gsvdU e a b | .gsvdUI e a b |
      .gsvdV e a b | .gsvdVI e a b | .gpinv e a b =>
      [.expr Γ e, .expr Γ a, .expr Γ b]

/-- A conservative list of the observations needed by a node. Inference
edges are explicit graph edges, not annotations added to application syntax. -/
def children : Node → List Node
  | .space Γ (.dsum s t) | .space Γ (.tprod s t) => [.space Γ s, .space Γ t]
  | .space Γ (.ffs _ s e) => [.space Γ s, .expr Γ e]
  | .space _ .empty | .space _ .real => []
  | .type Γ (.space s) => [.space Γ s]
  | .type Γ (.piTy d c) => [.type Γ d, .type (d :: Γ) c]
  | .expr Γ e =>
      .type Γ (ValExpr.inferTypeCtx Γ e) ::
      .space Γ (ValExpr.inferSpaceCtx Γ e) :: exprChildren Γ e

/-- Every path from this node has fewer than `n` dependency edges. Zero is
deliberately impossible, so each child has a strictly smaller bound. -/
def Bounded : Nat → Node → Prop
  | 0, _ => False
  | n + 1, root => ∀ child ∈ children root, Bounded n child

def Finite (root : Node) : Prop := ∃ n, Bounded n root

theorem Bounded.mono {n m : Nat} {root : Node}
    (h : Bounded n root) (hnm : n ≤ m) : Bounded m root := by
  induction n generalizing m root with
  | zero => exact False.elim h
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      intro child hc
      exact ih (h child hc) (by omega)

private theorem finite_list_bound (nodes : List Node)
    (h : ∀ node ∈ nodes, Finite node) :
    ∃ n, ∀ node ∈ nodes, Bounded n node := by
  induction nodes with
  | nil => exact ⟨0, by simp⟩
  | cons node nodes ih =>
    obtain ⟨n, hn⟩ := h node (by simp)
    obtain ⟨m, hm⟩ := ih (fun q hq => h q (by simp [hq]))
    refine ⟨max n m, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hn.mono (Nat.le_max_left _ _)
    · exact (hm q hq).mono (Nat.le_max_right _ _)

theorem Finite.intro {root : Node}
    (h : ∀ child ∈ children root, Finite child) : Finite root := by
  obtain ⟨n, hn⟩ := finite_list_bound (children root) h
  exact ⟨n + 1, hn⟩

theorem Finite.child {root child : Node} (h : Finite root)
    (hc : child ∈ children root) : Finite child := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => exact False.elim hn
  | succ n => exact ⟨n, hn child hc⟩

/-- The least certified dependency bound. Uncertified raw syntax gets zero;
no unfolding theorem may discard the recursive guard there. -/
noncomputable def rank (root : Node) : Nat := by
  classical
  exact if h : Finite root then Nat.find h else 0

theorem rank_spec {root : Node} (h : Finite root) : Bounded (rank root) root := by
  classical
  simpa only [rank, dif_pos h] using Nat.find_spec h

theorem finite_iff_rank_pos (root : Node) : Finite root ↔ 0 < rank root := by
  classical
  constructor
  · intro h
    have hs := rank_spec h
    cases hr : rank root with
    | zero => rw [hr] at hs; exact False.elim hs
    | succ n => omega
  · intro h
    by_contra hn
    simp only [rank, dif_neg hn] at h
    omega

theorem rank_le {root : Node} {n : Nat} (h : Bounded n root) : rank root ≤ n := by
  classical
  have hf : Finite root := ⟨n, h⟩
  simpa only [rank, dif_pos hf] using Nat.find_min' hf h

theorem rank_child_lt {root child : Node} (h : Finite root)
    (hc : child ∈ children root) : rank child < rank root := by
  have hr := rank_spec h
  cases heq : rank root with
  | zero => rw [heq] at hr; exact False.elim hr
  | succ n =>
    rw [heq] at hr
    exact Nat.lt_succ_of_le (rank_le (hr child hc))

theorem finite_iff_children (root : Node) :
    Finite root ↔ ∀ child ∈ children root, Finite child :=
  ⟨fun h _ hc => h.child hc, Finite.intro⟩

theorem Finite.inferType {Γ : List ValTy} {e : ValExpr}
    (h : Finite (.expr Γ e)) : Finite (.type Γ (ValExpr.inferTypeCtx Γ e)) :=
  h.child (by simp [children])

theorem Finite.inferSpace {Γ : List ValTy} {e : ValExpr}
    (h : Finite (.expr Γ e)) : Finite (.space Γ (ValExpr.inferSpaceCtx Γ e)) :=
  h.child (by simp [children])

theorem Finite.exprChild {Γ : List ValTy} {e : ValExpr} {child : Node}
    (h : Finite (.expr Γ e)) (hc : child ∈ exprChildren Γ e) : Finite child :=
  h.child (by simp only [children, List.mem_cons]; tauto)

theorem Finite.real {Γ : List ValTy} : Finite (.space Γ .real) :=
  .intro (by simp [children])

theorem Finite.empty {Γ : List ValTy} : Finite (.space Γ .empty) :=
  .intro (by simp [children])

theorem Finite.dsum {Γ : List ValTy} {a b : ValSpace}
    (ha : Finite (.space Γ a)) (hb : Finite (.space Γ b)) :
    Finite (.space Γ (.dsum a b)) :=
  .intro (by simpa only [children, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] using And.intro ha hb)

theorem Finite.tprod {Γ : List ValTy} {a b : ValSpace}
    (ha : Finite (.space Γ a)) (hb : Finite (.space Γ b)) :
    Finite (.space Γ (.tprod a b)) :=
  .intro (by simpa only [children, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] using And.intro ha hb)

theorem Finite.ffs {Γ : List ValTy} {p : ValFFSProp} {s : ValSpace} {e : ValExpr}
    (hs : Finite (.space Γ s)) (he : Finite (.expr Γ e)) :
    Finite (.space Γ (.ffs p s e)) :=
  .intro (by simpa only [children, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] using And.intro hs he)

theorem Finite.space {Γ : List ValTy} {s : ValSpace}
    (hs : Finite (.space Γ s)) : Finite (.type Γ (.space s)) :=
  .intro (by simpa only [children, List.mem_singleton, forall_eq] using hs)

theorem Finite.space_inv {Γ : List ValTy} {s : ValSpace}
    (hs : Finite (.type Γ (.space s))) : Finite (.space Γ s) :=
  hs.child (by simp [children])

theorem Finite.tensor_inv {Γ : List ValTy} {s t : ValSpace}
    (hs : Finite (.type Γ (.space (.tprod s t)))) :
    Finite (.space Γ s) ∧ Finite (.space Γ t) :=
  ⟨hs.space_inv.child (by simp [children]), hs.space_inv.child (by simp [children])⟩

theorem Finite.spaceOf {Γ : List ValTy} {t : ValTy}
    (h : Finite (.type Γ t)) : Finite (.space Γ t.spaceOf) := by
  cases t with
  | space s => exact h.space_inv
  | piTy d c => exact .empty

theorem Finite.piTy {Γ : List ValTy} {d c : ValTy}
    (hd : Finite (.type Γ d)) (hc : Finite (.type (d :: Γ) c)) :
    Finite (.type Γ (.piTy d c)) :=
  .intro (by simpa only [children, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq] using And.intro hd hc)

end GLang.ValueQueryDependencies
