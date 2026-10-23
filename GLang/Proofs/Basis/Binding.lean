import GLang.Annotated.BasisDenotation

/-! Frame projection and free-variable/substitution lemmas for bases. -/
namespace GLang

@[simp] theorem denotBasis_frame_domainBasis (σ : DEnv) (b₀ b₁ : Basis) :
    (denotBasis σ (.frame b₀ b₁)).domainBasis = denotBasis σ b₀ := by
  rw [denotBasis]; rfl

/-! ## FV lemmas for `Basis`.

These lemmas establish the FV/typing consistency that backs the
tightened `BasisValid` predicate. The key claims are:

  * `Basis.fv_sof_subset` : `Space.fv (Basis.sof b) ⊆ Basis.fv b`.
    The `.image b` clause of `BasisValid` references `(s₀, s₁, e)`
    extracted from `Basis.sof b`'s `.coker` shape — this lemma
    certifies those names are already in `Basis.fv (.image b) = Basis.fv b`.

  * `Basis.fv_tof_subset` : `Ty.fv (Basis.tof b) ⊆ Basis.fv b`.
    Backs the `.frame` clause's `TValid ε (.piTy x (tof b₀) (tof b₁)) ...`
    premise.

  * `Basis.fv_subst` : `Basis.fv (Basis.subst x v b) ⊆ Basis.fv b ∪ Term.fv v`.
    The basis-level analogue of the (currently un-stated) syntactic
    `Space.fv_subst` / `Term.fv_subst` / `Ty.fv_subst` lemmas. We
    bundle the helpers locally since they're not used elsewhere yet. -/

/-! ### Helper: `fv_subst` for `Space` / `Ty` / `Term`. -/

theorem Space.fv_subst (x : Name) (v : Term) (s : Space) :
    Space.fv (Space.subst x v s) ⊆ Space.fv s ∪ Term.fv v :=
  Space.fv_subst_subset x v s

theorem Ty.fv_subst (x : Name) (v : Term) (τ : Ty) :
    Ty.fv (Ty.subst x v τ) ⊆ Ty.fv τ ∪ Term.fv v :=
  Ty.fv_subst_subset x v τ

theorem Term.fv_subst (x : Name) (v : Term) (e : Term) :
    Term.fv (Term.subst x v e) ⊆ Term.fv e ∪ Term.fv v :=
  Term.fv_subst_subset x v e

/-! ### Basis-side FV stability. -/

/-- `Space.fv (Basis.sof b) ⊆ Basis.fv b`.

    All free variables of a basis's space-of are already free in the
    basis. This is what makes the `.image b` clause of `BasisValid`
    safe: when `BasisValid` extracts `(s₀, s₁, e)` from `sof b`'s
    `.coker` shape, those names live in `Basis.fv b = Basis.fv (.image b)`. -/
theorem Basis.fv_sof_subset : ∀ (b : Basis), Space.fv (Basis.sof b) ⊆ Basis.fv b
  | .empty => by simp [Basis.sof, Basis.fv, Space.fv]
  | .one   => by simp [Basis.sof, Basis.fv, Space.fv]
  | .dual b => by
      unfold Basis.sof Basis.fv Space.fv
      exact Basis.fv_sof_subset b
  | .dsum b₀ b₁ => by
      unfold Basis.sof Basis.fv Space.fv
      exact Finset.union_subset_union (Basis.fv_sof_subset b₀) (Basis.fv_sof_subset b₁)
  | .tprod b₀ b₁ => by
      unfold Basis.sof Basis.fv Space.fv
      exact Finset.union_subset_union (Basis.fv_sof_subset b₀) (Basis.fv_sof_subset b₁)
  | .proj s b₀ b₁ => by
      unfold Basis.sof Basis.fv
      exact (Finset.subset_union_left).trans Finset.subset_union_left
  | .image b => by
      unfold Basis.sof Basis.fv
      have ih := Basis.fv_sof_subset b
      -- Split on `Basis.sof b`. Only the `.coker` shape produces a
      -- nonempty FV; the others reduce to `Space.fv .empty = ∅`.
      cases h : Basis.sof b with
      | empty       => simp [Space.fv]
      | real        => simp [Space.fv]
      | dual _      => simp [Space.fv]
      | dsum _ _    => simp [Space.fv]
      | tprod _ _   => simp [Space.fv]
      | ker _ _ _   => simp [Space.fv]
      | coker s₀ s₁ e =>
          -- `Space.fv (.img s₀ s₁ e) = Space.fv (.coker s₀ s₁ e) = Space.fv (sof b)`.
          show Space.fv (.img s₀ s₁ e) ⊆ Basis.fv b
          have : Space.fv (.img s₀ s₁ e) = Space.fv (Basis.sof b) := by
            rw [h]
            rfl
          rw [this]
          exact ih
      | img _ _ _   => simp [Space.fv]
      | coimg _ _ _ => simp [Space.fv]
  | .terms s _ b => by
      unfold Basis.sof Basis.fv
      -- Space.fv (sof b) ⊆ Basis.fv b ⊆ Space.fv s ∪ Basis.fv b ⊆
      --   (Space.fv s ∪ Basis.fv b) ∪ es.foldr.
      exact (Basis.fv_sof_subset b).trans <|
        Finset.subset_union_right.trans Finset.subset_union_left
  | .frame _ _ => by
      unfold Basis.sof
      simp [Space.fv]

/-- `Ty.fv (Basis.tof b) ⊆ Basis.fv b`.

    The type-of of a basis only references variables already free in
    the basis. Backs the `.frame` clause of `BasisValid` (which embeds
    `TValid ε (.piTy x (tof b₀) (tof b₁)) ...`). -/
theorem Basis.fv_tof_subset : ∀ (b : Basis), Ty.fv (Basis.tof b) ⊆ Basis.fv b
  | .empty => by unfold Basis.tof Ty.fv; exact Basis.fv_sof_subset _
  | .one   => by unfold Basis.tof Ty.fv; exact Basis.fv_sof_subset _
  | .dual b => by unfold Basis.tof Ty.fv; exact Basis.fv_sof_subset _
  | .dsum _ _ => by unfold Basis.tof Ty.fv; exact Basis.fv_sof_subset _
  | .tprod _ _ => by unfold Basis.tof Ty.fv; exact Basis.fv_sof_subset _
  | .proj _ _ _ => by unfold Basis.tof Ty.fv; exact Basis.fv_sof_subset _
  | .image _ => by unfold Basis.tof Ty.fv; exact Basis.fv_sof_subset _
  | .terms _ _ _ => by unfold Basis.tof Ty.fv; exact Basis.fv_sof_subset _
  | .frame b₀ b₁ => by
      unfold Basis.tof Ty.fv Basis.fv
      exact Finset.union_subset_union (Basis.fv_tof_subset b₀) (Basis.fv_tof_subset b₁)

/-! ### `Basis.fv_subst`. -/

/-- `Basis.fv (Basis.subst x v b) ⊆ Basis.fv b ∪ Term.fv v`.

    Substitution can only introduce variables from `Term.fv v` on top of
    those already free in the basis. Mirrors the (locally proven)
    `Space.fv_subst` / `Term.fv_subst` / `Ty.fv_subst` lemmas. -/
theorem Basis.fv_subst (x : Name) (v : Term) (b : Basis) :
    Basis.fv (Basis.subst x v b) ⊆ Basis.fv b ∪ Term.fv v :=
  Basis.fv_subst_subset x v b

/-! ### `BasisValid`-irrelevance for FV-fresh substitutions.

When `x ∉ Basis.fv b`, `Basis.subst x v b = b` by
`Basis.subst_of_not_mem_fv`, so `BasisValid` is invariant under such
substitutions. This is the basis-level analogue of the trivial
substitution-irrelevance pattern. -/

theorem Basis.BasisValid_subst_of_not_mem_fv {ε : NLCtx} {x : Name} {v : Term}
    {b : Basis} (h : x ∉ Basis.fv b) :
    Basis.BasisValid ε b ↔ Basis.BasisValid ε (Basis.subst x v b) := by
  rw [Basis.subst_of_not_mem_fv x v b h]

end GLang
