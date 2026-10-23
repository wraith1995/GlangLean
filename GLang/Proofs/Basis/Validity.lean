import GLang.Annotated.BasisJudgments

/-! Basis validity inversions, standard bases, and binding properties. -/
namespace GLang

theorem Basis.FFSMatrixCompatible.tof_eq_space {b : Basis}
    (h : Basis.FFSMatrixCompatible b) :
    Basis.tof b = .space (Basis.sof b) := by
  obtain ⟨b₀, b₁, rfl⟩ := h
  rfl

/-- Matrix compatibility is preserved by source substitution. -/
theorem Basis.FFSMatrixCompatible.subst {b : Basis}
    (h : Basis.FFSMatrixCompatible b) (x : Name) (e : Term) :
    Basis.FFSMatrixCompatible (Basis.subst x e b) := by
  obtain ⟨b₀, b₁, rfl⟩ := h
  exact ⟨Basis.subst x e b₀, Basis.subst x e b₁, rfl⟩

/-- A basis whose exposed type is a space has that space as its syntactic
    `sof`. -/
theorem Basis.sof_eq_of_tof_eq_space {b : Basis} {s : Space}
    (h : Basis.tof b = .space s) : Basis.sof b = s := by
  cases b <;> simp [Basis.tof, Basis.sof] at h ⊢ <;> assumption

/-- `Basis.openVar` preserves `Basis.size` (opening swaps a `bvar` for a `var`,
    both size 0 leaves; structural). Needed for the `Basis.size`-recursion of
    `denotBasis`'s `.frame` arm (which opens `b₁`). -/
theorem Basis.size_openVar (k : Nat) (y : Name) :
    ∀ b : Basis, Basis.size (Basis.openRec k (.var y) b) = Basis.size b
  | .empty => rfl
  | .one => rfl
  | .dual b => by simp [Basis.openRec, Basis.size, Basis.size_openVar k y b]
  | .dsum b₀ b₁ => by
      simp [Basis.openRec, Basis.size, Basis.size_openVar k y b₀, Basis.size_openVar k y b₁]
  | .tprod b₀ b₁ => by
      simp [Basis.openRec, Basis.size, Basis.size_openVar k y b₀, Basis.size_openVar k y b₁]
  | .proj s b₀ b₁ => by
      simp [Basis.openRec, Basis.size, Space.size_openVar k y s,
        Basis.size_openVar k y b₀, Basis.size_openVar k y b₁]
  | .image b => by simp [Basis.openRec, Basis.size, Basis.size_openVar k y b]
  | .terms s es b => by
      simp only [Basis.openRec, Basis.size, Term.openRecList_eq_map,
        Space.size_openVar k y s, Basis.size_openVar k y b]
      have hmap : (es.map (Term.openRec k (.var y))).map Term.size = es.map Term.size := by
        rw [List.map_map]
        exact List.map_congr_left (fun e _ => Term.size_openVar k y e)
      rw [hmap]
  | .frame b₀ b₁ => by
      simp [Basis.openRec, Basis.size, Basis.size_openVar k y b₀,
        Basis.size_openVar (k+1) y b₁]

theorem Basis.BasisValid.dual_inv {ε b} (h : Basis.BasisValid ε (.dual b)) :
    Basis.BasisValid ε b := by cases h with | dual h _ => exact h

theorem Basis.BasisValid.dsum_inv {ε b₀ b₁} (h : Basis.BasisValid ε (.dsum b₀ b₁)) :
    Basis.BasisValid ε b₀ ∧ Basis.BasisValid ε b₁ := by
  cases h with | dsum h₀ h₁ _ _ => exact ⟨h₀, h₁⟩

theorem Basis.BasisValid.tprod_inv {ε b₀ b₁} (h : Basis.BasisValid ε (.tprod b₀ b₁)) :
    Basis.BasisValid ε b₀ ∧ Basis.BasisValid ε b₁ := by
  cases h with | tprod h₀ h₁ _ _ => exact ⟨h₀, h₁⟩

theorem Basis.BasisValid.image_inv {ε b} (h : Basis.BasisValid ε (.image b)) :
    Basis.BasisValid ε b ∧ ∃ s₀ s₁ e, Basis.sof b = .coker s₀ s₁ e ∧
      Nonempty (HasType ∅ ε e (.space (.tprod (.dual s₀) s₁))) := by
  cases h with | image hb hsof he => exact ⟨hb, _, _, _, hsof, he⟩

/-- `.terms` inversion. -/
theorem Basis.BasisValid.terms_inv {ε s es b} (h : Basis.BasisValid ε (.terms s es b)) :
    Basis.BasisValid ε b ∧ Basis.sof b = s ∧ Nonempty (SValid ε s) ∧
      (∀ e ∈ es, Nonempty (HasType ∅ ε e (.space s))) := by
  cases h with
  | terms hb htof hsv hes _ =>
      exact ⟨hb, Basis.sof_eq_of_tof_eq_space htof, hsv, hes⟩

/-- A valid explicit terms basis contains at least one explicit vector. -/
theorem Basis.BasisValid.terms_nonempty {ε s es b}
    (h : Basis.BasisValid ε (.terms s es b)) : es ≠ [] := by
  cases h with | terms _ _ _ _ hne => exact hne

/-- **Space-validity of a valid basis's space** (`sof` regularity): every
    constructor either carries the needed `SValid`/`HasType` data or recurses.
    The FFS shapes rebuild `SValid.ker/coker/img/coimg` from the sub-bases'
    IHs (via the carried `sof bᵢ = sᵢ` equations) + the witness typing; a
    `.frame` has `sof = .empty`. -/
theorem Basis.BasisValid.sof_valid {ε : NLCtx} {b : Basis}
    (h : Basis.BasisValid ε b) : Nonempty (SValid ε (Basis.sof b)) := by
  induction h with
  | empty => exact ⟨.empty⟩
  | one => exact ⟨.real⟩
  | dual _ _ ih => obtain ⟨v⟩ := ih; exact ⟨.dual v⟩
  | dsum _ _ _ _ ih₀ ih₁ =>
      obtain ⟨v₀⟩ := ih₀; obtain ⟨v₁⟩ := ih₁; exact ⟨.dsum v₀ v₁⟩
  | tprod _ _ _ _ ih₀ ih₁ =>
      obtain ⟨v₀⟩ := ih₀; obtain ⟨v₁⟩ := ih₁; exact ⟨.tprod v₀ v₁⟩
  | proj_ker _ _ ht₀ ht₁ he ih₀ ih₁ =>
      obtain ⟨v₀⟩ := ih₀; obtain ⟨v₁⟩ := ih₁; obtain ⟨w⟩ := he
      have hs₀ := Basis.sof_eq_of_tof_eq_space ht₀
      have hs₁ := Basis.sof_eq_of_tof_eq_space ht₁
      exact ⟨.ker (hs₀ ▸ v₀) (hs₁ ▸ v₁) w⟩
  | proj_coker _ _ ht₀ ht₁ he ih₀ ih₁ =>
      obtain ⟨v₀⟩ := ih₀; obtain ⟨v₁⟩ := ih₁; obtain ⟨w⟩ := he
      have hs₀ := Basis.sof_eq_of_tof_eq_space ht₀
      have hs₁ := Basis.sof_eq_of_tof_eq_space ht₁
      exact ⟨.coker (hs₀ ▸ v₀) (hs₁ ▸ v₁) w⟩
  | proj_img _ _ ht₀ ht₁ he ih₀ ih₁ =>
      obtain ⟨v₀⟩ := ih₀; obtain ⟨v₁⟩ := ih₁; obtain ⟨w⟩ := he
      have hs₀ := Basis.sof_eq_of_tof_eq_space ht₀
      have hs₁ := Basis.sof_eq_of_tof_eq_space ht₁
      exact ⟨.img (hs₀ ▸ v₀) (hs₁ ▸ v₁) w⟩
  | proj_coimg _ _ ht₀ ht₁ he ih₀ ih₁ =>
      obtain ⟨v₀⟩ := ih₀; obtain ⟨v₁⟩ := ih₁; obtain ⟨w⟩ := he
      have hs₀ := Basis.sof_eq_of_tof_eq_space ht₀
      have hs₁ := Basis.sof_eq_of_tof_eq_space ht₁
      exact ⟨.coimg (hs₀ ▸ v₀) (hs₁ ▸ v₁) w⟩
  | @image _ b' s₀ s₁ e _ hsof he ih =>
      obtain ⟨v⟩ := ih; obtain ⟨w⟩ := he
      have himg : Basis.sof (.image b') = .img s₀ s₁ e := by
        simp only [Basis.sof, hsof]
      rw [himg]
      rw [hsof] at v
      cases v with | coker v₀ v₁ _ => exact ⟨.img v₀ v₁ w⟩
  | @terms _ s es b' _ htof hsv _ _ _ =>
      have hsof : Basis.sof b' = s := Basis.sof_eq_of_tof_eq_space htof
      have ht : Basis.sof (.terms s es b') = s := by
        simp only [Basis.sof, hsof]
      rw [ht]; exact hsv
  | frame _ _ _ _ => exact ⟨.empty⟩

/-! ## Initial syntactic theorems. -/

/-- `sof` of a substituted basis is the substituted `sof`. Purely
    structural — substitution commutes with the syntactic `sof`. -/
theorem Basis.sof_subst (x : Name) (e : Term) (b : Basis) :
    Basis.sof (Basis.subst x e b) = Space.subst x e (Basis.sof b) := by
  induction b with
  | empty => rfl
  | one => rfl
  | dual b ih => simp [Basis.sof, Basis.subst, Space.subst, ih]
  | dsum b₀ b₁ ih₀ ih₁ =>
      simp [Basis.sof, Basis.subst, Space.subst, ih₀, ih₁]
  | tprod b₀ b₁ ih₀ ih₁ =>
      simp [Basis.sof, Basis.subst, Space.subst, ih₀, ih₁]
  | proj s b₀ b₁ _ _ => rfl
  | image b ih =>
      simp only [Basis.sof, Basis.subst]
      -- Pattern-match on `Basis.sof b`; only the `.coker` shape yields a
      -- nontrivial result, and the `ih` rewrites it into the substituted
      -- form so the `match` collapses on both sides.
      rcases hsof : Basis.sof b with _ | _ | _ | _ | _ | _ | _ | s₀ | s₀ | s₀
      all_goals
        rw [hsof] at ih
        simp [Space.subst] at ih ⊢
        try rw [ih]
  | terms s es b ih =>
      simp [Basis.sof, Basis.subst, ih]
  | frame b₀ b₁ _ _ =>
      simp [Basis.subst, Basis.sof, Space.subst]

/-- `tof` commutes with term-substitution (the `tof` analogue of `sof_subst`).
    Non-frame bases reduce to `.space (sof …)` and ride on `sof_subst`; the
    `.frame` case mirrors `Ty.subst`'s `.piTy` shadowing split. -/
theorem Basis.tof_subst (x : Name) (e : Term) (b : Basis) :
    Basis.tof (Basis.subst x e b) = Ty.subst x e (Basis.tof b) := by
  induction b with
  | empty => rfl
  | one => rfl
  | dual b ih => simp [Basis.tof, Basis.subst, Basis.sof, Ty.subst, Space.subst, Basis.sof_subst]
  | dsum b₀ b₁ _ _ =>
      simp [Basis.tof, Basis.subst, Basis.sof, Ty.subst, Space.subst, Basis.sof_subst]
  | tprod b₀ b₁ _ _ =>
      simp [Basis.tof, Basis.subst, Basis.sof, Ty.subst, Space.subst, Basis.sof_subst]
  | proj s b₀ b₁ _ _ =>
      simp [Basis.tof, Basis.subst, Basis.sof, Ty.subst, Space.subst, Basis.sof_subst]
  | image b _ =>
      show Ty.space (Basis.sof (Basis.subst x e (.image b)))
          = Ty.subst x e (Ty.space (Basis.sof (.image b)))
      rw [Basis.sof_subst, Ty.subst]
  | terms s es b _ =>
      simp [Basis.tof, Basis.subst, Basis.sof, Ty.subst, Space.subst, Basis.sof_subst]
  | frame b₀ b₁ ih₀ ih₁ =>
      simp [Basis.subst, Basis.tof, Ty.subst, ih₀, ih₁]

/-- `sof` commutes with opening a bound index (the `openRec` analogue of
    `sof_subst`). `k` need not be generalized: `sof (.frame …) = .empty`, so no
    case recurses under the frame binder. -/
theorem Basis.sof_openRec (k : Nat) (u : Term) (b : Basis) :
    Basis.sof (Basis.openRec k u b) = Space.openRec k u (Basis.sof b) := by
  induction b with
  | empty => rfl
  | one => rfl
  | dual b ih => simp [Basis.sof, Basis.openRec, Space.openRec, ih]
  | dsum b₀ b₁ ih₀ ih₁ => simp [Basis.sof, Basis.openRec, Space.openRec, ih₀, ih₁]
  | tprod b₀ b₁ ih₀ ih₁ => simp [Basis.sof, Basis.openRec, Space.openRec, ih₀, ih₁]
  | proj s b₀ b₁ _ _ => rfl
  | image b ih =>
      simp only [Basis.sof, Basis.openRec]
      rcases hsof : Basis.sof b with _ | _ | _ | _ | _ | _ | _ | s₀ | s₀ | s₀
      all_goals
        rw [hsof] at ih
        simp [Space.openRec] at ih ⊢
        try rw [ih]
  | terms s es b ih => simp [Basis.sof, Basis.openRec, ih]
  | frame b₀ b₁ _ _ => simp [Basis.openRec, Basis.sof, Space.openRec]

/-- `tof` commutes with opening a bound index (the `openRec` analogue of
    `tof_subst`). `k` IS generalized: the `.frame` codomain `tof` recurses under
    the binder at `k+1` (matching `Ty.openRec`'s `.piTy`). -/
theorem Basis.tof_openRec (u : Term) : ∀ (k : Nat) (b : Basis),
    Basis.tof (Basis.openRec k u b) = Ty.openRec k u (Basis.tof b) := by
  intro k b
  induction b generalizing k with
  | empty => rfl
  | one => rfl
  | dual b _ => simp [Basis.tof, Basis.openRec, Basis.sof, Ty.openRec, Space.openRec, Basis.sof_openRec]
  | dsum b₀ b₁ _ _ =>
      simp [Basis.tof, Basis.openRec, Basis.sof, Ty.openRec, Space.openRec, Basis.sof_openRec]
  | tprod b₀ b₁ _ _ =>
      simp [Basis.tof, Basis.openRec, Basis.sof, Ty.openRec, Space.openRec, Basis.sof_openRec]
  | proj s b₀ b₁ _ _ =>
      simp [Basis.tof, Basis.openRec, Basis.sof, Ty.openRec, Space.openRec, Basis.sof_openRec]
  | image b _ =>
      show Ty.space (Basis.sof (Basis.openRec k u (.image b)))
          = Ty.openRec k u (Ty.space (Basis.sof (.image b)))
      rw [Basis.sof_openRec, Ty.openRec]
  | terms s es b _ =>
      simp [Basis.tof, Basis.openRec, Basis.sof, Ty.openRec, Space.openRec, Basis.sof_openRec]
  | frame b₀ b₁ ih₀ ih₁ =>
      simp [Basis.openRec, Basis.tof, Ty.openRec, ih₀ k, ih₁ (k+1)]

/-- The source kind is determined by the type's space/function structure. -/
def Ty.structuralKind : Ty → Kind
  | .space _ => .base
  | .piTy a b => .arrow a.structuralKind b.structuralKind

/-- Opening changes terms in spaces, but preserves the type's kind. -/
theorem Ty.structuralKind_openRec (k : Nat) (u : Term) :
    (τ : Ty) → (Ty.openRec k u τ).structuralKind = τ.structuralKind
  | .space _ => rfl
  | .piTy a b => by
      simp only [Ty.openRec, Ty.structuralKind,
        Ty.structuralKind_openRec k u a, Ty.structuralKind_openRec (k + 1) u b]

/-- Basis validity derives type validity; frames need no extra kinding premise. -/
theorem Basis.BasisValid.tof_valid_structural {ε : NLCtx} {b : Basis}
    (h : Basis.BasisValid ε b) :
    Nonempty (TValid ε b.tof b.tof.structuralKind) := by
  have base {ε : NLCtx} {b : Basis} (hb : Basis.BasisValid ε b)
      (ht : b.tof = .space b.sof) :
      Nonempty (TValid ε b.tof b.tof.structuralKind) := by
    rw [ht]
    exact ⟨.space hb.sof_valid.some⟩
  induction h with
  | empty => exact base .empty rfl
  | one => exact base .one rfl
  | dual hb ht _ => exact base (.dual hb ht) rfl
  | dsum ha hb ht hu _ _ => exact base (.dsum ha hb ht hu) rfl
  | tprod ha hb ht hu _ _ => exact base (.tprod ha hb ht hu) rfl
  | proj_ker ha hb ht hu he _ _ => exact base (.proj_ker ha hb ht hu he) rfl
  | proj_coker ha hb ht hu he _ _ => exact base (.proj_coker ha hb ht hu he) rfl
  | proj_img ha hb ht hu he _ _ => exact base (.proj_img ha hb ht hu he) rfl
  | proj_coimg ha hb ht hu he _ _ => exact base (.proj_coimg ha hb ht hu he) rfl
  | image hb ht he _ => exact base (.image hb ht he) rfl
  | terms hb ht hs he hn _ => exact base (.terms hb ht hs he hn) rfl
  | frame L ha hb iha ihb =>
      refine ⟨.piTy L iha.some (fun y hy => ?_)⟩
      have hv := (ihb y hy).some
      simpa only [Basis.openVar, Basis.tof_openRec, Ty.openVar, Ty.structuralKind_openRec] using hv

/-- Frame inversion, including the type validity derived from the two premises. -/
theorem Basis.BasisValid.frame_inv {ε b₀ b₁} (h : Basis.BasisValid ε (.frame b₀ b₁)) :
    Basis.BasisValid ε b₀ ∧
    (∃ L : Finset Name, ∀ y, y ∉ L →
      Basis.BasisValid (Finmap.insert y (Basis.tof b₀) ε) (Basis.openVar y b₁)) ∧
    (∃ k₀ k₁ : Kind,
      Nonempty (TValid ε (.piTy (Basis.tof b₀) (Basis.tof b₁)) (.arrow k₀ k₁))) := by
  have ht := h.tof_valid_structural
  cases h with
  | frame L hb₀ hbody => exact ⟨hb₀, ⟨L, hbody⟩, _, _, ht⟩

/-- `Basis.empty` has space `⊥` and contains no free variables. -/
@[simp] theorem Basis.sof_empty : Basis.sof .empty = .empty := rfl
@[simp] theorem Basis.fv_empty  : Basis.fv  .empty = ∅      := rfl

/-- `Basis.one` has space `ℝ` and no free variables. -/
@[simp] theorem Basis.sof_one : Basis.sof .one = .real := rfl
@[simp] theorem Basis.fv_one  : Basis.fv  .one = ∅      := rfl

/-- The `Basis.empty` basis is always valid. -/
@[simp] theorem Basis.BasisValid_empty (ε : NLCtx) :
    Basis.BasisValid ε .empty := .empty

/-- The `Basis.one` basis is always valid. -/
@[simp] theorem Basis.BasisValid_one (ε : NLCtx) :
    Basis.BasisValid ε .one := .one

/-- `tof` and `sof` agree on non-frame bases. -/
theorem Basis.tof_of_not_frame :
    ∀ b : Basis, (∀ b₀ b₁, b ≠ .frame b₀ b₁) →
      Basis.tof b = .space (Basis.sof b)
  | .empty,       _ => rfl
  | .one,         _ => rfl
  | .dual _,      _ => rfl
  | .dsum _ _,    _ => rfl
  | .tprod _ _,   _ => rfl
  | .proj _ _ _,  _ => rfl
  | .image _,     _ => rfl
  | .terms _ _ _, _ => rfl
  | .frame b₀ b₁, h => absurd rfl (h b₀ b₁)

def Basis.stdSpace : Space → Basis
  | .empty           => .empty
  | .real            => .one
  | .dual s          => .dual (Basis.stdSpace s)
  | .dsum s₀ s₁      => .dsum (Basis.stdSpace s₀) (Basis.stdSpace s₁)
  | .tprod s₀ s₁     => .tprod (Basis.stdSpace s₀) (Basis.stdSpace s₁)
  | .ker s₀ s₁ e     => .proj (.ker s₀ s₁ e) (Basis.stdSpace s₀) (Basis.stdSpace s₁)
  | .coker s₀ s₁ e   => .proj (.coker s₀ s₁ e) (Basis.stdSpace s₀) (Basis.stdSpace s₁)
  | .img s₀ s₁ e     => .proj (.img s₀ s₁ e) (Basis.stdSpace s₀) (Basis.stdSpace s₁)
  | .coimg s₀ s₁ e   => .proj (.coimg s₀ s₁ e) (Basis.stdSpace s₀) (Basis.stdSpace s₁)

def Basis.std : Ty → Basis
  | .space s          => Basis.stdSpace s
  | .piTy τ₀ τ₁       => .frame (Basis.std τ₀) (Basis.std τ₁)

/-- The standard basis introduces exactly the free names already present in its space. -/
@[simp] theorem Basis.fv_stdSpace : ∀ s : Space,
    Basis.fv (Basis.stdSpace s) = Space.fv s
  | .empty => rfl
  | .real => rfl
  | .dual s => by simp [Basis.stdSpace, Basis.fv, Space.fv, Basis.fv_stdSpace s]
  | .dsum s₀ s₁ => by
      simp [Basis.stdSpace, Basis.fv, Space.fv, Basis.fv_stdSpace s₀,
        Basis.fv_stdSpace s₁]
  | .tprod s₀ s₁ => by
      simp [Basis.stdSpace, Basis.fv, Space.fv, Basis.fv_stdSpace s₀,
        Basis.fv_stdSpace s₁]
  | .ker s₀ s₁ e => by
      ext x
      simp [Basis.stdSpace, Basis.fv, Space.fv, Basis.fv_stdSpace s₀,
        Basis.fv_stdSpace s₁]
      aesop
  | .coker s₀ s₁ e => by
      ext x
      simp [Basis.stdSpace, Basis.fv, Space.fv, Basis.fv_stdSpace s₀,
        Basis.fv_stdSpace s₁]
      aesop
  | .img s₀ s₁ e => by
      ext x
      simp [Basis.stdSpace, Basis.fv, Space.fv, Basis.fv_stdSpace s₀,
        Basis.fv_stdSpace s₁]
      aesop
  | .coimg s₀ s₁ e => by
      ext x
      simp [Basis.stdSpace, Basis.fv, Space.fv, Basis.fv_stdSpace s₀,
        Basis.fv_stdSpace s₁]
      aesop

/-- `Basis.sof (Basis.stdSpace s) = s` — the standard basis of `s` has
    space `s`. Trivial structural induction on `s`. -/
@[simp] theorem Basis.sof_stdSpace : ∀ s : Space, Basis.sof (Basis.stdSpace s) = s
  | .empty           => rfl
  | .real            => rfl
  | .dual s          => by simp [Basis.stdSpace, Basis.sof, Basis.sof_stdSpace s]
  | .dsum s₀ s₁      => by
      simp [Basis.stdSpace, Basis.sof, Basis.sof_stdSpace s₀, Basis.sof_stdSpace s₁]
  | .tprod s₀ s₁     => by
      simp [Basis.stdSpace, Basis.sof, Basis.sof_stdSpace s₀, Basis.sof_stdSpace s₁]
  | .ker _ _ _       => rfl
  | .coker _ _ _     => rfl
  | .img _ _ _       => rfl
  | .coimg _ _ _     => rfl

/-- `Basis.tof (Basis.std τ) = τ` — the standard basis of `τ` has type
    `τ`. Structural induction on `τ`; the `.space` arm dispatches to
    `Basis.sof_stdSpace`, the `.piTy` arm uses both IHs and unfolds
    `Basis.tof` on the `.frame` constructor. -/
@[simp] theorem Basis.tof_std : ∀ τ : Ty, Basis.tof (Basis.std τ) = τ
  | .space s        => by
      -- `Basis.std (.space s) = Basis.stdSpace s`; `Basis.stdSpace s` is
      -- never a `.frame`, so `Basis.tof` reduces to `.space (Basis.sof
      -- (Basis.stdSpace s)) = .space s` (using `sof_stdSpace`).
      unfold Basis.std
      cases s <;> simp [Basis.stdSpace, Basis.tof, Basis.sof]
  | .piTy τ₀ τ₁   => by
      simp [Basis.std, Basis.tof, Basis.tof_std τ₀, Basis.tof_std τ₁]

/-- `tof (stdSpace s) = .space s`, the space specialization of `tof_std`. -/
@[simp] theorem Basis.tof_stdSpace (s : Space) :
    Basis.tof (Basis.stdSpace s) = .space s :=
  Basis.tof_std (.space s)

/-- `Basis.stdSpace` commutes with `Space.openRec`. Structural induction on `s`. -/
theorem Basis.stdSpace_openRec (k : Nat) (u : Term) :
    ∀ s : Space, Basis.stdSpace (Space.openRec k u s) = Basis.openRec k u (Basis.stdSpace s)
  | .empty => rfl
  | .real  => rfl
  | .dual s => by
      simp [Space.openRec, Basis.stdSpace, Basis.openRec, Basis.stdSpace_openRec k u s]
  | .dsum s₀ s₁ => by
      simp [Space.openRec, Basis.stdSpace, Basis.openRec,
        Basis.stdSpace_openRec k u s₀, Basis.stdSpace_openRec k u s₁]
  | .tprod s₀ s₁ => by
      simp [Space.openRec, Basis.stdSpace, Basis.openRec,
        Basis.stdSpace_openRec k u s₀, Basis.stdSpace_openRec k u s₁]
  | .ker s₀ s₁ e => by
      simp [Space.openRec, Basis.stdSpace, Basis.openRec,
        Basis.stdSpace_openRec k u s₀, Basis.stdSpace_openRec k u s₁]
  | .coker s₀ s₁ e => by
      simp [Space.openRec, Basis.stdSpace, Basis.openRec,
        Basis.stdSpace_openRec k u s₀, Basis.stdSpace_openRec k u s₁]
  | .img s₀ s₁ e => by
      simp [Space.openRec, Basis.stdSpace, Basis.openRec,
        Basis.stdSpace_openRec k u s₀, Basis.stdSpace_openRec k u s₁]
  | .coimg s₀ s₁ e => by
      simp [Space.openRec, Basis.stdSpace, Basis.openRec,
        Basis.stdSpace_openRec k u s₀, Basis.stdSpace_openRec k u s₁]

/-- `Basis.std` commutes with opening: `std (Ty.openRec k u τ) = openRec k u (std τ)`. -/
theorem Basis.std_openRec (u : Term) :
    ∀ (τ : Ty) (k : Nat),
      Basis.std (Ty.openRec k u τ) = Basis.openRec k u (Basis.std τ)
  | .space s, k => by
      simp [Ty.openRec, Basis.std, Basis.stdSpace_openRec k u s]
  | .piTy τ₀ τ₁, k => by
      simp [Ty.openRec, Basis.std, Basis.openRec,
        Basis.std_openRec u τ₀ k, Basis.std_openRec u τ₁ (k+1)]

/-- `Basis.std` commutes with `Ty.openVar`. -/
theorem Basis.std_openVar (y : Name) (τ : Ty) :
    Basis.std (Ty.openVar y τ) = Basis.openVar y (Basis.std τ) :=
  Basis.std_openRec (.var y) τ 0

/-- `Basis.stdSpace s` is valid in any well-typed context: if `SValid ε s`
    holds, then `Basis.BasisValid ε (Basis.stdSpace s)`. Structural recursion
    on `s : Space` (mutually inductive — uses well-founded recursion on
    `Space.size`; we case-split on the `SValid` constructor at each
    space-shape). -/
theorem Basis.stdSpace_valid : ∀ {ε : NLCtx} (s : Space), SValid ε s →
    Basis.BasisValid ε (Basis.stdSpace s)
  | _, .empty, _ => .empty
  | _, .real, _ => .one
  | _, .dual s, hs => by
      cases hs with
      | dual hs' =>
          exact .dual (Basis.stdSpace_valid s hs') (by
            rw [Basis.tof_stdSpace, Basis.sof_stdSpace])
  | _, .dsum s₀ s₁, hs => by
      cases hs with
      | dsum hs₀ hs₁ =>
          exact .dsum (Basis.stdSpace_valid s₀ hs₀) (Basis.stdSpace_valid s₁ hs₁)
            (by rw [Basis.tof_stdSpace, Basis.sof_stdSpace])
            (by rw [Basis.tof_stdSpace, Basis.sof_stdSpace])
  | _, .tprod s₀ s₁, hs => by
      cases hs with
      | tprod hs₀ hs₁ =>
          exact .tprod (Basis.stdSpace_valid s₀ hs₀) (Basis.stdSpace_valid s₁ hs₁)
            (by rw [Basis.tof_stdSpace, Basis.sof_stdSpace])
            (by rw [Basis.tof_stdSpace, Basis.sof_stdSpace])
  | ε, .ker s₀ s₁ e, hs => by
      cases hs with
      | ker hs₀ hs₁ he =>
          exact .proj_ker (Basis.stdSpace_valid s₀ hs₀) (Basis.stdSpace_valid s₁ hs₁)
            (Basis.tof_stdSpace _) (Basis.tof_stdSpace _) ⟨he⟩
  | ε, .coker s₀ s₁ e, hs => by
      cases hs with
      | coker hs₀ hs₁ he =>
          exact .proj_coker (Basis.stdSpace_valid s₀ hs₀) (Basis.stdSpace_valid s₁ hs₁)
            (Basis.tof_stdSpace _) (Basis.tof_stdSpace _) ⟨he⟩
  | ε, .img s₀ s₁ e, hs => by
      cases hs with
      | img hs₀ hs₁ he =>
          exact .proj_img (Basis.stdSpace_valid s₀ hs₀) (Basis.stdSpace_valid s₁ hs₁)
            (Basis.tof_stdSpace _) (Basis.tof_stdSpace _) ⟨he⟩
  | ε, .coimg s₀ s₁ e, hs => by
      cases hs with
      | coimg hs₀ hs₁ he =>
          exact .proj_coimg (Basis.stdSpace_valid s₀ hs₀) (Basis.stdSpace_valid s₁ hs₁)
            (Basis.tof_stdSpace _) (Basis.tof_stdSpace _) ⟨he⟩
  termination_by _ s => Space.size s
  decreasing_by all_goals (simp [Space.size]; try omega)

/-- `Basis.std τ` is valid in any well-typed context: if `TValid ε τ k`
    holds for some kind `k`, then `Basis.BasisValid ε (Basis.std τ)`.
    Structural recursion on `τ : Ty`; well-founded over `Ty.size`. -/
theorem Basis.std_valid : ∀ {ε : NLCtx} (τ : Ty) {k : Kind}, TValid ε τ k →
    Basis.BasisValid ε (Basis.std τ)
  | _, .space _, _, hτ => by
      cases hτ with
      | space hs => exact Basis.stdSpace_valid _ hs
  | ε, .piTy τ₀ τ₁, _, hτ => by
      cases hτ with
      | @piTy _ _ _ k₀ k₁ L hτ₀ hbody =>
          -- `Basis.std (.piTy τ₀ τ₁) = .frame (Basis.std τ₀) (Basis.std τ₁)`.
          -- Build the `.frame` constructor (avoid set `L`).
          show Basis.BasisValid ε (.frame (Basis.std τ₀) (Basis.std τ₁))
          -- cofinite body: for fresh `y ∉ L`, the IH on `Ty.openVar y τ₁`
          -- (via `hbody y`) gives `BasisValid` of `std (openVar y τ₁)`, rewritten
          -- to `openVar y (std τ₁)` with `tof (std τ₀) = τ₀`.
          have hbody' : ∀ y, y ∉ L →
              Basis.BasisValid (Finmap.insert y (Basis.tof (Basis.std τ₀)) ε)
                (Basis.openVar y (Basis.std τ₁)) := by
            intro y hy
            have hy' : Basis.BasisValid (Finmap.insert y τ₀ ε)
                (Basis.std (Ty.openVar y τ₁)) :=
              Basis.std_valid (Ty.openVar y τ₁) (hbody y hy)
            rw [Basis.tof_std τ₀, ← Basis.std_openVar]
            exact hy'
          exact Basis.BasisValid.frame L (Basis.std_valid τ₀ hτ₀) hbody'
  termination_by _ τ => Ty.size τ
  decreasing_by
    all_goals
      first
        | (simp only [Ty.openVar, Ty.size_openVar]; simp [Ty.size]; try omega)
        | (simp [Ty.size]; try omega)

/-- Substituting a name not free in the basis is the identity. LN version
    delegates to `Basis.subst_fresh` (in `GLang.SourceLN`). -/
theorem Basis.subst_of_not_mem_fv (x : Name) (v : Term) (b : Basis)
    (h : x ∉ Basis.fv b) : Basis.subst x v b = b :=
  Basis.subst_fresh x v b h

end GLang
