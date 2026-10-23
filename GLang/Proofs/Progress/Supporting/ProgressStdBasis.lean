

import GLang.Proofs.Basis.Binding
import GLang.Annotated.Judgments
import GLang.Operational.Ordinary

namespace GLang

theorem Basis.isStd_stdSpace : ∀ s : Space, (Basis.stdSpace s).isStd
  | .empty         => trivial
  | .real          => trivial
  | .dual s        => Basis.isStd_stdSpace s
  | .dsum s₀ s₁    => ⟨Basis.isStd_stdSpace s₀, Basis.isStd_stdSpace s₁⟩
  | .tprod s₀ s₁   => ⟨Basis.isStd_stdSpace s₀, Basis.isStd_stdSpace s₁⟩
  | .ker s₀ s₁ _   => ⟨Basis.isStd_stdSpace s₀, Basis.isStd_stdSpace s₁⟩
  | .coker s₀ s₁ _ => ⟨Basis.isStd_stdSpace s₀, Basis.isStd_stdSpace s₁⟩
  | .img s₀ s₁ _   => ⟨Basis.isStd_stdSpace s₀, Basis.isStd_stdSpace s₁⟩
  | .coimg s₀ s₁ _ => ⟨Basis.isStd_stdSpace s₀, Basis.isStd_stdSpace s₁⟩

/-- The standard basis of a type satisfies `\isStdBasis` (the `.piTy` arm
    builds a `.frame`, standard iff its components are). -/
theorem Basis.isStd_std : ∀ τ : Ty, (Basis.std τ).isStd
  | .space s    => Basis.isStd_stdSpace s
  | .piTy τ₀ τ₁ => ⟨Basis.isStd_std τ₀, Basis.isStd_std τ₁⟩

theorem Basis.htof_stdSpace (s : Space) :
    Basis.tof (Basis.stdSpace s) = .space (Basis.sof (Basis.stdSpace s)) := by
  rw [Basis.tof_stdSpace, Basis.sof_stdSpace]

/-! ## P6b — the hereditary space-basis predicate (`Basis.IsSpaceBasis`). -/

/-- **Hereditary well-formedness for SPACE bases**. -/
def Basis.IsSpaceBasis : Basis → Prop
  | .empty        => True
  | .one          => True
  | .dual b       => Basis.IsSpaceBasis b
  | .dsum b₀ b₁   => Basis.IsSpaceBasis b₀ ∧ Basis.IsSpaceBasis b₁
  | .tprod b₀ b₁  => Basis.IsSpaceBasis b₀ ∧ Basis.IsSpaceBasis b₁
  | .proj _ b₀ b₁ => Basis.IsSpaceBasis b₀ ∧ Basis.IsSpaceBasis b₁
  | .image b      => Basis.IsSpaceBasis b
  | .terms _ es b => es ≠ [] ∧ Basis.IsSpaceBasis b
  | .frame _ _    => False

/-! Component-projection accessors (all definitional — `IsSpaceBasis` is a
    structural recursion, so each constructor case reduces). -/

@[simp] theorem Basis.isSpaceBasis_empty : Basis.IsSpaceBasis .empty := trivial
@[simp] theorem Basis.isSpaceBasis_one : Basis.IsSpaceBasis .one := trivial
@[simp] theorem Basis.isSpaceBasis_dual {b : Basis} :
    Basis.IsSpaceBasis (.dual b) ↔ Basis.IsSpaceBasis b := Iff.rfl
@[simp] theorem Basis.isSpaceBasis_dsum {b₀ b₁ : Basis} :
    Basis.IsSpaceBasis (.dsum b₀ b₁)
      ↔ Basis.IsSpaceBasis b₀ ∧ Basis.IsSpaceBasis b₁ := Iff.rfl
@[simp] theorem Basis.isSpaceBasis_tprod {b₀ b₁ : Basis} :
    Basis.IsSpaceBasis (.tprod b₀ b₁)
      ↔ Basis.IsSpaceBasis b₀ ∧ Basis.IsSpaceBasis b₁ := Iff.rfl
@[simp] theorem Basis.isSpaceBasis_proj {s : Space} {b₀ b₁ : Basis} :
    Basis.IsSpaceBasis (.proj s b₀ b₁)
      ↔ Basis.IsSpaceBasis b₀ ∧ Basis.IsSpaceBasis b₁ := Iff.rfl
@[simp] theorem Basis.isSpaceBasis_image {b : Basis} :
    Basis.IsSpaceBasis (.image b) ↔ Basis.IsSpaceBasis b := Iff.rfl
@[simp] theorem Basis.isSpaceBasis_terms {s : Space} {es : List Term}
    {b : Basis} :
    Basis.IsSpaceBasis (.terms s es b)
      ↔ es ≠ [] ∧ Basis.IsSpaceBasis b := Iff.rfl
@[simp] theorem Basis.isSpaceBasis_frame {b₀ b₁ : Basis} :
    ¬ Basis.IsSpaceBasis (.frame b₀ b₁) := fun h => h

theorem Basis.IsSpaceBasis.tof_eq : ∀ {b : Basis}, Basis.IsSpaceBasis b →
    Basis.tof b = .space (Basis.sof b)
  | .empty, _        => rfl
  | .one, _          => rfl
  | .dual _, _       => rfl
  | .dsum _ _, _     => rfl
  | .tprod _ _, _    => rfl
  | .proj _ _ _, _   => rfl
  | .image _, _      => rfl
  | .terms _ _ _, _  => rfl
  | .frame _ _, h    => False.elim h

/-- The standard basis of a space is a hereditary space basis (`stdSpace`
    never produces `.image`, `.terms`, or `.frame`). -/
theorem Basis.isSpaceBasis_stdSpace : ∀ s : Space,
    Basis.IsSpaceBasis (Basis.stdSpace s)
  | .empty         => trivial
  | .real          => trivial
  | .dual s        => Basis.isSpaceBasis_stdSpace s
  | .dsum s₀ s₁    => ⟨Basis.isSpaceBasis_stdSpace s₀, Basis.isSpaceBasis_stdSpace s₁⟩
  | .tprod s₀ s₁   => ⟨Basis.isSpaceBasis_stdSpace s₀, Basis.isSpaceBasis_stdSpace s₁⟩
  | .ker s₀ s₁ _   => ⟨Basis.isSpaceBasis_stdSpace s₀, Basis.isSpaceBasis_stdSpace s₁⟩
  | .coker s₀ s₁ _ => ⟨Basis.isSpaceBasis_stdSpace s₀, Basis.isSpaceBasis_stdSpace s₁⟩
  | .img s₀ s₁ _   => ⟨Basis.isSpaceBasis_stdSpace s₀, Basis.isSpaceBasis_stdSpace s₁⟩
  | .coimg s₀ s₁ _ => ⟨Basis.isSpaceBasis_stdSpace s₀, Basis.isSpaceBasis_stdSpace s₁⟩

/-- For a SPACE basis, the standard basis of its type IS the standard basis
    of its space: `Basis.std (tof b) = Basis.stdSpace (sof b)` (rewrite by
    `htof`, then `Basis.std` reduces on `.space`). The bridge between
    `lem:cobProg`'s conclusion shape (`Basis.std (Basis.tof b)`) and the
    composition kit's `Basis.stdSpace (Basis.sof b)` currency. -/
theorem Basis.std_tof_eq_stdSpace {b : Basis}
    (htof : Basis.tof b = .space (Basis.sof b)) :
    Basis.std (Basis.tof b) = Basis.stdSpace (Basis.sof b) := by
  rw [htof]; rfl

/-- `Basis.std_tof_eq_stdSpace` packaged on the hereditary predicate. -/
theorem Basis.IsSpaceBasis.std_tof_eq {b : Basis}
    (h : Basis.IsSpaceBasis b) :
    Basis.std (Basis.tof b) = Basis.stdSpace (Basis.sof b) :=
  Basis.std_tof_eq_stdSpace h.tof_eq

/-! ## P6b — the `Space`-level ⊕-chain (`Space.dsumChain`).

`EvalBB.terms_rref` evaluates the term chain `Term.dsumChain e es` at the
basis chain `Basis.dsumChain b' es.length`; the chain's SPACE is the
matching `Space`-level fold below. Mirrors `Basis.dsumChain` exactly
(left-associated `n` extra `⊕ s` layers). -/

/-- `n` extra `⊕ s` layers onto `s` — the `Space` of an n+1-fold ⊕-chain
    `((s ⊕ s) ⊕ ⋯) ⊕ s` (companion of `Basis.dsumChain` / `Term.dsumChain`,
    `Syntax.lean`). -/
def Space.dsumChain (s : Space) : Nat → Space
  | 0     => s
  | n + 1 => .dsum (Space.dsumChain s n) s

@[simp] theorem Space.dsumChain_zero (s : Space) :
    Space.dsumChain s 0 = s := rfl

theorem Space.dsumChain_succ (s : Space) (n : Nat) :
    Space.dsumChain s (n + 1) = .dsum (Space.dsumChain s n) s := rfl

/-- `sof` commutes with the ⊕-chain:
    `sof (Basis.dsumChain b n) = Space.dsumChain (sof b) n`. -/
theorem Basis.sof_dsumChain (b : Basis) :
    ∀ n : Nat, Basis.sof (Basis.dsumChain b n)
      = Space.dsumChain (Basis.sof b) n
  | 0 => rfl
  | n + 1 => by
      simp only [Basis.dsumChain, Space.dsumChain, Basis.sof,
        Basis.sof_dsumChain b n]

/-- A ⊕-chain over a SPACE basis is a SPACE basis (`tof = .space ∘ sof`):
    the `n = 0` layer is `b` itself, every later layer is a `.dsum`. -/
theorem Basis.tof_dsumChain {b : Basis}
    (htof : Basis.tof b = .space (Basis.sof b)) :
    ∀ n : Nat, Basis.tof (Basis.dsumChain b n)
      = .space (Basis.sof (Basis.dsumChain b n))
  | 0 => htof
  | _ + 1 => rfl

/-- The ⊕-chain preserves hereditary space-basis-ness. -/
theorem Basis.IsSpaceBasis.dsumChain {b : Basis} (h : Basis.IsSpaceBasis b) :
    ∀ n : Nat, Basis.IsSpaceBasis (Basis.dsumChain b n)
  | 0 => h
  | n + 1 => ⟨Basis.IsSpaceBasis.dsumChain h n, h⟩

/-! ## Hereditary type-basis well-formedness (`Basis.IsTyBasis`)

This lives beside `IsSpaceBasis`, below both operational progress and the
adequacy semantics, so exact basis certificates can carry the same public
shape guard without importing the progress theorem stack. -/

/-- A hereditary type basis is a hereditary space basis at every non-frame
node, and recursively a type basis on both sides of a frame. -/
def Basis.IsTyBasis : Basis → Prop
  | .frame b₀ b₁ => Basis.IsTyBasis b₀ ∧ Basis.IsTyBasis b₁
  | .empty => Basis.IsSpaceBasis .empty
  | .one => Basis.IsSpaceBasis .one
  | .dual b => Basis.IsSpaceBasis (.dual b)
  | .dsum b₀ b₁ => Basis.IsSpaceBasis (.dsum b₀ b₁)
  | .tprod b₀ b₁ => Basis.IsSpaceBasis (.tprod b₀ b₁)
  | .proj s b₀ b₁ => Basis.IsSpaceBasis (.proj s b₀ b₁)
  | .image b => Basis.IsSpaceBasis (.image b)
  | .terms s es b => Basis.IsSpaceBasis (.terms s es b)

@[simp] theorem Basis.isTyBasis_frame {b₀ b₁ : Basis} :
    Basis.IsTyBasis (.frame b₀ b₁) ↔
      Basis.IsTyBasis b₀ ∧ Basis.IsTyBasis b₁ := Iff.rfl

/-- A hereditary space basis is a hereditary type basis. -/
theorem Basis.IsSpaceBasis.toIsTyBasis :
    ∀ {b : Basis}, Basis.IsSpaceBasis b → Basis.IsTyBasis b
  | .empty, h | .one, h | .dual _, h | .dsum _ _, h | .tprod _ _, h
  | .proj _ _ _, h | .image _, h | .terms _ _ _, h => h
  | .frame _ _, h => False.elim h

/-- A non-frame hereditary type basis is a hereditary space basis. -/
theorem Basis.IsTyBasis.toIsSpaceBasis :
    ∀ {b : Basis}, Basis.IsTyBasis b →
      (∀ b₀ b₁, b ≠ .frame b₀ b₁) → Basis.IsSpaceBasis b
  | .empty, h, _ | .one, h, _ | .dual _, h, _ | .dsum _ _, h, _
  | .tprod _ _, h, _ | .proj _ _ _, h, _ | .image _, h, _
  | .terms _ _ _, h, _ => h
  | .frame b₀ b₁, _, hne => absurd rfl (hne b₀ b₁)

/-- A hereditarily well-shaped basis whose exposed type is a space is a
    hereditary space basis. -/
theorem Basis.IsTyBasis.toIsSpaceBasis_of_tof_eq {b : Basis} {s : Space}
    (h : Basis.IsTyBasis b) (htof : Basis.tof b = .space s) :
    Basis.IsSpaceBasis b :=
  h.toIsSpaceBasis (fun b₀ b₁ heq => by
    subst b
    simp [Basis.tof] at htof)

/-- Opening changes terms occurring in a basis, but never its constructor
    tree or the length of a `.terms` list.  Hence hereditary space-basis shape
    can also be reflected from an opened basis back to its closed source. -/
theorem Basis.IsSpaceBasis.of_openRec (k : Nat) (u : Term) :
    ∀ {b : Basis}, Basis.IsSpaceBasis (Basis.openRec k u b) →
      Basis.IsSpaceBasis b
  | .empty, _ => trivial
  | .one, _ => trivial
  | .dual b, h => Basis.IsSpaceBasis.of_openRec k u (b := b) h
  | .dsum b₀ b₁, h =>
      ⟨Basis.IsSpaceBasis.of_openRec k u h.1,
        Basis.IsSpaceBasis.of_openRec k u h.2⟩
  | .tprod b₀ b₁, h =>
      ⟨Basis.IsSpaceBasis.of_openRec k u h.1,
        Basis.IsSpaceBasis.of_openRec k u h.2⟩
  | .proj _ b₀ b₁, h =>
      ⟨Basis.IsSpaceBasis.of_openRec k u h.1,
        Basis.IsSpaceBasis.of_openRec k u h.2⟩
  | .image b, h => Basis.IsSpaceBasis.of_openRec k u (b := b) h
  | .terms _ es b, h => by
      refine ⟨?_, Basis.IsSpaceBasis.of_openRec k u h.2⟩
      simpa [Term.openRecList] using h.1
  | .frame _ _, h => False.elim h

/-- The type-basis analogue of `IsSpaceBasis.of_openRec`. -/
theorem Basis.IsTyBasis.of_openRec (u : Term) :
    ∀ {b : Basis} (k : Nat), Basis.IsTyBasis (Basis.openRec k u b) →
      Basis.IsTyBasis b
  | .frame b₀ b₁, k, h =>
      ⟨Basis.IsTyBasis.of_openRec u k h.1,
        Basis.IsTyBasis.of_openRec u (k + 1) h.2⟩
  | .empty, k, h => Basis.IsSpaceBasis.of_openRec k u h
  | .one, k, h => Basis.IsSpaceBasis.of_openRec k u h
  | .dual _, k, h => Basis.IsSpaceBasis.of_openRec k u h
  | .dsum _ _, k, h => Basis.IsSpaceBasis.of_openRec k u h
  | .tprod _ _, k, h => Basis.IsSpaceBasis.of_openRec k u h
  | .proj _ _ _, k, h => Basis.IsSpaceBasis.of_openRec k u h
  | .image _, k, h => Basis.IsSpaceBasis.of_openRec k u h
  | .terms _ _ _, k, h => Basis.IsSpaceBasis.of_openRec k u h

/-- The strengthened validity rules enforce hereditary basis shape.  Frames
    may occur at genuine dependent-function positions (and recurse there),
    but cannot be hidden below a space-basis constructor; explicit terms
    bases are nonempty. -/
theorem Basis.BasisValid.isTyBasis {Gamma : NLCtx} {b : Basis}
    (h : Basis.BasisValid Gamma b) : Basis.IsTyBasis b := by
  induction h with
  | empty => trivial
  | one => trivial
  | dual _ htof ih => exact ih.toIsSpaceBasis_of_tof_eq htof
  | dsum _ _ htof₀ htof₁ ih₀ ih₁ =>
      exact ⟨ih₀.toIsSpaceBasis_of_tof_eq htof₀,
        ih₁.toIsSpaceBasis_of_tof_eq htof₁⟩
  | tprod _ _ htof₀ htof₁ ih₀ ih₁ =>
      exact ⟨ih₀.toIsSpaceBasis_of_tof_eq htof₀,
        ih₁.toIsSpaceBasis_of_tof_eq htof₁⟩
  | proj_ker _ _ htof₀ htof₁ _ ih₀ ih₁ =>
      exact ⟨ih₀.toIsSpaceBasis_of_tof_eq htof₀,
        ih₁.toIsSpaceBasis_of_tof_eq htof₁⟩
  | proj_coker _ _ htof₀ htof₁ _ ih₀ ih₁ =>
      exact ⟨ih₀.toIsSpaceBasis_of_tof_eq htof₀,
        ih₁.toIsSpaceBasis_of_tof_eq htof₁⟩
  | proj_img _ _ htof₀ htof₁ _ ih₀ ih₁ =>
      exact ⟨ih₀.toIsSpaceBasis_of_tof_eq htof₀,
        ih₁.toIsSpaceBasis_of_tof_eq htof₁⟩
  | proj_coimg _ _ htof₀ htof₁ _ ih₀ ih₁ =>
      exact ⟨ih₀.toIsSpaceBasis_of_tof_eq htof₀,
        ih₁.toIsSpaceBasis_of_tof_eq htof₁⟩
  | image _ hsof _ ih =>
      exact ih.toIsSpaceBasis (fun b₀ b₁ heq => by
        subst heq
        simp [Basis.sof] at hsof)
  | terms _ htof _ _ hne ih =>
      exact ⟨hne, ih.toIsSpaceBasis_of_tof_eq htof⟩
  | frame L _ _ ih₀ ihbody =>
      refine ⟨ih₀, ?_⟩
      obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset L
      exact Basis.IsTyBasis.of_openRec (.var y) 0 (ihbody y hy)

/-- The literal standard basis of any type is hereditarily well formed. -/
theorem Basis.isTyBasis_std : ∀ τ : Ty, Basis.IsTyBasis (Basis.std τ)
  | .space s => (Basis.isSpaceBasis_stdSpace s).toIsTyBasis
  | .piTy τ₀ τ₁ => ⟨Basis.isTyBasis_std τ₀, Basis.isTyBasis_std τ₁⟩

/-- `stdSpace` commutes with the ⊕-chain: the n+1-fold chain of the standard
    basis IS the standard basis of the n+1-fold chain space — aligns
    `EvalBB.terms_rref`'s `Basis.dsumChain b' es.length` (at `b' := stdSpace s`)
    with `progress_std`'s output basis `Basis.std (.space (Space.dsumChain s
    es.length))`. -/
theorem Basis.stdSpace_dsumChain (s : Space) :
    ∀ n : Nat, Basis.dsumChain (Basis.stdSpace s) n
      = Basis.stdSpace (Space.dsumChain s n)
  | 0 => rfl
  | n + 1 => by
      simp only [Basis.dsumChain, Space.dsumChain, Basis.stdSpace,
        Basis.stdSpace_dsumChain s n]

end GLang
