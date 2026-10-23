import GLang.Graded.BridgeBwd

/-!
# Proof-preserving freshening of source cofinite binders

The source typing judgments are proof relevant: a consumer may recurse over the
particular `SValid`/`TValid`/`SubType`/`HasType` witness it receives.  Merely
knowing that a fresh name exists is therefore not enough when such a consumer
must reserve an ambient finite set (for example the names of an evaluation
context).

This module rebuilds the complete mutual source derivation while enlarging
every cofinite binder's avoid set.  It changes neither the judgment indices nor
the typing rules.  The recursion also enters the `HasType` witnesses stored in
fundamental spaces and subtyping derivations.
-/

namespace GLang
namespace Adequacy
namespace CofiniteFreshen

/-- Avoid set used by a type binder. -/
def typeAvoid (A : Finset Name) (Gamma : NLCtx) (L : Finset Name) : Finset Name :=
  L ∪ A ∪ Gamma.keys

/-- Avoid set used by a term binder.  Both source contexts are reserved; for
nonlinear lambdas `Delta` is empty, so this specializes to `typeAvoid`. -/
def termAvoid (A : Finset Name) (Delta : LCtx) (Gamma : NLCtx)
    (L : Finset Name) : Finset Name :=
  L ∪ A ∪ Delta.keys ∪ Gamma.keys

@[simp] theorem mem_typeAvoid {A : Finset Name} {Gamma : NLCtx}
    {L : Finset Name} {x : Name} :
    x ∈ typeAvoid A Gamma L ↔ x ∈ L ∨ x ∈ A ∨ x ∈ Gamma.keys := by
  simp [typeAvoid]

@[simp] theorem mem_termAvoid {A : Finset Name} {Delta : LCtx}
    {Gamma : NLCtx} {L : Finset Name} {x : Name} :
    x ∈ termAvoid A Delta Gamma L ↔
      x ∈ L ∨ x ∈ A ∨ x ∈ Delta.keys ∨ x ∈ Gamma.keys := by
  simp [termAvoid]

theorem original_subset_typeAvoid (A : Finset Name) (Gamma : NLCtx)
    (L : Finset Name) : L ⊆ typeAvoid A Gamma L := by
  intro x hx
  exact mem_typeAvoid.mpr (Or.inl hx)

theorem ambient_subset_typeAvoid (A : Finset Name) (Gamma : NLCtx)
    (L : Finset Name) : A ⊆ typeAvoid A Gamma L := by
  intro x hx
  exact mem_typeAvoid.mpr (Or.inr (Or.inl hx))

theorem nonlinearKeys_subset_typeAvoid (A : Finset Name) (Gamma : NLCtx)
    (L : Finset Name) : Gamma.keys ⊆ typeAvoid A Gamma L := by
  intro x hx
  exact mem_typeAvoid.mpr (Or.inr (Or.inr hx))

theorem original_subset_termAvoid (A : Finset Name) (Delta : LCtx)
    (Gamma : NLCtx) (L : Finset Name) : L ⊆ termAvoid A Delta Gamma L := by
  intro x hx
  exact mem_termAvoid.mpr (Or.inl hx)

theorem ambient_subset_termAvoid (A : Finset Name) (Delta : LCtx)
    (Gamma : NLCtx) (L : Finset Name) : A ⊆ termAvoid A Delta Gamma L := by
  intro x hx
  exact mem_termAvoid.mpr (Or.inr (Or.inl hx))

theorem linearKeys_subset_termAvoid (A : Finset Name) (Delta : LCtx)
    (Gamma : NLCtx) (L : Finset Name) : Delta.keys ⊆ termAvoid A Delta Gamma L := by
  intro x hx
  exact mem_termAvoid.mpr (Or.inr (Or.inr (Or.inl hx)))

theorem nonlinearKeys_subset_termAvoid (A : Finset Name) (Delta : LCtx)
    (Gamma : NLCtx) (L : Finset Name) : Gamma.keys ⊆ termAvoid A Delta Gamma L := by
  intro x hx
  exact mem_termAvoid.mpr (Or.inr (Or.inr (Or.inr hx)))

/-! ## Hereditary binder-hygiene contract

The four predicates below are the observable contract of this module.  At
each cofinite binder they require the binder's actual avoid set to contain the
ambient set and the keys of the contexts in which that binder occurs.  They
then recurse through every premise, including FFS `HasType` witnesses.
-/

mutual

/-- Every binder nested in a space-validity derivation reserves `A` and its
current source-context keys. -/
def SBinderHygiene (A : Finset Name) :
    {Gamma : NLCtx} → {s : Space} → SValid Gamma s → Prop
  | _, _, .empty => True
  | _, _, .real => True
  | _, _, .dual hs => SBinderHygiene A hs
  | _, _, .dsum hs0 hs1 => SBinderHygiene A hs0 ∧ SBinderHygiene A hs1
  | _, _, .tprod hs0 hs1 => SBinderHygiene A hs0 ∧ SBinderHygiene A hs1
  | _, _, .ker hs0 hs1 he =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧ BinderHygiene A he
  | _, _, .coker hs0 hs1 he =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧ BinderHygiene A he
  | _, _, .img hs0 hs1 he =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧ BinderHygiene A he
  | _, _, .coimg hs0 hs1 he =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧ BinderHygiene A he

/-- Every dependent-type binder reserves `A` and the current nonlinear keys,
hereditarily through its domain and opened bodies. -/
def TBinderHygiene (A : Finset Name) :
    {Gamma : NLCtx} → {tau : Ty} → {k : Kind} → TValid Gamma tau k → Prop
  | _, _, _, .space hs => SBinderHygiene A hs
  | Gamma, _, _, .piTy L ht0 hbody =>
      A ⊆ L ∧ Gamma.keys ⊆ L ∧ TBinderHygiene A ht0 ∧
        ∀ y (hy : y ∉ L), TBinderHygiene A (hbody y hy)

/-- Every binder nested in a subtyping derivation reserves `A` and its
current source-context keys. -/
def SubBinderHygiene (A : Finset Name) :
    {Gamma : NLCtx} → {s0 s1 : Space} → SubType Gamma s0 s1 → Prop
  | _, _, _, .sub_ker hs0 hs1 he =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧ BinderHygiene A he
  | _, _, _, .sub_coker hs0 hs1 he =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧ BinderHygiene A he
  | _, _, _, .sub_img hs0 hs1 he =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧ BinderHygiene A he
  | _, _, _, .sub_coimg hs0 hs1 he =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧ BinderHygiene A he

/-- Every term binder reserves `A`, its current nonlinear keys, and (for a
linear lambda) its current linear keys, hereditarily through all premises. -/
def BinderHygiene (A : Finset Name) :
    {Delta : LCtx} → {Gamma : NLCtx} → {e : Term} → {tau : Ty} →
      HasType Delta Gamma e tau → Prop
  | _, _, _, _, .zero hs => SBinderHygiene A hs
  | _, _, _, _, .smul hs _ h0 h1 =>
      SBinderHygiene A hs ∧ BinderHygiene A h0 ∧ BinderHygiene A h1
  | _, _, _, _, .add hs h0 h1 =>
      SBinderHygiene A hs ∧ BinderHygiene A h0 ∧ BinderHygiene A h1
  | _, _, _, _, .inner hs => SBinderHygiene A hs
  | _, _, _, _, .real_lit _ => True
  | _, _, _, _, .app_linear hs0 hs1 _ h0 h1 =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧
        BinderHygiene A h0 ∧ BinderHygiene A h1
  | _, _, _, _, .app_inner hs _ h0 h1 =>
      SBinderHygiene A hs ∧ BinderHygiene A h0 ∧ BinderHygiene A h1
  | _, _, _, _, .app_nonlinear h0 h1 => BinderHygiene A h0 ∧ BinderHygiene A h1
  | _, _, _, _, .var_lin => True
  | _, _, _, _, .var_nlin _ => True
  | _, _, _, _, .pinv_tensor hs0 hs1 he =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧ BinderHygiene A he
  | _, _, _, _, .pinv_dual hs he => SBinderHygiene A hs ∧ BinderHygiene A he
  | _, _, _, _, .promote _ _ _ _ he => BinderHygiene A he
  | _, _, _, _, .dsumE hs0 hs1 h0 h1 =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧
        BinderHygiene A h0 ∧ BinderHygiene A h1
  | _, _, _, _, .tprodE hs0 hs1 _ h0 h1 =>
      SBinderHygiene A hs0 ∧ SBinderHygiene A hs1 ∧
        BinderHygiene A h0 ∧ BinderHygiene A h1
  | Delta, Gamma, _, _, .llam_real L hs hbody =>
      A ⊆ L ∧ Delta.keys ⊆ L ∧ Gamma.keys ⊆ L ∧
        SBinderHygiene A hs ∧
        ∀ y (hy : y ∉ L), BinderHygiene A (hbody y hy)
  | Delta, Gamma, _, _, .llam_tensor L _ hs0 hs hbody =>
      A ⊆ L ∧ Delta.keys ⊆ L ∧ Gamma.keys ⊆ L ∧
        SBinderHygiene A hs0 ∧ SBinderHygiene A hs ∧
        ∀ y (hy : y ∉ L), BinderHygiene A (hbody y hy)
  | _, _, _, _, .embed hsub => SubBinderHygiene A hsub
  | _, Gamma, _, _, .nllam L ht hbody =>
      A ⊆ L ∧ Gamma.keys ⊆ L ∧ TBinderHygiene A ht ∧
        ∀ y (hy : y ∉ L), BinderHygiene A (hbody y hy)

end

mutual

/-- Rebuild a space-validity proof, reserving `A` at every nested cofinite
binder (including those inside embedded term witnesses). -/
def svalid (A : Finset Name) :
    {Gamma : NLCtx} → {s : Space} → SValid Gamma s → SValid Gamma s
  | _, _, .empty => .empty
  | _, _, .real => .real
  | _, _, .dual hs => .dual (svalid A hs)
  | _, _, .dsum hs0 hs1 => .dsum (svalid A hs0) (svalid A hs1)
  | _, _, .tprod hs0 hs1 => .tprod (svalid A hs0) (svalid A hs1)
  | _, _, .ker hs0 hs1 he =>
      .ker (svalid A hs0) (svalid A hs1) (hasType A he)
  | _, _, .coker hs0 hs1 he =>
      .coker (svalid A hs0) (svalid A hs1) (hasType A he)
  | _, _, .img hs0 hs1 he =>
      .img (svalid A hs0) (svalid A hs1) (hasType A he)
  | _, _, .coimg hs0 hs1 he =>
      .coimg (svalid A hs0) (svalid A hs1) (hasType A he)

/-- Rebuild a type-validity proof, reserving `A` and the current nonlinear
context at every dependent-type binder. -/
def tvalid (A : Finset Name) :
    {Gamma : NLCtx} → {tau : Ty} → {k : Kind} →
      TValid Gamma tau k → TValid Gamma tau k
  | _, _, _, .space hs => .space (svalid A hs)
  | Gamma, _, _, .piTy L ht0 hbody =>
      .piTy (typeAvoid A Gamma L) (tvalid A ht0)
        (fun y hy =>
          tvalid A (hbody y (by
            intro hyL
            exact hy (mem_typeAvoid.mpr (Or.inl hyL)))))

/-- Rebuild a subtyping proof, recursively freshening its formation and term
witnesses. -/
def subtype (A : Finset Name) :
    {Gamma : NLCtx} → {s0 s1 : Space} →
      SubType Gamma s0 s1 → SubType Gamma s0 s1
  | _, _, _, .sub_ker hs0 hs1 he =>
      .sub_ker (svalid A hs0) (svalid A hs1) (hasType A he)
  | _, _, _, .sub_coker hs0 hs1 he =>
      .sub_coker (svalid A hs0) (svalid A hs1) (hasType A he)
  | _, _, _, .sub_img hs0 hs1 he =>
      .sub_img (svalid A hs0) (svalid A hs1) (hasType A he)
  | _, _, _, .sub_coimg hs0 hs1 he =>
      .sub_coimg (svalid A hs0) (svalid A hs1) (hasType A he)

/-- Rebuild a term-typing proof, reserving `A` and both current source
contexts at every term binder. -/
def hasType (A : Finset Name) :
    {Delta : LCtx} → {Gamma : NLCtx} → {e : Term} → {tau : Ty} →
      HasType Delta Gamma e tau → HasType Delta Gamma e tau
  | _, _, _, _, .zero hs => .zero (svalid A hs)
  | _, _, _, _, .smul hs hd h0 h1 =>
      .smul (svalid A hs) hd (hasType A h0) (hasType A h1)
  | _, _, _, _, .add hs h0 h1 =>
      .add (svalid A hs) (hasType A h0) (hasType A h1)
  | _, _, _, _, .inner hs => .inner (svalid A hs)
  | _, _, _, _, .real_lit r => .real_lit r
  | _, _, _, _, .app_linear hs0 hs1 hd h0 h1 =>
      .app_linear (svalid A hs0) (svalid A hs1) hd
        (hasType A h0) (hasType A h1)
  | _, _, _, _, .app_inner hs hd h0 h1 =>
      .app_inner (svalid A hs) hd (hasType A h0) (hasType A h1)
  | _, _, _, _, .app_nonlinear h0 h1 =>
      .app_nonlinear (hasType A h0) (hasType A h1)
  | _, _, _, _, .var_lin => .var_lin
  | _, _, _, _, .var_nlin hlookup => .var_nlin hlookup
  | _, _, _, _, .pinv_tensor hs0 hs1 he =>
      .pinv_tensor (svalid A hs0) (svalid A hs1) (hasType A he)
  | _, _, _, _, .pinv_dual hs he =>
      .pinv_dual (svalid A hs) (hasType A he)
  | _, _, _, _, .promote lin hdDelta hdGamma hfresh he =>
      .promote lin hdDelta hdGamma hfresh (hasType A he)
  | _, _, _, _, .dsumE hs0 hs1 h0 h1 =>
      .dsumE (svalid A hs0) (svalid A hs1) (hasType A h0) (hasType A h1)
  | _, _, _, _, .tprodE hs0 hs1 hd h0 h1 =>
      .tprodE (svalid A hs0) (svalid A hs1) hd
        (hasType A h0) (hasType A h1)
  | Delta, Gamma, _, _, .llam_real L hs hbody =>
      .llam_real (termAvoid A Delta Gamma L) (svalid A hs)
        (fun y hy =>
          hasType A (hbody y (by
            intro hyL
            exact hy (mem_termAvoid.mpr (Or.inl hyL)))))
  | Delta, Gamma, _, _, .llam_tensor L hne hs0 hs hbody =>
      .llam_tensor (termAvoid A Delta Gamma L) hne
        (svalid A hs0) (svalid A hs)
        (fun y hy =>
          hasType A (hbody y (by
            intro hyL
            exact hy (mem_termAvoid.mpr (Or.inl hyL)))))
  | _, _, _, _, .embed hsub => .embed (subtype A hsub)
  | _, Gamma, _, _, .nllam L ht hbody =>
      .nllam (typeAvoid A Gamma L) (tvalid A ht)
        (fun y hy =>
          hasType A (hbody y (by
            intro hyL
            exact hy (mem_typeAvoid.mpr (Or.inl hyL)))))

end

/-! ## The freshener establishes the hygiene contract -/

mutual

/-- The freshened space-validity derivation satisfies `SBinderHygiene`. -/
def svalid_binderHygiene (A : Finset Name) :
    {Gamma : NLCtx} → {s : Space} → (h : SValid Gamma s) →
      SBinderHygiene A (svalid A h)
  | _, _, .empty => True.intro
  | _, _, .real => True.intro
  | _, _, .dual hs => svalid_binderHygiene A hs
  | _, _, .dsum hs0 hs1 =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1⟩
  | _, _, .tprod hs0 hs1 =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1⟩
  | _, _, .ker hs0 hs1 he =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A he⟩
  | _, _, .coker hs0 hs1 he =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A he⟩
  | _, _, .img hs0 hs1 he =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A he⟩
  | _, _, .coimg hs0 hs1 he =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A he⟩

/-- The freshened type-validity derivation satisfies `TBinderHygiene`. -/
def tvalid_binderHygiene (A : Finset Name) :
    {Gamma : NLCtx} → {tau : Ty} → {k : Kind} →
      (h : TValid Gamma tau k) → TBinderHygiene A (tvalid A h)
  | _, _, _, .space hs => svalid_binderHygiene A hs
  | Gamma, _, _, .piTy L ht0 hbody =>
      ⟨ambient_subset_typeAvoid A Gamma L,
        nonlinearKeys_subset_typeAvoid A Gamma L,
        tvalid_binderHygiene A ht0,
        fun y hy =>
          tvalid_binderHygiene A (hbody y (by
            intro hyL
            exact hy (mem_typeAvoid.mpr (Or.inl hyL))))⟩

/-- The freshened subtyping derivation satisfies `SubBinderHygiene`. -/
def subtype_binderHygiene (A : Finset Name) :
    {Gamma : NLCtx} → {s0 s1 : Space} → (h : SubType Gamma s0 s1) →
      SubBinderHygiene A (subtype A h)
  | _, _, _, .sub_ker hs0 hs1 he =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A he⟩
  | _, _, _, .sub_coker hs0 hs1 he =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A he⟩
  | _, _, _, .sub_img hs0 hs1 he =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A he⟩
  | _, _, _, .sub_coimg hs0 hs1 he =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A he⟩

/-- The freshened term-typing derivation satisfies `BinderHygiene`. -/
def hasType_binderHygiene (A : Finset Name) :
    {Delta : LCtx} → {Gamma : NLCtx} → {e : Term} → {tau : Ty} →
      (h : HasType Delta Gamma e tau) → BinderHygiene A (hasType A h)
  | _, _, _, _, .zero hs => svalid_binderHygiene A hs
  | _, _, _, _, .smul hs _ h0 h1 =>
      ⟨svalid_binderHygiene A hs,
        hasType_binderHygiene A h0, hasType_binderHygiene A h1⟩
  | _, _, _, _, .add hs h0 h1 =>
      ⟨svalid_binderHygiene A hs,
        hasType_binderHygiene A h0, hasType_binderHygiene A h1⟩
  | _, _, _, _, .inner hs => svalid_binderHygiene A hs
  | _, _, _, _, .real_lit _ => True.intro
  | _, _, _, _, .app_linear hs0 hs1 _ h0 h1 =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A h0, hasType_binderHygiene A h1⟩
  | _, _, _, _, .app_inner hs _ h0 h1 =>
      ⟨svalid_binderHygiene A hs,
        hasType_binderHygiene A h0, hasType_binderHygiene A h1⟩
  | _, _, _, _, .app_nonlinear h0 h1 =>
      ⟨hasType_binderHygiene A h0, hasType_binderHygiene A h1⟩
  | _, _, _, _, .var_lin => True.intro
  | _, _, _, _, .var_nlin _ => True.intro
  | _, _, _, _, .pinv_tensor hs0 hs1 he =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A he⟩
  | _, _, _, _, .pinv_dual hs he =>
      ⟨svalid_binderHygiene A hs, hasType_binderHygiene A he⟩
  | _, _, _, _, .promote _ _ _ _ he => hasType_binderHygiene A he
  | _, _, _, _, .dsumE hs0 hs1 h0 h1 =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A h0, hasType_binderHygiene A h1⟩
  | _, _, _, _, .tprodE hs0 hs1 _ h0 h1 =>
      ⟨svalid_binderHygiene A hs0, svalid_binderHygiene A hs1,
        hasType_binderHygiene A h0, hasType_binderHygiene A h1⟩
  | Delta, Gamma, _, _, .llam_real L hs hbody =>
      ⟨ambient_subset_termAvoid A Delta Gamma L,
        linearKeys_subset_termAvoid A Delta Gamma L,
        nonlinearKeys_subset_termAvoid A Delta Gamma L,
        svalid_binderHygiene A hs,
        fun y hy =>
          hasType_binderHygiene A (hbody y (by
            intro hyL
            exact hy (mem_termAvoid.mpr (Or.inl hyL))))⟩
  | Delta, Gamma, _, _, .llam_tensor L _ hs0 hs hbody =>
      ⟨ambient_subset_termAvoid A Delta Gamma L,
        linearKeys_subset_termAvoid A Delta Gamma L,
        nonlinearKeys_subset_termAvoid A Delta Gamma L,
        svalid_binderHygiene A hs0,
        svalid_binderHygiene A hs,
        fun y hy =>
          hasType_binderHygiene A (hbody y (by
            intro hyL
            exact hy (mem_termAvoid.mpr (Or.inl hyL))))⟩
  | _, _, _, _, .embed hsub => subtype_binderHygiene A hsub
  | _, Gamma, _, _, .nllam L ht hbody =>
      ⟨ambient_subset_typeAvoid A Gamma L,
        nonlinearKeys_subset_typeAvoid A Gamma L,
        tvalid_binderHygiene A ht,
        fun y hy =>
          hasType_binderHygiene A (hbody y (by
            intro hyL
            exact hy (mem_typeAvoid.mpr (Or.inl hyL))))⟩

end

/-! ## Hereditary preservation of promotion-freedom

These maps deliberately retain a source `promote` node if one is present.
Consequently freshening is not a normalization pass, but it preserves the
strong hereditary `Graded.*PromotionFree` predicates exactly in the direction
needed after `normalizeCheckedTyping`.
-/

mutual

/-- Freshening preserves hereditary promotion-freedom for spaces. -/
def svalid_promotionFree (A : Finset Name) :
    {Gamma : NLCtx} → {s : Space} → (h : SValid Gamma s) →
      Graded.SPromotionFree h → Graded.SPromotionFree (svalid A h)
  | _, _, .empty, _ => True.intro
  | _, _, .real, _ => True.intro
  | _, _, .dual hs, hfree => svalid_promotionFree A hs hfree
  | _, _, .dsum hs0 hs1, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2⟩
  | _, _, .tprod hs0 hs1, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2⟩
  | _, _, .ker hs0 hs1 he, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A he hfree.2.2⟩
  | _, _, .coker hs0 hs1 he, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A he hfree.2.2⟩
  | _, _, .img hs0 hs1 he, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A he hfree.2.2⟩
  | _, _, .coimg hs0 hs1 he, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A he hfree.2.2⟩

/-- Freshening preserves hereditary promotion-freedom for types. -/
def tvalid_promotionFree (A : Finset Name) :
    {Gamma : NLCtx} → {tau : Ty} → {k : Kind} →
      (h : TValid Gamma tau k) →
      Graded.TPromotionFree h → Graded.TPromotionFree (tvalid A h)
  | _, _, _, .space hs, hfree => svalid_promotionFree A hs hfree
  | _, _, _, .piTy L ht0 hbody, hfree =>
      ⟨tvalid_promotionFree A ht0 hfree.1,
        fun y hy =>
          let hyL : y ∉ L := fun hyOld =>
            hy (mem_typeAvoid.mpr (Or.inl hyOld))
          tvalid_promotionFree A (hbody y hyL) (hfree.2 y hyL)⟩

/-- Freshening preserves hereditary promotion-freedom for subtyping. -/
def subtype_promotionFree (A : Finset Name) :
    {Gamma : NLCtx} → {s0 s1 : Space} →
      (h : SubType Gamma s0 s1) →
      Graded.SubPromotionFree h → Graded.SubPromotionFree (subtype A h)
  | _, _, _, .sub_ker hs0 hs1 he, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A he hfree.2.2⟩
  | _, _, _, .sub_coker hs0 hs1 he, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A he hfree.2.2⟩
  | _, _, _, .sub_img hs0 hs1 he, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A he hfree.2.2⟩
  | _, _, _, .sub_coimg hs0 hs1 he, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A he hfree.2.2⟩

/-- Freshening preserves hereditary promotion-freedom for term typing. -/
def hasType_promotionFree (A : Finset Name) :
    {Delta : LCtx} → {Gamma : NLCtx} → {e : Term} → {tau : Ty} →
      (h : HasType Delta Gamma e tau) →
      Graded.PromotionFree h → Graded.PromotionFree (hasType A h)
  | _, _, _, _, .zero hs, hfree => svalid_promotionFree A hs hfree
  | _, _, _, _, .smul hs _ h0 h1, hfree =>
      ⟨svalid_promotionFree A hs hfree.1,
        hasType_promotionFree A h0 hfree.2.1,
        hasType_promotionFree A h1 hfree.2.2⟩
  | _, _, _, _, .add hs h0 h1, hfree =>
      ⟨svalid_promotionFree A hs hfree.1,
        hasType_promotionFree A h0 hfree.2.1,
        hasType_promotionFree A h1 hfree.2.2⟩
  | _, _, _, _, .inner hs, hfree => svalid_promotionFree A hs hfree
  | _, _, _, _, .real_lit _, _ => True.intro
  | _, _, _, _, .app_linear hs0 hs1 _ h0 h1, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A h0 hfree.2.2.1,
        hasType_promotionFree A h1 hfree.2.2.2⟩
  | _, _, _, _, .app_inner hs _ h0 h1, hfree =>
      ⟨svalid_promotionFree A hs hfree.1,
        hasType_promotionFree A h0 hfree.2.1,
        hasType_promotionFree A h1 hfree.2.2⟩
  | _, _, _, _, .app_nonlinear h0 h1, hfree =>
      ⟨hasType_promotionFree A h0 hfree.1,
        hasType_promotionFree A h1 hfree.2⟩
  | _, _, _, _, .var_lin, _ => True.intro
  | _, _, _, _, .var_nlin _, _ => True.intro
  | _, _, _, _, .pinv_tensor hs0 hs1 he, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A he hfree.2.2⟩
  | _, _, _, _, .pinv_dual hs he, hfree =>
      ⟨svalid_promotionFree A hs hfree.1,
        hasType_promotionFree A he hfree.2⟩
  | _, _, _, _, .promote _ _ _ _ _, hfree => False.elim hfree
  | _, _, _, _, .dsumE hs0 hs1 h0 h1, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A h0 hfree.2.2.1,
        hasType_promotionFree A h1 hfree.2.2.2⟩
  | _, _, _, _, .tprodE hs0 hs1 _ h0 h1, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs1 hfree.2.1,
        hasType_promotionFree A h0 hfree.2.2.1,
        hasType_promotionFree A h1 hfree.2.2.2⟩
  | _, _, _, _, .llam_real L hs hbody, hfree =>
      ⟨svalid_promotionFree A hs hfree.1,
        fun y hy =>
          let hyL : y ∉ L := fun hyOld =>
            hy (mem_termAvoid.mpr (Or.inl hyOld))
          hasType_promotionFree A (hbody y hyL) (hfree.2 y hyL)⟩
  | _, _, _, _, .llam_tensor L _ hs0 hs hbody, hfree =>
      ⟨svalid_promotionFree A hs0 hfree.1,
        svalid_promotionFree A hs hfree.2.1,
        fun y hy =>
          let hyL : y ∉ L := fun hyOld =>
            hy (mem_termAvoid.mpr (Or.inl hyOld))
          hasType_promotionFree A (hbody y hyL) (hfree.2.2 y hyL)⟩
  | _, _, _, _, .embed hsub, hfree => subtype_promotionFree A hsub hfree
  | _, _, _, _, .nllam L ht hbody, hfree =>
      ⟨tvalid_promotionFree A ht hfree.1,
        fun y hy =>
          let hyL : y ∉ L := fun hyOld =>
            hy (mem_typeAvoid.mpr (Or.inl hyOld))
          hasType_promotionFree A (hbody y hyL) (hfree.2 y hyL)⟩

end

/-- A freshened proof paired with promotion-freedom, for consumers that must
retain both pieces as dependent data. -/
def hasTypeFree (A : Finset Name)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) (hfree : Graded.PromotionFree h) :
    {h' : HasType Delta Gamma e tau // Graded.PromotionFree h'} :=
  ⟨hasType A h, hasType_promotionFree A h hfree⟩

/-- The proof contained in the existing `hasTypeFree` package also satisfies
the hereditary binder-hygiene contract. -/
theorem hasTypeFree_binderHygiene (A : Finset Name)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) (hfree : Graded.PromotionFree h) :
    BinderHygiene A (hasTypeFree A h hfree).1 :=
  hasType_binderHygiene A h

/-- A source typing proof carrying both guarantees needed by checked progress:
it has no promotion anywhere in its mutual tree, and every cofinite binder
reserves the chosen ambient names and the context keys at that node. -/
structure FreeHygienicTyping (A : Finset Name)
    (Delta : LCtx) (Gamma : NLCtx) (e : Term) (tau : Ty) : Type where
  typing : HasType Delta Gamma e tau
  promotionFree : Graded.PromotionFree typing
  binderHygiene : BinderHygiene A typing

/-- Strengthened package for callers that consume promotion-freedom and binder
hygiene together.  `hasTypeFree` remains unchanged for existing callers. -/
def hasTypeFreeHygienic (A : Finset Name)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) (hfree : Graded.PromotionFree h) :
    FreeHygienicTyping A Delta Gamma e tau where
  typing := hasType A h
  promotionFree := hasType_promotionFree A h hfree
  binderHygiene := hasType_binderHygiene A h

end CofiniteFreshen
end Adequacy
end GLang
