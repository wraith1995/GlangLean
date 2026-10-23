import GLang.Proofs.Value.Partial.PartialValueQuotient

/-! Error-sensitive extensional relations for partial dependent type
interpretations. Unlike membership, related functions must preserve equivalent
higher-order arguments and agree on errors as well as successful results. -/
namespace GLang.PartialValueDomains
universe u
open PaperValueDomains PaperValueDomains.ExtensionalQuotient

/-- Two partially interpreted types relate successful values only when both
types denote; function outputs are compared in their actual partial fibres. -/
def PartialRelated : (τ : ValTy) → Except DimError (PartialValType τ) →
    Except DimError (PartialValType τ) → τ.carrierEl → τ.carrierEl → Prop
  | .space _, .ok n, .ok m, a, b => a = b ∧ a.length = n ∧ b.length = m
  | .piTy d c, .ok (D,F), .ok (E,G), f, g =>
      ∀ a b, PartialRelated d (.ok D) (.ok E) a b →
        PartialRel (PartialRelated c (F a) (G b)) (f a) (g b)
  | _, _, _, _, _ => False

/-- Type coherence includes agreement on failure, recursively in every pair
of equivalent successful arguments. It is local to the type's fibres. -/
def PartialCoherent : (τ : ValTy) → Except DimError (PartialValType τ) →
    Except DimError (PartialValType τ) → Prop
  | _, .error e, .error e' => e = e'
  | .space _, .ok n, .ok m => n = m
  | .piTy d c, .ok (D,F), .ok (E,G) =>
      PartialCoherent d (.ok D) (.ok E) ∧
      ∀ a b, PartialRelated d (.ok D) (.ok E) a b → PartialCoherent c (F a) (G b)
  | _, _, _ => False

theorem partialRelated_symm (τ : ValTy) (T U : Except DimError (PartialValType τ))
    (a b : τ.carrierEl) (h : PartialRelated τ T U a b) : PartialRelated τ U T b a := by
  cases τ with
  | space s =>
    cases T <;> cases U <;> try exact False.elim h
    exact ⟨h.1.symm,h.2.2,h.2.1⟩
  | piTy d c =>
    cases T <;> cases U <;> try exact False.elim h
    rename_i T U
    rcases T with ⟨D,F⟩
    rcases U with ⟨E,G⟩
    intro x y hxy
    exact PartialRel.symm (fun u v huv => partialRelated_symm c _ _ u v huv)
      (h y x (partialRelated_symm d _ _ x y hxy))
termination_by sizeOf τ

theorem partialCoherent_symm (τ : ValTy) (T U : Except DimError (PartialValType τ))
    (h : PartialCoherent τ T U) : PartialCoherent τ U T := by
  cases τ with
  | space s =>
    cases T <;> cases U <;> try exact False.elim h
    all_goals exact h.symm
  | piTy d c =>
    cases T <;> cases U <;> try exact False.elim h
    · exact h.symm
    · rename_i T U
      rcases T with ⟨D,F⟩
      rcases U with ⟨E,G⟩
      exact ⟨partialCoherent_symm d _ _ h.1, fun a b hab =>
        partialCoherent_symm c _ _ (h.2 b a (partialRelated_symm d _ _ a b hab))⟩
termination_by sizeOf τ

/-- Coherent interpretations agree on whether the type itself fails. -/
theorem partialCoherent_error {τ : ValTy} {T : Except DimError (PartialValType τ)}
    {err : DimError} (h : PartialCoherent τ (.error err) T) : T = .error err := by
  cases τ <;> cases T <;> simp_all [PartialCoherent]

/-- Relatedness laws for a pairwise coherent family of partial types. -/
structure PartialFamilyLaws (τ : ValTy) {I : Type u}
    (T : I → Except DimError (PartialValType τ)) : Prop where
  transport : ∀ i j k l a b,
    PartialRelated τ (T i) (T j) a b ↔ PartialRelated τ (T k) (T l) a b
  trans : ∀ i j k a b c,
    PartialRelated τ (T i) (T j) a b → PartialRelated τ (T j) (T k) b c →
      PartialRelated τ (T i) (T k) a c

private theorem partial_rel_transport {A : Type} {R S : A → A → Prop}
    (h : ∀ a b, R a b ↔ S a b) (r s : Except DimError A) :
    PartialRel R r s ↔ PartialRel S r s := by
  cases r <;> cases s <;> simp_all only [PartialRel]

private theorem partial_rel_trans {A : Type} {R S T : A → A → Prop}
    (h : ∀ a b c, R a b → S b c → T a c) {r s t : Except DimError A}
    (hrs : PartialRel R r s) (hst : PartialRel S s t) : PartialRel T r t := by
  cases r <;> cases s <;> cases t <;> simp_all only [PartialRel]
  exact h _ _ _ hrs hst

private def ArgumentClass {I : Type u} (d : ValTy) (D : I → PartialValType d)
    (i : I) (a : d.carrierEl) :=
  {p : I × d.carrierEl // PartialRelated d (.ok (D i)) (.ok (D p.1)) a p.2}

/-- Type-local coherence proves the PER laws; no evaluator-invariance
hypothesis or agreement on unrelated oracle calls is used. -/
theorem partialFamily_laws (τ : ValTy) {I : Type u}
    (T : I → Except DimError (PartialValType τ))
    (hc : ∀ i j, PartialCoherent τ (T i) (T j)) : PartialFamilyLaws τ T := by
  classical
  by_cases hf : ∃ i err, T i = .error err
  · obtain ⟨i,err,hi⟩ := hf
    have hall : ∀ j, T j = .error err := fun j => partialCoherent_error (hi ▸ hc i j)
    constructor
    · intro i j k l a b
      simp only [hall]
    · intro i j k a b c h
      rw [hall i, hall j] at h
      cases τ <;> exact False.elim h
  · have hs : ∀ i, ∃ t, T i = .ok t := by
      intro i
      cases ht : T i with
      | error e => exact False.elim (hf ⟨i,e,ht⟩)
      | ok t => exact ⟨t,rfl⟩
    let S : I → PartialValType τ := fun i => Classical.choose (hs i)
    have hS : ∀ i, T i = .ok (S i) := fun i => Classical.choose_spec (hs i)
    cases τ with
    | space s =>
      have hdim : ∀ i j, S i = S j := by
        intro i j
        have h := hc i j
        simpa only [hS, PartialCoherent] using h
      constructor
      · intro i j k l a b
        simp only [hS, PartialRelated, hdim i k, hdim j l]
      · intro i j k a b c hab hbc
        simp only [hS, PartialRelated] at hab hbc ⊢
        exact ⟨hab.1.trans hbc.1, hab.2.1,hbc.2.2⟩
    | piTy d c =>
      let D : I → PartialValType d := fun i => (S i).1
      let F : I → d.carrierEl → Except DimError (PartialValType c) := fun i => (S i).2
      have hdom : ∀ i j, PartialCoherent d (.ok (D i)) (.ok (D j)) := by
        intro i j
        have h := hc i j
        rw [hS i, hS j] at h
        exact h.1
      have hfib : ∀ i j a b, PartialRelated d (.ok (D i)) (.ok (D j)) a b →
          PartialCoherent c (F i a) (F j b) := by
        intro i j a b hab
        have h := hc i j
        rw [hS i, hS j] at h
        exact h.2 a b hab
      have hd := partialFamily_laws d (fun i => .ok (D i)) hdom
      have classCoherent (i : I) (a : d.carrierEl) :
          ∀ p q : ArgumentClass d D i a,
          PartialCoherent c (F p.val.1 p.val.2) (F q.val.1 q.val.2) := by
        intro p q
        exact hfib _ _ _ _ (hd.trans _ _ _ _ _ _
          (partialRelated_symm d _ _ _ _ p.property) q.property)
      have classLaws (i : I) (a : d.carrierEl) :=
        partialFamily_laws c (fun p : ArgumentClass d D i a => F p.val.1 p.val.2)
          (classCoherent i a)
      have forward : ∀ i j k l f g,
          PartialRelated (.piTy d c) (T i) (T j) f g →
          PartialRelated (.piTy d c) (T k) (T l) f g := by
        intro i j k l f g hfg
        rw [hS i, hS j] at hfg
        rw [hS k, hS l]
        intro x y hxy
        have hxy0 := (hd.transport k l i j x y).1 hxy
        have hxx := hd.trans k l k x y x hxy (partialRelated_symm d _ _ _ _ hxy)
        let p : ArgumentClass d D k x := ⟨⟨i,x⟩,(hd.transport k k k i x x).1 hxx⟩
        let q : ArgumentClass d D k x := ⟨⟨j,y⟩,(hd.transport k l k j x y).1 hxy⟩
        let p' : ArgumentClass d D k x := ⟨⟨k,x⟩,hxx⟩
        let q' : ArgumentClass d D k x := ⟨⟨l,y⟩,hxy⟩
        exact (partial_rel_transport (fun a b =>
          (classLaws k x).transport p q p' q' a b) _ _).1 (hfg x y hxy0)
      constructor
      · intro i j k l f g
        exact ⟨forward i j k l f g, forward k l i j f g⟩
      · intro i j k f g h hfg hgh
        rw [hS i, hS j] at hfg
        rw [hS j, hS k] at hgh
        rw [hS i, hS k]
        intro x z hxz
        have hxy := (hd.transport i k i j x z).1 hxz
        have hzz := hd.trans k i k z x z (partialRelated_symm d _ _ _ _ hxz) hxz
        have hyz := (hd.transport k k j k z z).1 hzz
        have hxx := hd.trans i k i x z x hxz (partialRelated_symm d _ _ _ _ hxz)
        let p : ArgumentClass d D i x := ⟨⟨i,x⟩,hxx⟩
        let q : ArgumentClass d D i x := ⟨⟨j,z⟩,hxy⟩
        let r : ArgumentClass d D i x := ⟨⟨k,z⟩,hxz⟩
        exact partial_rel_trans (fun a b c hab hbc =>
          (classLaws i x).trans p q r a b c hab hbc) (hfg x z hxy) (hgh z z hyz)
termination_by sizeOf τ

/-- The successful part of a coherent partial interpretation is an actual
partial equivalence relation, including at arbitrary higher-order types. -/
noncomputable def partialPER (τ : ValTy) (T : Except DimError (PartialValType τ))
    (hc : PartialCoherent τ T T) : ExtensionalQuotient.PER τ.carrierEl where
  rel := PartialRelated τ T T
  symm := partialRelated_symm τ T T _ _
  trans := (partialFamily_laws τ (fun _ : Unit => T) (fun _ _ => hc)).trans () () () _ _ _

end GLang.PartialValueDomains
