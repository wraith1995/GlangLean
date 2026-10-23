import GLang.Proofs.Value.Presentation.PaperValueDependentCoherence

namespace GLang.PaperValueDomains

/-- Laws scoped to one type and one pairwise coherent family of worlds. -/
structure CoherentFamilyLaws (orc : FFSOracleSem) (τ : ValTy)
    {I : Type u} (w : I → World) : Prop where
  transport : ∀ i j k l (a : (w i |>.denot orc τ).El)
    (b : (w j |>.denot orc τ).El) (a' : (w k |>.denot orc τ).El)
    (b' : (w l |>.denot orc τ).El), HEq a a' → HEq b b' →
    (Related orc τ (w i) (w j) a b ↔ Related orc τ (w k) (w l) a' b')
  trans : ∀ i j k (a : (w i |>.denot orc τ).El)
    (b : (w j |>.denot orc τ).El) (c : (w k |>.denot orc τ).El),
    Related orc τ (w i) (w j) a b → Related orc τ (w j) (w k) b c →
    Related orc τ (w i) (w k) a c

private theorem partial_transport {A A' B B' : Type}
    (hA : A = A') (hB : B = B') {R : A → B → Prop} {S : A' → B' → Prop}
    (hRS : ∀ a b a' b', HEq a a' → HEq b b' → (R a b ↔ S a' b'))
    {r : Except DimError A} {r' : Except DimError B}
    {s : Except DimError A'} {s' : Except DimError B'}
    (hr : HEq r s) (hr' : HEq r' s') : PartialRel R r r' ↔ PartialRel S s s' := by
  cases hA; cases hB
  obtain rfl := eq_of_heq hr
  obtain rfl := eq_of_heq hr'
  cases r <;> cases r' <;> simp only [PartialRel]
  exact hRS _ _ _ _ HEq.rfl HEq.rfl

private theorem apply_heq {A B : Type} {F : A → Type} {G : B → Type}
    (hA : A = B) (hFG : ∀ a b, HEq a b → F a = G b)
    (f : ∀ a, F a) (g : ∀ b, G b) (hf : HEq f g)
    (a : A) (b : B) (hab : HEq a b) : HEq (f a) (g b) := by
  cases hA
  have heq : F = G := funext fun x => hFG x x HEq.rfl
  cases heq
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hab
  rfl

private theorem partial_trans {A : Type u} {B : Type v} {C : Type w} {R : A → B → Prop}
    {S : B → C → Prop} {T : A → C → Prop}
    (ht : ∀ a b c, R a b → S b c → T a c)
    {a : Except DimError A} {b : Except DimError B} {c : Except DimError C}
    (h : PartialRel R a b) (h' : PartialRel S b c) : PartialRel T a c := by
  cases a <;> cases b <;> cases c <;> simp_all only [PartialRel]
  exact ht _ _ _ h h'

private def ArgumentClass (orc : FFSOracleSem) (d : ValTy) {I : Type u}
    (w : I → World) (i : I) (a : (w i |>.denot orc d).El) :=
  {p : (j : I) × (w j |>.denot orc d).El // Related orc d (w i) (w p.1) a p.2}

private noncomputable def argumentWorld (orc : FFSOracleSem) (d : ValTy) {I : Type u}
    (w : I → World) (i : I) (a : (w i |>.denot orc d).El)
    (p : ArgumentClass orc d w i a) : World := (w p.val.1).push orc d p.val.2

/-- Pairwise coherence at the actual type suffices for supported transport and
transitivity. No agreement on arbitrary oracle queries is assumed. -/
theorem coherentFamily_laws (orc : FFSOracleSem) (τ : ValTy) {I : Type u}
    (w : I → World) (hc : ∀ i j, TypeCoherent orc τ (w i) (w j)) :
    CoherentFamilyLaws orc τ w := by
  cases τ with
  | space s =>
    constructor
    · intro i j k l a b a' b' ha hb
      obtain rfl := eq_of_heq ha
      obtain rfl := eq_of_heq hb
      have hi := (leafAgreement_shapes _ _ s (hc i k)).2
      have hj := (leafAgreement_shapes _ _ s (hc j l)).2
      simp only [Related, hi, hj]
      rfl
    · intro i j k a b c hab hbc
      exact ⟨hab.1.trans hbc.1, hab.2.1, hbc.2.2⟩
  | piTy d c =>
    have hd := coherentFamily_laws orc d w (fun i j => (hc i j).1)
    have classCoherent (i : I) (a : (w i |>.denot orc d).El) :
        ∀ p q : ArgumentClass orc d w i a,
        TypeCoherent orc c (argumentWorld orc d w i a p) (argumentWorld orc d w i a q) := by
      intro p q
      exact (hc p.val.1 q.val.1).2 p.val.2 q.val.2
        (hd.trans _ _ _ _ _ _ (related_symm orc d _ _ _ _ p.property) q.property)
    have classLaws (i : I) (a : (w i |>.denot orc d).El) :=
      coherentFamily_laws orc c (argumentWorld orc d w i a) (classCoherent i a)
    have forward : ∀ i j k l (f : (w i |>.denot orc (.piTy d c)).El)
        (g : (w j |>.denot orc (.piTy d c)).El)
        (f' : (w k |>.denot orc (.piTy d c)).El)
        (g' : (w l |>.denot orc (.piTy d c)).El), HEq f f' → HEq g g' →
        Related orc (.piTy d c) (w i) (w j) f g →
        Related orc (.piTy d c) (w k) (w l) f' g' := by
      intro i j k l f g f' g' hf hg hfg x' y' hxy'
      let x := cast (World.carrier_eq orc d (w k) (w i)) x'
      let y := cast (World.carrier_eq orc d (w l) (w j)) y'
      have hx : HEq x x' := cast_heq _ _
      have hy : HEq y y' := cast_heq _ _
      have hxy := (hd.transport i j k l x y x' y' hx hy).2 hxy'
      have hxx' := hd.trans k l k x' y' x' hxy' (related_symm orc d _ _ _ _ hxy')
      have hxx := (hd.transport k k k i x' x' x' x HEq.rfl hx.symm).1 hxx'
      have hxy0 := (hd.transport k l k j x' y' x' y HEq.rfl hy.symm).1 hxy'
      let p : ArgumentClass orc d w k x' := ⟨⟨i,x⟩,hxx⟩
      let q : ArgumentClass orc d w k x' := ⟨⟨j,y⟩,hxy0⟩
      let p' : ArgumentClass orc d w k x' := ⟨⟨k,x'⟩,hxx'⟩
      let q' : ArgumentClass orc d w k x' := ⟨⟨l,y'⟩,hxy'⟩
      have hfout := apply_heq (World.carrier_eq orc d (w i) (w k))
        (fun a b _ => congrArg (Except DimError) (World.carrier_eq orc c ((w i).push orc d a) ((w k).push orc d b))) f f' hf x x' hx
      have hgout := apply_heq (World.carrier_eq orc d (w j) (w l))
        (fun a b _ => congrArg (Except DimError) (World.carrier_eq orc c ((w j).push orc d a) ((w l).push orc d b))) g g' hg y y' hy
      exact (partial_transport (World.carrier_eq orc c _ _) (World.carrier_eq orc c _ _)
        (fun a b a' b' ha hb => (classLaws k x').transport p q p' q' a b a' b' ha hb)
        hfout hgout).1 (hfg x y hxy)
    constructor
    · intro i j k l f g f' g' hf hg
      exact ⟨forward i j k l f g f' g' hf hg, forward k l i j f' g' f g hf.symm hg.symm⟩
    · intro i j k f g h hfg hgh x z hxz
      let y := cast (World.carrier_eq orc d (w k) (w j)) z
      have hy : HEq y z := cast_heq _ _
      have hxy := (hd.transport i k i j x z x y HEq.rfl hy.symm).1 hxz
      have hzz := hd.trans k i k z x z (related_symm orc d _ _ _ _ hxz) hxz
      have hyz := (hd.transport k k j k z z y z hy.symm HEq.rfl).1 hzz
      have hxx := hd.trans i k i x z x hxz (related_symm orc d _ _ _ _ hxz)
      let p : ArgumentClass orc d w i x := ⟨⟨i,x⟩,hxx⟩
      let q : ArgumentClass orc d w i x := ⟨⟨j,y⟩,hxy⟩
      let r : ArgumentClass orc d w i x := ⟨⟨k,z⟩,hxz⟩
      exact partial_trans (fun a b c hab hbc => (classLaws i x).trans p q r a b c hab hbc)
        (hfg x y hxy) (hgh y z hyz)
termination_by sizeOf τ

/-- Four-world fibre transport follows from type-local family coherence; only
supported argument classes are consulted under dependent binders. -/
theorem coherentFamily_fiber (orc : FFSOracleSem) (τ : ValTy) {I : Type u}
    (w : I → World) (hc : ∀ i j, TypeCoherent orc τ (w i) (w j))
    (i j k l : I) : FiberAgreement orc τ (w i) (w j) (w k) (w l) := by
  cases τ with
  | space s => exact ⟨hc i k, hc j l⟩
  | piTy d c =>
    have hdom : ∀ i j, TypeCoherent orc d (w i) (w j) := fun i j => (hc i j).1
    have hd := coherentFamily_laws orc d w hdom
    refine ⟨coherentFamily_fiber orc d w hdom i j k l, ?_⟩
    intro a b a' b' ha hb hab
    have haa := hd.trans i j i a b a hab (related_symm orc d _ _ _ _ hab)
    have haa' := (hd.transport i i i k a a a a' HEq.rfl ha).1 haa
    have hab' := (hd.transport i j i l a b a b' HEq.rfl hb).1 hab
    let p : ArgumentClass orc d w i a := ⟨⟨i,a⟩,haa⟩
    let q : ArgumentClass orc d w i a := ⟨⟨j,b⟩,hab⟩
    let p' : ArgumentClass orc d w i a := ⟨⟨k,a'⟩,haa'⟩
    let q' : ArgumentClass orc d w i a := ⟨⟨l,b'⟩,hab'⟩
    have hclass : ∀ p q : ArgumentClass orc d w i a,
        TypeCoherent orc c (argumentWorld orc d w i a p) (argumentWorld orc d w i a q) := by
      intro p q
      exact (hc p.val.1 q.val.1).2 p.val.2 q.val.2
        (hd.trans _ _ _ _ _ _ (related_symm orc d _ _ _ _ p.property) q.property)
    exact coherentFamily_fiber orc c (argumentWorld orc d w i a) hclass p q p' q'
termination_by sizeOf τ

/-- Actual callbacks may be retained while changing to any other two worlds
in a type-coherent family. -/
theorem coherentFamily_runtime_transport (orc : FFSOracleSem) (τ : ValTy) {I : Type u}
    (w : I → World) (hc : ∀ i j, TypeCoherent orc τ (w i) (w j))
    (i j k l : I) (v v' : ValValSem)
    (h : RuntimeRelated orc τ (w i) (w j) v v') :
    RuntimeRelated orc τ (w k) (w l) v v' :=
  runtime_fiber_transport orc τ _ _ _ _ (coherentFamily_fiber orc τ w hc i j k l) v v' h

/-- Runtime transitivity uses the same supported argument classes. -/
theorem coherentFamily_runtime_trans (orc : FFSOracleSem) (τ : ValTy) {I : Type u}
    (w : I → World) (hc : ∀ i j, TypeCoherent orc τ (w i) (w j))
    (i j k : I) (v v' v'' : ValValSem)
    (h : RuntimeRelated orc τ (w i) (w j) v v')
    (h' : RuntimeRelated orc τ (w j) (w k) v' v'') :
    RuntimeRelated orc τ (w i) (w k) v v'' := by
  cases τ with
  | space s =>
    cases v <;> cases v' <;> cases v''
    all_goals try (exact False.elim h)
    all_goals try (exact False.elim h')
    exact (coherentFamily_laws orc (.space s) w hc).trans i j k _ _ _ h h'
  | piTy d c =>
    cases v <;> cases v' <;> cases v''
    all_goals try (exact False.elim h)
    all_goals try (exact False.elim h')
    rename_i A f B g C hfun
    obtain ⟨hA,hB,hfg⟩ := h
    obtain ⟨hB',hC,hgh⟩ := h'
    have hd := coherentFamily_laws orc d w (fun i j => (hc i j).1)
    refine ⟨hA,hC,?_⟩
    intro x z hxz
    let y := cast (hB.trans (World.carrier_eq orc d (w j) (w k))).symm (hC ▸ z)
    have hy : HEq (hB ▸ y) (hC ▸ z) :=
      (cast_heq hB y).trans (cast_heq _ (hC ▸ z))
    have hxy := (hd.transport i k i j (hA ▸ x) (hC ▸ z)
      (hA ▸ x) (hB ▸ y) HEq.rfl hy.symm).1 hxz
    have hzz := hd.trans k i k (hC ▸ z) (hA ▸ x) (hC ▸ z)
      (related_symm orc d _ _ _ _ hxz) hxz
    have hyz := (hd.transport k k j k (hC ▸ z) (hC ▸ z)
      (hB ▸ y) (hC ▸ z) hy.symm HEq.rfl).1 hzz
    have hxx := hd.trans i k i (hA ▸ x) (hC ▸ z) (hA ▸ x)
      hxz (related_symm orc d _ _ _ _ hxz)
    let p : ArgumentClass orc d w i (hA ▸ x) := ⟨⟨i,hA ▸ x⟩,hxx⟩
    let q : ArgumentClass orc d w i (hA ▸ x) := ⟨⟨j,hB ▸ y⟩,hxy⟩
    let r : ArgumentClass orc d w i (hA ▸ x) := ⟨⟨k,hC ▸ z⟩,hxz⟩
    have hclass : ∀ p q : ArgumentClass orc d w i (hA ▸ x),
        TypeCoherent orc c (argumentWorld orc d w i (hA ▸ x) p)
          (argumentWorld orc d w i (hA ▸ x) q) := by
      intro p q
      exact (hc p.val.1 q.val.1).2 p.val.2 q.val.2
        (hd.trans _ _ _ _ _ _ (related_symm orc d _ _ _ _ p.property) q.property)
    exact partial_trans
      (fun a b z hab hbc => coherentFamily_runtime_trans orc c
        (argumentWorld orc d w i (hA ▸ x)) hclass p q r a b z hab hbc)
      (hfg x y hxy) (hgh y z hyz)
termination_by sizeOf τ

end GLang.PaperValueDomains
