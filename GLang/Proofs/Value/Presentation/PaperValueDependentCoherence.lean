import GLang.Proofs.Value.Presentation.PaperValueCheckedExtensionality
import GLang.Proofs.Adequacy.Raw.RawNonBetaValueKernel

/-! Local typed-query coherence transports dependent logical relations across
changes of runtime representatives in their worlds. This is a semantic fibre
lemma, not an assumption that evaluation already respects the relation. -/
namespace GLang.PaperValueDomains

/-- Semantic worlds affect finite dimensions, not the underlying Lean carrier. -/
theorem World.carrier_eq (orc : FFSOracleSem) (τ : ValTy) (w u : World) :
    (w.denot orc τ).El = (u.denot orc τ).El :=
  (denotValTyS_El_eq_carrierEl_raw orc w.env w.types w.values τ).trans
    (denotValTyS_El_eq_carrierEl_raw orc u.env u.types u.values τ).symm

/-- A dependent type has equal typed FFS observations in related worlds,
recursively in every fibre selected by related successful arguments. -/
def TypeCoherent (orc : FFSOracleSem) : ValTy → World → World → Prop
  | .space s, w, w' =>
      SpaceOracleAgreement (orc w.env w.types w.values) (orc w'.env w'.types w'.values) s
  | .piTy d c, w, w' =>
      TypeCoherent orc d w w' ∧
      ∀ a b, Related orc d w w' a b →
        TypeCoherent orc c (w.push orc d a) (w'.push orc d b)

/-- Only FFS leaves of the type are observed. At arrows the obligation recurs
in the actual input-selected fibres, and only for related inputs. -/
def FiberAgreement (orc : FFSOracleSem) : ValTy → World → World → World → World → Prop
  | .space s, w, w', u, u' =>
      SpaceOracleAgreement (orc w.env w.types w.values) (orc u.env u.types u.values) s ∧
      SpaceOracleAgreement (orc w'.env w'.types w'.values) (orc u'.env u'.types u'.values) s
  | .piTy d c, w, w', u, u' =>
      FiberAgreement orc d w w' u u' ∧
      ∀ a b a' b', HEq a a' → HEq b b' → Related orc d w w' a b →
        FiberAgreement orc c (w.push orc d a) (w'.push orc d b)
          (u.push orc d a') (u'.push orc d b')

private theorem partial_heq_iff {A A' B B' : Type}
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

private theorem function_apply_heq {A B : Type} {F : A → Type} {G : B → Type}
    (hA : A = B) (hFG : ∀ a b, HEq a b → F a = G b)
    (f : ∀ a, F a) (g : ∀ b, G b) (hf : HEq f g)
    (a : A) (b : B) (hab : HEq a b) : HEq (f a) (g b) := by
  cases hA
  have heq : F = G := funext fun x => hFG x x HEq.rfl
  cases heq
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hab
  rfl

/-- Replace both worlds of a dependent relation while retaining the same
underlying typed representatives. Coherence is required only at typed leaves
and recursively selected related fibres. -/
theorem related_fiber_transport (orc : FFSOracleSem) (τ : ValTy)
    (w w' u u' : World) (hc : FiberAgreement orc τ w w' u u')
    (a : (w.denot orc τ).El) (b : (w'.denot orc τ).El)
    (a' : (u.denot orc τ).El) (b' : (u'.denot orc τ).El)
    (ha : HEq a a') (hb : HEq b b') :
    Related orc τ w w' a b ↔ Related orc τ u u' a' b' := by
  cases τ with
  | space s =>
    have hleft := (leafAgreement_shapes _ _ s hc.1).2
    have hright := (leafAgreement_shapes _ _ s hc.2).2
    obtain rfl := eq_of_heq ha
    obtain rfl := eq_of_heq hb
    simp only [Related, hleft, hright]
    rfl
  | piTy d c =>
    have hd := World.carrier_eq orc d w u
    have hd' := World.carrier_eq orc d w' u'
    constructor
    · intro hab x' y' hxy'
      let x : (w.denot orc d).El := cast hd.symm x'
      let y : (w'.denot orc d).El := cast hd'.symm y'
      have hx : HEq x x' := cast_heq hd.symm x'
      have hy : HEq y y' := cast_heq hd'.symm y'
      have hxy := (related_fiber_transport orc d w w' u u' hc.1 x y x' y' hx hy).2 hxy'
      have hfib := hc.2 x y x' y' hx hy hxy
      have haout := function_apply_heq hd
        (fun x x' _ => congrArg (Except DimError)
          (World.carrier_eq orc c (w.push orc d x) (u.push orc d x'))) a a' ha x x' hx
      have hbout := function_apply_heq hd'
        (fun y y' _ => congrArg (Except DimError)
          (World.carrier_eq orc c (w'.push orc d y) (u'.push orc d y'))) b b' hb y y' hy
      exact (partial_heq_iff
        (World.carrier_eq orc c (w.push orc d x) (u.push orc d x'))
        (World.carrier_eq orc c (w'.push orc d y) (u'.push orc d y'))
        (fun z z' t t' hz hz' => related_fiber_transport orc c _ _ _ _ hfib z z' t t' hz hz')
        haout hbout).1 (hab x y hxy)
    · intro hab x y hxy
      let x' : (u.denot orc d).El := cast hd x
      let y' : (u'.denot orc d).El := cast hd' y
      have hx : HEq x x' := (cast_heq hd x).symm
      have hy : HEq y y' := (cast_heq hd' y).symm
      have hxy' := (related_fiber_transport orc d w w' u u' hc.1 x y x' y' hx hy).1 hxy
      have hfib := hc.2 x y x' y' hx hy hxy
      have haout := function_apply_heq hd
        (fun x x' _ => congrArg (Except DimError)
          (World.carrier_eq orc c (w.push orc d x) (u.push orc d x'))) a a' ha x x' hx
      have hbout := function_apply_heq hd'
        (fun y y' _ => congrArg (Except DimError)
          (World.carrier_eq orc c (w'.push orc d y) (u'.push orc d y'))) b b' hb y y' hy
      exact (partial_heq_iff
        (World.carrier_eq orc c (w.push orc d x) (u.push orc d x'))
        (World.carrier_eq orc c (w'.push orc d y) (u'.push orc d y'))
        (fun z z' t t' hz hz' => related_fiber_transport orc c _ _ _ _ hfib z z' t t' hz hz')
        haout hbout).2 (hab x' y' hxy')
termination_by sizeOf τ

theorem SpaceOracleAgreement.symm (q q' : FFSOracle) (s : ValSpace)
    (h : SpaceOracleAgreement q q' s) : SpaceOracleAgreement q' q s := by
  cases s with
  | empty | real => trivial
  | dsum s t | tprod s t => exact ⟨SpaceOracleAgreement.symm q q' s h.1,
      SpaceOracleAgreement.symm q q' t h.2⟩
  | ffs p s e => exact Eq.symm h
termination_by sizeOf s

/-- Reverse a fibre transport certificate. -/
theorem FiberAgreement.symm (orc : FFSOracleSem) (τ : ValTy)
    (w w' u u' : World) (hc : FiberAgreement orc τ w w' u u') :
    FiberAgreement orc τ u u' w w' := by
  cases τ with
  | space s =>
    exact ⟨SpaceOracleAgreement.symm _ _ _ hc.1, SpaceOracleAgreement.symm _ _ _ hc.2⟩
  | piTy d c =>
    refine ⟨FiberAgreement.symm orc d w w' u u' hc.1, ?_⟩
    intro a' b' a b ha hb hab'
    have hab := (related_fiber_transport orc d w w' u u' hc.1 a b a' b' ha.symm hb.symm).2 hab'
    exact FiberAgreement.symm orc c _ _ _ _ (hc.2 a b a' b' ha.symm hb.symm hab)
termination_by sizeOf τ

/-- Runtime callbacks retain their identity; only their dependent world
interpretations change. Local typed-query coherence is sufficient for this
transport, including all latent callback errors. -/
theorem runtime_fiber_transport (orc : FFSOracleSem) (τ : ValTy)
    (w w' u u' : World) (hc : FiberAgreement orc τ w w' u u')
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') :
    RuntimeRelated orc τ u u' v v' := by
  cases τ with
  | space s =>
    cases v <;> cases v' <;> try exact h.elim
    exact (related_fiber_transport orc (.space s) w w' u u' hc _ _ _ _ HEq.rfl HEq.rfl).1 h
  | piTy d c =>
    cases v <;> cases v' <;> try exact h.elim
    rename_i T f U g
    obtain ⟨hT, hU, hfg⟩ := h
    let hT' := hT.trans (World.carrier_eq orc d w u)
    let hU' := hU.trans (World.carrier_eq orc d w' u')
    refine ⟨hT', hU', ?_⟩
    intro a b hab'
    have ha : HEq (hT ▸ a) (hT' ▸ a) := (cast_heq hT a).trans (cast_heq hT' a).symm
    have hb : HEq (hU ▸ b) (hU' ▸ b) := (cast_heq hU b).trans (cast_heq hU' b).symm
    have hab := (related_fiber_transport orc d w w' u u' hc.1 _ _ _ _ ha hb).2 hab'
    have hfib := hc.2 _ _ _ _ ha hb hab
    have hres := hfg a b hab
    cases hf : f a <;> cases hg : g b <;> simp only [hf, hg, PartialRel] at hres ⊢
    · exact runtime_fiber_transport orc c _ _ _ _ hfib _ _ hres
termination_by sizeOf τ

/-- The transport is an equivalence, so it may be used in either direction
when changing the stack representation of a dependent fibre. -/
theorem runtime_fiber_transport_iff (orc : FFSOracleSem) (τ : ValTy)
    (w w' u u' : World) (hc : FiberAgreement orc τ w w' u u')
    (v v' : ValValSem) :
    RuntimeRelated orc τ w w' v v' ↔ RuntimeRelated orc τ u u' v v' :=
  ⟨runtime_fiber_transport orc τ w w' u u' hc v v',
    runtime_fiber_transport orc τ u u' w w' (hc.symm orc τ w w' u u') v v'⟩

theorem SpaceOracleAgreement.trans (q q' q'' : FFSOracle) (s : ValSpace)
    (h : SpaceOracleAgreement q q' s) (h' : SpaceOracleAgreement q' q'' s) :
    SpaceOracleAgreement q q'' s := by
  cases s with
  | empty | real => trivial
  | dsum s t | tprod s t => exact ⟨SpaceOracleAgreement.trans q q' q'' s h.1 h'.1,
      SpaceOracleAgreement.trans q q' q'' t h.2 h'.2⟩
  | ffs p s e => exact Eq.trans h h'
termination_by sizeOf s

/-- Recursive type coherence survives a change of representatives whose
local dependent fibres satisfy the four-world transport certificate. -/
theorem TypeCoherent.fiber_transport (orc : FFSOracleSem) (τ : ValTy)
    (w w' u u' : World) (hf : FiberAgreement orc τ w w' u u')
    (hc : TypeCoherent orc τ w w') : TypeCoherent orc τ u u' := by
  cases τ with
  | space s =>
    exact SpaceOracleAgreement.trans _ _ _ s
      (SpaceOracleAgreement.symm _ _ s hf.1)
      (SpaceOracleAgreement.trans _ _ _ s hc hf.2)
  | piTy d c =>
    refine ⟨TypeCoherent.fiber_transport orc d w w' u u' hf.1 hc.1, ?_⟩
    intro a' b' hab'
    let hd := World.carrier_eq orc d w u
    let hd' := World.carrier_eq orc d w' u'
    let a : (w.denot orc d).El := cast hd.symm a'
    let b : (w'.denot orc d).El := cast hd'.symm b'
    have ha : HEq a a' := cast_heq hd.symm a'
    have hb : HEq b b' := cast_heq hd'.symm b'
    have hab := (related_fiber_transport orc d w w' u u' hf.1 a b a' b' ha hb).2 hab'
    exact TypeCoherent.fiber_transport orc c _ _ _ _ (hf.2 a b a' b' ha hb hab) (hc.2 a b hab)
termination_by sizeOf τ

end GLang.PaperValueDomains
