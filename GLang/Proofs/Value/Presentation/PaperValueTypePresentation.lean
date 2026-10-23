import GLang.Proofs.Value.Presentation.PaperValueDependentCoherence

namespace GLang.PaperValueDomains
open ValSoundOfDenot

/-- Same-shape type presentations may differ in every dependent annotation.
Only corresponding leaf dimensions and recursively selected fibres must agree.
This is algebraic presentation coherence, not an evaluation contract. -/
def TypePresentation (orc : FFSOracleSem) :
    ValTy → ValTy → World → World → World → World → Prop
  | .space s, .space t, w, w', u, u' =>
      ValSpace.dof (orc w.env w.types w.values) s = ValSpace.dof (orc u.env u.types u.values) t ∧
      ValSpace.dof (orc w'.env w'.types w'.values) s = ValSpace.dof (orc u'.env u'.types u'.values) t
  | .piTy d c, .piTy d' c', w, w', u, u' =>
      TypePresentation orc d d' w w' u u' ∧
      ∀ a b a' b', HEq a a' → HEq b b' →
        TypePresentation orc c c' (w.push orc d a) (w'.push orc d b)
          (u.push orc d' a') (u'.push orc d' b')
  | _, _, _, _, _, _ => False

 theorem presentation_carrier (orc : FFSOracleSem) {τ υ : ValTy}
    (h : ValTy.SameShape τ υ) (w u : World) :
    (w.denot orc τ).El = (u.denot orc υ).El := by
  rw [denotValTyS_El_eq_carrierEl_raw, denotValTyS_El_eq_carrierEl_raw]
  exact ValTy.SameShape.carrierEl_eq h

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

theorem presentation_related_transport (orc : FFSOracleSem) (τ υ : ValTy)
    (hshape : ValTy.SameShape τ υ) (w w' u u' : World)
    (hc : TypePresentation orc τ υ w w' u u')
    (a : (w.denot orc τ).El) (b : (w'.denot orc τ).El)
    (a' : (u.denot orc υ).El) (b' : (u'.denot orc υ).El)
    (ha : HEq a a') (hb : HEq b b') :
    Related orc τ w w' a b ↔ Related orc υ u u' a' b' := by
  cases τ <;> cases υ
  case space.space s t =>
    obtain rfl := eq_of_heq ha
    obtain rfl := eq_of_heq hb
    simp only [Related, hc.1, hc.2]
    rfl
  case space.piTy => exact hshape.elim
  case piTy.space => exact hshape.elim
  case piTy.piTy d c d2 c2 =>
    have hd := presentation_carrier orc hshape.1 w u
    have hd' := presentation_carrier orc hshape.1 w' u'
    constructor
    · intro hab x' y' hxy'
      let x : (w.denot orc d).El := cast hd.symm x'
      let y : (w'.denot orc d).El := cast hd'.symm y'
      have hx : HEq x x' := cast_heq hd.symm x'
      have hy : HEq y y' := cast_heq hd'.symm y'
      have hxy := (presentation_related_transport orc d d2 hshape.1 w w' u u' hc.1 x y x' y' hx hy).2 hxy'
      have hfib := hc.2 x y x' y' hx hy
      have haout := function_apply_heq hd
        (fun x x' _ => congrArg (Except DimError)
          (presentation_carrier orc hshape.2 (w.push orc d x) (u.push orc d2 x'))) a a' ha x x' hx
      have hbout := function_apply_heq hd'
        (fun y y' _ => congrArg (Except DimError)
          (presentation_carrier orc hshape.2 (w'.push orc d y) (u'.push orc d2 y'))) b b' hb y y' hy
      exact (partial_heq_iff
        (presentation_carrier orc hshape.2 (w.push orc d x) (u.push orc d2 x'))
        (presentation_carrier orc hshape.2 (w'.push orc d y) (u'.push orc d2 y'))
        (fun z z' t t' hz hz' => presentation_related_transport orc c c2 hshape.2 _ _ _ _ hfib z z' t t' hz hz')
        haout hbout).1 (hab x y hxy)
    · intro hab x y hxy
      let x' : (u.denot orc d2).El := cast hd x
      let y' : (u'.denot orc d2).El := cast hd' y
      have hx : HEq x x' := (cast_heq hd x).symm
      have hy : HEq y y' := (cast_heq hd' y).symm
      have hxy' := (presentation_related_transport orc d d2 hshape.1 w w' u u' hc.1 x y x' y' hx hy).1 hxy
      have hfib := hc.2 x y x' y' hx hy
      have haout := function_apply_heq hd
        (fun x x' _ => congrArg (Except DimError)
          (presentation_carrier orc hshape.2 (w.push orc d x) (u.push orc d2 x'))) a a' ha x x' hx
      have hbout := function_apply_heq hd'
        (fun y y' _ => congrArg (Except DimError)
          (presentation_carrier orc hshape.2 (w'.push orc d y) (u'.push orc d2 y'))) b b' hb y y' hy
      exact (partial_heq_iff
        (presentation_carrier orc hshape.2 (w.push orc d x) (u.push orc d2 x'))
        (presentation_carrier orc hshape.2 (w'.push orc d y) (u'.push orc d2 y'))
        (fun z z' t t' hz hz' => presentation_related_transport orc c c2 hshape.2 _ _ _ _ hfib z z' t t' hz hz')
        haout hbout).2 (hab x' y' hxy')
termination_by sizeOf τ

theorem runtime_presentation_transport (orc : FFSOracleSem) (τ υ : ValTy)
    (hshape : ValTy.SameShape τ υ)
    (w w' u u' : World) (hc : TypePresentation orc τ υ w w' u u')
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') :
    RuntimeRelated orc υ u u' v v' := by
  cases τ <;> cases υ
  case space.piTy => exact hshape.elim
  case piTy.space => exact hshape.elim
  case space.space s t =>
    cases v <;> cases v' <;> try exact h.elim
    exact (presentation_related_transport orc (.space s) (.space t) hshape w w' u u' hc _ _ _ _ HEq.rfl HEq.rfl).1 h
  case piTy.piTy d c d2 c2 =>
    cases v <;> cases v' <;> try exact h.elim
    rename_i T f U g
    obtain ⟨hT, hU, hfg⟩ := h
    let hT' := hT.trans (presentation_carrier orc hshape.1 w u)
    let hU' := hU.trans (presentation_carrier orc hshape.1 w' u')
    refine ⟨hT', hU', ?_⟩
    intro a b hab'
    have ha : HEq (hT ▸ a) (hT' ▸ a) := (cast_heq hT a).trans (cast_heq hT' a).symm
    have hb : HEq (hU ▸ b) (hU' ▸ b) := (cast_heq hU b).trans (cast_heq hU' b).symm
    have hab := (presentation_related_transport orc d d2 hshape.1 w w' u u' hc.1 _ _ _ _ ha hb).2 hab'
    have hfib := hc.2 _ _ _ _ ha hb
    have hres := hfg a b hab
    cases hf : f a <;> cases hg : g b <;> simp only [hf, hg, PartialRel] at hres ⊢
    · exact runtime_presentation_transport orc c c2 hshape.2 _ _ _ _ hfib _ _ hres
termination_by sizeOf τ

end GLang.PaperValueDomains
