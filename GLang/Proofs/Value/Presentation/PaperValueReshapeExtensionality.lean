import GLang.Proofs.Value.Presentation.PaperValueCheckedExtensionality

/-! Relational bridges for the live checked reshape. Base conversions preserve
matching errors as well as successful arrays. First-order arrows use the
actual paired source/target stacks, including dependent codomain dimensions. -/
namespace GLang.PaperValueDomains

/-- Replace local stacks while retaining the named semantic environment. -/
def World.restack (w : World) (Γ : List ValTy) (Δ : List ValValSem) : World :=
  ⟨w.env, Γ, Δ⟩

/-- Paired-context base reshape needs agreement only on the target dimension.
The source relation already supplies equal arrays of exact source lengths. -/
theorem reshape_between_space_related (orc : FFSOracleSem) (ss st : ValSpace)
    (w w' : World) (Γt Γt' : List ValTy) (Δt Δt' : List ValValSem)
    (v v' : ValValSem) (hv : RuntimeRelated orc (.space ss) w w' v v')
    (ht : ValSpace.dof (orc w.env Γt Δt) st =
      ValSpace.dof (orc w'.env Γt' Δt') st) :
    PartialRel (RuntimeRelated orc (.space st)
      (w.restack Γt Δt) (w'.restack Γt' Δt'))
      (reshapDenotSemBetweenS orc w.env Γt Δt w.types w.values v (.space st) (.space ss))
      (reshapDenotSemBetweenS orc w'.env Γt' Δt' w'.types w'.values v' (.space st) (.space ss)) := by
  cases v <;> cases v' <;> try exact hv.elim
  rename_i a b
  obtain ⟨rfl, ha, hb⟩ := hv
  simp only [reshapDenotSemBetweenS, reshapArrayBetweenS,
    ← ha, ← hb, if_pos rfl, ← ht]
  by_cases hsize : a.length = ValSpace.dof (orc w.env Γt Δt) st
  · simp only [hsize, if_pos rfl, PartialRel]
    exact ⟨rfl, hsize, hsize.trans ht⟩
  · simp only [if_neg hsize, if_true, PartialRel]

/-- The public base reshape is the equal-stack instance of the paired bridge. -/
theorem reshape_space_related (orc : FFSOracleSem) (ss st : ValSpace)
    (w w' : World) (v v' : ValValSem)
    (hv : RuntimeRelated orc (.space ss) w w' v v')
    (ht : ValSpace.dof (orc w.env w.types w.values) st =
      ValSpace.dof (orc w'.env w'.types w'.values) st) :
    PartialRel (RuntimeRelated orc (.space st) w w')
      (reshapDenotSemS orc w.env w.types w.values v (.space st) (.space ss))
      (reshapDenotSemS orc w'.env w'.types w'.values v' (.space st) (.space ss)) := by
  simpa only [reshapDenotSemS_eq_between, World.restack] using
    reshape_between_space_related orc ss st w w' w.types w'.types w.values w'.values v v' hv ht

/-- The actual expression evaluator's base reshape respects the relation,
including failures of the operand or either shape check. -/
theorem eval_reshape_space_related (orc : FFSOracleSem) (ss st : ValSpace)
    (w w' : World) (e e' : ValExpr)
    (he : PartialRel (RuntimeRelated orc (.space ss) w w')
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semS orc w'.env w'.types w'.values e'))
    (ht : ValSpace.dof (orc w.env w.types w.values) st =
      ValSpace.dof (orc w'.env w'.types w'.values) st) :
    PartialRel (RuntimeRelated orc (.space st) w w')
      (denotValB_semS orc w.env w.types w.values (.reshap e (.space st) (.space ss)))
      (denotValB_semS orc w'.env w'.types w'.values (.reshap e' (.space st) (.space ss))) := by
  rw [denotValB_semS.eq_17, denotValB_semS.eq_17]
  cases hl : denotValB_semS orc w.env w.types w.values e <;>
    cases hr : denotValB_semS orc w'.env w'.types w'.values e' <;>
    simp only [hl, hr, PartialRel] at he
  · cases he; rfl
  · exact reshape_space_related orc ss st w w' _ _ he ht

private theorem reshape_reify_array {s : ValSpace} {a : FlatArray} {n : Nat}
    (h : a.length = n) : ValValSem.fromEl (.space s n) a = .array a := by
  simp only [ValValSem.fromEl]
  congr 1
  apply FlatArray.ext h.symm
  intro i
  simp [FlatArray.resize, FlatArray.ofFn, FlatArray.get, h]

/-- First-order function reshape, including dependent FFS output dimensions.
Only source-domain dimensions and the target output dimensions in related
argument worlds must agree. All domain/result mismatch errors are preserved. -/
theorem reshape_firstOrder_related (orc : FFSOracleSem)
    (ss₀ ss₁ st₀ st₁ : ValSpace) (w w' : World) (v v' : ValValSem)
    (hv : RuntimeRelated orc (.piTy (.space ss₀) (.space ss₁)) w w' v v')
    (hs : ValSpace.dof (orc w.env w.types w.values) ss₀ =
      ValSpace.dof (orc w'.env w'.types w'.values) ss₀)
    (ht : ∀ a b, Related orc (.space st₀) w w' a b →
      ValSpace.dof (orc (w.push orc (.space st₀) a).env
        (w.push orc (.space st₀) a).types (w.push orc (.space st₀) a).values) st₁ =
      ValSpace.dof (orc (w'.push orc (.space st₀) b).env
        (w'.push orc (.space st₀) b).types (w'.push orc (.space st₀) b).values) st₁) :
    PartialRel (RuntimeRelated orc (.piTy (.space st₀) (.space st₁)) w w')
      (reshapDenotSemS orc w.env w.types w.values v
        (.piTy (.space st₀) (.space st₁)) (.piTy (.space ss₀) (.space ss₁)))
      (reshapDenotSemS orc w'.env w'.types w'.values v'
        (.piTy (.space st₀) (.space st₁)) (.piTy (.space ss₀) (.space ss₁))) := by
  classical
  cases v <;> cases v' <;> try exact hv.elim
  rename_i T f U g
  obtain ⟨hT, hU, hfg⟩ := hv
  subst T; subst U
  refine ⟨rfl, rfl, ?_⟩
  intro a b hab
  have ha := hab.2.1
  have hb := hab.2.2
  have htarget := ht a b hab
  obtain ⟨rfl, _, _⟩ := hab
  simp only [World.denot, denotValTyS, ValValSem.fromElChecked_space_of_length _ _ _ ha,
    ValValSem.fromElChecked_space_of_length _ _ _ hb,
    reshapDenotSemBetweenS, reshapArrayBetweenS, ← ha, ← hb, if_true]
  by_cases hsource : a.length = ValSpace.dof (orc w.env w.types w.values) ss₀
  · have hsource' := hsource.trans hs
    have haS := reshape_reify_array (s := ss₀) hsource
    have hbS := reshape_reify_array (s := ss₀) hsource'
    have haT := reshape_reify_array (s := st₀) ha
    have hbT := reshape_reify_array (s := st₀) hb
    have hresult := hfg a a ⟨rfl, hsource, hsource'⟩
    simp only [if_pos hsource, if_pos hsource', if_true, ValValSem.toEl_space_array,
      ValValSem.applyTyped, dite_true]
    simp only [World.push, World.denot, denotValTyS, haS, hbS] at hresult
    simp only [World.push, World.denot, denotValTyS, haT, hbT] at htarget ⊢
    cases hf : f a <;> cases hg : g a <;> simp only [hf, hg, PartialRel] at hresult
    · cases hresult; rfl
    · exact reshape_between_space_related orc ss₁ st₁
        ⟨w.env, .space ss₀ :: w.types, .array a :: w.values⟩
        ⟨w'.env, .space ss₀ :: w'.types, .array a :: w'.values⟩
        (.space st₀ :: w.types) (.space st₀ :: w'.types)
        (.array a :: w.values) (.array a :: w'.values) _ _ hresult htarget
  · have hsource' : a.length ≠ ValSpace.dof (orc w'.env w'.types w'.values) ss₀ := by
      simpa only [← hs] using hsource
    simp only [if_neg hsource, if_neg hsource', if_false, PartialRel]

/-- Expression-level first-order reshape follows from the immediate operand
relation; operand errors propagate unchanged. -/
theorem eval_reshape_firstOrder_related (orc : FFSOracleSem)
    (ss₀ ss₁ st₀ st₁ : ValSpace) (w w' : World) (e e' : ValExpr)
    (he : PartialRel (RuntimeRelated orc (.piTy (.space ss₀) (.space ss₁)) w w')
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semS orc w'.env w'.types w'.values e'))
    (hs : ValSpace.dof (orc w.env w.types w.values) ss₀ =
      ValSpace.dof (orc w'.env w'.types w'.values) ss₀)
    (ht : ∀ a b, Related orc (.space st₀) w w' a b →
      ValSpace.dof (orc (w.push orc (.space st₀) a).env
        (w.push orc (.space st₀) a).types (w.push orc (.space st₀) a).values) st₁ =
      ValSpace.dof (orc (w'.push orc (.space st₀) b).env
        (w'.push orc (.space st₀) b).types (w'.push orc (.space st₀) b).values) st₁) :
    PartialRel (RuntimeRelated orc (.piTy (.space st₀) (.space st₁)) w w')
      (denotValB_semS orc w.env w.types w.values
        (.reshap e (.piTy (.space st₀) (.space st₁)) (.piTy (.space ss₀) (.space ss₁))))
      (denotValB_semS orc w'.env w'.types w'.values
        (.reshap e' (.piTy (.space st₀) (.space st₁)) (.piTy (.space ss₀) (.space ss₁)))) := by
  rw [denotValB_semS.eq_17, denotValB_semS.eq_17]
  cases hl : denotValB_semS orc w.env w.types w.values e <;>
    cases hr : denotValB_semS orc w'.env w'.types w'.values e' <;>
    simp only [hl, hr, PartialRel] at he
  · cases he; rfl
  · exact reshape_firstOrder_related orc ss₀ ss₁ st₀ st₁ w w' _ _ he hs ht

end GLang.PaperValueDomains
