import GLang.Elaboration.PaperRules

open GLang
namespace SurfacePaperTests

-- Regularity for arbitrary (including dependent) result types.
example {d g e t} (hw : Surface.InductiveCtxWF d g)
    (ht : Surface.HasType d g e t) :
    ∃ k, Nonempty (Surface.TValid g t k) := SurfacePaper.regular hw ht

-- Compose shortened rules, then use the proved elaborator. No space-validity
-- premises or internal derivations are supplied by the caller.
example {d₀ d₁ g f x s t}
    (hw : Surface.InductiveCtxWF (d₀ ∪ d₁) g) (hd : Finmap.Disjoint d₀ d₁)
    (hf : Surface.HasType d₀ g f (.space (.tprod (.dual s) t)))
    (hx : Surface.HasType d₁ g x (.space s)) :
    ∃ (D : LCtx) (E : NLCtx) (a : Term) (T : Ty),
      D.erase = d₀ ∪ d₁ ∧ E.erase = g ∧ InductiveCtxWF D E ∧
      a.erase = .add (.app f x) (.app f x) ∧ T.erase = .space t ∧
      Nonempty (HasType D E a T) := by
  have happ := SurfacePaper.app_linear hw hd hf hx
  exact SurfaceElaboration.typing hw (SurfacePaper.add hw happ happ)

example {d g a b s} (hw : Surface.InductiveCtxWF d g)
    (ha : Surface.HasType d g a (.space s))
    (hb : Surface.HasType d g b (.space s)) :
    ∃ (D : LCtx) (E : NLCtx),
      D.erase = d ∧ E.erase = g ∧ InductiveCtxWF D E ∧
      ∃! p, SurfaceElaboration.TermLift D E (.add a b) (.space s) p :=
  SurfacePaper.typing_unique hw (SurfacePaper.add hw ha hb)

#print axioms SurfacePaper.elaborate_unique
#print axioms SurfacePaper.typing_unique

-- All four fundamental subspaces use only the map-typing premise.
example {g e s t} (hw : Surface.InductiveCtxWF ∅ g)
    (h : Surface.HasType ∅ g e (.space (.tprod (.dual s) t))) :
    Nonempty (Surface.SValid g (.ker e)) ∧
    Nonempty (Surface.SValid g (.coker e)) ∧
    Nonempty (Surface.SValid g (.img e)) ∧
    Nonempty (Surface.SValid g (.coimg e)) ∧
    Nonempty (Surface.SubType g (.ker e) s) ∧
    Nonempty (Surface.SubType g (.coker e) s) ∧
    Nonempty (Surface.SubType g (.img e) t) ∧
    Nonempty (Surface.SubType g (.coimg e) t) := by
  exact ⟨⟨SurfacePaper.ker hw h⟩, ⟨SurfacePaper.coker hw h⟩,
    ⟨SurfacePaper.img hw h⟩, ⟨SurfacePaper.coimg hw h⟩,
    ⟨SurfacePaper.sub_ker hw h⟩, ⟨SurfacePaper.sub_coker hw h⟩,
    ⟨SurfacePaper.sub_img hw h⟩, ⟨SurfacePaper.sub_coimg hw h⟩⟩

-- The erased syntax really contains no space field, even before typing.
example (s : Space) (es : List Term) (b : Basis) :
    (Basis.terms s es b).erase = .terms (es.map Term.erase) b.erase := rfl

-- Typed uniqueness reconstructs the dropped field from the fallback basis.
example {ε s t es fs b c}
    (h : Basis.BasisValid ε (.terms s es b))
    (h' : Basis.BasisValid ε (.terms t fs c))
    (he : (es.map Term.erase) = fs.map Term.erase) (hb : b.erase = c.erase) :
    s = t := by
  have hh := h.annotation_unique h' (by simp only [Basis.erase,he,hb])
  exact (Basis.terms.inj hh).1

#print axioms SurfacePaper.regular
#print axioms SurfacePaper.app_linear
#print axioms SurfacePaper.smul
#print axioms SurfacePaper.app_inner
#print axioms SurfacePaper.pinv_tensor
#print axioms SurfacePaper.pinv_dual
#print axioms SurfacePaper.dsumE
#print axioms SurfacePaper.tprodE
#print axioms SurfaceElaboration.complete
#print axioms Basis.BasisValid.annotation_unique

end SurfacePaperTests
