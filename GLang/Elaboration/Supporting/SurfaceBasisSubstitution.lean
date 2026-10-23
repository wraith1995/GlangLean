import GLang.Elaboration.BasisErasure

namespace GLang

def Surface.Basis.subst (x : Name) (u : Surface.Term) : Surface.Basis → Surface.Basis
  | .empty => .empty
  | .one => .one
  | .dual b => .dual (b.subst x u)
  | .dsum a b => .dsum (a.subst x u) (b.subst x u)
  | .tprod a b => .tprod (a.subst x u) (b.subst x u)
  | .proj s a b => .proj (s.subst x u) (a.subst x u) (b.subst x u)
  | .image b => .image (b.subst x u)
  | .terms es b => .terms (es.map (Surface.Term.subst x u)) (b.subst x u)
  | .frame a b => .frame (a.subst x u) (b.subst x u)

theorem Basis.erase_subst (b : Basis) (x : Name) (u : Term) :
    (Basis.subst x u b).erase = Surface.Basis.subst x u.erase b.erase := by
  induction b with
  | terms s es b ih =>
      simp only [Basis.subst, Basis.erase, Surface.Basis.subst, List.map_map, Function.comp_def,
        Term.erase_subst, ih]
  | _ => simp_all only [Basis.subst, Basis.erase, Surface.Basis.subst, Space.erase_subst]

end GLang
