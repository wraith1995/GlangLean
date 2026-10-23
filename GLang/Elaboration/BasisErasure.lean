import GLang.Elaboration.Erasure

/-! Erasure of annotated bases and compatibility with opening. -/
namespace GLang

def Basis.erase : Basis → Surface.Basis
  | .empty => .empty
  | .one => .one
  | .dual b => .dual b.erase
  | .dsum a b => .dsum a.erase b.erase
  | .tprod a b => .tprod a.erase b.erase
  | .proj s a b => .proj s.erase a.erase b.erase
  | .image b => .image b.erase
  | .terms _ es b => .terms (es.map Term.erase) b.erase
  | .frame a b => .frame a.erase b.erase

theorem Basis.erase_openRec (b : Basis) (k : Nat) (u : Term) :
    (b.openRec k u).erase = b.erase.openRec k u.erase := by
  induction b generalizing k with
  | terms s es b ih =>
      simp [Basis.openRec, Basis.erase, Surface.Basis.openRec, Space.erase_openRec,
        Term.openRecList_eq_map, List.map_map, Term.erase_openRec, ih]
  | _ => simp_all [Basis.openRec, Basis.erase, Surface.Basis.openRec, Space.erase_openRec]

end GLang
