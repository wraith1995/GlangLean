import GLang.Proofs.Basis.Binding

/-!
# A conservative syntactic height for pair-certificate construction

The constructive pair-store proof alternates between basis syntax and source
syntax.  Source binders additionally ask for the standard basis of their
domain at the preceding pair depth.  The ordinary `size` functions are not a
sound bound for that alternation: `Basis.stdSpace` expands an FFS space into a
projected basis and therefore may be larger than `Space.size`.

This file defines one deliberately conservative family of heights.  The
space and type heights already budget for their standard bases, while basis
height counts every embedded source judgment.  Opening merely replaces a
bound-variable leaf by a named-variable leaf, so all four heights are
invariant under `openRec`/`openVar`.

The heights are internal proof-engineering measures.  They are not intended
to become hypotheses of the public checked-progress or adequacy theorems.
-/

namespace GLang
namespace RawCertifiedPairCreationDepth

mutual

/-- Height of a space together with all source syntax embedded in its FFS
constructors.  Its equations are chosen so that `Basis.stdSpace s` fits in
the same height. -/
def spaceHeight : Space -> Nat
  | .empty => 1
  | .real => 1
  | .dual s => spaceHeight s + 1
  | .dsum s0 s1 => spaceHeight s0 + spaceHeight s1 + 1
  | .tprod s0 s1 => spaceHeight s0 + spaceHeight s1 + 1
  | .ker s0 s1 e =>
      spaceHeight s0 + spaceHeight s1 + termHeight e + 1
  | .coker s0 s1 e =>
      spaceHeight s0 + spaceHeight s1 + termHeight e + 1
  | .img s0 s1 e =>
      spaceHeight s0 + spaceHeight s1 + termHeight e + 1
  | .coimg s0 s1 e =>
      spaceHeight s0 + spaceHeight s1 + termHeight e + 1

/-- Height of a type, including enough room for its standard frame. -/
def tyHeight : Ty -> Nat
  | .space s => spaceHeight s
  | .piTy tau0 tau1 => tyHeight tau0 + tyHeight tau1 + 1

/-- Height of source syntax.  All annotations are included because validity
and typing derivations traverse them even when the runtime term does not. -/
def termHeight : Term -> Nat
  | .bvar _ => 1
  | .var _ => 1
  | .real _ => 1
  | .zero s => spaceHeight s + 1
  | .inner s => spaceHeight s + 1
  | .embed s => spaceHeight s + 1
  | .smul e0 e1 => termHeight e0 + termHeight e1 + 1
  | .add e0 e1 => termHeight e0 + termHeight e1 + 1
  | .dsumE e0 e1 => termHeight e0 + termHeight e1 + 1
  | .tprodE e0 e1 => termHeight e0 + termHeight e1 + 1
  | .appN e0 e1 => termHeight e0 + termHeight e1 + 1
  | .appL s0 s1 e0 e1 =>
      spaceHeight s0 + spaceHeight s1 + termHeight e0 + termHeight e1 + 1
  | .appI s e0 e1 =>
      spaceHeight s + termHeight e0 + termHeight e1 + 1
  | .llam s0 s1 e =>
      spaceHeight s0 + spaceHeight s1 + termHeight e + 1
  | .nllam tau e => tyHeight tau + termHeight e + 1
  | .pinvT s0 s1 e =>
      spaceHeight s0 + spaceHeight s1 + termHeight e + 1
  | .pinvD s e => spaceHeight s + termHeight e + 1

end

/-- Maximum source height in a finite explicit vector list. -/
def termListHeight : List Term -> Nat
  | [] => 0
  | e :: es => termHeight e + termListHeight es

/-- Height of basis syntax and all source syntax directly stored in it.

The projected-basis arm uses `max (spaceHeight s) (...)`, without adding a
second layer on top of `spaceHeight s`.  This is deliberate: for an FFS
space, `spaceHeight s` already includes the projected constructor and its two
standard component bases.  Consequently `stdSpace` is height-nonincreasing. -/
def basisHeight : Basis -> Nat
  | .empty => 1
  | .one => 1
  | .dual b => basisHeight b + 1
  | .dsum b0 b1 => basisHeight b0 + basisHeight b1 + 1
  | .tprod b0 b1 => basisHeight b0 + basisHeight b1 + 1
  | .proj s b0 b1 =>
      max (spaceHeight s) (basisHeight b0 + basisHeight b1 + 1)
  | .image b => basisHeight b + 1
  | .terms s es b =>
      spaceHeight s + termListHeight es + basisHeight b + 1
  | .frame b0 b1 => basisHeight b0 + basisHeight b1 + 1

/-! ## Opening invariance -/

mutual

theorem spaceHeight_openRec (k : Nat) (y : Name) :
    forall s, spaceHeight (Space.openRec k (.var y) s) = spaceHeight s
  | .empty => rfl
  | .real => rfl
  | .dual s => by
      simp only [Space.openRec, spaceHeight, spaceHeight_openRec k y s]
  | .dsum s0 s1 => by
      simp only [Space.openRec, spaceHeight, spaceHeight_openRec k y s0,
        spaceHeight_openRec k y s1]
  | .tprod s0 s1 => by
      simp only [Space.openRec, spaceHeight, spaceHeight_openRec k y s0,
        spaceHeight_openRec k y s1]
  | .ker s0 s1 e => by
      simp only [Space.openRec, spaceHeight, spaceHeight_openRec k y s0,
        spaceHeight_openRec k y s1, termHeight_openRec k y e]
  | .coker s0 s1 e => by
      simp only [Space.openRec, spaceHeight, spaceHeight_openRec k y s0,
        spaceHeight_openRec k y s1, termHeight_openRec k y e]
  | .img s0 s1 e => by
      simp only [Space.openRec, spaceHeight, spaceHeight_openRec k y s0,
        spaceHeight_openRec k y s1, termHeight_openRec k y e]
  | .coimg s0 s1 e => by
      simp only [Space.openRec, spaceHeight, spaceHeight_openRec k y s0,
        spaceHeight_openRec k y s1, termHeight_openRec k y e]

theorem tyHeight_openRec (k : Nat) (y : Name) :
    forall tau, tyHeight (Ty.openRec k (.var y) tau) = tyHeight tau
  | .space s => by
      simp only [Ty.openRec, tyHeight, spaceHeight_openRec k y s]
  | .piTy tau0 tau1 => by
      simp only [Ty.openRec, tyHeight, tyHeight_openRec k y tau0,
        tyHeight_openRec (k + 1) y tau1]

theorem termHeight_openRec (k : Nat) (y : Name) :
    forall e, termHeight (Term.openRec k (.var y) e) = termHeight e
  | .bvar i => by
      simp only [Term.openRec]
      split <;> simp only [termHeight]
  | .var x => rfl
  | .real r => rfl
  | .zero s => by
      simp only [Term.openRec, termHeight, spaceHeight_openRec k y s]
  | .inner s => by
      simp only [Term.openRec, termHeight, spaceHeight_openRec k y s]
  | .embed s => by
      simp only [Term.openRec, termHeight, spaceHeight_openRec k y s]
  | .smul e0 e1 => by
      simp only [Term.openRec, termHeight, termHeight_openRec k y e0,
        termHeight_openRec k y e1]
  | .add e0 e1 => by
      simp only [Term.openRec, termHeight, termHeight_openRec k y e0,
        termHeight_openRec k y e1]
  | .dsumE e0 e1 => by
      simp only [Term.openRec, termHeight, termHeight_openRec k y e0,
        termHeight_openRec k y e1]
  | .tprodE e0 e1 => by
      simp only [Term.openRec, termHeight, termHeight_openRec k y e0,
        termHeight_openRec k y e1]
  | .appN e0 e1 => by
      simp only [Term.openRec, termHeight, termHeight_openRec k y e0,
        termHeight_openRec k y e1]
  | .appL s0 s1 e0 e1 => by
      simp only [Term.openRec, termHeight, spaceHeight_openRec k y s0,
        spaceHeight_openRec k y s1, termHeight_openRec k y e0,
        termHeight_openRec k y e1]
  | .appI s e0 e1 => by
      simp only [Term.openRec, termHeight, spaceHeight_openRec k y s,
        termHeight_openRec k y e0, termHeight_openRec k y e1]
  | .llam s0 s1 e => by
      simp only [Term.openRec, termHeight, spaceHeight_openRec k y s0,
        spaceHeight_openRec k y s1, termHeight_openRec (k + 1) y e]
  | .nllam tau e => by
      simp only [Term.openRec, termHeight, tyHeight_openRec k y tau,
        termHeight_openRec (k + 1) y e]
  | .pinvT s0 s1 e => by
      simp only [Term.openRec, termHeight, spaceHeight_openRec k y s0,
        spaceHeight_openRec k y s1, termHeight_openRec k y e]
  | .pinvD s e => by
      simp only [Term.openRec, termHeight, spaceHeight_openRec k y s,
        termHeight_openRec k y e]

end

theorem termListHeight_map_openRec (k : Nat) (y : Name) :
    forall es,
      termListHeight (es.map (Term.openRec k (.var y))) = termListHeight es
  | [] => rfl
  | e :: es => by
      simp only [List.map_cons, termListHeight, termHeight_openRec k y e,
        termListHeight_map_openRec k y es]

theorem basisHeight_openRec (k : Nat) (y : Name) :
    forall b, basisHeight (Basis.openRec k (.var y) b) = basisHeight b
  | .empty => rfl
  | .one => rfl
  | .dual b => by
      simp only [Basis.openRec, basisHeight, basisHeight_openRec k y b]
  | .dsum b0 b1 => by
      simp only [Basis.openRec, basisHeight, basisHeight_openRec k y b0,
        basisHeight_openRec k y b1]
  | .tprod b0 b1 => by
      simp only [Basis.openRec, basisHeight, basisHeight_openRec k y b0,
        basisHeight_openRec k y b1]
  | .proj s b0 b1 => by
      simp only [Basis.openRec, basisHeight, spaceHeight_openRec k y s,
        basisHeight_openRec k y b0, basisHeight_openRec k y b1]
  | .image b => by
      simp only [Basis.openRec, basisHeight, basisHeight_openRec k y b]
  | .terms s es b => by
      simp only [Basis.openRec, basisHeight, spaceHeight_openRec k y s,
        basisHeight_openRec k y b, Term.openRecList_eq_map,
        termListHeight_map_openRec k y es]
  | .frame b0 b1 => by
      simp only [Basis.openRec, basisHeight, basisHeight_openRec k y b0,
        basisHeight_openRec (k + 1) y b1]

@[simp] theorem spaceHeight_openRec_zero (y : Name) (s : Space) :
    spaceHeight (Space.openRec 0 (.var y) s) = spaceHeight s :=
  spaceHeight_openRec 0 y s

@[simp] theorem tyHeight_openVar (y : Name) (tau : Ty) :
    tyHeight (Ty.openVar y tau) = tyHeight tau :=
  tyHeight_openRec 0 y tau

@[simp] theorem termHeight_openVar (y : Name) (e : Term) :
    termHeight (Term.openVar y e) = termHeight e :=
  termHeight_openRec 0 y e

@[simp] theorem basisHeight_openVar (y : Name) (b : Basis) :
    basisHeight (Basis.openVar y b) = basisHeight b :=
  basisHeight_openRec 0 y b

/-! ## Standard-basis bounds -/

theorem basisHeight_stdSpace_le : forall s,
    basisHeight (Basis.stdSpace s) <= spaceHeight s
  | .empty => by simp [Basis.stdSpace, basisHeight, spaceHeight]
  | .real => by simp [Basis.stdSpace, basisHeight, spaceHeight]
  | .dual s => by
      simp only [Basis.stdSpace, basisHeight, spaceHeight]
      exact Nat.add_le_add_right (basisHeight_stdSpace_le s) 1
  | .dsum s0 s1 => by
      simp only [Basis.stdSpace, basisHeight, spaceHeight]
      have h0 := basisHeight_stdSpace_le s0
      have h1 := basisHeight_stdSpace_le s1
      omega
  | .tprod s0 s1 => by
      simp only [Basis.stdSpace, basisHeight, spaceHeight]
      have h0 := basisHeight_stdSpace_le s0
      have h1 := basisHeight_stdSpace_le s1
      omega
  | .ker s0 s1 e => by
      simp only [Basis.stdSpace, basisHeight, spaceHeight]
      apply max_le
      · exact le_rfl
      · have h0 := basisHeight_stdSpace_le s0
        have h1 := basisHeight_stdSpace_le s1
        omega
  | .coker s0 s1 e => by
      simp only [Basis.stdSpace, basisHeight, spaceHeight]
      apply max_le
      · exact le_rfl
      · have h0 := basisHeight_stdSpace_le s0
        have h1 := basisHeight_stdSpace_le s1
        omega
  | .img s0 s1 e => by
      simp only [Basis.stdSpace, basisHeight, spaceHeight]
      apply max_le
      · exact le_rfl
      · have h0 := basisHeight_stdSpace_le s0
        have h1 := basisHeight_stdSpace_le s1
        omega
  | .coimg s0 s1 e => by
      simp only [Basis.stdSpace, basisHeight, spaceHeight]
      apply max_le
      · exact le_rfl
      · have h0 := basisHeight_stdSpace_le s0
        have h1 := basisHeight_stdSpace_le s1
        omega

theorem basisHeight_std_le : forall tau,
    basisHeight (Basis.std tau) <= tyHeight tau
  | .space s => by
      simpa only [Basis.std, tyHeight] using basisHeight_stdSpace_le s
  | .piTy tau0 tau1 => by
      simp only [Basis.std, basisHeight, tyHeight]
      have h0 := basisHeight_std_le tau0
      have h1 := basisHeight_std_le tau1
      omega

/-! ## Exposure and strict-subproblem bounds -/

/-- A basis always budgets for the space exposed by `sof`. -/
theorem spaceHeight_sof_le : forall b,
    spaceHeight (Basis.sof b) <= basisHeight b
  | .empty => by simp [Basis.sof, spaceHeight, basisHeight]
  | .one => by simp [Basis.sof, spaceHeight, basisHeight]
  | .dual b => by
      simp only [Basis.sof, spaceHeight, basisHeight]
      exact Nat.add_le_add_right (spaceHeight_sof_le b) 1
  | .dsum b0 b1 => by
      simp only [Basis.sof, spaceHeight, basisHeight]
      have h0 := spaceHeight_sof_le b0
      have h1 := spaceHeight_sof_le b1
      omega
  | .tprod b0 b1 => by
      simp only [Basis.sof, spaceHeight, basisHeight]
      have h0 := spaceHeight_sof_le b0
      have h1 := spaceHeight_sof_le b1
      omega
  | .proj s b0 b1 => by
      simp only [Basis.sof, basisHeight]
      exact Nat.le_max_left _ _
  | .image b => by
      have ih := spaceHeight_sof_le b
      cases h : Basis.sof b <;>
        simp only [Basis.sof, h, spaceHeight, basisHeight] at ih ⊢ <;>
        omega
  | .terms s es b => by
      simp only [Basis.sof, basisHeight]
      have h := spaceHeight_sof_le b
      omega
  | .frame b0 b1 => by
      simp only [Basis.sof, spaceHeight, basisHeight]
      omega

/-- The complete exposed type of a basis fits in the basis's own height. -/
theorem tyHeight_tof_le : forall b,
    tyHeight (Basis.tof b) <= basisHeight b
  | .frame b0 b1 => by
      simp only [Basis.tof, tyHeight, basisHeight]
      have h0 := tyHeight_tof_le b0
      have h1 := tyHeight_tof_le b1
      omega
  | .empty | .one | .dual _ | .dsum _ _ | .tprod _ _ | .proj _ _ _ |
      .image _ | .terms _ _ _ => by
      simp only [Basis.tof, tyHeight]
      exact spaceHeight_sof_le _

/-- Standardizing an exposed basis type never increases this construction
height.  This is the arithmetic fact used to build both sides of a non-frame
quad at one common predecessor depth. -/
theorem basisHeight_std_tof_le (b : Basis) :
    basisHeight (Basis.std (Basis.tof b)) <= basisHeight b :=
  le_trans (basisHeight_std_le (Basis.tof b)) (tyHeight_tof_le b)

theorem basisHeight_frame_domain_lt (b0 b1 : Basis) :
    basisHeight b0 < basisHeight (.frame b0 b1) := by
  simp only [basisHeight]
  omega

theorem basisHeight_frame_body_open_lt (y : Name) (b0 b1 : Basis) :
    basisHeight (Basis.openVar y b1) < basisHeight (.frame b0 b1) := by
  simp only [basisHeight, basisHeight_openVar]
  omega

theorem basisHeight_std_pi_domain_lt (tau0 tau1 : Ty) :
    basisHeight (Basis.std tau0) < tyHeight (.piTy tau0 tau1) := by
  simp only [tyHeight]
  have h := basisHeight_std_le tau0
  omega

/-- A dependent type has enough additive budget to construct its standard
domain first and then continue through the opened codomain. -/
theorem basisHeight_std_add_openTy_lt_pi
    (y : Name) (tau0 tau1 : Ty) :
    basisHeight (Basis.std tau0) + tyHeight (Ty.openVar y tau1) <
      tyHeight (.piTy tau0 tau1) := by
  simp only [tyHeight, tyHeight_openVar]
  have h := basisHeight_std_le tau0
  omega

theorem basisHeight_std_nllam_domain_lt (tau : Ty) (e : Term) :
    basisHeight (Basis.std tau) < termHeight (.nllam tau e) := by
  simp only [termHeight]
  have h := basisHeight_std_le tau
  omega

/-- A nonlinear lambda has enough additive budget to construct its standard
domain first and then traverse the opened body. -/
theorem basisHeight_std_add_openTerm_lt_nllam
    (y : Name) (tau : Ty) (e : Term) :
    basisHeight (Basis.std tau) + termHeight (Term.openVar y e) <
      termHeight (.nllam tau e) := by
  simp only [termHeight, termHeight_openVar]
  have h := basisHeight_std_le tau
  omega

theorem basisHeight_std_llam_domain_lt
    (s0 s1 : Space) (e : Term) :
    basisHeight (Basis.stdSpace s0) < termHeight (.llam s0 s1 e) := by
  simp only [termHeight]
  have h := basisHeight_stdSpace_le s0
  omega

/-- A linear lambda likewise budgets first for its standard domain and then
for the opened source body. -/
theorem basisHeight_stdSpace_add_openTerm_lt_llam
    (y : Name) (s0 s1 : Space) (e : Term) :
    basisHeight (Basis.stdSpace s0) + termHeight (Term.openVar y e) <
      termHeight (.llam s0 s1 e) := by
  simp only [termHeight, termHeight_openVar]
  have h := basisHeight_stdSpace_le s0
  omega

theorem basisHeight_frame_domain_add_body_open_lt
    (y : Name) (b0 b1 : Basis) :
    basisHeight b0 + basisHeight (Basis.openVar y b1) <
      basisHeight (.frame b0 b1) := by
  simp only [basisHeight, basisHeight_openVar]
  omega

end RawCertifiedPairCreationDepth
end GLang
