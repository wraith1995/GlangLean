import GLang.Proofs.Progress.Certificates.RawCertifiedCallProgress

namespace GLang
namespace RawCertifiedCobProgressMutualSpike

open OperationalStrengthening
open RawCertifiedOperational
open RawCertifiedProgressScratch
open RawCertifiedHereditaryStore

/-! ## Basis-indexed local-side certificate -/

/-- Local variable-basis validity for every source judgment embedded in one
*chosen* `BasisValid` derivation.

The index is the proof, not just the basis syntax.  This matters because
`HasType` is proof-relevant: two derivations with the same conclusion can
place `promote` at different positions and hence expose different premise
contexts.  Each source field packages one explicit derivation together with
its local-side tree.  It need not be definitionally the opaque witness inside
`Nonempty` carried by `BasisValid`: the checked constructors consume any
derivation of the same indexed source judgment. -/
inductive CheckedLocalSideBasisValid (Psi0 : EvalCtx) :
    {Gamma : NLCtx} -> {b : Basis} ->
      Basis.BasisValid Gamma b -> Prop
  | empty {Gamma} :
      CheckedLocalSideBasisValid Psi0
        (Basis.BasisValid.empty : Basis.BasisValid Gamma .empty)
  | one {Gamma} :
      CheckedLocalSideBasisValid Psi0
        (Basis.BasisValid.one : Basis.BasisValid Gamma .one)
  | dual {Gamma b} {hb : Basis.BasisValid Gamma b}
      {htof : Basis.tof b = .space (Basis.sof b)}
      (side : CheckedLocalSideBasisValid Psi0 hb) :
      CheckedLocalSideBasisValid Psi0 (.dual hb htof)
  | dsum {Gamma b0 b1}
      {hb0 : Basis.BasisValid Gamma b0}
      {hb1 : Basis.BasisValid Gamma b1}
      {htof0 : Basis.tof b0 = .space (Basis.sof b0)}
      {htof1 : Basis.tof b1 = .space (Basis.sof b1)}
      (side0 : CheckedLocalSideBasisValid Psi0 hb0)
      (side1 : CheckedLocalSideBasisValid Psi0 hb1) :
      CheckedLocalSideBasisValid Psi0 (.dsum hb0 hb1 htof0 htof1)
  | tprod {Gamma b0 b1}
      {hb0 : Basis.BasisValid Gamma b0}
      {hb1 : Basis.BasisValid Gamma b1}
      {htof0 : Basis.tof b0 = .space (Basis.sof b0)}
      {htof1 : Basis.tof b1 = .space (Basis.sof b1)}
      (side0 : CheckedLocalSideBasisValid Psi0 hb0)
      (side1 : CheckedLocalSideBasisValid Psi0 hb1) :
      CheckedLocalSideBasisValid Psi0 (.tprod hb0 hb1 htof0 htof1)
  | proj_ker {Gamma s0 s1 e b0 b1}
      {hb0 : Basis.BasisValid Gamma b0}
      {hb1 : Basis.BasisValid Gamma b1}
      {htof0 : Basis.tof b0 = .space s0} {htof1 : Basis.tof b1 = .space s1}
      {ht : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))}
      (side0 : CheckedLocalSideBasisValid Psi0 hb0)
      (side1 : CheckedLocalSideBasisValid Psi0 hb1)
      (termSide : exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBases Psi0 ht0)) :
      CheckedLocalSideBasisValid Psi0
        (.proj_ker hb0 hb1 htof0 htof1 ht)
  | proj_coker {Gamma s0 s1 e b0 b1}
      {hb0 : Basis.BasisValid Gamma b0}
      {hb1 : Basis.BasisValid Gamma b1}
      {htof0 : Basis.tof b0 = .space s0} {htof1 : Basis.tof b1 = .space s1}
      {ht : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))}
      (side0 : CheckedLocalSideBasisValid Psi0 hb0)
      (side1 : CheckedLocalSideBasisValid Psi0 hb1)
      (termSide : exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBases Psi0 ht0)) :
      CheckedLocalSideBasisValid Psi0
        (.proj_coker hb0 hb1 htof0 htof1 ht)
  | proj_img {Gamma s0 s1 e b0 b1}
      {hb0 : Basis.BasisValid Gamma b0}
      {hb1 : Basis.BasisValid Gamma b1}
      {htof0 : Basis.tof b0 = .space s0} {htof1 : Basis.tof b1 = .space s1}
      {ht : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))}
      (side0 : CheckedLocalSideBasisValid Psi0 hb0)
      (side1 : CheckedLocalSideBasisValid Psi0 hb1)
      (termSide : exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBases Psi0 ht0)) :
      CheckedLocalSideBasisValid Psi0
        (.proj_img hb0 hb1 htof0 htof1 ht)
  | proj_coimg {Gamma s0 s1 e b0 b1}
      {hb0 : Basis.BasisValid Gamma b0}
      {hb1 : Basis.BasisValid Gamma b1}
      {htof0 : Basis.tof b0 = .space s0} {htof1 : Basis.tof b1 = .space s1}
      {ht : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))}
      (side0 : CheckedLocalSideBasisValid Psi0 hb0)
      (side1 : CheckedLocalSideBasisValid Psi0 hb1)
      (termSide : exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBases Psi0 ht0)) :
      CheckedLocalSideBasisValid Psi0
        (.proj_coimg hb0 hb1 htof0 htof1 ht)
  | image {Gamma b s0 s1 e}
      {hb : Basis.BasisValid Gamma b}
      {hsof : Basis.sof b = .coker s0 s1 e}
      {ht : Nonempty (HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)))}
      (side : CheckedLocalSideBasisValid Psi0 hb)
      (termSide : exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBases Psi0 ht0)) :
      CheckedLocalSideBasisValid Psi0 (.image hb hsof ht)
  | terms {Gamma s es b}
      {hb : Basis.BasisValid Gamma b} {htof : Basis.tof b = .space s}
      {hs : Nonempty (SValid Gamma s)}
      {hts : forall e, e ∈ es ->
        Nonempty (HasType (∅ : LCtx) Gamma e (.space s))}
      {hne : es ≠ []}
      (side : CheckedLocalSideBasisValid Psi0 hb)
      (spaceSide : exists hs0 : SValid Gamma s,
        Nonempty (CheckedLocalSideS Psi0 hs0))
      (termSides : forall e (he : e ∈ es),
        exists ht0 : HasType (∅ : LCtx) Gamma e (.space s),
          Nonempty (CheckedLocalSideBases Psi0 ht0)) :
      CheckedLocalSideBasisValid Psi0 (.terms hb htof hs hts hne)
  | frame {Gamma b0 b1 k0 k1}
      {L : Finset Name} {hb0 : Basis.BasisValid Gamma b0}
      {hbody : forall y, y ∉ L ->
        Basis.BasisValid (Finmap.insert y (Basis.tof b0) Gamma)
          (Basis.openVar y b1)}
      (domainSide : CheckedLocalSideBasisValid Psi0 hb0)
      (bodySide : forall y (hy : y ∉ L),
        CheckedLocalSideBasisValid Psi0 (hbody y hy))
      (typeSide : exists ht0 : TValid Gamma
          (.piTy (Basis.tof b0) (Basis.tof b1)) (.arrow k0 k1),
        Nonempty (CheckedLocalSideT Psi0 ht0)) :
      CheckedLocalSideBasisValid Psi0 (.frame L hb0 hbody)

/-! The source-term fields are not decorative: these projections are the
exact evidence absent from `CheckedCobToStd` in each non-structural branch. -/

theorem CheckedLocalSideBasisValid.proj_ker_term
    {Psi0 : EvalCtx} {Gamma : NLCtx} {s0 s1 : Space} {e : Term}
    {b0 b1 : Basis} {hb0 : Basis.BasisValid Gamma b0}
    {hb1 : Basis.BasisValid Gamma b1}
    {htof0 : Basis.tof b0 = .space s0} {htof1 : Basis.tof b1 = .space s1}
    {ht : Nonempty (HasType (∅ : LCtx) Gamma e
      (.space (.tprod (.dual s0) s1)))}
    (h : CheckedLocalSideBasisValid Psi0
      (.proj_ker hb0 hb1 htof0 htof1 ht)) :
    exists ht0 : HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)),
      Nonempty (CheckedLocalSideBases Psi0 ht0) := by
  cases h with
  | proj_ker _ _ termSide => exact termSide

theorem CheckedLocalSideBasisValid.image_term
    {Psi0 : EvalCtx} {Gamma : NLCtx} {b : Basis}
    {hbImage : Basis.BasisValid Gamma (.image b)}
    (h : CheckedLocalSideBasisValid Psi0 hbImage) :
    exists s0 s1 e, Basis.sof b = .coker s0 s1 e /\
      exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBases Psi0 ht0) := by
  cases h <;> aesop

theorem CheckedLocalSideBasisValid.terms_term
    {Psi0 : EvalCtx} {Gamma : NLCtx} {s : Space} {es : List Term}
    {b : Basis} {hb : Basis.BasisValid Gamma b}
    {htof : Basis.tof b = .space s} {hs : Nonempty (SValid Gamma s)}
    {hts : forall e, e ∈ es ->
      Nonempty (HasType (∅ : LCtx) Gamma e (.space s))}
    {hne : es ≠ []}
    (h : CheckedLocalSideBasisValid Psi0 (.terms hb htof hs hts hne))
    {e : Term} (he : e ∈ es) :
    exists ht0 : HasType (∅ : LCtx) Gamma e (.space s),
      Nonempty (CheckedLocalSideBases Psi0 ht0) := by
  cases h with
  | terms _ _ termSides => exact termSides e he

/-! ## Fuel-indexed cross-closed replacement

The preceding certificate says which source judgments occur inside a basis,
but its inherited `CheckedLocalSideBases` stops at `BasisValid` at a variable
leaf.  It therefore does not by itself authorize the next
`term(var) -> selected basis` call.  The following version closes that edge.

Both directions spend one depth layer:

* a source variable at depth `n+1` selects a basis certified at depth `n`;
* a non-structural basis at depth `n+1` embeds source evidence at depth `n`.

Structural recursion inside either syntax stays at the current depth.  Depth
zero permits arbitrary source structure with no usable variable lookup and
only the five term-free basis constructors. -/

/-- A family of proof-indexed basis-side obligations. -/
abbrev CheckedSelectedBasisSide :=
  forall {Gamma : NLCtx} {b : Basis}, Basis.BasisValid Gamma b -> Prop

def CheckedLocalTermSideBasisWithWorld
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    (W : EvalCtx → Prop) :
    {Delta : LCtx} -> {Gamma : NLCtx} -> {e : Term} -> {tau : Ty} ->
      HasType Delta Gamma e tau -> Prop
  | _, Gamma, _, _, @HasType.var_lin _ x s =>
      forall Psi' : EvalCtx, W Psi' ->
        (V2.VarsCovered (Finmap.singleton x s) Gamma Psi' ->
          exists b v, EvalCtx.lookup Psi' (x, b) = some v /\
            Basis.tof b = .space s /\
            exists hb : Basis.BasisValid Gamma b, selected hb) /\
        (forall b v, EvalCtx.lookup Psi' (x, b) = some v ->
          Basis.tof b = .space s -> Basis.BasisValid Gamma b)
  | _, Gamma, _, _, @HasType.var_nlin _ x tau _ =>
      forall Psi' : EvalCtx, W Psi' ->
        (V2.VarsCovered (∅ : LCtx) Gamma Psi' ->
          exists b v, EvalCtx.lookup Psi' (x, b) = some v /\
            Basis.tof b = tau /\
            exists hb : Basis.BasisValid Gamma b, selected hb) /\
        (forall b v, EvalCtx.lookup Psi' (x, b) = some v ->
          Basis.tof b = tau -> Basis.BasisValid Gamma b)
  | _, _, _, _, _ => True

/-- Backwards-compatible standard-future specialization. -/
abbrev CheckedLocalTermSideBasisWith
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) : Prop :=
  CheckedLocalTermSideBasisWithWorld selected Psi (CheckedStdFuture Psi) h

/-- Source-side certificates parameterized by the selected-basis obligation. -/
structure CheckedLocalSideSWithWorld
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    (W : EvalCtx → Prop)
    {Gamma : NLCtx} {s : Space} (h : SValid Gamma s) : Type where
  shallow : CheckedLocalSideS Psi h
  deep :
    @SValid.below
      (fun _ _ _ => True)
      (fun _ _ _ _ => True)
      (fun _ _ _ _ => True)
      (fun _ _ _ _ he =>
        CheckedLocalTermSideBasisWithWorld selected Psi W he)
      Gamma s h

structure CheckedLocalSideTWithWorld
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    (W : EvalCtx → Prop)
    {Gamma : NLCtx} {tau : Ty} {k : Kind}
    (h : TValid Gamma tau k) : Type where
  shallow : CheckedLocalSideT Psi h
  deep :
    @TValid.below
      (fun _ _ _ => True)
      (fun _ _ _ _ => True)
      (fun _ _ _ _ => True)
      (fun _ _ _ _ he =>
        CheckedLocalTermSideBasisWithWorld selected Psi W he)
      Gamma tau k h

structure CheckedLocalSideSubWithWorld
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    (W : EvalCtx → Prop)
    {Gamma : NLCtx} {s0 s1 : Space}
    (h : SubType Gamma s0 s1) : Type where
  shallow : CheckedLocalSideSub Psi h
  deep :
    @SubType.below
      (fun _ _ _ => True)
      (fun _ _ _ _ => True)
      (fun _ _ _ _ => True)
      (fun _ _ _ _ he =>
        CheckedLocalTermSideBasisWithWorld selected Psi W he)
      Gamma s0 s1 h

structure CheckedLocalSideBasesWithWorld
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    (W : EvalCtx → Prop)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) : Type where
  shallow : CheckedLocalSideBases Psi h
  deepHere : CheckedLocalTermSideBasisWithWorld selected Psi W h
  deepDescendants :
    @HasType.below
      (fun _ _ _ => True)
      (fun _ _ _ _ => True)
      (fun _ _ _ _ => True)
      (fun _ _ _ _ he =>
        CheckedLocalTermSideBasisWithWorld selected Psi W he)
      Delta Gamma e tau h

/-- Backwards-compatible standard-future specializations. -/
abbrev CheckedLocalSideSWith
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    {Gamma : NLCtx} {s : Space} (h : SValid Gamma s) : Type :=
  CheckedLocalSideSWithWorld selected Psi (CheckedStdFuture Psi) h

abbrev CheckedLocalSideTWith
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    {Gamma : NLCtx} {tau : Ty} {k : Kind}
    (h : TValid Gamma tau k) : Type :=
  CheckedLocalSideTWithWorld selected Psi (CheckedStdFuture Psi) h

abbrev CheckedLocalSideSubWith
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    {Gamma : NLCtx} {s0 s1 : Space}
    (h : SubType Gamma s0 s1) : Type :=
  CheckedLocalSideSubWithWorld selected Psi (CheckedStdFuture Psi) h

abbrev CheckedLocalSideBasesWith
    (selected : CheckedSelectedBasisSide) (Psi : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) : Type :=
  CheckedLocalSideBasesWithWorld selected Psi (CheckedStdFuture Psi) h

/-- At basis depth zero there is no basis-to-source cross edge. -/
inductive CheckedLocalSideBasisZero :
    {Gamma : NLCtx} -> {b : Basis} ->
      Basis.BasisValid Gamma b -> Prop
  | empty {Gamma} : CheckedLocalSideBasisZero
      (Basis.BasisValid.empty : Basis.BasisValid Gamma .empty)
  | one {Gamma} : CheckedLocalSideBasisZero
      (Basis.BasisValid.one : Basis.BasisValid Gamma .one)
  | dual {Gamma b} {hb : Basis.BasisValid Gamma b}
      {htof : Basis.tof b = .space (Basis.sof b)}
      (side : CheckedLocalSideBasisZero hb) :
      CheckedLocalSideBasisZero (.dual hb htof)
  | dsum {Gamma b0 b1}
      {hb0 : Basis.BasisValid Gamma b0}
      {hb1 : Basis.BasisValid Gamma b1}
      {htof0 : Basis.tof b0 = .space (Basis.sof b0)}
      {htof1 : Basis.tof b1 = .space (Basis.sof b1)}
      (side0 : CheckedLocalSideBasisZero hb0)
      (side1 : CheckedLocalSideBasisZero hb1) :
      CheckedLocalSideBasisZero (.dsum hb0 hb1 htof0 htof1)
  | tprod {Gamma b0 b1}
      {hb0 : Basis.BasisValid Gamma b0}
      {hb1 : Basis.BasisValid Gamma b1}
      {htof0 : Basis.tof b0 = .space (Basis.sof b0)}
      {htof1 : Basis.tof b1 = .space (Basis.sof b1)}
      (side0 : CheckedLocalSideBasisZero hb0)
      (side1 : CheckedLocalSideBasisZero hb1) :
      CheckedLocalSideBasisZero (.tprod hb0 hb1 htof0 htof1)

def CheckedLocalSideBasisSyntaxLayer
    (Psi : EvalCtx) (selected : EvalCtx → CheckedSelectedBasisSide)
    (Gamma : NLCtx) : Basis -> Prop
  | .empty => True
  | .one => True
  | .dual b =>
      exists hb : Basis.BasisValid Gamma b,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b
  | .dsum b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b0) /\
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b1)
  | .tprod b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b0) /\
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b1)
  | .proj (.ker s0 s1 e) b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b0) /\
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b1) /\
      Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
      exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBasesWith (selected Psi) Psi ht0)
  | .proj (.coker s0 s1 e) b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b0) /\
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b1) /\
      Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
      exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBasesWith (selected Psi) Psi ht0)
  | .proj (.img s0 s1 e) b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b0) /\
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b1) /\
      Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
      exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBasesWith (selected Psi) Psi ht0)
  | .proj (.coimg s0 s1 e) b0 b1 =>
      (exists hb0 : Basis.BasisValid Gamma b0,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b0) /\
      (exists hb1 : Basis.BasisValid Gamma b1,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b1) /\
      Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
      exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBasesWith (selected Psi) Psi ht0)
  | .proj _ _ _ => False
  | .image b =>
      exists s0 s1 e, exists hb : Basis.BasisValid Gamma b,
        Basis.sof b = .coker s0 s1 e /\
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b /\
        exists ht0 : HasType (∅ : LCtx) Gamma e
            (.space (.tprod (.dual s0) s1)),
          Nonempty (CheckedLocalSideBasesWith (selected Psi) Psi ht0)
  | .terms s es b =>
      (exists hb : Basis.BasisValid Gamma b,
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b) /\
      Basis.sof b = s /\
      (exists hs0 : SValid Gamma s,
        Nonempty (CheckedLocalSideSWith (selected Psi) Psi hs0)) /\
      forall e (he : e ∈ es),
        exists ht0 : HasType (∅ : LCtx) Gamma e (.space s),
          Nonempty (CheckedLocalSideBasesWith (selected Psi) Psi ht0)
  | .frame b0 b1 =>
      exists k0 k1, exists L : Finset Name,
        exists hb0 : Basis.BasisValid Gamma b0,
        exists hbody : forall y, y ∉ L ->
          Basis.BasisValid (Finmap.insert y (Basis.tof b0) Gamma)
            (Basis.openVar y b1),
        CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b0 /\
        (forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
          forall y (hy : y ∉ L) (bArg : Basis) (v : ValExpr),
          Basis.BasisValid Gamma bArg -> Basis.tof bArg = Basis.tof b0 ->
          (forall _hb0x : Basis.BasisValid
              (Finmap.insert y (Basis.tof b0) Gamma) b0,
            CheckedLocalSideBasisSyntaxLayer (Psi'.extend y bArg v) selected
              (Finmap.insert y (Basis.tof b0) Gamma) b0) /\
            CheckedLocalSideBasisSyntaxLayer (Psi'.extend y bArg v) selected
              (Finmap.insert y (Basis.tof b0) Gamma) (Basis.openVar y b1)) /\
        exists ht0 : TValid Gamma
            (.piTy (Basis.tof b0) (Basis.tof b1)) (.arrow k0 k1),
          Nonempty (CheckedLocalSideTWith (selected Psi) Psi ht0)
termination_by b => Basis.size b
decreasing_by
  all_goals simp [Basis.size, Basis.size_openVar] <;> omega

/-- Proof-indexed façade used by consumers.  The proof argument guarantees
validity of the root; the syntax layer carries the particular child/source
proofs chosen for recursive calls. -/
def CheckedLocalSideBasisLayer
    (Psi : EvalCtx) (selected : EvalCtx → CheckedSelectedBasisSide)
    {Gamma : NLCtx} {b : Basis} (_hb : Basis.BasisValid Gamma b) : Prop :=
  CheckedLocalSideBasisSyntaxLayer Psi selected Gamma b

/-- No selected basis is available below source depth zero. -/
def NoCheckedSelectedBasis : CheckedSelectedBasisSide := fun _ => False

/-- Fuel-indexed basis closure.  At zero only term-free basis structure is
allowed; at a successor, embedded source judgments see the preceding source
depth while basis children remain in the same `BasisLayer`. -/
def CheckedLocalSideBasisDepth (Psi : EvalCtx) :
    Nat -> {Gamma : NLCtx} -> {b : Basis} ->
      Basis.BasisValid Gamma b -> Prop
  | 0, _, _, hb => CheckedLocalSideBasisZero hb
  | n + 1, _, _, hb =>
      CheckedLocalSideBasisLayer Psi
        (fun Psi' => match n with
          | 0 => NoCheckedSelectedBasis
          | m + 1 => fun hb' => CheckedLocalSideBasisDepth Psi' m hb') hb
termination_by n _ _ _ => n

/-- The selected-basis family visible to source evidence at depth `n`. -/
def CheckedSelectedBasisAt (Psi : EvalCtx) : Nat -> CheckedSelectedBasisSide
  | 0 => NoCheckedSelectedBasis
  | n + 1 => fun hb => CheckedLocalSideBasisDepth Psi n hb

/-- The four source certificates at depth `n`.  A variable leaf sees
`CheckedSelectedBasisAt Psi n`: no selected basis at zero, and a basis at
depth `n-1` at a successor. -/
abbrev CheckedLocalSideSDepth (Psi : EvalCtx) (n : Nat)
    {Gamma : NLCtx} {s : Space} (h : SValid Gamma s) : Type :=
  CheckedLocalSideSWith (CheckedSelectedBasisAt Psi n) Psi h

abbrev CheckedLocalSideTDepth (Psi : EvalCtx) (n : Nat)
    {Gamma : NLCtx} {tau : Ty} {k : Kind} (h : TValid Gamma tau k) : Type :=
  CheckedLocalSideTWith (CheckedSelectedBasisAt Psi n) Psi h

abbrev CheckedLocalSideSubDepth (Psi : EvalCtx) (n : Nat)
    {Gamma : NLCtx} {s0 s1 : Space} (h : SubType Gamma s0 s1) : Type :=
  CheckedLocalSideSubWith (CheckedSelectedBasisAt Psi n) Psi h

abbrev CheckedLocalSideBasesDepth (Psi : EvalCtx) (n : Nat)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (h : HasType Delta Gamma e tau) : Type :=
  CheckedLocalSideBasesWith (CheckedSelectedBasisAt Psi n) Psi h

/-- User-facing existential closure. The numeric depth records finite rank in
the alternating term/basis reconstruction dependency graph; frame callbacks
may still be infinitely branching. No constructor from bare ordinary-progress
premises is currently claimed. A future raw-history construction additionally
needs proof-local basis locality/validity through context restriction. -/
def CheckedLocalSideBasisFinite (Psi : EvalCtx)
    {Gamma : NLCtx} {b : Basis} (hb : Basis.BasisValid Gamma b) : Prop :=
  exists n, CheckedLocalSideBasisDepth Psi n hb

def CheckedLocalSideBasesFinite (Psi : EvalCtx)
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    (ht : HasType Delta Gamma e tau) : Prop :=
  exists n, Nonempty (CheckedLocalSideBasesDepth Psi n ht)

/-! ### Source-tree constructors and erasure -/

def CheckedLocalSideSWith.ofBelowPair
    {selected : CheckedSelectedBasisSide} {Psi : EvalCtx}
    {Gamma : NLCtx} {s : Space} {h : SValid Gamma s}
    (shallowPair : PProd True
      (SValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he) h))
    (deepPair : PProd True
      (SValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWith selected Psi he) h)) :
    CheckedLocalSideSWith selected Psi h :=
  ⟨CheckedLocalSideS.ofBelowPair shallowPair, deepPair.2⟩

def CheckedLocalSideTWith.ofBelowPair
    {selected : CheckedSelectedBasisSide} {Psi : EvalCtx}
    {Gamma : NLCtx} {tau : Ty} {k : Kind} {h : TValid Gamma tau k}
    (shallowPair : PProd True
      (TValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he) h))
    (deepPair : PProd True
      (TValid.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWith selected Psi he) h)) :
    CheckedLocalSideTWith selected Psi h :=
  ⟨CheckedLocalSideT.ofBelowPair shallowPair, deepPair.2⟩

def CheckedLocalSideSubWith.ofBelowPair
    {selected : CheckedSelectedBasisSide} {Psi : EvalCtx}
    {Gamma : NLCtx} {s0 s1 : Space} {h : SubType Gamma s0 s1}
    (shallowPair : PProd True
      (SubType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he) h))
    (deepPair : PProd True
      (SubType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWith selected Psi he) h)) :
    CheckedLocalSideSubWith selected Psi h :=
  ⟨CheckedLocalSideSub.ofBelowPair shallowPair, deepPair.2⟩

def CheckedLocalSideBasesWith.ofBelowPair
    {selected : CheckedSelectedBasisSide} {Psi : EvalCtx}
    {Delta : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {h : HasType Delta Gamma e tau}
    (shallowPair : PProd (CheckedLocalTermSideBasis Psi h)
      (HasType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he => CheckedLocalTermSideBasis Psi he) h))
    (deepPair : PProd (CheckedLocalTermSideBasisWith selected Psi h)
      (HasType.below
        (motive_1 := fun _ _ _ => True)
        (motive_2 := fun _ _ _ _ => True)
        (motive_3 := fun _ _ _ _ => True)
        (motive_4 := fun _ _ _ _ he =>
          CheckedLocalTermSideBasisWith selected Psi he) h)) :
    CheckedLocalSideBasesWith selected Psi h :=
  ⟨CheckedLocalSideBases.ofBelowPair shallowPair, deepPair.1, deepPair.2⟩

def CheckedLocalSideBasesWith.promoteInner
    {selected : CheckedSelectedBasisSide} {Psi : EvalCtx}
    {Delta lin : LCtx} {Gamma : NLCtx} {e : Term} {tau : Ty}
    {hdisjDelta : Finmap.Disjoint lin Delta}
    {hdisjGamma : Finmap.Disjoint lin.toNL Gamma}
    {hfresh : PromoteFresh lin Delta Gamma}
    {hinner : HasType (lin ∪ Delta) Gamma e tau}
    (h : CheckedLocalSideBasesWith selected Psi
      (.promote lin hdisjDelta hdisjGamma hfresh hinner)) :
    CheckedLocalSideBasesWith selected Psi hinner :=
  ⟨h.shallow.promoteInner, h.deepDescendants.1, h.deepDescendants.2⟩

def CheckedLocalSideSDepth.toShallow
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {s : Space}
    {h : SValid Gamma s} (side : CheckedLocalSideSDepth Psi n h) :
    CheckedLocalSideS Psi h := side.shallow

def CheckedLocalSideTDepth.toShallow
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {tau : Ty} {k : Kind}
    {h : TValid Gamma tau k} (side : CheckedLocalSideTDepth Psi n h) :
    CheckedLocalSideT Psi h := side.shallow

def CheckedLocalSideSubDepth.toShallow
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {s0 s1 : Space}
    {h : SubType Gamma s0 s1} (side : CheckedLocalSideSubDepth Psi n h) :
    CheckedLocalSideSub Psi h := side.shallow

def CheckedLocalSideBasesDepth.toShallow
    {Psi : EvalCtx} {n : Nat} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {tau : Ty} {h : HasType Delta Gamma e tau}
    (side : CheckedLocalSideBasesDepth Psi n h) :
    CheckedLocalSideBases Psi h := side.shallow

def CheckedLocalSideBasesDepth.promoteInner
    {Psi : EvalCtx} {n : Nat} {Delta lin : LCtx} {Gamma : NLCtx}
    {e : Term} {tau : Ty}
    {hdisjDelta : Finmap.Disjoint lin Delta}
    {hdisjGamma : Finmap.Disjoint lin.toNL Gamma}
    {hfresh : PromoteFresh lin Delta Gamma}
    {hinner : HasType (lin ∪ Delta) Gamma e tau}
    (h : CheckedLocalSideBasesDepth Psi n
      (.promote lin hdisjDelta hdisjGamma hfresh hinner)) :
    CheckedLocalSideBasesDepth Psi n hinner :=
  CheckedLocalSideBasesWith.promoteInner h

/-! ### Basis-layer inversions -/

theorem CheckedLocalSideBasisDepth.dual_child
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma (.dual b)}
    (side : CheckedLocalSideBasisDepth Psi n hb) :
    exists hb0 : Basis.BasisValid Gamma b,
      CheckedLocalSideBasisDepth Psi n hb0 := by
  cases n with
  | zero =>
      have side' : CheckedLocalSideBasisZero hb := by
        simpa only [CheckedLocalSideBasisDepth] using side
      cases side' with
      | @dual _ hb0 _ side0 =>
          refine ⟨hb0, ?_⟩
          simpa only [CheckedLocalSideBasisDepth] using side0
  | succ n =>
      simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer] using side

theorem CheckedLocalSideBasisDepth.dsum_children
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.dsum b0 b1)}
    (side : CheckedLocalSideBasisDepth Psi n hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedLocalSideBasisDepth Psi n hb0) /\
    exists hb1 : Basis.BasisValid Gamma b1,
      CheckedLocalSideBasisDepth Psi n hb1 := by
  cases n with
  | zero =>
      have side' : CheckedLocalSideBasisZero hb := by
        simpa only [CheckedLocalSideBasisDepth] using side
      cases side' with
      | @dsum _ _ hb0 hb1 _ _ side0 side1 =>
          refine ⟨⟨hb0, ?_⟩, ⟨hb1, ?_⟩⟩
          · simpa only [CheckedLocalSideBasisDepth] using side0
          · simpa only [CheckedLocalSideBasisDepth] using side1
  | succ n =>
      simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer] using side

theorem CheckedLocalSideBasisDepth.tprod_children
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.tprod b0 b1)}
    (side : CheckedLocalSideBasisDepth Psi n hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedLocalSideBasisDepth Psi n hb0) /\
    exists hb1 : Basis.BasisValid Gamma b1,
      CheckedLocalSideBasisDepth Psi n hb1 := by
  cases n with
  | zero =>
      have side' : CheckedLocalSideBasisZero hb := by
        simpa only [CheckedLocalSideBasisDepth] using side
      cases side' with
      | @tprod _ _ hb0 hb1 _ _ side0 side1 =>
          refine ⟨⟨hb0, ?_⟩, ⟨hb1, ?_⟩⟩
          · simpa only [CheckedLocalSideBasisDepth] using side0
          · simpa only [CheckedLocalSideBasisDepth] using side1
  | succ n =>
      simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
        CheckedLocalSideBasisSyntaxLayer] using side

theorem CheckedLocalSideBasisDepth.proj_ker_parts
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {s0 s1 : Space} {e : Term} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.proj (.ker s0 s1 e) b0 b1)}
    (side : CheckedLocalSideBasisDepth Psi (n + 1) hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedLocalSideBasisDepth Psi (n + 1) hb0) /\
    (exists hb1 : Basis.BasisValid Gamma b1,
      CheckedLocalSideBasisDepth Psi (n + 1) hb1) /\
    Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
    exists ht0 : HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)),
      Nonempty (CheckedLocalSideBasesDepth Psi n ht0) := by
  simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
    CheckedLocalSideBasisSyntaxLayer, CheckedSelectedBasisAt] using side

theorem CheckedLocalSideBasisDepth.proj_coker_parts
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {s0 s1 : Space} {e : Term} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.proj (.coker s0 s1 e) b0 b1)}
    (side : CheckedLocalSideBasisDepth Psi (n + 1) hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedLocalSideBasisDepth Psi (n + 1) hb0) /\
    (exists hb1 : Basis.BasisValid Gamma b1,
      CheckedLocalSideBasisDepth Psi (n + 1) hb1) /\
    Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
    exists ht0 : HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)),
      Nonempty (CheckedLocalSideBasesDepth Psi n ht0) := by
  simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
    CheckedLocalSideBasisSyntaxLayer, CheckedSelectedBasisAt] using side

theorem CheckedLocalSideBasisDepth.proj_img_parts
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {s0 s1 : Space} {e : Term} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.proj (.img s0 s1 e) b0 b1)}
    (side : CheckedLocalSideBasisDepth Psi (n + 1) hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedLocalSideBasisDepth Psi (n + 1) hb0) /\
    (exists hb1 : Basis.BasisValid Gamma b1,
      CheckedLocalSideBasisDepth Psi (n + 1) hb1) /\
    Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
    exists ht0 : HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)),
      Nonempty (CheckedLocalSideBasesDepth Psi n ht0) := by
  simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
    CheckedLocalSideBasisSyntaxLayer, CheckedSelectedBasisAt] using side

theorem CheckedLocalSideBasisDepth.proj_coimg_parts
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {s0 s1 : Space} {e : Term} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.proj (.coimg s0 s1 e) b0 b1)}
    (side : CheckedLocalSideBasisDepth Psi (n + 1) hb) :
    (exists hb0 : Basis.BasisValid Gamma b0,
      CheckedLocalSideBasisDepth Psi (n + 1) hb0) /\
    (exists hb1 : Basis.BasisValid Gamma b1,
      CheckedLocalSideBasisDepth Psi (n + 1) hb1) /\
    Basis.sof b0 = s0 /\ Basis.sof b1 = s1 /\
    exists ht0 : HasType (∅ : LCtx) Gamma e
        (.space (.tprod (.dual s0) s1)),
      Nonempty (CheckedLocalSideBasesDepth Psi n ht0) := by
  simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
    CheckedLocalSideBasisSyntaxLayer, CheckedSelectedBasisAt] using side

theorem CheckedLocalSideBasisDepth.image_parts
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {b : Basis}
    {hb : Basis.BasisValid Gamma (.image b)}
    (side : CheckedLocalSideBasisDepth Psi (n + 1) hb) :
    exists s0 s1 e, exists hb0 : Basis.BasisValid Gamma b,
      Basis.sof b = .coker s0 s1 e /\
      CheckedLocalSideBasisDepth Psi (n + 1) hb0 /\
      exists ht0 : HasType (∅ : LCtx) Gamma e
          (.space (.tprod (.dual s0) s1)),
        Nonempty (CheckedLocalSideBasesDepth Psi n ht0) := by
  simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
    CheckedLocalSideBasisSyntaxLayer, CheckedSelectedBasisAt] using side

theorem CheckedLocalSideBasisDepth.terms_parts
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx}
    {s : Space} {es : List Term} {b : Basis}
    {hb : Basis.BasisValid Gamma (.terms s es b)}
    (side : CheckedLocalSideBasisDepth Psi (n + 1) hb) :
    (exists hb0 : Basis.BasisValid Gamma b,
      CheckedLocalSideBasisDepth Psi (n + 1) hb0) /\
    Basis.sof b = s /\
    (exists hs0 : SValid Gamma s,
      Nonempty (CheckedLocalSideSDepth Psi n hs0)) /\
    forall e (he : e ∈ es),
      exists ht0 : HasType (∅ : LCtx) Gamma e (.space s),
        Nonempty (CheckedLocalSideBasesDepth Psi n ht0) := by
  simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
    CheckedLocalSideBasisSyntaxLayer, CheckedSelectedBasisAt] using side

theorem CheckedLocalSideBasisDepth.frame_parts
    {Psi : EvalCtx} {n : Nat} {Gamma : NLCtx} {b0 b1 : Basis}
    {hb : Basis.BasisValid Gamma (.frame b0 b1)}
    (side : CheckedLocalSideBasisDepth Psi (n + 1) hb) :
    exists k0 k1, exists L : Finset Name,
      exists hb0 : Basis.BasisValid Gamma b0,
      exists hbody : forall y, y ∉ L ->
        Basis.BasisValid (Finmap.insert y (Basis.tof b0) Gamma)
          (Basis.openVar y b1),
      CheckedLocalSideBasisDepth Psi (n + 1) hb0 /\
      (forall (Psi' : EvalCtx), CheckedStdFuture Psi Psi' ->
        forall y (hy : y ∉ L) (bArg : Basis) (v : ValExpr),
        Basis.BasisValid Gamma bArg -> Basis.tof bArg = Basis.tof b0 ->
        (forall hb0x : Basis.BasisValid
            (Finmap.insert y (Basis.tof b0) Gamma) b0,
          CheckedLocalSideBasisDepth (Psi'.extend y bArg v) (n + 1)
            hb0x) /\
        CheckedLocalSideBasisDepth (Psi'.extend y bArg v) (n + 1)
          (hbody y hy)) /\
      exists ht0 : TValid Gamma
          (.piTy (Basis.tof b0) (Basis.tof b1)) (.arrow k0 k1),
        Nonempty (CheckedLocalSideTDepth Psi n ht0) := by
  simpa [CheckedLocalSideBasisDepth, CheckedLocalSideBasisLayer,
    CheckedLocalSideBasisSyntaxLayer, CheckedSelectedBasisAt] using side

/-! ### Exact depth-scoped progress/COB seam -/

/-- Checked standard progress at one source depth below a fixed raw root. -/
def CheckedTermProgressDepth (Psi0 : EvalCtx) (n : Nat) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {e : Term} {tau : Ty}
    (ht : HasType (∅ : LCtx) Gamma e tau),
    CheckedStdFuture Psi0 Psi ->
    CheckedLocalSideBasesDepth Psi0 n ht ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
    exists v tauv,
      C.Term (∅ : LCtx) Gamma Psi e (Basis.std tau) v tauv

/-- Checked COB at a fixed positive/zero basis depth. -/
def CheckedCobToStdDepth (Psi0 : EvalCtx) (n : Nat) : Prop :=
  forall {Gamma : NLCtx} {Psi : EvalCtx} {b : Basis}
    (hb : Basis.BasisValid Gamma b),
    CheckedStdFuture Psi0 Psi ->
    CheckedLocalSideBasisDepth Psi0 n hb ->
    V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
    V2.StoredWF Psi -> V2.CtxWF' (∅ : LCtx) Gamma ->
    Basis.IsSpaceBasis b ->
    exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))

/-- This is the one remaining nonstructural COB layer theorem.  It is
strictly decreasing in cross depth: basis depth `n+1` exposes embedded source
trees at depth `n`.  Structural basis recursion stays inside the conclusion's
`n+1` layer and decreases `Basis.size`. -/
def CheckedCobFromTermDepth : Prop :=
  forall (Psi0 : EvalCtx) (n : Nat),
    CheckedTermProgressDepth Psi0 n -> CheckedCobToStdDepth Psi0 (n + 1)

def CheckedLocalSideBasisDepthNLCtxMono : Prop :=
  forall {Psi : EvalCtx} {n : Nat} {Gamma Gamma' : NLCtx} {b : Basis}
    (hb : Basis.BasisValid Gamma b),
    CheckedLocalSideBasisDepth Psi n hb -> NLCtxIncl Gamma Gamma' ->
    exists hb' : Basis.BasisValid Gamma' b,
      CheckedLocalSideBasisDepth Psi n hb'

/-! ## Honest adequacy-scoped mutual targets -/

/-- Checked closed-term progress below one current raw root.  The side
tree is rooted at `Psi0`, while `Psi` may additionally contain the literal
standard placeholders introduced by checked binders. -/
def RawScopedCheckedClosedStdProgress : Prop :=
  forall (orc : FFSOracleSem)
    (Delta0 : LCtx) (Gamma0 : NLCtx) (Psi0 : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (rho : ValEnvSem),
    RawConsistent orc Delta0 Gamma0 Psi0 GammaV sigma rho ->
    forall (Gamma : NLCtx) (Psi : EvalCtx) (e : Term) (tau : Ty)
      (ht : HasType (∅ : LCtx) Gamma e tau),
      CheckedStdFuture Psi0 Psi ->
      CheckedLocalSideBases Psi0 ht ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.CtxWF' (∅ : LCtx) Gamma ->
      exists v tauv, C.Term (∅ : LCtx) Gamma Psi e (Basis.std tau) v tauv

/-- Checked COB progress with exactly the missing local-side tree added. -/
def RawScopedCheckedCobToStd : Prop :=
  forall (orc : FFSOracleSem)
    (Delta0 : LCtx) (Gamma0 : NLCtx) (Psi0 : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (rho : ValEnvSem),
    RawConsistent orc Delta0 Gamma0 Psi0 GammaV sigma rho ->
    forall (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis)
      (hb : Basis.BasisValid Gamma b),
      CheckedStdFuture Psi0 Psi ->
      CheckedLocalSideBasisValid Psi0 hb ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.CtxWF' (∅ : LCtx) Gamma -> Basis.IsSpaceBasis b ->
      exists env, C.Cob Gamma Psi b env (Basis.std (Basis.tof b))

/-- Exact-basis type progress has the same basis-side requirement: its space
case evaluates source witnesses contained in `Basis.sof b`, and its frame
case repeats that work in the opened codomain. -/
def RawScopedCheckedExactBasisTyProgress : Prop :=
  forall (orc : FFSOracleSem)
    (Delta0 : LCtx) (Gamma0 : NLCtx) (Psi0 : EvalCtx)
    (GammaV : ValCtx) (sigma : DEnv) (rho : ValEnvSem),
    RawConsistent orc Delta0 Gamma0 Psi0 GammaV sigma rho ->
    forall (Gamma : NLCtx) (Psi : EvalCtx) (b : Basis)
      (hb : Basis.BasisValid Gamma b),
      CheckedStdFuture Psi0 Psi ->
      CheckedLocalSideBasisValid Psi0 hb ->
      V2.PCarrier Psi -> V2.VarsCovered (∅ : LCtx) Gamma Psi ->
      V2.CtxWF' (∅ : LCtx) Gamma -> Basis.IsTyBasis b ->
      exists tauv, C.TyAt Gamma Psi b tauv

/-- The constructive endpoint is one simultaneous package.  In a proof by
creation history, `closedTerm` handles source recursion at a fixed history
layer, `cob`/`exactTy` handle basis recursion at that layer, and a variable
leaf re-enters `cob` at the strict creation prefix of its selected key. -/
structure RawScopedCheckedMutual : Prop where
  closedTerm : RawScopedCheckedClosedStdProgress
  cob : RawScopedCheckedCobToStd
  exactTy : RawScopedCheckedExactBasisTyProgress

/-! ## The strict history edge is constructively available -/

/-- A nonempty suffix of exact-key-fresh evaluator extensions.  Its left endpoint is
the evaluator immediately *before* some stored entry was created; hence it is
the strict component needed when a variable leaf re-enters the mutual proof
for that entry's basis. -/
inductive RawEvalStrictSuffix : EvalCtx -> EvalCtx -> Prop
  | here {Psi : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
      (fresh : (x, b) ∉ Psi) :
      RawEvalStrictSuffix Psi (Psi.extend x b v)
  | tail {Psi0 Psi : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
      (prior : RawEvalStrictSuffix Psi0 Psi)
      (fresh : (x, b) ∉ Psi) :
      RawEvalStrictSuffix Psi0 (Psi.extend x b v)

private theorem evalCtx_subctx_extend_of_fresh
    {Psi : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
    (fresh : (x, b) ∉ Psi) :
    Psi.Subctx (Psi.extend x b v) := by
  exact EvalCtx.Subctx.extend_right_of_key_fresh fresh v

/-- Every strict history suffix preserves all lookups from its creation
prefix. -/
theorem RawEvalStrictSuffix.subctx
    (h : RawEvalStrictSuffix Psi0 Psi) : Psi0.Subctx Psi := by
  induction h with
  | here fresh => exact evalCtx_subctx_extend_of_fresh fresh
  | tail prior fresh ih =>
      exact ih.trans (evalCtx_subctx_extend_of_fresh fresh)

/-- Raw-consistency lookup returns the preceding consistency proof, basis validity, dependencies, evaluator suffix, and current lookup. -/
theorem RawConsistent.lookup_creation_strict
    {orc : FFSOracleSem}
    {Delta : LCtx} {Gamma : NLCtx} {Psi : EvalCtx}
    {GammaV : ValCtx} {sigma : DEnv} {rho : ValEnvSem}
    (h : RawConsistent orc Delta Gamma Psi GammaV sigma rho)
    {x : VName} {b : Basis} (hmem : (x, b) ∈ Psi) :
    exists (Delta0 : LCtx) (Gamma0 : NLCtx) (Psi0 : EvalCtx)
      (GammaV0 : ValCtx) (sigma0 : DEnv) (rho0 : ValEnvSem)
      (v : ValExpr),
      RawConsistent orc Delta0 Gamma0 Psi0 GammaV0 sigma0 rho0 /\
      (x, b) ∉ Psi0 /\
      Basis.BasisValid Gamma0 b /\
      Basis.fv b ⊆ Psi0.keyNames /\
      Basis.IsTyBasis b /\
      RawEvalStrictSuffix Psi0 Psi /\
      EvalCtx.lookup Psi (x, b) = some v := by
  induction h with
  | empty => exact absurd hmem Finmap.notMem_empty
  | @extend_lin Delta Gamma Psi GammaV sigma rho x' b' v' tauv xs s yV
      hprefix hx htof hb hTy hinfer hinferSpace hfvv hlc hnr
      hxs hden hagree hdims ih =>
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with heq | hold
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact ⟨Delta, Gamma, Psi, GammaV, sigma, rho, v', hprefix,
          hprefix.freshEvalName hx b, hb, hprefix.basisFvPrefix hb,
          hb.isTyBasis, .here (hprefix.freshEvalName hx b), by
            simp [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]⟩
      · obtain ⟨Delta0, Gamma0, Psi0, GammaV0, sigma0, rho0, v,
          hp, hfresh, hb0, hfv0, his0, hsuffix, hlookup⟩ := ih hold
        have hxx : x ≠ x' := fun heqName =>
          hprefix.freshEvalName hx b (heqName ▸ hold)
        have hkey : (x, b) ≠ (x', b') := fun heqPair =>
          hxx (Prod.mk.inj heqPair).1
        exact ⟨Delta0, Gamma0, Psi0, GammaV0, sigma0, rho0, v,
          hp, hfresh, hb0, hfv0, his0,
          .tail hsuffix (hprefix.freshEvalName hx b'), by
            simpa [EvalCtx.lookup, EvalCtx.extend,
              Finmap.lookup_insert_of_ne _ hkey] using hlookup⟩
  | @extend_nl Delta Gamma Psi GammaV sigma rho x' b' v' tauv xs yV
      hprefix hx hb hTy hinfer hinferSpace hfvv hlc hnr
      hxs hden hagree hdims _hanchor ih =>
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with heq | hold
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact ⟨Delta, Gamma, Psi, GammaV, sigma, rho, v', hprefix,
          hprefix.freshEvalName hx b, hb, hprefix.basisFvPrefix hb,
          hb.isTyBasis, .here (hprefix.freshEvalName hx b), by
            simp [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]⟩
      · obtain ⟨Delta0, Gamma0, Psi0, GammaV0, sigma0, rho0, v,
          hp, hfresh, hb0, hfv0, his0, hsuffix, hlookup⟩ := ih hold
        have hxx : x ≠ x' := fun heqName =>
          hprefix.freshEvalName hx b (heqName ▸ hold)
        have hkey : (x, b) ≠ (x', b') := fun heqPair =>
          hxx (Prod.mk.inj heqPair).1
        exact ⟨Delta0, Gamma0, Psi0, GammaV0, sigma0, rho0, v,
          hp, hfresh, hb0, hfv0, his0,
          .tail hsuffix (hprefix.freshEvalName hx b'), by
            simpa [EvalCtx.lookup, EvalCtx.extend,
              Finmap.lookup_insert_of_ne _ hkey] using hlookup⟩
  | @extend_rep Delta Gamma Psi GammaV sigma rho x' b' v' tauv xs yV
      hprefix hkey hsource hsigma hb hTy hinfer hinferSpace hfvv hlc
      hxs hden hagree hdims hanchor ih =>
      simp only [EvalCtx.extend] at hmem
      rcases Finmap.mem_insert.mp hmem with heq | hold
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        exact ⟨Delta, Gamma, Psi, GammaV, sigma, rho, v', hprefix,
          hkey, hb, hprefix.basisFvPrefix hb, hb.isTyBasis, .here hkey, by
            simp [EvalCtx.lookup, EvalCtx.extend, Finmap.lookup_insert]⟩
      · obtain ⟨Delta0, Gamma0, Psi0, GammaV0, sigma0, rho0, v,
          hp, hfresh, hb0, hfv0, his0, hsuffix, hlookup⟩ := ih hold
        have hneq : (x, b) ≠ (x', b') := fun heqPair => hkey (heqPair ▸ hold)
        exact ⟨Delta0, Gamma0, Psi0, GammaV0, sigma0, rho0, v,
          hp, hfresh, hb0, hfv0, his0, .tail hsuffix hkey, by
            simpa [EvalCtx.lookup, EvalCtx.extend,
              Finmap.lookup_insert_of_ne _ hneq] using hlookup⟩

/-! ## Why one syntax-only recursion cannot close the cycle -/

/-- Arbitrarily large hereditary space bases, used to expose the variable
edge of the call graph. -/
def tallBasis : Nat -> Basis
  | 0 => .one
  | n + 1 => .dual (tallBasis n)

@[simp] theorem tallBasis_size : forall n,
    Basis.size (tallBasis n) = n + 1
  | 0 => rfl
  | n + 1 => by
      simp only [tallBasis, Basis.size, tallBasis_size n]
      omega

theorem tallBasis_valid (Gamma : NLCtx) : forall n,
    Basis.BasisValid Gamma (tallBasis n)
  | 0 => .one
  | n + 1 => .dual (tallBasis_valid Gamma n) (by cases n <;> rfl)

@[simp] theorem tallBasis_isSpace : forall n,
    Basis.IsSpaceBasis (tallBasis n)
  | 0 => trivial
  | n + 1 => tallBasis_isSpace n

theorem tallBasis_isTy (n : Nat) : Basis.IsTyBasis (tallBasis n) :=
  (tallBasis_isSpace n).toIsTyBasis

/-- A variable node can select a basis larger than any proposed bound.  Thus
the edge `term progress(var) -> exact type/COB(stored basis)` is not a
decrease in `Term.size`, `Basis.size`, or their naive sum.  Its decrease is
the creation-prefix component supplied by raw history. -/
theorem variable_can_select_arbitrarily_large_basis (x : VName) (n : Nat) :
    exists b : Basis,
      Basis.BasisValid (∅ : NLCtx) b /\ Basis.IsTyBasis b /\
      Term.size (.var x) + n < Basis.size b := by
  refine ⟨tallBasis (n + 1), tallBasis_valid ∅ (n + 1),
    tallBasis_isTy (n + 1), ?_⟩
  simp only [Term.size, tallBasis_size]
  omega

/-- In the opposite direction, every direct projected-basis witness is a
strict syntactic subproblem.  This is the same-history component of the
required lexicographic measure. -/
theorem proj_ker_witness_size_lt
    (s0 s1 : Space) (e : Term) (b0 b1 : Basis) :
    Term.size e < Basis.size (.proj (.ker s0 s1 e) b0 b1) := by
  simp only [Basis.size, Space.size]
  omega

theorem proj_coker_witness_size_lt
    (s0 s1 : Space) (e : Term) (b0 b1 : Basis) :
    Term.size e < Basis.size (.proj (.coker s0 s1 e) b0 b1) := by
  simp only [Basis.size, Space.size]
  omega

theorem proj_img_witness_size_lt
    (s0 s1 : Space) (e : Term) (b0 b1 : Basis) :
    Term.size e < Basis.size (.proj (.img s0 s1 e) b0 b1) := by
  simp only [Basis.size, Space.size]
  omega

theorem proj_coimg_witness_size_lt
    (s0 s1 : Space) (e : Term) (b0 b1 : Basis) :
    Term.size e < Basis.size (.proj (.coimg s0 s1 e) b0 b1) := by
  simp only [Basis.size, Space.size]
  omega

theorem terms_member_size_lt
    (s : Space) (es : List Term) (b : Basis) {e : Term}
    (he : e ∈ es) :
    Term.size e < Basis.size (.terms s es b) := by
  have hmem : Term.size e ∈ es.map Term.size := List.mem_map.mpr ⟨e, he, rfl⟩
  have hle : Term.size e <= (es.map Term.size).sum :=
    List.le_sum_of_mem hmem
  simp only [Basis.size]
  omega

end RawCertifiedCobProgressMutualSpike
end GLang
