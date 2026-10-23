import GLang.Proofs.Progress.Certificates.Pairs.RawCertifiedPairContextSelected

/-!
# Hybrid evaluator futures for source and frame binders

An ordinary source binder does not immediately install a key in the current
evaluator.  Every later occurrence of that name is nevertheless required to
use its standard basis.  A dependent-frame callback is different: it installs
one literal, possibly nonstandard, endpoint key in the evaluator root.

`CheckedHybridFuture Psi0 Psi reserved` expresses exactly that mixture.  It
is a fresh arbitrary future, except that a name in `reserved` which was absent
from the root may only appear at the standard basis of its recorded type.
Names already owned by the root are unrestricted, so literal frame endpoints
remain available.  With an empty reservation context this is precisely
`CheckedFreshFuture`.

This module contains only the world algebra and fixed-depth selected package.
It changes no operational or typing rule and introduces no assumptions.
-/

namespace GLang
namespace RawCertifiedPairHybridFuture

open OperationalStrengthening
open RawCertifiedHereditaryStore
open RawCertifiedPairCertificate
open RawCertifiedConsistentPairStore
open RawCertifiedPairContextStandardSelf
open RawCertifiedPairContextSelected

/-- Fresh evaluator growth in which source-binder slots are standard-only.

The `x ∉ Psi0.names` guard is essential.  If a frame endpoint has already
installed a literal key for `x` in the root, the reservation does not rewrite
that endpoint to standard form. -/
structure CheckedHybridFuture
    (Psi0 Psi : EvalCtx) (reserved : NLCtx) : Prop where
  fresh : CheckedFreshFuture Psi0 Psi
  reserved_standard : forall {x : VName} {tau : Ty},
    reserved.lookup x = some tau -> x ∉ Psi0.names ->
    forall {b : Basis} {v : ValExpr},
      EvalCtx.lookup Psi (x, b) = some v -> Basis.tof b = tau ->
        b = Basis.std tau

/-- Reflexivity for every reservation context.  A reserved name absent from
the root has no root lookup to constrain. -/
theorem CheckedHybridFuture.refl (Psi : EvalCtx) (reserved : NLCtx) :
    CheckedHybridFuture Psi Psi reserved where
  fresh := CheckedFreshFuture.refl Psi
  reserved_standard := by
    intro x tau hreserved hx b v hlookup htof
    exact False.elim (hx (EvalCtx.mem_names_of_lookup hlookup))

/-- Forget the reservation policy. -/
theorem CheckedHybridFuture.toFresh
    {Psi0 Psi : EvalCtx} {reserved : NLCtx}
    (h : CheckedHybridFuture Psi0 Psi reserved) :
    CheckedFreshFuture Psi0 Psi :=
  h.fresh

/-- Empty reservations impose no additional condition. -/
theorem CheckedHybridFuture.ofFresh_empty
    {Psi0 Psi : EvalCtx} (h : CheckedFreshFuture Psi0 Psi) :
    CheckedHybridFuture Psi0 Psi (∅ : NLCtx) where
  fresh := h
  reserved_standard := by
    intro x tau hlookup
    simp only [Finmap.lookup_empty] at hlookup
    contradiction

/-- Standard-only growth respects every reservation context. -/
theorem CheckedHybridFuture.ofStandard
    {Psi0 Psi : EvalCtx} {reserved : NLCtx}
    (h : CheckedStdFuture Psi0 Psi) :
    CheckedHybridFuture Psi0 Psi reserved where
  fresh := RawCertifiedConsistentPairStore.CheckedStdFuture.toFresh h
  reserved_standard := by
    intro x tau hreserved hx b v hlookup htof
    rcases RawConsistentRank.CheckedStdFuture.lookup_root_or_standard
        h hlookup with hroot | hextra
    · exact False.elim (hx (EvalCtx.mem_names_of_lookup hroot))
    · exact hextra.2.1.trans (congrArg Basis.std htof)

/-- Hybrid futures with the same reservation policy compose. -/
theorem CheckedHybridFuture.trans
    {Psi0 Psi1 Psi2 : EvalCtx} {reserved : NLCtx}
    (h01 : CheckedHybridFuture Psi0 Psi1 reserved)
    (h12 : CheckedHybridFuture Psi1 Psi2 reserved) :
    CheckedHybridFuture Psi0 Psi2 reserved where
  fresh := h01.fresh.trans h12.fresh
  reserved_standard := by
    intro x tau hreserved hx0 b v hlookup htof
    by_cases hx1 : x ∈ Psi1.names
    · have hroot : EvalCtx.lookup Psi1 (x, b) = some v :=
        h12.fresh.lookup_root_of_root_name hx1 hlookup
      exact h01.reserved_standard hreserved hx0 hroot htof
    · exact h12.reserved_standard hreserved hx1 hlookup htof

/-- Adding reservation entries only restricts the admissible future worlds.
This contravariant map is used when an ordinary source binder is introduced.
-/
theorem CheckedHybridFuture.of_reserved_incl
    {Psi0 Psi : EvalCtx} {reserved0 reserved1 : NLCtx}
    (hinc : NLCtxIncl reserved0 reserved1)
    (h : CheckedHybridFuture Psi0 Psi reserved1) :
    CheckedHybridFuture Psi0 Psi reserved0 where
  fresh := h.fresh
  reserved_standard := by
    intro x tau hlookup hx b v hkey htof
    exact h.reserved_standard (hinc x tau hlookup) hx hkey htof

/-- Extend by one literal frame endpoint whose name is fresh and is not an
ordinary reserved slot. -/
theorem CheckedHybridFuture.extend
    {Psi0 Psi : EvalCtx} {reserved : NLCtx}
    (h : CheckedHybridFuture Psi0 Psi reserved)
    {y : VName} (hyPsi : y ∉ Psi.names) (hyReserved : y ∉ reserved)
    (bArg : Basis) (v : ValExpr) :
    CheckedHybridFuture Psi0 (Psi.extend y bArg v) reserved := by
  apply h.trans
  refine {
    fresh := (CheckedFreshFuture.refl Psi).extend hyPsi bArg v
    reserved_standard := ?_ }
  intro x tau hreserved hx b vX hlookup htof
  have hxy : x ≠ y := by
    intro hxy
    subst x
    exact hyReserved (Finmap.mem_of_lookup_eq_some hreserved)
  have hkey : (x, b) ≠ (y, bArg) := by
    intro heq
    exact hxy (Prod.mk.inj heq).1
  have hlookup0 : EvalCtx.lookup Psi (x, b) = some vX := by
    simpa only [EvalCtx.lookup, EvalCtx.extend,
      Finmap.lookup_insert_of_ne _ hkey] using hlookup
  exact False.elim (hx (EvalCtx.mem_names_of_lookup hlookup0))

/-- One fixed-depth selected package stable in hybrid worlds. -/
structure CheckedHybridSelectedAt
    (Psi : EvalCtx) (Gamma : NLCtx) (reserved : NLCtx)
    (depth : Nat) (b : Basis) : Prop where
  valid : Basis.BasisValid Gamma b
  quad : forall {Psi' : EvalCtx} {Gamma' : NLCtx},
    CheckedHybridFuture Psi Psi' reserved ->
    NLCtxIncl Gamma Gamma' ->
    V2.CtxWF' (∅ : LCtx) Gamma' ->
      CheckedPairDepthQuad Psi' depth Gamma' b

/-- Fresh-stable packages are hybrid-stable under any reservation policy. -/
theorem CheckedFreshSelectedAt.toHybrid
    {Psi : EvalCtx} {Gamma reserved : NLCtx} {depth : Nat} {b : Basis}
    (p : CheckedFreshSelectedAt Psi Gamma depth b) :
    CheckedHybridSelectedAt Psi Gamma reserved depth b where
  valid := p.valid
  quad hfuture hGamma hwf := p.quad hfuture.fresh hGamma hwf

/-- With no reservations, hybrid stability recovers full fresh stability. -/
theorem CheckedHybridSelectedAt.toFresh_empty
    {Psi : EvalCtx} {Gamma : NLCtx} {depth : Nat} {b : Basis}
    (p : CheckedHybridSelectedAt Psi Gamma (∅ : NLCtx) depth b) :
    CheckedFreshSelectedAt Psi Gamma depth b where
  valid := p.valid
  quad hfuture hGamma hwf :=
    p.quad (CheckedHybridFuture.ofFresh_empty hfuture) hGamma hwf

/-- Re-root a hybrid package through an admissible hybrid future. -/
theorem CheckedHybridSelectedAt.rebase
    {Psi Psi' : EvalCtx} {Gamma Gamma' reserved : NLCtx}
    {depth : Nat} {b : Basis}
    (p : CheckedHybridSelectedAt Psi Gamma reserved depth b)
    (hfuture : CheckedHybridFuture Psi Psi' reserved)
    (hGamma : NLCtxIncl Gamma Gamma') :
    CheckedHybridSelectedAt Psi' Gamma' reserved depth b where
  valid := raw_basisValid_mono p.valid hGamma
  quad hfuture' hGamma' hwf :=
    p.quad (hfuture.trans hfuture') (hGamma.trans hGamma') hwf

/-- Raise the selected-pair depth. -/
theorem CheckedHybridSelectedAt.monoDepth
    {Psi : EvalCtx} {Gamma reserved : NLCtx} {b : Basis} {n m : Nat}
    (hnm : n ≤ m)
    (p : CheckedHybridSelectedAt Psi Gamma reserved n b) :
    CheckedHybridSelectedAt Psi Gamma reserved m b where
  valid := p.valid
  quad hfuture hGamma hwf :=
    CheckedPairDepthQuad.monoDepth hnm (p.quad hfuture hGamma hwf)

/-- Strengthening the reservation policy preserves a package. -/
theorem CheckedHybridSelectedAt.strengthenReserved
    {Psi : EvalCtx} {Gamma reserved0 reserved1 : NLCtx}
    {depth : Nat} {b : Basis}
    (hinc : NLCtxIncl reserved0 reserved1)
    (p : CheckedHybridSelectedAt Psi Gamma reserved0 depth b) :
    CheckedHybridSelectedAt Psi Gamma reserved1 depth b where
  valid := p.valid
  quad hfuture hGamma hwf :=
    p.quad (hfuture.of_reserved_incl hinc) hGamma hwf

/-- Standardize all four orientations of an existing hybrid quad. -/
theorem CheckedHybridSelectedAt.toStandard
    {Psi : EvalCtx} {Gamma reserved : NLCtx} {depth : Nat} {b : Basis}
    (p : CheckedHybridSelectedAt Psi Gamma reserved depth b) :
    CheckedHybridSelectedAt Psi Gamma reserved depth
      (Basis.std (Basis.tof b)) := by
  obtain ⟨k, ⟨ht⟩⟩ := p.valid.tof_tvalid
  refine ⟨Basis.std_valid _ ht, ?_⟩
  intro Psi' Gamma' hfuture hGamma hwf
  have q := p.quad hfuture hGamma hwf
  refine { self := ?_, toStd := ?_, fromStd := ?_, stdSelf := ?_ }
  all_goals simpa only [Basis.tof_std] using q.stdSelf

end RawCertifiedPairHybridFuture
end GLang
