import GLang.Elaboration.Supporting.SourceBinderReconstruction
import GLang.Proofs.Source.SourceContextInductive

/-! Closing a valid basis at a fresh nonlinear declaration reconstructs a frame. -/
namespace GLang

/-- Valid bases have no dangling indices outside their frame binders. -/
theorem Basis.BasisValid.localClosed {E b} (h : Basis.BasisValid E b) : b.lc := by
  induction h with
  | empty => exact .empty
  | one => exact .one
  | dual hb ht ih => exact .dual ih
  | dsum ha hb ht hu iha ihb => exact .dsum iha ihb
  | tprod ha hb ht hu iha ihb => exact .tprod iha ihb
  | proj_ker ha hb ht hu he iha ihb =>
    exact .proj (Basis.BasisValid.proj_ker ha hb ht hu he).sof_valid.some.lc iha ihb
  | proj_coker ha hb ht hu he iha ihb =>
    exact .proj (Basis.BasisValid.proj_coker ha hb ht hu he).sof_valid.some.lc iha ihb
  | proj_img ha hb ht hu he iha ihb =>
    exact .proj (Basis.BasisValid.proj_img ha hb ht hu he).sof_valid.some.lc iha ihb
  | proj_coimg ha hb ht hu he iha ihb =>
    exact .proj (Basis.BasisValid.proj_coimg ha hb ht hu he).sof_valid.some.lc iha ihb
  | image hb hs he ih => exact .image ih
  | terms hb ht hs he hn ih => exact .terms hs.some.lc (fun e he' => (he e he').some.lc) ih
  | frame L ha hb iha ihb => exact .frame L iha ihb

/-- Every valid basis has a kinded type, including dependent frames. -/
noncomputable def Basis.BasisValid.typeValid {E b} (h : Basis.BasisValid E b) :
    Σ k, TValid E b.tof k := by
  exact ⟨_, h.tof_valid_structural.some⟩

theorem Basis.open_closeRec (b : Basis) (k : Nat) (x y : Name) :
    Basis.openRec k (.var y) (Basis.closeRec k x b) =
      Basis.subst x (.var y) (Basis.openRec k (.var y) b) := by
  induction b generalizing k with
  | terms s es b ih =>
    simp [Basis.closeRec, Basis.openRec, Basis.subst, Space.open_closeRec,
      Term.openRecList_eq_map, Term.closeRecList_eq_map,
      List.map_map, Term.open_closeRec, ih]
  | _ => simp_all [Basis.closeRec, Basis.openRec, Basis.subst, Space.open_closeRec]

theorem Basis.open_close_lc {b : Basis} (h : b.lc) (x y : Name) :
    Basis.openVar y (Basis.closeRec 0 x b) = Basis.subst x (.var y) b := by
  rw [Basis.openVar, Basis.open_closeRec, Basis.openRec_lc h]

theorem Basis.sof_closeRec (b : Basis) (k : Nat) (x : Name) :
    (Basis.closeRec k x b).sof = Space.closeRec k x b.sof := by
  induction b generalizing k with
  | image b ih =>
    simp only [Basis.closeRec, Basis.sof, ih]
    cases b.sof <;> rfl
  | _ => simp_all [Basis.closeRec, Basis.sof, Space.closeRec]

theorem Basis.tof_closeRec (b : Basis) (k : Nat) (x : Name) :
    (Basis.closeRec k x b).tof = Ty.closeRec k x b.tof := by
  induction b generalizing k with
  | frame a b iha ihb => simp [Basis.closeRec,Basis.tof,Ty.closeRec,iha,ihb]
  | _ => simp_all [Basis.closeRec,Basis.tof,Ty.closeRec,← Basis.sof_closeRec,Space.closeRec]

open RawCertifiedOperational.RenameProof

/-- A single fresh valid basis body reconstructs a cofinite valid frame. -/
theorem Basis.BasisValid.close_frame {E A B x}
    (hw : Metatheory.SourceContextWF ∅ E) (ha : Basis.BasisValid E A)
    (hx : x ∉ E) (hb : Basis.BasisValid (Finmap.insert x A.tof E) B) :
    Basis.BasisValid E (.frame A (Basis.closeRec 0 x B)) := by
  obtain ⟨ka,hta⟩ := ha.typeValid
  refine .frame (E.keys ∪ {x}) ha ?_
  · intro y hy
    simp only [Finset.mem_union,Finset.mem_singleton,not_or] at hy
    have hyE : y ∉ E := fun h => hy.1 (Finmap.mem_keys.mpr h)
    have hren := basisValid_rename (Ne.symm hy.2)
      (show y ∉ Finmap.insert x A.tof E from by simp [hy.2,hyE]) hb
    have hxA : x ∉ A.tof.fv := fun h => hx (Finmap.mem_keys.mp (hta.fv_closure h))
    have hfr : NLCtxFresh x E := fun z t ht hm => hx (hw.scoping.nl_fv_in_ε z t ht x hm)
    rw [renameNLCtx_insert,Equiv.swap_apply_left,Ty.subst_fresh x (.var y) A.tof hxA,
      renameNLCtx_eq_self hx hyE hfr] at hren
    simpa only [Basis.open_close_lc hb.localClosed] using hren

end GLang
