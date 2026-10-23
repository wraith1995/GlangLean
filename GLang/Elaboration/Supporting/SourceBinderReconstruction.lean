import GLang.Elaboration.Supporting.SurfaceClosing
import GLang.Proofs.Progress.Certificates.RawCertifiedRenameProof

/-! Reconstruct a cofinite binder from one fresh, typed internal instance. -/
namespace GLang

mutual
  theorem Space.open_closeRec (a : Space) (k : Nat) (x y : Name) :
      Space.openRec k (.var y) (Space.closeRec k x a) =
        Space.subst x (.var y) (Space.openRec k (.var y) a) := by
    cases a <;> simp only [Space.closeRec, Space.openRec, Space.subst,
      Space.open_closeRec, Term.open_closeRec]
  theorem Ty.open_closeRec (a : Ty) (k : Nat) (x y : Name) :
      Ty.openRec k (.var y) (Ty.closeRec k x a) =
        Ty.subst x (.var y) (Ty.openRec k (.var y) a) := by
    cases a <;> simp only [Ty.closeRec, Ty.openRec, Ty.subst,
      Space.open_closeRec, Ty.open_closeRec]
  theorem Term.open_closeRec (a : Term) (k : Nat) (x y : Name) :
      Term.openRec k (.var y) (Term.closeRec k x a) =
        Term.subst x (.var y) (Term.openRec k (.var y) a) := by
    cases a <;> simp only [Term.closeRec, Term.openRec, Term.subst,
      Space.open_closeRec, Ty.open_closeRec, Term.open_closeRec]
    · split <;> simp [Term.subst]
    · rename_i z
      by_cases h : z = x
      · subst z; simp [Term.openRec]
      · simp [h, Ne.symm h, Term.openRec]
end

/-- Reopening the closure of a locally closed type is a name substitution. -/
theorem Ty.open_close_lc {a : Ty} (h : a.lc) (x y : Name) :
    Ty.openVar y (Ty.closeRec 0 x a) = Ty.subst x (.var y) a := by
  rw [Ty.openVar, Ty.open_closeRec, Ty.openRec_lc h]

/-- Reopening the closure of a locally closed term is a name substitution. -/
theorem Term.open_close_lc {a : Term} (h : a.lc) (x y : Name) :
    Term.openVar y (Term.closeRec 0 x a) = Term.subst x (.var y) a := by
  rw [Term.openVar, Term.open_closeRec, Term.openRec_lc h]

open RawCertifiedOperational.RenameProof

private theorem ctx_fresh_nl {Δ ε x} (h : CtxWF Δ ε) (hx : x ∉ ε) :
    NLCtxFresh x ε :=
  fun z t ht hxt => hx (h.nl_fv_in_ε z t ht x hxt)

private theorem ctx_fresh_lin {Δ ε x} (h : CtxWF Δ ε) (hx : x ∉ ε) :
    LCtxFresh x Δ :=
  fun z s hs hxs => hx (h.lin_fv_in_ε z s hs x hxs)

/-- A single fresh kinded codomain suffices to build a dependent function type.
The reconstructed body is the closure of that codomain, not a separate choice
for each fresh variable. -/
noncomputable def TValid.close_pi {Δ ε a b ka kb x}
    (hctx : CtxWF Δ ε) (ha : TValid ε a ka) (hx : x ∉ ε)
    (hb : TValid (Finmap.insert x a ε) b kb) :
    TValid ε (.piTy a (Ty.closeRec 0 x b)) (.arrow ka kb) := by
  refine .piTy (ε.keys ∪ {x}) ha ?_
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  have hyε : y ∉ ε := fun h => hy.1 (Finmap.mem_keys.mpr h)
  have hxy : x ≠ y := Ne.symm hy.2
  have hren := tvalid_rename hxy
    (show y ∉ Finmap.insert x a ε from by simp [hy.2, hyε]) hb
  have hxA : x ∉ a.fv := fun h => hx (Finmap.mem_keys.mp (ha.fv_closure h))
  rw [renameNLCtx_insert, Equiv.swap_apply_left,
    Ty.subst_fresh x (.var y) a hxA,
    renameNLCtx_eq_self hx hyε (ctx_fresh_nl hctx hx)] at hren
  simpa only [Ty.open_close_lc hb.lc] using hren

/-- Reconstruct all fresh nonlinear openings of one typed term and result type. -/
noncomputable def HasType.close_nonlinear_body {Δ ε a b e ka x}
    (hctx : CtxWF Δ ε) (ha : TValid ε a ka) (hx : x ∉ ε)
    (hb : HasType ∅ (Finmap.insert x a ε) e b) (hblc : b.lc) :
    ∀ y, y ∉ ε.keys ∪ {x} →
      HasType ∅ (Finmap.insert y a ε)
        (Term.openVar y (Term.closeRec 0 x e))
        (Ty.openVar y (Ty.closeRec 0 x b)) := by
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  have hyε : y ∉ ε := fun h => hy.1 (Finmap.mem_keys.mpr h)
  have hren := hasType_rename (Ne.symm hy.2) Finmap.notMem_empty
    (show y ∉ Finmap.insert x a ε from by simp [hy.2, hyε])
    (Graded.CtxDisj.empty _) hb
  have hxA : x ∉ a.fv := fun h => hx (Finmap.mem_keys.mp (ha.fv_closure h))
  rw [renameLCtx_empty, renameNLCtx_insert, Equiv.swap_apply_left,
    Ty.subst_fresh x (.var y) a hxA,
    renameNLCtx_eq_self hx hyε (ctx_fresh_nl hctx hx)] at hren
  -- Result-type local closure is supplied separately by the binder's kinding
  -- premise; term typing alone permits unformed context entries.
  rw [Term.open_close_lc hb.lc, Ty.open_close_lc hblc]
  exact hren

/-- All fresh linear openings of the closure of a single typed instance. -/
noncomputable def HasType.close_linear_body {Δ ε a b e x}
    (hctx : CtxWF Δ ε) (ha : SValid ε a) (hb : SValid ε b)
    (hxΔ : x ∉ Δ) (hxε : x ∉ ε)
    (he : HasType (Finmap.insert x a Δ) ε e (.space b)) :
    ∀ y, y ∉ Δ.keys ∪ ε.keys ∪ {x} →
      HasType (Finmap.insert y a Δ) ε
        (Term.openVar y (Term.closeRec 0 x e)) (.space b) := by
  intro y hy
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hy
  have hyΔ : y ∉ Δ := fun h => hy.1.1 (Finmap.mem_keys.mpr h)
  have hyε : y ∉ ε := fun h => hy.1.2 (Finmap.mem_keys.mpr h)
  have hren := hasType_rename (Ne.symm hy.2)
    (show y ∉ Finmap.insert x a Δ from by simp [hy.2, hyΔ]) hyε
    (Graded.CtxDisj.insert' hctx.disjoint hxε) he
  have hxA : x ∉ a.fv := fun h => hxε (Finmap.mem_keys.mp (ha.fv_closure h))
  have hxB : x ∉ b.fv := fun h => hxε (Finmap.mem_keys.mp (hb.fv_closure h))
  rw [renameLCtx_insert, Equiv.swap_apply_left,
    Space.subst_fresh x (.var y) a hxA,
    renameLCtx_eq_self hxΔ hyΔ (ctx_fresh_lin hctx hxε),
    renameNLCtx_eq_self hxε hyε (ctx_fresh_nl hctx hxε),
    Ty.subst, Space.subst_fresh x (.var y) b hxB] at hren
  simpa only [Term.open_close_lc he.lc] using hren

/-- Build a nonlinear lambda from one fresh typed body and its kinded type. -/
noncomputable def HasType.close_nllam {Δ ε a b e ka kb x}
    (hctx : CtxWF Δ ε) (ha : TValid ε a ka) (hx : x ∉ ε)
    (hb : TValid (Finmap.insert x a ε) b kb)
    (he : HasType ∅ (Finmap.insert x a ε) e b) :
    HasType ∅ ε (.nllam a (Term.closeRec 0 x e))
      (.piTy a (Ty.closeRec 0 x b)) :=
  .nllam (ε.keys ∪ {x}) (TValid.close_pi hctx ha hx hb)
    (HasType.close_nonlinear_body hctx ha hx he hb.lc)

/-- Build a scalar-valued linear lambda from one fresh typed body. -/
noncomputable def HasType.close_llam_real {Δ ε a e x}
    (hctx : CtxWF Δ ε) (ha : SValid ε a) (hxΔ : x ∉ Δ) (hxε : x ∉ ε)
    (he : HasType (Finmap.insert x a Δ) ε e (.space .real)) :
    HasType Δ ε (.llam a .real (Term.closeRec 0 x e)) (.space (.dual a)) :=
  .llam_real (Δ.keys ∪ ε.keys ∪ {x}) ha
    (HasType.close_linear_body hctx ha .real hxΔ hxε he)

/-- Build a non-scalar linear lambda from one fresh typed body. -/
noncomputable def HasType.close_llam_tensor {Δ ε a b e x}
    (hctx : CtxWF Δ ε) (ha : SValid ε a) (hb : SValid ε b) (hne : b ≠ .real)
    (hxΔ : x ∉ Δ) (hxε : x ∉ ε)
    (he : HasType (Finmap.insert x a Δ) ε e (.space b)) :
    HasType Δ ε (.llam a b (Term.closeRec 0 x e)) (.space (.tprod (.dual a) b)) :=
  .llam_tensor (Δ.keys ∪ ε.keys ∪ {x}) hne ha hb
    (HasType.close_linear_body hctx ha hb hxΔ hxε he)

end GLang
