import GLang.Proofs.Progress.Certificates.RawCertifiedRename
import GLang.Graded.BridgeBwd
import GLang.Graded.Subst

/-!
# Constructive checked renaming

This module is intentionally separate from `RawCertifiedRename`: it develops
the source-context alpha transport needed to inhabit `CheckedRenameLaws`.
-/

namespace GLang
namespace RawCertifiedOperational

open Basis (BasisValid)

namespace RenameProof

/-- Reindex a constant-family `Finmap` by the transposition `x <-> y`, while
mapping every stored payload. -/
noncomputable def mapCtx {A B : Type} (x y : Name) (f : A -> B)
    (m : Finmap (fun _ : Name => A)) : Finmap (fun _ : Name => B) :=
  Finmap.keysLookupEquiv.symm
    ⟨(m.keys.image (Equiv.swap x y),
      fun z => (m.lookup (Equiv.swap x y z)).map f), by
        intro z
        simp only [Option.isSome_map, Finset.mem_image]
        constructor
        · intro hz
          refine ⟨Equiv.swap x y z, ?_, ?_⟩
          · simpa only [Finmap.lookup_isSome] using hz
          · exact Equiv.swap_apply_self x y z
        · rintro ⟨w, hw, hwz⟩
          have : w = Equiv.swap x y z := by
            rw [<- hwz, Equiv.swap_apply_self]
          subst w
          simpa only [Finmap.lookup_isSome] using hw⟩

@[simp] theorem mapCtx_lookup {A B : Type} (x y : Name) (f : A -> B)
    (m : Finmap (fun _ : Name => A)) (z : Name) :
    (mapCtx x y f m).lookup z = (m.lookup (Equiv.swap x y z)).map f := by
  let p : { q : Finset Name × (∀ _ : Name, Option B) //
      ∀ i, (q.2 i).isSome ↔ i ∈ q.1 } :=
    ⟨(m.keys.image (Equiv.swap x y),
      fun w => (m.lookup (Equiv.swap x y w)).map f), by
        intro w
        simp only [Option.isSome_map, Finset.mem_image]
        constructor
        · intro hw
          refine ⟨Equiv.swap x y w, ?_, Equiv.swap_apply_self x y w⟩
          simpa only [Finmap.lookup_isSome] using hw
        · rintro ⟨u, hu, huw⟩
          have : u = Equiv.swap x y w := by
            rw [<- huw, Equiv.swap_apply_self]
          subst u
          simpa only [Finmap.lookup_isSome] using hu⟩
  have h := congrArg (fun q => q.val.2 z)
    (Finmap.keysLookupEquiv.apply_symm_apply p)
  exact h

noncomputable def renameLCtx (x y : Name) (Delta : LCtx) : LCtx :=
  mapCtx x y (Space.subst x (.var y)) Delta

noncomputable def renameNLCtx (x y : Name) (Gamma : NLCtx) : NLCtx :=
  mapCtx x y (Ty.subst x (.var y)) Gamma

@[simp] theorem renameLCtx_lookup (x y z : Name) (Delta : LCtx) :
    (renameLCtx x y Delta).lookup z =
      (Delta.lookup (Equiv.swap x y z)).map (Space.subst x (.var y)) :=
  mapCtx_lookup x y _ Delta z

@[simp] theorem renameNLCtx_lookup (x y z : Name) (Gamma : NLCtx) :
    (renameNLCtx x y Gamma).lookup z =
      (Gamma.lookup (Equiv.swap x y z)).map (Ty.subst x (.var y)) :=
  mapCtx_lookup x y _ Gamma z

@[simp] theorem renameLCtx_empty (x y : Name) :
    renameLCtx x y (∅ : LCtx) = ∅ := by
  apply Finmap.ext_lookup
  intro z
  simp

@[simp] theorem renameNLCtx_empty (x y : Name) :
    renameNLCtx x y (∅ : NLCtx) = ∅ := by
  apply Finmap.ext_lookup
  intro z
  simp

@[simp] theorem renameLCtx_insert (x y z : Name) (s : Space) (Delta : LCtx) :
    renameLCtx x y (Finmap.insert z s Delta) =
      Finmap.insert (Equiv.swap x y z) (Space.subst x (.var y) s)
        (renameLCtx x y Delta) := by
  apply Finmap.ext_lookup
  intro w
  by_cases hw : w = Equiv.swap x y z
  · subst w
    rw [renameLCtx_lookup, Equiv.swap_apply_self, Finmap.lookup_insert,
      Finmap.lookup_insert]
    rfl
  · have hsw : Equiv.swap x y w ≠ z := by
      intro h
      apply hw
      rw [← h, Equiv.swap_apply_self]
    simp [hw, hsw]

@[simp] theorem renameNLCtx_insert (x y z : Name) (tau : Ty) (Gamma : NLCtx) :
    renameNLCtx x y (Finmap.insert z tau Gamma) =
      Finmap.insert (Equiv.swap x y z) (Ty.subst x (.var y) tau)
        (renameNLCtx x y Gamma) := by
  apply Finmap.ext_lookup
  intro w
  by_cases hw : w = Equiv.swap x y z
  · subst w
    rw [renameNLCtx_lookup, Equiv.swap_apply_self, Finmap.lookup_insert,
      Finmap.lookup_insert]
    rfl
  · have hsw : Equiv.swap x y w ≠ z := by
      intro h
      apply hw
      rw [← h, Equiv.swap_apply_self]
    simp [hw, hsw]

@[simp] theorem renameLCtx_singleton (x y z : Name) (s : Space) :
    renameLCtx x y (Finmap.singleton z s) =
      Finmap.singleton (Equiv.swap x y z) (Space.subst x (.var y) s) := by
  apply Finmap.ext_lookup
  intro w
  by_cases hw : w = Equiv.swap x y z
  · subst w
    rw [renameLCtx_lookup, Equiv.swap_apply_self]
    simp
  · have hsw : Equiv.swap x y w ≠ z := by
      intro h
      apply hw
      rw [← h, Equiv.swap_apply_self]
    rw [renameLCtx_lookup,
      Finmap.lookup_eq_none.mpr (by simpa [Finmap.mem_singleton] using hsw),
      Finmap.lookup_eq_none.mpr (by simpa [Finmap.mem_singleton] using hw)]
    rfl

@[simp] theorem renameLCtx_union (x y : Name) (Delta0 Delta1 : LCtx) :
    renameLCtx x y (Delta0 ∪ Delta1) =
      renameLCtx x y Delta0 ∪ renameLCtx x y Delta1 := by
  apply Finmap.ext_lookup
  intro z
  by_cases hz : Equiv.swap x y z ∈ Delta0
  · have hz' : z ∈ renameLCtx x y Delta0 := by
      rw [Finmap.mem_iff]
      obtain ⟨s, hs⟩ := Finmap.mem_iff.mp hz
      rw [renameLCtx_lookup, hs]
      exact ⟨_, rfl⟩
    rw [renameLCtx_lookup, Finmap.lookup_union_left hz,
      Finmap.lookup_union_left hz', renameLCtx_lookup]
  · have hz' : z ∉ renameLCtx x y Delta0 := by
      intro hm
      rw [Finmap.mem_iff] at hm
      obtain ⟨s, hs⟩ := hm
      rw [renameLCtx_lookup] at hs
      cases hraw : Delta0.lookup (Equiv.swap x y z) with
      | none => rw [hraw] at hs; contradiction
      | some a => exact hz (Finmap.mem_of_lookup_eq_some hraw)
    rw [renameLCtx_lookup, Finmap.lookup_union_right hz,
      Finmap.lookup_union_right hz', renameLCtx_lookup]

@[simp] theorem renameNLCtx_union (x y : Name) (Gamma0 Gamma1 : NLCtx) :
    renameNLCtx x y (Gamma0 ∪ Gamma1) =
      renameNLCtx x y Gamma0 ∪ renameNLCtx x y Gamma1 := by
  apply Finmap.ext_lookup
  intro z
  by_cases hz : Equiv.swap x y z ∈ Gamma0
  · have hz' : z ∈ renameNLCtx x y Gamma0 := by
      rw [Finmap.mem_iff]
      obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp hz
      rw [renameNLCtx_lookup, htau]
      exact ⟨_, rfl⟩
    rw [renameNLCtx_lookup, Finmap.lookup_union_left hz,
      Finmap.lookup_union_left hz', renameNLCtx_lookup]
  · have hz' : z ∉ renameNLCtx x y Gamma0 := by
      intro hm
      rw [Finmap.mem_iff] at hm
      obtain ⟨tau, htau⟩ := hm
      rw [renameNLCtx_lookup] at htau
      cases hraw : Gamma0.lookup (Equiv.swap x y z) with
      | none => rw [hraw] at htau; contradiction
      | some a => exact hz (Finmap.mem_of_lookup_eq_some hraw)
    rw [renameNLCtx_lookup, Finmap.lookup_union_right hz,
      Finmap.lookup_union_right hz', renameNLCtx_lookup]

@[simp] theorem renameLCtx_toNL (x y : Name) (Delta : LCtx) :
    renameNLCtx x y Delta.toNL = (renameLCtx x y Delta).toNL := by
  apply Finmap.ext_lookup
  intro z
  rw [renameNLCtx_lookup]
  cases h : Delta.lookup (Equiv.swap x y z) with
  | none =>
      have hn : (renameLCtx x y Delta).lookup z = none := by simp [h]
      have hn' : z ∉ renameLCtx x y Delta := Finmap.lookup_eq_none.mp hn
      have hsrc : Delta.toNL.lookup (Equiv.swap x y z) = none :=
        Finmap.lookup_eq_none.mpr
          (fun hm => (Finmap.lookup_eq_none.mp h) ((LCtx.mem_toNL_iff _ _).mp hm))
      rw [hsrc, Finmap.lookup_eq_none.mpr
        (fun hm => hn' ((LCtx.mem_toNL_iff _ _).mp hm))]
      rfl
  | some s =>
      rw [LCtx.toNL_lookup Delta _ _ h]
      have hr : (renameLCtx x y Delta).lookup z =
          some (Space.subst x (.var y) s) := by simp [h]
      rw [LCtx.toNL_lookup _ _ _ hr]
      rfl

theorem renameLCtx_disjoint {x y : Name} {Delta0 Delta1 : LCtx}
    (h : Finmap.Disjoint Delta0 Delta1) :
    Finmap.Disjoint (renameLCtx x y Delta0) (renameLCtx x y Delta1) := by
  intro z hz0 hz1
  rw [Finmap.mem_iff] at hz0 hz1
  obtain ⟨s0, hs0⟩ := hz0
  obtain ⟨s1, hs1⟩ := hz1
  rw [renameLCtx_lookup] at hs0 hs1
  cases h0 : Delta0.lookup (Equiv.swap x y z) with
  | none => rw [h0] at hs0; contradiction
  | some a =>
      cases h1 : Delta1.lookup (Equiv.swap x y z) with
      | none => rw [h1] at hs1; contradiction
      | some b =>
          exact h (Equiv.swap x y z)
            (Finmap.mem_of_lookup_eq_some h0)
            (Finmap.mem_of_lookup_eq_some h1)

theorem renameNLCtx_disjoint {x y : Name} {Gamma0 Gamma1 : NLCtx}
    (h : Finmap.Disjoint Gamma0 Gamma1) :
    Finmap.Disjoint (renameNLCtx x y Gamma0) (renameNLCtx x y Gamma1) := by
  intro z hz0 hz1
  rw [Finmap.mem_iff] at hz0 hz1
  obtain ⟨tau0, h0'⟩ := hz0
  obtain ⟨tau1, h1'⟩ := hz1
  rw [renameNLCtx_lookup] at h0' h1'
  cases h0 : Gamma0.lookup (Equiv.swap x y z) with
  | none => rw [h0] at h0'; contradiction
  | some a =>
      cases h1 : Gamma1.lookup (Equiv.swap x y z) with
      | none => rw [h1] at h1'; contradiction
      | some b =>
          exact h (Equiv.swap x y z)
            (Finmap.mem_of_lookup_eq_some h0)
            (Finmap.mem_of_lookup_eq_some h1)

theorem renameLCtx_notMem {x y z : Name} {Delta : LCtx}
    (h : Equiv.swap x y z ∉ Delta) : z ∉ renameLCtx x y Delta := by
  intro hz
  rw [Finmap.mem_iff] at hz
  obtain ⟨s, hs⟩ := hz
  rw [renameLCtx_lookup] at hs
  cases hraw : Delta.lookup (Equiv.swap x y z) with
  | none => rw [hraw] at hs; contradiction
  | some a => exact h (Finmap.mem_of_lookup_eq_some hraw)

theorem renameNLCtx_notMem {x y z : Name} {Gamma : NLCtx}
    (h : Equiv.swap x y z ∉ Gamma) : z ∉ renameNLCtx x y Gamma := by
  intro hz
  rw [Finmap.mem_iff] at hz
  obtain ⟨tau, htau⟩ := hz
  rw [renameNLCtx_lookup] at htau
  cases hraw : Gamma.lookup (Equiv.swap x y z) with
  | none => rw [hraw] at htau; contradiction
  | some a => exact h (Finmap.mem_of_lookup_eq_some hraw)

/-! ## Graded source alpha-renaming

The graded source system has no promotion rule, so alpha-renaming is a
straight equivariance proof.  We use the same transposition as `mapCtx` and
rewrite the types stored in each entry.  At the checked boundary the target
name is fresh, making this permutation exactly the desired one-way
substitution `x := y`.
-/

noncomputable def renameTCtx (x y : Name) (f : Name → Option Ty) :
    Name → Option Ty :=
  fun z => (f (Equiv.swap x y z)).map (Ty.subst x (.var y))

noncomputable def renameGCtx (x y : Name) (G : Graded.GCtx) : Graded.GCtx :=
  fun z => (G (Equiv.swap x y z)).map
    (fun p => (p.1, Ty.subst x (.var y) p.2))

@[simp] theorem renameTCtx_apply (x y z : Name) (f : Name → Option Ty) :
    renameTCtx x y f z =
      (f (Equiv.swap x y z)).map (Ty.subst x (.var y)) := rfl

@[simp] theorem renameGCtx_apply (x y z : Name) (G : Graded.GCtx) :
    renameGCtx x y G z =
      (G (Equiv.swap x y z)).map
        (fun p => (p.1, Ty.subst x (.var y) p.2)) := rfl

theorem renameTCtx_update {x y z : Name} {f : Name → Option Ty}
    {tau : Ty} (hzx : z ≠ x) (hzy : z ≠ y) :
    renameTCtx x y (Function.update f z (some tau)) =
      Function.update (renameTCtx x y f) z
        (some (Ty.subst x (.var y) tau)) := by
  funext w
  rcases eq_or_ne w z with rfl | hwz
  · simp only [renameTCtx_apply]
    have hswap : Equiv.swap x y w = w := Equiv.swap_apply_of_ne_of_ne hzx hzy
    rw [hswap, Function.update_self]
    simp only [Function.update_self]
    rfl
  · rw [Function.update_of_ne hwz]
    simp only [renameTCtx_apply]
    have hswap : Equiv.swap x y w ≠ z := by
      intro h
      apply hwz
      calc
        w = Equiv.swap x y (Equiv.swap x y w) :=
          (Equiv.swap_apply_self x y w).symm
        _ = Equiv.swap x y z := congrArg (Equiv.swap x y) h
        _ = z := Equiv.swap_apply_of_ne_of_ne hzx hzy
    rw [Function.update_of_ne hswap]

theorem renameGCtx_update {x y z : Name} {G : Graded.GCtx}
    {v : Option (Graded.GGrade × Ty)} (hzx : z ≠ x) (hzy : z ≠ y) :
    renameGCtx x y (Function.update G z v) =
      Function.update (renameGCtx x y G) z
        (v.map (fun p => (p.1, Ty.subst x (.var y) p.2))) := by
  funext w
  rcases eq_or_ne w z with rfl | hwz
  · simp only [renameGCtx_apply]
    have hswap : Equiv.swap x y w = w := Equiv.swap_apply_of_ne_of_ne hzx hzy
    rw [hswap, Function.update_self]
    simp only [Function.update_self]
  · rw [Function.update_of_ne hwz]
    simp only [renameGCtx_apply]
    have hswap : Equiv.swap x y w ≠ z := by
      intro h
      apply hwz
      calc
        w = Equiv.swap x y (Equiv.swap x y w) :=
          (Equiv.swap_apply_self x y w).symm
        _ = Equiv.swap x y z := congrArg (Equiv.swap x y) h
        _ = z := Equiv.swap_apply_of_ne_of_ne hzx hzy
    rw [Function.update_of_ne hswap]

theorem renameGCtx_gadd (x y : Name) (G0 G1 : Graded.GCtx) :
    ∀ z, renameGCtx x y (fun w => Graded.gadd (G0 w) (G1 w)) z =
      Graded.gadd (renameGCtx x y G0 z) (renameGCtx x y G1 z) := by
  intro z
  simp only [renameGCtx_apply]
  cases G0 (Equiv.swap x y z) with
  | none => cases G1 (Equiv.swap x y z) <;> rfl
  | some p =>
      obtain ⟨g0, tau0⟩ := p
      cases G1 (Equiv.swap x y z) with
      | none => rfl
      | some p => obtain ⟨g1, tau1⟩ := p; rfl

theorem renameGCtx_split {x y : Name} {G G0 G1 : Graded.GCtx}
    (h : ∀ z, G z = Graded.gadd (G0 z) (G1 z)) :
    ∀ z, renameGCtx x y G z =
      Graded.gadd (renameGCtx x y G0 z) (renameGCtx x y G1 z) := by
  intro z
  simp only [renameGCtx_apply, h]
  cases G0 (Equiv.swap x y z) with
  | none => cases G1 (Equiv.swap x y z) <;> rfl
  | some p =>
      obtain ⟨g0, tau0⟩ := p
      cases G1 (Equiv.swap x y z) with
      | none => rfl
      | some p => obtain ⟨g1, tau1⟩ := p; rfl

theorem rename_typeCtxOmega (x y : Name) (G : Graded.GCtx) :
    renameTCtx x y (Graded.typeCtxOmega G) =
      Graded.typeCtxOmega (renameGCtx x y G) := by
  funext z
  simp only [renameTCtx_apply, renameGCtx_apply, Graded.typeCtxOmega]
  cases G (Equiv.swap x y z) with
  | none => rfl
  | some p => obtain ⟨g, tau⟩ := p; cases g <;> rfl

theorem rename_resurrect (x y : Name) (f : Name → Option Ty) :
    renameGCtx x y (Graded.resurrect f) =
      Graded.resurrect (renameTCtx x y f) := by
  funext z
  simp only [renameGCtx_apply, renameTCtx_apply, Graded.resurrect]
  cases f (Equiv.swap x y z) <;> rfl

theorem Graded.TypeAgree.rename {x y : Name} {G0 G1 : Graded.GCtx}
    (h : Graded.TypeAgree G0 G1) :
    Graded.TypeAgree (renameGCtx x y G0) (renameGCtx x y G1) := by
  intro z g0 tau0 g1 tau1 h0 h1
  simp only [renameGCtx_apply] at h0 h1
  cases hg0 : G0 (Equiv.swap x y z) with
  | none => rw [hg0] at h0; contradiction
  | some p0 =>
      obtain ⟨g0', tau0'⟩ := p0
      cases hg1 : G1 (Equiv.swap x y z) with
      | none => rw [hg1] at h1; contradiction
      | some p1 =>
          obtain ⟨g1', tau1'⟩ := p1
          rw [hg0] at h0
          rw [hg1] at h1
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h0 h1
          rw [← h0.2, ← h1.2,
            h (Equiv.swap x y z) g0' tau0' g1' tau1' hg0 hg1]

theorem Graded.NoLin.rename {x y : Name} {G : Graded.GCtx}
    (h : Graded.NoLin G) : Graded.NoLin (renameGCtx x y G) := by
  intro z tau hz
  simp only [renameGCtx_apply] at hz
  cases hg : G (Equiv.swap x y z) with
  | none => rw [hg] at hz; contradiction
  | some p =>
      obtain ⟨g, tau'⟩ := p
      rw [hg] at hz
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hz
      exact h (Equiv.swap x y z) tau' (by simpa [hz.1] using hg)

theorem Graded.gadd_eq_none_iff {a b : Option (Graded.GGrade × Ty)} :
    Graded.gadd a b = none ↔ a = none ∧ b = none := by
  cases a <;> cases b <;> simp [Graded.gadd]

theorem renameGCtx_none_at_y {x y : Name} {G : Graded.GCtx}
    (hx : G x = none) : renameGCtx x y G y = none := by
  simp [renameGCtx_apply, hx]

theorem renameTCtx_none_at_y {x y : Name} {f : Name → Option Ty}
    (hx : f x = none) : renameTCtx x y f y = none := by
  simp [renameTCtx_apply, hx]

set_option maxHeartbeats 1600000 in
mutual

noncomputable def gsvalid_rename {x y : Name} (hxy : x ≠ y) :
    {f : Name → Option Ty} → {s : Space} → f y = none →
      Graded.GSValid f s →
      Graded.GSValid (renameTCtx x y f) (Space.subst x (.var y) s)
  | _, _, _, .empty => .empty
  | _, _, _, .real => .real
  | _, _, hy, .dual h => .dual (gsvalid_rename hxy hy h)
  | _, _, hy, .dsum h0 h1 =>
      .dsum (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1)
  | _, _, hy, .tprod h0 h1 =>
      .tprod (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1)
  | f, _, hy, .ker h0 h1 he => by
      refine .ker (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1) ?_
      have hye : Graded.resurrect f y = none := by simp [Graded.resurrect, hy]
      have hr := ghastype_rename hxy hye he
      rw [rename_resurrect] at hr
      simpa only [Ty.subst, Space.subst] using hr
  | f, _, hy, .coker h0 h1 he => by
      refine .coker (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1) ?_
      have hye : Graded.resurrect f y = none := by simp [Graded.resurrect, hy]
      have hr := ghastype_rename hxy hye he
      rw [rename_resurrect] at hr
      simpa only [Ty.subst, Space.subst] using hr
  | f, _, hy, .img h0 h1 he => by
      refine .img (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1) ?_
      have hye : Graded.resurrect f y = none := by simp [Graded.resurrect, hy]
      have hr := ghastype_rename hxy hye he
      rw [rename_resurrect] at hr
      simpa only [Ty.subst, Space.subst] using hr
  | f, _, hy, .coimg h0 h1 he => by
      refine .coimg (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1) ?_
      have hye : Graded.resurrect f y = none := by simp [Graded.resurrect, hy]
      have hr := ghastype_rename hxy hye he
      rw [rename_resurrect] at hr
      simpa only [Ty.subst, Space.subst] using hr

noncomputable def gtvalid_rename {x y : Name} (hxy : x ≠ y) :
    {f : Name → Option Ty} → {tau : Ty} → {k : Kind} → f y = none →
      Graded.GTValid f tau k →
      Graded.GTValid (renameTCtx x y f) (Ty.subst x (.var y) tau) k
  | _, _, _, hy, .space hs => .space (gsvalid_rename hxy hy hs)
  | f, _, _, hy, @Graded.GTValid.piTy _ tau0 tau1 k0 k1 L h0 hcod => by
      refine Graded.GTValid.piTy (L ∪ {x, y})
        (gtvalid_rename hxy hy h0) ?_
      intro z hz
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hz
      obtain ⟨hzL, hzx, hzy⟩ := hz
      have hy' : Function.update f z (some tau0) y = none := by
        rw [Function.update_of_ne (Ne.symm hzy), hy]
      have hr := gtvalid_rename hxy hy' (hcod z hzL)
      rw [renameTCtx_update hzx hzy,
        Graded.Ty.subst_openVar_ne Term.lc.var hzx] at hr
      simpa only [Option.map_some] using hr

noncomputable def gsubtype_rename {x y : Name} (hxy : x ≠ y) :
    {f : Name → Option Ty} → {s0 s1 : Space} → f y = none →
      Graded.GSubType f s0 s1 →
      Graded.GSubType (renameTCtx x y f)
        (Space.subst x (.var y) s0) (Space.subst x (.var y) s1)
  | f, _, _, hy, @Graded.GSubType.sub_ker _ e s0 s1 h0 h1 he => by
      refine .sub_ker (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1) ?_
      have hye : Graded.resurrect f y = none := by simp [Graded.resurrect, hy]
      have hr := ghastype_rename hxy hye he
      rw [rename_resurrect x y f] at hr
      exact hr
  | f, _, _, hy, @Graded.GSubType.sub_coker _ e s0 s1 h0 h1 he => by
      refine .sub_coker (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1) ?_
      have hye : Graded.resurrect f y = none := by simp [Graded.resurrect, hy]
      have hr := ghastype_rename hxy hye he
      rw [rename_resurrect x y f] at hr
      exact hr
  | f, _, _, hy, @Graded.GSubType.sub_img _ e s0 s1 h0 h1 he => by
      refine .sub_img (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1) ?_
      have hye : Graded.resurrect f y = none := by simp [Graded.resurrect, hy]
      have hr := ghastype_rename hxy hye he
      rw [rename_resurrect x y f] at hr
      exact hr
  | f, _, _, hy, @Graded.GSubType.sub_coimg _ e s0 s1 h0 h1 he => by
      refine .sub_coimg (gsvalid_rename hxy hy h0) (gsvalid_rename hxy hy h1) ?_
      have hye : Graded.resurrect f y = none := by simp [Graded.resurrect, hy]
      have hr := ghastype_rename hxy hye he
      rw [rename_resurrect x y f] at hr
      exact hr

noncomputable def ghastype_rename {x y : Name} (hxy : x ≠ y) :
    {G : Graded.GCtx} → {e : Term} → {tau : Ty} → G y = none →
      Graded.GHasType G e tau →
      Graded.GHasType (renameGCtx x y G)
        (Term.subst x (.var y) e) (Ty.subst x (.var y) tau)
  | G, _, _, hy, .gzero hs => by
      apply Graded.GHasType.gzero
      rw [← rename_typeCtxOmega]
      exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs
  | G, _, _, hy,
      @Graded.GHasType.gsmul _ G0 G1 e0 e1 s hs hsp hta h0 h1 => by
      have hnone : Graded.gadd (G0 y) (G1 y) = none := by rw [← hsp y, hy]
      obtain ⟨hy0, hy1⟩ := Graded.gadd_eq_none_iff.mp hnone
      exact .gsmul
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs)
        (renameGCtx_split hsp)
        (Graded.TypeAgree.rename hta) (ghastype_rename hxy hy0 h0)
          (ghastype_rename hxy hy1 h1)
  | G, _, _, hy, .gadd hs h0 h1 => by
      exact .gadd
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs)
        (ghastype_rename hxy hy h0) (ghastype_rename hxy hy h1)
  | G, _, _, hy, .ginner hs hnl => by
      exact .ginner
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs)
        (Graded.NoLin.rename hnl)
  | _, _, _, _, .greal_lit r hnl => .greal_lit r (Graded.NoLin.rename hnl)
  | G, _, _, hy,
      @Graded.GHasType.gapp_linear _ G0 G1 e0 e1 s0 s1 hs0 hs1 hsp hta h0 h1 => by
      have hnone : Graded.gadd (G0 y) (G1 y) = none := by rw [← hsp y, hy]
      obtain ⟨hy0, hy1⟩ := Graded.gadd_eq_none_iff.mp hnone
      exact .gapp_linear
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs0)
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs1)
        (renameGCtx_split hsp)
        (Graded.TypeAgree.rename hta) (ghastype_rename hxy hy0 h0)
          (ghastype_rename hxy hy1 h1)
  | G, _, _, hy,
      @Graded.GHasType.gapp_inner _ G0 G1 e0 e1 s hs hsp hta h0 h1 => by
      have hnone : Graded.gadd (G0 y) (G1 y) = none := by rw [← hsp y, hy]
      obtain ⟨hy0, hy1⟩ := Graded.gadd_eq_none_iff.mp hnone
      exact .gapp_inner
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs)
        (renameGCtx_split hsp)
        (Graded.TypeAgree.rename hta) (ghastype_rename hxy hy0 h0)
          (ghastype_rename hxy hy1 h1)
  | G, _, _, hy, @Graded.GHasType.gapp_nonlinear _ e0 ea tau0 tau1 hnl h0 h1 => by
      have hcomm : Ty.subst x (.var y) (Ty.instantiate ea tau1) =
          Ty.instantiate (Term.subst x (.var y) ea)
            (Ty.subst x (.var y) tau1) :=
        Ty.subst_openRec x (.var y) Term.lc.var tau1 0 ea
      rw [hcomm]
      exact .gapp_nonlinear (Graded.NoLin.rename hnl)
        (ghastype_rename hxy hy h0) (ghastype_rename hxy hy h1)
  | G, _, _, hy, @Graded.GHasType.gvar _ z g tau hz hg hlin => by
      have hzy : z ≠ y := by rintro rfl; rw [hy] at hz; contradiction
      by_cases hzx : z = x
      · subst z
        simp only [Term.subst, if_pos rfl]
        apply Graded.GHasType.gvar
        · simp only [renameGCtx_apply, Equiv.swap_apply_right]
          rw [hz]
          rfl
        · exact hg
        · intro w hwy tauw hw
          simp only [renameGCtx_apply] at hw
          cases hs : G (Equiv.swap x y w) with
          | none => rw [hs] at hw; contradiction
          | some p =>
              obtain ⟨gw, tw⟩ := p
              rw [hs] at hw
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
              have hswx : Equiv.swap x y w ≠ x := by
                intro heq
                apply hwy
                calc
                  w = Equiv.swap x y (Equiv.swap x y w) :=
                    (Equiv.swap_apply_self x y w).symm
                  _ = Equiv.swap x y x := congrArg (Equiv.swap x y) heq
                  _ = y := Equiv.swap_apply_left x y
              exact hlin _ hswx tw (by simpa [hw.1] using hs)
      · have hfix : Equiv.swap x y z = z :=
          Equiv.swap_apply_of_ne_of_ne hzx hzy
        simp only [Term.subst, if_neg (Ne.symm hzx)]
        apply Graded.GHasType.gvar
        · simp only [renameGCtx_apply, hfix]
          rw [hz]
          rfl
        · exact hg
        · intro w hwz tauw hw
          simp only [renameGCtx_apply] at hw
          cases hs : G (Equiv.swap x y w) with
          | none => rw [hs] at hw; contradiction
          | some p =>
              obtain ⟨gw, tw⟩ := p
              rw [hs] at hw
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hw
              have hswz : Equiv.swap x y w ≠ z := by
                intro heq
                apply hwz
                calc
                  w = Equiv.swap x y (Equiv.swap x y w) :=
                    (Equiv.swap_apply_self x y w).symm
                  _ = Equiv.swap x y z := congrArg (Equiv.swap x y) heq
                  _ = z := hfix
              exact hlin _ hswz tw (by simpa [hw.1] using hs)
  | G, _, _, hy, .gpinv_tensor hs0 hs1 hnl he => by
      exact .gpinv_tensor
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs0)
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs1)
        (Graded.NoLin.rename hnl) (ghastype_rename hxy hy he)
  | G, _, _, hy, .gpinv_dual hs hnl he => by
      exact .gpinv_dual
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs)
        (Graded.NoLin.rename hnl) (ghastype_rename hxy hy he)
  | G, _, _, hy, .gdsumE hs0 hs1 h0 h1 => by
      exact .gdsumE
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs0)
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs1)
        (ghastype_rename hxy hy h0) (ghastype_rename hxy hy h1)
  | G, _, _, hy,
      @Graded.GHasType.gtprodE _ G0 G1 e0 e1 s0 s1 hs0 hs1 hsp hta h0 h1 => by
      have hnone : Graded.gadd (G0 y) (G1 y) = none := by rw [← hsp y, hy]
      obtain ⟨hy0, hy1⟩ := Graded.gadd_eq_none_iff.mp hnone
      exact .gtprodE
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs0)
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs1)
        (renameGCtx_split hsp)
        (Graded.TypeAgree.rename hta) (ghastype_rename hxy hy0 h0)
          (ghastype_rename hxy hy1 h1)
  | G, _, _, hy, @Graded.GHasType.gllam_real _ s e L hs hbody => by
      refine Graded.GHasType.gllam_real (L ∪ {x, y})
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs) ?_
      intro z hz
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hz
      obtain ⟨hzL, hzx, hzy⟩ := hz
      have hy' : Function.update G z (some (Graded.GGrade.one, .space s)) y = none := by
        rw [Function.update_of_ne (Ne.symm hzy), hy]
      have hr := ghastype_rename hxy hy' (hbody z hzL)
      rw [renameGCtx_update hzx hzy,
        Graded.Term.subst_openVar_ne Term.lc.var hzx] at hr
      simpa only [Option.map_some, Ty.subst] using hr
  | G, _, _, hy, @Graded.GHasType.gllam_tensor _ s0 s e L hne hs0 hs hbody => by
      refine Graded.GHasType.gllam_tensor (L ∪ {x, y})
        (Graded.space_subst_ne_real x (.var y) hne)
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs0)
        (by rw [← rename_typeCtxOmega]
            exact gsvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) hs) ?_
      intro z hz
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hz
      obtain ⟨hzL, hzx, hzy⟩ := hz
      have hy' : Function.update G z (some (Graded.GGrade.one, .space s0)) y = none := by
        rw [Function.update_of_ne (Ne.symm hzy), hy]
      have hr := ghastype_rename hxy hy' (hbody z hzL)
      rw [renameGCtx_update hzx hzy,
        Graded.Term.subst_openVar_ne Term.lc.var hzx] at hr
      simpa only [Option.map_some, Ty.subst] using hr
  | G, _, _, hy, .gembed hsub hnl => by
      exact .gembed
        (by rw [← rename_typeCtxOmega]
            exact gsubtype_rename hxy (by simp [Graded.typeCtxOmega, hy]) hsub)
        (Graded.NoLin.rename hnl)
  | G, _, _, hy,
      @Graded.GHasType.gnllam _ tau0 tau1 k0 k1 e L htv hnl hbody => by
      refine Graded.GHasType.gnllam (L ∪ {x, y})
        (by rw [← rename_typeCtxOmega]
            exact gtvalid_rename hxy (by simp [Graded.typeCtxOmega, hy]) htv)
        (Graded.NoLin.rename hnl) ?_
      intro z hz
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hz
      obtain ⟨hzL, hzx, hzy⟩ := hz
      have hy' : Function.update G z (some (Graded.GGrade.omega, tau0)) y = none := by
        rw [Function.update_of_ne (Ne.symm hzy), hy]
      have hr := ghastype_rename hxy hy' (hbody z hzL)
      rw [renameGCtx_update hzx hzy,
        Graded.Term.subst_openVar_ne Term.lc.var hzx,
        Graded.Ty.subst_openVar_ne Term.lc.var hzx] at hr
      simpa only [Option.map_some] using hr

end

theorem rename_asTypeCtx (x y : Name) (Gamma : NLCtx) :
    Graded.asTypeCtx (renameNLCtx x y Gamma) =
      renameTCtx x y (Graded.asTypeCtx Gamma) := by
  funext z
  simp only [Graded.asTypeCtx, renameNLCtx_lookup, renameTCtx_apply]

theorem rename_tr (x y : Name) (Delta : LCtx) (Gamma : NLCtx) :
    Graded.tr (renameLCtx x y Delta) (renameNLCtx x y Gamma) =
      renameGCtx x y (Graded.tr Delta Gamma) := by
  funext z
  simp only [Graded.tr, renameLCtx_lookup, renameNLCtx_lookup,
    renameGCtx_apply]
  cases Delta.lookup (Equiv.swap x y z) with
  | none => cases Gamma.lookup (Equiv.swap x y z) <;> rfl
  | some s => rfl

theorem Graded.CtxDisj.rename {x y : Name} {Delta : LCtx} {Gamma : NLCtx}
    (h : Graded.CtxDisj Delta Gamma) :
    Graded.CtxDisj (renameLCtx x y Delta) (renameNLCtx x y Gamma) := by
  intro z hzD hzG
  rw [Finmap.mem_iff] at hzD hzG
  obtain ⟨s, hs⟩ := hzD
  obtain ⟨tau, htau⟩ := hzG
  rw [renameLCtx_lookup] at hs
  rw [renameNLCtx_lookup] at htau
  cases hd : Delta.lookup (Equiv.swap x y z) with
  | none => rw [hd] at hs; contradiction
  | some s' =>
      cases hg : Gamma.lookup (Equiv.swap x y z) with
      | none => rw [hg] at htau; contradiction
      | some tau' =>
          exact h (Equiv.swap x y z)
            (Finmap.mem_of_lookup_eq_some hd) (Finmap.mem_of_lookup_eq_some hg)

noncomputable def svalid_rename {x y : Name} {Gamma : NLCtx} {s : Space}
    (hxy : x ≠ y) (hy : y ∉ Gamma) (h : SValid Gamma s) :
    SValid (renameNLCtx x y Gamma) (Space.subst x (.var y) s) := by
  have hy' : Graded.asTypeCtx Gamma y = none :=
    Finmap.lookup_eq_none.mpr hy
  have hg := gsvalid_rename hxy hy' (Graded.svalidBridge h)
  rw [← rename_asTypeCtx] at hg
  exact Graded.svalidBwd hg (fun _ _ hz => hz)

noncomputable def tvalid_rename {x y : Name} {Gamma : NLCtx} {tau : Ty}
    {k : Kind} (hxy : x ≠ y) (hy : y ∉ Gamma) (h : TValid Gamma tau k) :
    TValid (renameNLCtx x y Gamma) (Ty.subst x (.var y) tau) k := by
  have hy' : Graded.asTypeCtx Gamma y = none :=
    Finmap.lookup_eq_none.mpr hy
  have hg := gtvalid_rename hxy hy' (Graded.tvalidBridge h)
  rw [← rename_asTypeCtx] at hg
  exact Graded.tvalidBwd hg (fun _ _ hz => hz)

noncomputable def subtype_rename {x y : Name} {Gamma : NLCtx}
    {s0 s1 : Space} (hxy : x ≠ y) (hy : y ∉ Gamma)
    (h : SubType Gamma s0 s1) :
    SubType (renameNLCtx x y Gamma)
      (Space.subst x (.var y) s0) (Space.subst x (.var y) s1) := by
  have hy' : Graded.asTypeCtx Gamma y = none :=
    Finmap.lookup_eq_none.mpr hy
  have hg := gsubtype_rename hxy hy' (Graded.subtypeBridge h)
  rw [← rename_asTypeCtx] at hg
  exact Graded.subtypeBwd hg (fun _ _ hz => hz)

noncomputable def hasType_rename {x y : Name} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {tau : Ty} (hxy : x ≠ y) (hyD : y ∉ Delta)
    (hyG : y ∉ Gamma) (hd : Graded.CtxDisj Delta Gamma)
    (h : HasType Delta Gamma e tau) :
    HasType (renameLCtx x y Delta) (renameNLCtx x y Gamma)
      (Term.subst x (.var y) e) (Ty.subst x (.var y) tau) := by
  have hytr : Graded.tr Delta Gamma y = none := by
    simp only [Graded.tr, Finmap.lookup_eq_none.mpr hyD,
      Finmap.lookup_eq_none.mpr hyG]
  have hg := ghastype_rename hxy hytr (Graded.hasTypeBridge hd h)
  rw [← rename_tr] at hg
  exact Graded.hasTypeBridgeBwd (Graded.CtxDisj.rename hd) hg

noncomputable def hasTypeBasis_rename {x y : Name} {Delta : LCtx}
    {Gamma : NLCtx} {e : Term} {b : Basis} (hxy : x ≠ y)
    (hyD : y ∉ Delta) (hyG : y ∉ Gamma)
    (hd : Graded.CtxDisj Delta Gamma)
    (h : HasType Delta Gamma e (Basis.tof b)) :
    HasType (renameLCtx x y Delta) (renameNLCtx x y Gamma)
      (Term.subst x (.var y) e) (Basis.tof (Basis.subst x (.var y) b)) := by
  rw [Basis.tof_subst]
  exact hasType_rename hxy hyD hyG hd h

noncomputable def basisValid_rename {x y : Name} {Gamma : NLCtx} {b : Basis}
    (hxy : x ≠ y) (hy : y ∉ Gamma) (h : BasisValid Gamma b) :
    BasisValid (renameNLCtx x y Gamma) (Basis.subst x (.var y) b) := by
  induction h with
  | empty => exact .empty
  | one => exact .one
  | dual _ htof ih =>
      exact .dual (ih hy)
        (by simp only [Basis.tof_subst, htof, Ty.subst, Basis.sof_subst])
  | dsum _ _ htof0 htof1 ih0 ih1 =>
      exact .dsum (ih0 hy) (ih1 hy)
        (by simp only [Basis.tof_subst, htof0, Ty.subst, Basis.sof_subst])
        (by simp only [Basis.tof_subst, htof1, Ty.subst, Basis.sof_subst])
  | tprod _ _ htof0 htof1 ih0 ih1 =>
      exact .tprod (ih0 hy) (ih1 hy)
        (by simp only [Basis.tof_subst, htof0, Ty.subst, Basis.sof_subst])
        (by simp only [Basis.tof_subst, htof1, Ty.subst, Basis.sof_subst])
  | proj_ker hb0 hb1 hs0 hs1 he ih0 ih1 =>
      exact .proj_ker (ih0 hy) (ih1 hy)
        (by simp only [Basis.tof_subst, hs0, Ty.subst])
        (by simp only [Basis.tof_subst, hs1, Ty.subst])
        (he.map (hasType_rename hxy
          (Finmap.lookup_eq_none.mp (show (∅ : LCtx).lookup y = none by rfl)) hy
          (Graded.CtxDisj.empty _)))
  | proj_coker hb0 hb1 hs0 hs1 he ih0 ih1 =>
      exact .proj_coker (ih0 hy) (ih1 hy)
        (by simp only [Basis.tof_subst, hs0, Ty.subst])
        (by simp only [Basis.tof_subst, hs1, Ty.subst])
        (he.map (hasType_rename hxy
          (Finmap.lookup_eq_none.mp (show (∅ : LCtx).lookup y = none by rfl)) hy
          (Graded.CtxDisj.empty _)))
  | proj_img hb0 hb1 hs0 hs1 he ih0 ih1 =>
      exact .proj_img (ih0 hy) (ih1 hy)
        (by simp only [Basis.tof_subst, hs0, Ty.subst])
        (by simp only [Basis.tof_subst, hs1, Ty.subst])
        (he.map (hasType_rename hxy
          (Finmap.lookup_eq_none.mp (show (∅ : LCtx).lookup y = none by rfl)) hy
          (Graded.CtxDisj.empty _)))
  | proj_coimg hb0 hb1 hs0 hs1 he ih0 ih1 =>
      exact .proj_coimg (ih0 hy) (ih1 hy)
        (by simp only [Basis.tof_subst, hs0, Ty.subst])
        (by simp only [Basis.tof_subst, hs1, Ty.subst])
        (he.map (hasType_rename hxy
          (Finmap.lookup_eq_none.mp (show (∅ : LCtx).lookup y = none by rfl)) hy
          (Graded.CtxDisj.empty _)))
  | image hb hsof he ih =>
      exact .image (ih hy)
        (by rw [Basis.sof_subst, hsof]; rfl)
        (he.map (hasType_rename hxy
          (Finmap.lookup_eq_none.mp (show (∅ : LCtx).lookup y = none by rfl)) hy
          (Graded.CtxDisj.empty _)))
  | terms hb htof hsv hes hne ih =>
      simp only [Basis.subst]
      refine Basis.BasisValid.terms (ih hy)
        (by simp only [Basis.tof_subst, htof, Ty.subst])
        (hsv.map (svalid_rename hxy hy)) ?_ ?_
      intro e he
      simp only [List.mem_map] at he
      obtain ⟨e0, he0, rfl⟩ := he
      exact (hes e0 he0).map
        (hasType_rename hxy
          (Finmap.lookup_eq_none.mp (show (∅ : LCtx).lookup y = none by rfl)) hy
          (Graded.CtxDisj.empty _))
      exact fun hempty => hne (List.map_eq_nil_iff.mp hempty)
  | frame L hb0 hbody ih0 ihbody =>
      rename_i epsilon b0 b1
      refine Basis.BasisValid.frame (L ∪ {x, y}) (ih0 hy) ?_
      intro z hz
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hz
      obtain ⟨hzL, hzx, hzy⟩ := hz
      have hyins : y ∉ Finmap.insert z (Basis.tof b0) epsilon := by
        intro hm
        rcases Finmap.mem_insert.mp hm with hyz | hm
        · exact hzy hyz.symm
        · exact hy hm
      have hr := ihbody z hzL hyins
      rw [renameNLCtx_insert, Equiv.swap_apply_of_ne_of_ne hzx hzy,
        Basis.subst_openRec x (.var y) Term.lc.var b1 0 (.var z),
        Term.subst, if_neg (Ne.symm hzx)] at hr
      rw [Basis.tof_subst]
      exact hr

/-! ## Freshness carried through the checked tree -/

def LCtxFresh (a : Name) (Delta : LCtx) : Prop :=
  ∀ z s, Delta.lookup z = some s → a ∉ Space.fv s

def NLCtxFresh (a : Name) (Gamma : NLCtx) : Prop :=
  ∀ z tau, Gamma.lookup z = some tau → a ∉ Ty.fv tau

theorem lctxFresh_of_ctxWF {Delta : LCtx} {Gamma : NLCtx}
    (h : V2.CtxWF' Delta Gamma) {a : Name} (ha : a ∉ Gamma) :
    LCtxFresh a Delta := by
  intro z s hz has
  exact ha (Finmap.mem_keys.mp (h.lin_fv z s hz has))

theorem nlctxFresh_of_ctxWF {Delta : LCtx} {Gamma : NLCtx}
    (h : V2.CtxWF' Delta Gamma) {a : Name} (ha : a ∉ Gamma) :
    NLCtxFresh a Gamma := by
  intro z tau hz hat
  exact ha (Finmap.mem_keys.mp (h.nl_fv z tau hz hat))

theorem LCtxFresh.empty (a : Name) : LCtxFresh a (∅ : LCtx) := by
  intro z s hz
  simp only [Finmap.lookup_empty] at hz
  contradiction

theorem LCtxFresh.of_union_left {a : Name} {D0 D1 : LCtx}
    (h : LCtxFresh a (D0 ∪ D1)) : LCtxFresh a D0 := by
  intro z s hz
  exact h z s (by
    by_cases hm : z ∈ D0
    · rw [Finmap.lookup_union_left hm]; exact hz
    · exact absurd (Finmap.mem_of_lookup_eq_some hz) hm)

theorem LCtxFresh.of_union_right {a : Name} {D0 D1 : LCtx}
    (hd : Finmap.Disjoint D0 D1) (h : LCtxFresh a (D0 ∪ D1)) :
    LCtxFresh a D1 := by
  intro z s hz
  have hm1 : z ∈ D1 := Finmap.mem_of_lookup_eq_some hz
  have hm0 : z ∉ D0 := fun hm => hd z hm hm1
  exact h z s (by rw [Finmap.lookup_union_right hm0]; exact hz)

theorem LCtxFresh.union {a : Name} {D0 D1 : LCtx}
    (h0 : LCtxFresh a D0) (h1 : LCtxFresh a D1) :
    LCtxFresh a (D0 ∪ D1) := by
  intro z s hz
  by_cases hm : z ∈ D0
  · exact h0 z s ((Finmap.lookup_union_left hm).symm.trans hz)
  · exact h1 z s ((Finmap.lookup_union_right hm).symm.trans hz)

theorem NLCtxFresh.of_union_left {a : Name} {G0 G1 : NLCtx}
    (h : NLCtxFresh a (G0 ∪ G1)) : NLCtxFresh a G0 := by
  intro z tau hz
  exact h z tau (by
    have hm := Finmap.mem_of_lookup_eq_some hz
    rw [Finmap.lookup_union_left hm]
    exact hz)

theorem NLCtxFresh.of_union_right {a : Name} {G0 G1 : NLCtx}
    (hd : Finmap.Disjoint G0 G1) (h : NLCtxFresh a (G0 ∪ G1)) :
    NLCtxFresh a G1 := by
  intro z tau hz
  have hm1 : z ∈ G1 := Finmap.mem_of_lookup_eq_some hz
  have hm0 : z ∉ G0 := fun hm => hd z hm hm1
  exact h z tau (by rw [Finmap.lookup_union_right hm0]; exact hz)

theorem NLCtxFresh.of_incl {a : Name} {G G' : NLCtx}
    (h : NLCtxFresh a G') (hle : NLCtxIncl G G') : NLCtxFresh a G := by
  intro z tau hz
  exact h z tau (hle z tau hz)

theorem LCtxFresh.insert {a z : Name} {s : Space} {Delta : LCtx}
    (haz : a ≠ z) (has : a ∉ Space.fv s) (h : LCtxFresh a Delta) :
    LCtxFresh a (Finmap.insert z s Delta) := by
  intro w sw hw
  by_cases hwz : w = z
  · subst w
    rw [Finmap.lookup_insert, Option.some.injEq] at hw
    simpa [← hw] using has
  · rw [Finmap.lookup_insert_of_ne _ hwz] at hw
    exact h w sw hw

theorem NLCtxFresh.insert {a z : Name} {tau : Ty} {Gamma : NLCtx}
    (haz : a ≠ z) (hat : a ∉ Ty.fv tau) (h : NLCtxFresh a Gamma) :
    NLCtxFresh a (Finmap.insert z tau Gamma) := by
  intro w tw hw
  by_cases hwz : w = z
  · subst w
    rw [Finmap.lookup_insert, Option.some.injEq] at hw
    simpa [← hw] using hat
  · rw [Finmap.lookup_insert_of_ne _ hwz] at hw
    exact h w tw hw

theorem NLCtxFresh.toLCtx {a : Name} {lin : LCtx}
    (h : NLCtxFresh a lin.toNL) : LCtxFresh a lin := by
  intro z s hz
  have := h z (.space s) (LCtx.toNL_lookup lin z s hz)
  simpa only [Ty.fv] using this

theorem notMem_of_incl {a : Name} {G G' : NLCtx}
    (hle : NLCtxIncl G G') (h : a ∉ G') : a ∉ G := by
  intro ha
  obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp ha
  exact h (Finmap.mem_of_lookup_eq_some (hle a tau htau))

theorem notMem_union_left {a : Name} {m n : NLCtx}
    (h : a ∉ m ∪ n) : a ∉ m :=
  fun hm => h (Finmap.mem_union.mpr (Or.inl hm))

theorem notMem_union_right {a : Name} {m n : NLCtx}
    (h : a ∉ m ∪ n) : a ∉ n :=
  fun hn => h (Finmap.mem_union.mpr (Or.inr hn))

theorem space_subst_fresh_of_ne {a x y : Name} {s : Space}
    (hax : a ≠ x) (hay : a ≠ y) (ha : a ∉ Space.fv s) :
    a ∉ Space.fv (Space.subst x (.var y) s) := by
  intro hm
  rcases Finset.mem_union.mp (Space.fv_subst x (.var y) s hm) with hs | hv
  · exact ha hs
  · exact hay (by simpa only [Term.fv, Finset.mem_singleton] using hv)

theorem ty_subst_fresh_of_ne {a x y : Name} {tau : Ty}
    (hax : a ≠ x) (hay : a ≠ y) (ha : a ∉ Ty.fv tau) :
    a ∉ Ty.fv (Ty.subst x (.var y) tau) := by
  intro hm
  rcases Finset.mem_union.mp (Ty.fv_subst x (.var y) tau hm) with ht | hv
  · exact ha ht
  · exact hay (by simpa only [Term.fv, Finset.mem_singleton] using hv)

theorem promoteFresh_rename {x y : Name} {lin Delta : LCtx} {Gamma : NLCtx}
    (hxy : x ≠ y) (hylin : y ∉ lin)
    (hyD : LCtxFresh y Delta) (hyl : LCtxFresh y lin)
    (hyG : NLCtxFresh y Gamma) (h : PromoteFresh lin Delta Gamma) :
    PromoteFresh (renameLCtx x y lin) (renameLCtx x y Delta)
      (renameNLCtx x y Gamma) where
  fresh_Δ := by
    intro a ha z s hz
    rw [Finmap.mem_iff] at ha
    obtain ⟨sa, hsa⟩ := ha
    rw [renameLCtx_lookup] at hsa
    cases hsl : lin.lookup (Equiv.swap x y a) with
    | none => rw [hsl] at hsa; contradiction
    | some sl =>
      have hamem := Finmap.mem_of_lookup_eq_some hsl
      rw [renameLCtx_lookup] at hz
      cases hD : Delta.lookup (Equiv.swap x y z) with
      | none => rw [hD] at hz; contradiction
      | some sd =>
        have hsd : Space.subst x (.var y) sd = s := by
          rw [hD] at hz
          exact Option.some.inj hz
        rw [← hsd]
        by_cases hay : a = y
        · subst a
          have hxmem : x ∈ lin := by
            simpa only [Equiv.swap_apply_right] using hamem
          have hxf := h.fresh_Δ x hxmem _ _ hD
          rw [Space.subst_fresh x (.var y) sd hxf]
          exact hyD _ _ hD
        · have hax : a ≠ x := by
            intro hax
            subst a
            exact hylin (by simpa only [Equiv.swap_apply_left] using hamem)
          have hfix : Equiv.swap x y a = a :=
            Equiv.swap_apply_of_ne_of_ne hax hay
          exact space_subst_fresh_of_ne hax hay
            (by simpa [hfix] using h.fresh_Δ _ hamem _ _ hD)
  fresh_lin := by
    intro a ha z s hz
    rw [Finmap.mem_iff] at ha
    obtain ⟨sa, hsa⟩ := ha
    rw [renameLCtx_lookup] at hsa
    cases hsl : lin.lookup (Equiv.swap x y a) with
    | none => rw [hsl] at hsa; contradiction
    | some sl =>
      have hamem := Finmap.mem_of_lookup_eq_some hsl
      rw [renameLCtx_lookup] at hz
      cases hD : lin.lookup (Equiv.swap x y z) with
      | none => rw [hD] at hz; contradiction
      | some sd =>
        have hsd : Space.subst x (.var y) sd = s := by
          rw [hD] at hz
          exact Option.some.inj hz
        rw [← hsd]
        by_cases hay : a = y
        · subst a
          have hxmem : x ∈ lin := by
            simpa only [Equiv.swap_apply_right] using hamem
          have hxf := h.fresh_lin x hxmem _ _ hD
          rw [Space.subst_fresh x (.var y) sd hxf]
          exact hyl _ _ hD
        · have hax : a ≠ x := by
            intro hax
            subst a
            exact hylin (by simpa only [Equiv.swap_apply_left] using hamem)
          have hfix : Equiv.swap x y a = a :=
            Equiv.swap_apply_of_ne_of_ne hax hay
          exact space_subst_fresh_of_ne hax hay
            (by simpa [hfix] using h.fresh_lin _ hamem _ _ hD)
  fresh_ε := by
    intro a ha z tau hz
    rw [Finmap.mem_iff] at ha
    obtain ⟨sa, hsa⟩ := ha
    rw [renameLCtx_lookup] at hsa
    cases hsl : lin.lookup (Equiv.swap x y a) with
    | none => rw [hsl] at hsa; contradiction
    | some sl =>
      have hamem := Finmap.mem_of_lookup_eq_some hsl
      rw [renameNLCtx_lookup] at hz
      cases hG : Gamma.lookup (Equiv.swap x y z) with
      | none => rw [hG] at hz; contradiction
      | some tg =>
        have htg : Ty.subst x (.var y) tg = tau := by
          rw [hG] at hz
          exact Option.some.inj hz
        rw [← htg]
        by_cases hay : a = y
        · subst a
          have hxmem : x ∈ lin := by
            simpa only [Equiv.swap_apply_right] using hamem
          have hxf := h.fresh_ε x hxmem _ _ hG
          rw [Ty.subst_fresh x (.var y) tg hxf]
          exact hyG _ _ hG
        · have hax : a ≠ x := by
            intro hax
            subst a
            exact hylin (by simpa only [Equiv.swap_apply_left] using hamem)
          have hfix : Equiv.swap x y a = a :=
            Equiv.swap_apply_of_ne_of_ne hax hay
          exact ty_subst_fresh_of_ne hax hay
            (by simpa [hfix] using h.fresh_ε _ hamem _ _ hG)

structure NLReady (a : Name) (Gamma : NLCtx) : Prop where
  notMem : a ∉ Gamma
  fresh : NLCtxFresh a Gamma

structure TermReady (a : Name) (Delta : LCtx) (Gamma : NLCtx) : Prop where
  notMemL : a ∉ Delta
  notMemN : a ∉ Gamma
  freshL : LCtxFresh a Delta
  freshN : NLCtxFresh a Gamma
  disjoint : Graded.CtxDisj Delta Gamma

theorem NLReady.ofWF {a : Name} {Delta : LCtx} {Gamma : NLCtx}
    (h : V2.CtxWF' Delta Gamma) (ha : a ∉ Gamma) : NLReady a Gamma :=
  ⟨ha, nlctxFresh_of_ctxWF h ha⟩

theorem TermReady.ofWF {a : Name} {Delta : LCtx} {Gamma : NLCtx}
    (h : V2.CtxWF' Delta Gamma) (haD : a ∉ Delta) (haG : a ∉ Gamma) :
    TermReady a Delta Gamma :=
  ⟨haD, haG, lctxFresh_of_ctxWF h haG, nlctxFresh_of_ctxWF h haG, h.disjoint⟩

theorem TermReady.empty {a : Name} {Gamma : NLCtx} (h : NLReady a Gamma) :
    TermReady a ∅ Gamma :=
  ⟨Finmap.notMem_empty, h.notMem, LCtxFresh.empty a, h.fresh,
    Graded.CtxDisj.empty _⟩

theorem NLReady.insert {a z : Name} {tau : Ty} {Gamma : NLCtx}
    (h : NLReady a Gamma) (haz : a ≠ z) (hat : a ∉ Ty.fv tau) :
    NLReady a (Finmap.insert z tau Gamma) := by
  refine ⟨?_, NLCtxFresh.insert haz hat h.fresh⟩
  intro hm
  rcases Finmap.mem_insert.mp hm with haz' | ha
  · exact haz haz'
  · exact h.notMem ha

theorem TermReady.insertL {a z : Name} {s : Space} {Delta : LCtx}
    {Gamma : NLCtx} (h : TermReady a Delta Gamma) (haz : a ≠ z)
    (has : a ∉ Space.fv s) (hzG : z ∉ Gamma) :
    TermReady a (Finmap.insert z s Delta) Gamma :=
  ⟨by
      intro hm
      rcases Finmap.mem_insert.mp hm with haz' | ha
      · exact haz haz'
      · exact h.notMemL ha,
    h.notMemN, LCtxFresh.insert haz has h.freshL, h.freshN,
    Graded.CtxDisj.insert' h.disjoint hzG⟩

theorem TermReady.of_union_left {a : Name} {D0 D1 : LCtx} {Gamma : NLCtx}
    (h : TermReady a (D0 ∪ D1) Gamma) : TermReady a D0 Gamma :=
  ⟨fun ha => h.notMemL (Finmap.mem_union.mpr (Or.inl ha)), h.notMemN,
    h.freshL.of_union_left, h.freshN,
    Graded.CtxDisj.of_union_left h.disjoint⟩

theorem TermReady.of_union_right {a : Name} {D0 D1 : LCtx} {Gamma : NLCtx}
    (hd : Finmap.Disjoint D0 D1) (h : TermReady a (D0 ∪ D1) Gamma) :
    TermReady a D1 Gamma :=
  ⟨fun ha => h.notMemL (Finmap.mem_union.mpr (Or.inr ha)), h.notMemN,
    LCtxFresh.of_union_right hd h.freshL, h.freshN,
    Graded.CtxDisj.of_union_right h.disjoint⟩

theorem TermReady.nl_smaller {a : Name} {Delta : LCtx} {G G' : NLCtx}
    (hle : NLCtxIncl G G') (h : TermReady a Delta G') : TermReady a Delta G :=
  ⟨h.notMemL, notMem_of_incl hle h.notMemN, h.freshL,
    NLCtxFresh.of_incl h.freshN hle,
    fun z hzD hzG => by
      obtain ⟨tau, htau⟩ := Finmap.mem_iff.mp hzG
      exact h.disjoint z hzD (Finmap.mem_of_lookup_eq_some (hle z tau htau))⟩

theorem NLReady.nl_smaller {a : Name} {G G' : NLCtx}
    (hle : NLCtxIncl G G') (h : NLReady a G') : NLReady a G :=
  ⟨notMem_of_incl hle h.notMem, NLCtxFresh.of_incl h.fresh hle⟩

theorem TermReady.promoteInner {a : Name} {lin Delta : LCtx} {Gamma : NLCtx}
    (hdlin : Finmap.Disjoint lin Delta)
    (hdGamma : Finmap.Disjoint lin.toNL Gamma)
    (h : TermReady a Delta (lin.toNL ∪ Gamma)) :
    TermReady a (lin ∪ Delta) Gamma := by
  have halinNL : a ∉ lin.toNL := notMem_union_left h.notMemN
  have halin : a ∉ lin := fun ha => halinNL ((LCtx.mem_toNL_iff lin a).mpr ha)
  have haG : a ∉ Gamma := notMem_union_right h.notMemN
  have hflin : LCtxFresh a lin :=
    NLCtxFresh.toLCtx (h.freshN.of_union_left)
  have hfG : NLCtxFresh a Gamma :=
    NLCtxFresh.of_union_right hdGamma h.freshN
  exact ⟨fun ha => by
      rcases Finmap.mem_union.mp ha with hl | hd
      · exact halin hl
      · exact h.notMemL hd,
    haG, hflin.union h.freshL, hfG,
    Graded.CtxDisj.promote_inner h.disjoint hdGamma⟩

theorem freshSpace_of_valid {a : Name} {Gamma : NLCtx} {s : Space}
    (ha : a ∉ Gamma) (h : SValid Gamma s) : a ∉ Space.fv s :=
  fun hm => ha (Finmap.mem_keys.mp (SValid.fv_closure h hm))

theorem freshTy_of_valid {a : Name} {Gamma : NLCtx} {tau : Ty} {k : Kind}
    (ha : a ∉ Gamma) (h : TValid Gamma tau k) : a ∉ Ty.fv tau :=
  fun hm => ha (Finmap.mem_keys.mp (TValid.fv_closure h hm))

theorem TermReady.toNL {a : Name} {Delta : LCtx} {Gamma : NLCtx}
    (h : TermReady a Delta Gamma) : NLReady a Gamma :=
  ⟨h.notMemN, h.freshN⟩

theorem NLCtxIncl.rename {x y : Name} {Gamma Gamma' : NLCtx}
    (h : NLCtxIncl Gamma Gamma') :
    NLCtxIncl (renameNLCtx x y Gamma) (renameNLCtx x y Gamma') := by
  intro z tau hz
  rw [renameNLCtx_lookup] at hz ⊢
  cases hG : Gamma.lookup (Equiv.swap x y z) with
  | none => rw [hG] at hz; contradiction
  | some tau0 =>
    rw [hG] at hz
    obtain rfl := Option.some.inj hz
    rw [h _ _ hG]
    rfl

theorem renameNLCtx_eq_self {x y : Name} {Gamma : NLCtx}
    (hx : x ∉ Gamma) (hy : y ∉ Gamma) (hfr : NLCtxFresh x Gamma) :
    renameNLCtx x y Gamma = Gamma := by
  apply Finmap.ext_lookup
  intro z
  rw [renameNLCtx_lookup]
  by_cases hzx : z = x
  · subst z
    rw [Equiv.swap_apply_left, Finmap.lookup_eq_none.mpr hy,
      Finmap.lookup_eq_none.mpr hx]
    rfl
  · by_cases hzy : z = y
    · subst z
      rw [Equiv.swap_apply_right, Finmap.lookup_eq_none.mpr hx,
        Finmap.lookup_eq_none.mpr hy]
      rfl
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
      cases hz : Gamma.lookup z with
      | none => rfl
      | some tau =>
        simp only [Option.map_some, Option.some.injEq]
        exact Ty.subst_fresh x (.var y) tau (hfr z tau hz)

theorem renameLCtx_eq_self {x y : Name} {Delta : LCtx}
    (hx : x ∉ Delta) (hy : y ∉ Delta) (hfr : LCtxFresh x Delta) :
    renameLCtx x y Delta = Delta := by
  apply Finmap.ext_lookup
  intro z
  rw [renameLCtx_lookup]
  by_cases hzx : z = x
  · subst z
    rw [Equiv.swap_apply_left, Finmap.lookup_eq_none.mpr hy,
      Finmap.lookup_eq_none.mpr hx]
    rfl
  · by_cases hzy : z = y
    · subst z
      rw [Equiv.swap_apply_right, Finmap.lookup_eq_none.mpr hx,
        Finmap.lookup_eq_none.mpr hy]
      rfl
    · rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]
      cases hz : Delta.lookup z with
      | none => rfl
      | some s =>
        simp only [Option.map_some, Option.some.injEq]
        exact Space.subst_fresh x (.var y) s (hfr z s hz)

theorem Basis.subst_openVar_ne_rename {x y z : Name} {b : Basis}
    (hzx : z ≠ x) :
    Basis.subst x (.var y) (Basis.openVar z b) =
      Basis.openVar z (Basis.subst x (.var y) b) := by
  simp only [Basis.openVar,
    Basis.subst_openRec x (.var y) Term.lc.var b 0 (.var z),
    Term.subst, if_neg (Ne.symm hzx)]

theorem Ty.subst_openVar_ne_rename {x y z : Name} {tau : Ty}
    (hzx : z ≠ x) :
    Ty.subst x (.var y) (Ty.openVar z tau) =
      Ty.openVar z (Ty.subst x (.var y) tau) := by
  simp only [Ty.openVar,
    Ty.subst_openRec x (.var y) Term.lc.var tau 0 (.var z),
    Term.subst, if_neg (Ne.symm hzx)]

theorem Term.subst_openVar_ne_rename {x y z : Name} {e : Term}
    (hzx : z ≠ x) :
    Term.subst x (.var y) (Term.openVar z e) =
      Term.openVar z (Term.subst x (.var y) e) := by
  simp only [Term.openVar,
    Term.subst_openRec x (.var y) Term.lc.var e 0 (.var z),
    Term.subst, if_neg (Ne.symm hzx)]

theorem ValTy.subst_openVar_ne_rename {x z : VName} {arg : ValExpr}
    {tauy tauv : ValTy} (harg : ValExpr.lc arg) (hzx : z ≠ x) :
    ValTy.subst x arg (ValTy.openVar z tauy tauv) =
      ValTy.openVar z (ValTy.subst x arg tauy)
        (ValTy.subst x arg tauv) := by
  simp only [ValTy.openVar,
    ValTy.subst_openRec x arg harg tauv 0 (.var z tauy),
    ValExpr.subst, if_neg hzx]

theorem ValExpr.subst_openVar_ne_rename {x z : VName} {arg : ValExpr}
    {tauy : ValTy} {v : ValExpr} (harg : ValExpr.lc arg) (hzx : z ≠ x) :
    ValExpr.subst x arg (ValExpr.openVar z tauy v) =
      ValExpr.openVar z (ValTy.subst x arg tauy)
        (ValExpr.subst x arg v) := by
  simp only [ValExpr.openVar,
    ValExpr.subst_openRec x arg harg v 0 (.var z tauy),
    ValExpr.subst, if_neg hzx]

/-- A space-basis shape equation is invariant under source substitution. -/
theorem Basis.tof_space_subst (x : VName) (u : Term) {b : Basis}
    (h : Basis.tof b = .space (Basis.sof b)) :
    Basis.tof (Basis.subst x u b) =
      .space (Basis.sof (Basis.subst x u b)) := by
  simp only [Basis.tof_subst, h, Ty.subst, Basis.sof_subst]

/-- `isStd` only inspects the constructor tree of a basis. -/
theorem Basis.isStd_subst (x : VName) (u : Term) (b : Basis) :
    Basis.isStd (Basis.subst x u b) = Basis.isStd b := by
  induction b with
  | empty => rfl
  | one => rfl
  | dual b ih => simp only [Basis.subst, Basis.isStd, ih]
  | dsum _ _ ih0 ih1 => simp only [Basis.subst, Basis.isStd, ih0, ih1]
  | tprod _ _ ih0 ih1 => simp only [Basis.subst, Basis.isStd, ih0, ih1]
  | proj _ _ _ ih0 ih1 => simp only [Basis.subst, Basis.isStd, ih0, ih1]
  | image _ _ => simp only [Basis.subst, Basis.isStd]
  | terms _ _ _ _ => simp only [Basis.subst, Basis.isStd]
  | frame _ _ ih0 ih1 => simp only [Basis.subst, Basis.isStd, ih0, ih1]

/-- The hereditary space-basis guard is purely structural and survives
source substitution. -/
theorem Basis.isSpaceBasis_subst_iff (x : VName) (u : Term) (b : Basis) :
    Basis.IsSpaceBasis (Basis.subst x u b) ↔ Basis.IsSpaceBasis b := by
  induction b with
  | empty => rfl
  | one => rfl
  | dual b ih => simpa only [Basis.subst, Basis.IsSpaceBasis, ih]
  | dsum b0 b1 ih0 ih1 =>
      simpa only [Basis.subst, Basis.IsSpaceBasis, ih0, ih1]
  | tprod b0 b1 ih0 ih1 =>
      simpa only [Basis.subst, Basis.IsSpaceBasis, ih0, ih1]
  | proj s b0 b1 ih0 ih1 =>
      simpa only [Basis.subst, Basis.IsSpaceBasis, ih0, ih1]
  | image b ih => simpa only [Basis.subst, Basis.IsSpaceBasis, ih]
  | terms s es b ih =>
      simp only [Basis.subst, Basis.IsSpaceBasis, ih]
      constructor
      · rintro ⟨hm, hb⟩
        exact ⟨fun he => hm (List.map_eq_nil_iff.mpr he), hb⟩
      · rintro ⟨he, hb⟩
        exact ⟨fun hm => he (List.map_eq_nil_iff.mp hm), hb⟩
  | frame b0 b1 ih0 ih1 => rfl

/-- The hereditary type-basis guard is purely structural and survives
source substitution. -/
theorem Basis.isTyBasis_subst_iff (x : VName) (u : Term) (b : Basis) :
    Basis.IsTyBasis (Basis.subst x u b) ↔ Basis.IsTyBasis b := by
  induction b with
  | empty => rfl
  | one => rfl
  | dual b ih => exact Basis.isSpaceBasis_subst_iff x u (.dual b)
  | dsum b0 b1 ih0 ih1 => exact Basis.isSpaceBasis_subst_iff x u (.dsum b0 b1)
  | tprod b0 b1 ih0 ih1 => exact Basis.isSpaceBasis_subst_iff x u (.tprod b0 b1)
  | proj s b0 b1 ih0 ih1 => exact Basis.isSpaceBasis_subst_iff x u (.proj s b0 b1)
  | image b ih => exact Basis.isSpaceBasis_subst_iff x u (.image b)
  | terms s es b ih => exact Basis.isSpaceBasis_subst_iff x u (.terms s es b)
  | frame b0 b1 ih0 ih1 =>
      simpa only [Basis.subst, Basis.IsTyBasis, ih0, ih1]

theorem Basis.IsTyBasis.subst {x : VName} {u : Term} {b : Basis}
    (h : Basis.IsTyBasis b) : Basis.IsTyBasis (Basis.subst x u b) :=
  (Basis.isTyBasis_subst_iff x u b).2 h

def RenameCutValue (v : ValExpr) : Prop :=
  (∃ z tauv, v = .var z tauv) ∨ (∃ i sv, v = .delta i sv)

theorem opStep_var_lookup_of_cut {Psi : EvalCtx} {z : VName} {b : Basis}
    {v : ValExpr} (hv : RenameCutValue v)
    (h : ValExpr.OpStep Psi (.var z) b v) :
    EvalCtx.lookup Psi (z, b) = some v := by
  rcases hv with ⟨w, tauv, rfl⟩ | ⟨i, sv, rfl⟩ <;>
    cases h with
    | var hlookup => exact hlookup

/-! ## Five-way checked alpha transport -/

set_option maxRecDepth 10000 in
local macro "solve_checked_rename" "(" rec:term "," h:term ","
    xx:term "," yy:term "," bb:term "," tt:term "," aa:term "," hh:term
    "," hv:term ")" : tactic =>
  `(tactic| (
    let x : VName := $xx
    let y : VName := $yy
    let bX : Basis := $bb
    let tauVX : ValTy := $tt
    let arg : ValExpr := $aa
    have hxy : x ≠ y := $hh
    have harg : RenameCutValue arg := $hv
    refine ($rec
      (motive_1 := fun Gamma Psi s sv _ =>
        NLReady y Gamma -> forall Psi',
          ESubst x bX tauVX (.var y) arg Psi Psi' ->
          C.Space (renameNLCtx x y Gamma) Psi'
            (Space.subst x (.var y) s) (ValSpace.subst x arg sv))
      (motive_2 := fun Gamma Psi tau tauV _ =>
        NLReady y Gamma -> forall Psi',
          ESubst x bX tauVX (.var y) arg Psi Psi' ->
          C.Ty (renameNLCtx x y Gamma) Psi'
            (Ty.subst x (.var y) tau) (ValTy.subst x arg tauV))
      (motive_3 := fun Gamma Psi b tauV _ =>
        NLReady y Gamma -> forall Psi',
          ESubst x bX tauVX (.var y) arg Psi Psi' ->
          C.TyAt (renameNLCtx x y Gamma) Psi'
            (Basis.subst x (.var y) b) (ValTy.subst x arg tauV))
      (motive_4 := fun Gamma Psi b0 env b1 _ =>
        NLReady y Gamma -> forall Psi',
          ESubst x bX tauVX (.var y) arg Psi Psi' ->
          C.Cob (renameNLCtx x y Gamma) Psi'
            (Basis.subst x (.var y) b0) (ValExpr.subst x arg env)
            (Basis.subst x (.var y) b1))
      (motive_5 := fun Delta Gamma Psi e b v tauV _ =>
        TermReady y Delta Gamma -> forall Psi',
          ESubst x bX tauVX (.var y) arg Psi Psi' ->
          C.Term (renameLCtx x y Delta) (renameNLCtx x y Gamma) Psi'
            (Term.subst x (.var y) e) (Basis.subst x (.var y) b)
            (ValExpr.subst x arg v) (ValTy.subst x arg tauV))
      ?spaceReal ?spaceEmpty ?spaceDual ?spaceKer ?spaceCoker
      ?spaceImg ?spaceCoimg ?spaceTprod ?spaceDsum
      ?tySpace ?tyPi
      ?tyAtSpace ?tyAtFrame
      ?cobInverse ?cobTrans ?cobTprod ?cobDsum ?cobDualStd ?cobImage
      ?cobImageSvds ?cobProjKerCoker ?cobProjImgCoimg ?cobTermsRref
      ?cobRefl ?cobProjKerCokerCod ?cobProjImgCoimgDom
      ?termVarLin ?termVarNlin ?termPromote ?termCob ?termReshape
      ?termScale ?termAdd ?termDsum ?termTprod ?termPinvTStd
      ?termPinvTGpinv ?termPinvDStd ?termPinvDGpinv ?termInnerStd
      ?termEmbedKer ?termEmbedCoker ?termEmbedImg ?termEmbedCoimg
      ?termAppL ?termAppI ?termNllam ?termAppNVal
      ?termFrameReanchor ?termFrameEta ?termLlam ?termLlamReal
      ?termZero ?termRlit $h)
    case spaceReal =>
      intro Gamma Psi ready Psi' hes
      simp only [Space.subst, ValSpace.subst]
      exact .real
    case spaceEmpty =>
      intro Gamma Psi ready Psi' hes
      simp only [Space.subst, ValSpace.subst]
      exact .empty
    case spaceDual =>
      intro Gamma Psi s sv hs h ih ready Psi' hes
      exact .dual (hs.map (svalid_rename hxy ready.notMem))
        (ih ready Psi' hes)
    case spaceKer =>
      intro Gamma Psi s0 s1 e b leev svb hs hb hcompat hsvb he
        ihS ihE ready Psi' hes
      refine .ker (b := Basis.subst x (.var y) b)
        (hs.map (svalid_rename hxy ready.notMem)) ?_ ?_ ?_ ?_
      · rw [Basis.sof_subst, hb]
        rfl
      · exact hcompat.subst x (.var y)
      · rw [Basis.sof_subst]
        exact ihS ready Psi' hes
      · simpa only [renameLCtx_empty] using
          ihE (TermReady.empty ready) Psi' hes
    case spaceCoker =>
      intro Gamma Psi s0 s1 e b leev svb hs hb hcompat hsvb he
        ihS ihE ready Psi' hes
      refine .coker (b := Basis.subst x (.var y) b)
        (hs.map (svalid_rename hxy ready.notMem)) ?_ ?_ ?_ ?_
      · rw [Basis.sof_subst, hb]
        rfl
      · exact hcompat.subst x (.var y)
      · rw [Basis.sof_subst]
        exact ihS ready Psi' hes
      · simpa only [renameLCtx_empty] using
          ihE (TermReady.empty ready) Psi' hes
    case spaceImg =>
      intro Gamma Psi s0 s1 e b leev svb hs hb hcompat hsvb he
        ihS ihE ready Psi' hes
      refine .img (b := Basis.subst x (.var y) b)
        (hs.map (svalid_rename hxy ready.notMem)) ?_ ?_ ?_ ?_
      · rw [Basis.sof_subst, hb]
        rfl
      · exact hcompat.subst x (.var y)
      · rw [Basis.sof_subst]
        exact ihS ready Psi' hes
      · simpa only [renameLCtx_empty] using
          ihE (TermReady.empty ready) Psi' hes
    case spaceCoimg =>
      intro Gamma Psi s0 s1 e b leev svb hs hb hcompat hsvb he
        ihS ihE ready Psi' hes
      refine .coimg (b := Basis.subst x (.var y) b)
        (hs.map (svalid_rename hxy ready.notMem)) ?_ ?_ ?_ ?_
      · rw [Basis.sof_subst, hb]
        rfl
      · exact hcompat.subst x (.var y)
      · rw [Basis.sof_subst]
        exact ihS ready Psi' hes
      · simpa only [renameLCtx_empty] using
          ihE (TermReady.empty ready) Psi' hes
    case spaceTprod =>
      intro Gamma Psi s0 s1 sv0 sv1 hs h0 h1 ih0 ih1 ready Psi' hes
      exact .tprod (hs.map (svalid_rename hxy ready.notMem))
        (ih0 ready Psi' hes) (ih1 ready Psi' hes)
    case spaceDsum =>
      intro Gamma Psi s0 s1 sv0 sv1 hs h0 h1 ih0 ih1 ready Psi' hes
      exact .dsum (hs.map (svalid_rename hxy ready.notMem))
        (ih0 ready Psi' hes) (ih1 ready Psi' hes)
    case tySpace =>
      intro Gamma Psi s sv h ih ready Psi' hes
      exact .space (ih ready Psi' hes)
    case tyPi =>
      intro Gamma Psi b0 tau0 tau1 tauv0 tauv1 k0 k1 ht hb hbv h0 L h1
        ih0 ih1 ready Psi' hes
      have hyPi := freshTy_of_valid ready.notMem (Classical.choice ht)
      have hy0 : y ∉ Ty.fv tau0 := by
        intro hm
        exact hyPi (by simp only [Ty.fv, Finset.mem_union]; exact Or.inl hm)
      refine .piTy (ht.map (tvalid_rename hxy ready.notMem))
        ((Basis.tof_subst x (.var y) _).trans
          (congrArg (Ty.subst x (.var y)) hb))
        (basisValid_rename hxy ready.notMem hbv)
        (ih0 ready Psi' hes)
        (L ∪ {x, y} ∪ EvalCtx.avoid Psi ∪ EvalCtx.avoid Psi') ?_
      intro z hz
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hz
      obtain ⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩ := hz
      have hes' := ESubst.extend (bz := b0) (tv0z := tauv0) hes hzx
        (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
      have hr := ih1 z hzL (ready.insert (Ne.symm hzy) hy0) _ hes'
      rw [renameNLCtx_insert,
        Equiv.swap_apply_of_ne_of_ne hzx hzy,
        Ty.subst_openVar_ne_rename hzx,
        ValTy.subst_openVar_ne_rename hes.lcarg hzx] at hr
      exact hr
    case tyAtSpace =>
      intro Gamma Psi b sv htof hbv hspace ih ready Psi' hes
      refine .space (Basis.tof_space_subst x (.var y) htof)
        (basisValid_rename hxy ready.notMem hbv) ?_
      rw [Basis.sof_subst]
      exact ih ready Psi' hes
    case tyAtFrame =>
      intro Gamma Psi b0 b1 tauv0 tauv1 hbv hdom L hcod ih0 ih1
        ready Psi' hes
      obtain ⟨_, _, k0, k1, htv⟩ := hbv.frame_inv
      have hyPi := freshTy_of_valid ready.notMem (Classical.choice htv)
      have hy0 : y ∉ Ty.fv (Basis.tof b0) := by
        intro hm
        exact hyPi (by simp only [Ty.fv, Finset.mem_union]; exact Or.inl hm)
      refine .frame (basisValid_rename hxy ready.notMem hbv)
        (ih0 ready Psi' hes)
        (L ∪ {x, y} ∪ EvalCtx.avoid Psi ∪ EvalCtx.avoid Psi') ?_
      intro z hz
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hz
      obtain ⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩ := hz
      have hes' := ESubst.extend (bz := b0) (tv0z := tauv0) hes hzx
        (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
      have hr := ih1 z hzL (ready.insert (Ne.symm hzy) hy0) _ hes'
      rw [renameNLCtx_insert,
        Equiv.swap_apply_of_ne_of_ne hzx hzy,
        Basis.subst_openVar_ne_rename hzx,
        ValTy.subst_openVar_ne_rename hes.lcarg hzx] at hr
      simpa only [Basis.tof_subst] using hr
    case cobInverse =>
      intro Gamma Psi b0 b1 leev hb0 hb1 h ih ready Psi' hes
      have hres := C.Cob.inverse
        (basisValid_rename hxy ready.notMem hb0)
        (basisValid_rename hxy ready.notMem hb1)
        (ih ready Psi' hes)
      simpa only [ValExpr.subst] using hres
    case cobTrans =>
      intro Gamma Psi b0 b1 b2 env0 env1 sv hb0 hb2 h0 h1 hsv
        ih0 ih1 ihs ready Psi' hes
      have hres := C.Cob.trans
        (basisValid_rename hxy ready.notMem hb0)
        (basisValid_rename hxy ready.notMem hb2)
        (ih0 ready Psi' hes) (ih1 ready Psi' hes)
        (by rw [Basis.sof_subst]; exact ihs ready Psi' hes)
      simpa only [ValExpr.subst, ValExpr.subst_reshapBase,
        ValSpace.subst] using hres
    case cobTprod =>
      intro Gamma Psi b0 b1 b0' b1' env0 env1 hbS hbT h0 h1
        ih0 ih1 ready Psi' hes
      have hres := C.Cob.tprod
        (basisValid_rename hxy ready.notMem hbS)
        (basisValid_rename hxy ready.notMem hbT)
        (ih0 ready Psi' hes) (ih1 ready Psi' hes)
      simpa only [Basis.subst, ValExpr.subst] using hres
    case cobDsum =>
      intro Gamma Psi b0 b1 b0' b1' env0 env1 hbS hbT h0 h1
        ih0 ih1 ready Psi' hes
      have hres := C.Cob.dsum
        (basisValid_rename hxy ready.notMem hbS)
        (basisValid_rename hxy ready.notMem hbT)
        (ih0 ready Psi' hes) (ih1 ready Psi' hes)
      simpa only [Basis.subst, ValExpr.subst] using hres
    case cobDualStd =>
      intro Gamma Psi b0 leev htof hbS hbT hb1 ih ready Psi' hes
      have hrec := ih ready Psi' hes
      rw [← Basis.std_subst, ← Basis.tof_subst] at hrec
      have hres := C.Cob.dual_std
        (Basis.tof_space_subst x (.var y) htof)
        (basisValid_rename hxy ready.notMem hbS)
        (by
          have hr := basisValid_rename hxy ready.notMem hbT
          rwa [← Basis.std_subst, ← Basis.tof_subst] at hr)
        hrec
      simpa only [Basis.subst, ValExpr.subst, ← Basis.std_subst,
        ← Basis.tof_subst] using hres
    case cobImage =>
      intro Gamma Psi b0 b0' leev hbS hbT hcoker h ih ready Psi' hes
      obtain ⟨s0, s1, e, hc⟩ := hcoker
      have hres := C.Cob.image
        (basisValid_rename hxy ready.notMem hbS)
        (basisValid_rename hxy ready.notMem hbT)
        ⟨Space.subst x (.var y) s0, Space.subst x (.var y) s1,
          Term.subst x (.var y) e, by
            rw [Basis.sof_subst, hc]
            rfl⟩
        (ih ready Psi' hes)
      simpa only [Basis.subst, ValExpr.subst] using hres
    case cobImageSvds =>
      intro Gamma Psi b0 b1 e leev s0 s1 svb hbS hbT hs0 hs1 hb0 hb1
        hsvb he ihs ihe ready Psi' hes
      have hsource := ValExpr.imageCoords_inferSpaceCtx_subst x arg leev svb
      have hres := C.Cob.image_svds
        (basisValid_rename hxy ready.notMem hbS)
        (basisValid_rename hxy ready.notMem hbT)
        (by rw [Basis.sof_subst, hs0])
        (by rw [Basis.sof_subst, hs1])
        ((Basis.isStd_subst x (.var y) b0).symm ▸ hb0)
        ((Basis.isStd_subst x (.var y) b1).symm ▸ hb1)
        (by
          simpa only [Basis.sof, Basis.subst, Space.subst,
            Basis.sof_subst] using ihs ready Psi' hes)
        (ihe (TermReady.empty ready) Psi' hes)
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst, hsource, ValExpr.imageCoords_subst,
        ValSpace.subst, ValExpr.subst_reshapBase, Basis.sof_subst] using hres
    case cobProjKerCoker =>
      intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env2 env3
        sv0 sv1 sv sv' sv0' hbS hbT hs hsofb0 hsofb1
        hsv0 hsv1 hsv hsv' hsv0' hcob hembd hproj
        ihsv0 ihsv1 ihsv ihsv' ihsv0' ihcob ihembd ihproj
        ready Psi' hes
      have hs' : Space.subst x (.var y) s =
          .ker (Space.subst x (.var y) s0) (Space.subst x (.var y) s1)
            (Term.subst x (.var y) e) ∨
          Space.subst x (.var y) s =
          .coker (Space.subst x (.var y) s0) (Space.subst x (.var y) s1)
            (Term.subst x (.var y) e) :=
        hs.imp (fun h => by simp only [h, Space.subst])
          (fun h => by simp only [h, Space.subst])
      have hembd' := ihembd (TermReady.empty ready) Psi' hes
      have hproj' := ihproj (TermReady.empty ready) Psi' hes
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst] at hembd' hproj'
      have hres := C.Cob.proj_ker_coker
        (basisValid_rename hxy ready.notMem hbS)
        (basisValid_rename hxy ready.notMem hbT)
        hs'
        (by rw [Basis.sof_subst, hsofb0])
        (by rw [Basis.sof_subst, hsofb1])
        (by rw [Basis.sof_subst]; exact ihsv0 ready Psi' hes)
        (by rw [Basis.sof_subst]; exact ihsv1 ready Psi' hes)
        (ihsv ready Psi' hes) (ihsv' ready Psi' hes)
        (by rw [Basis.sof_subst]; exact ihsv0' ready Psi' hes)
        (ihcob ready Psi' hes) hembd' hproj'
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst] using hres
    case cobProjImgCoimg =>
      intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env2 env3
        sv0 sv1 sv sv' sv1' hbS hbT hs hsofb0 hsofb1
        hsv0 hsv1 hsv hsv' hsv1' hcob hembd hproj
        ihsv0 ihsv1 ihsv ihsv' ihsv1' ihcob ihembd ihproj
        ready Psi' hes
      have hs' : Space.subst x (.var y) s =
          .img (Space.subst x (.var y) s0) (Space.subst x (.var y) s1)
            (Term.subst x (.var y) e) ∨
          Space.subst x (.var y) s =
          .coimg (Space.subst x (.var y) s0) (Space.subst x (.var y) s1)
            (Term.subst x (.var y) e) :=
        hs.imp (fun h => by simp only [h, Space.subst])
          (fun h => by simp only [h, Space.subst])
      have hembd' := ihembd (TermReady.empty ready) Psi' hes
      have hproj' := ihproj (TermReady.empty ready) Psi' hes
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst] at hembd' hproj'
      have hres := C.Cob.proj_img_coimg
        (basisValid_rename hxy ready.notMem hbS)
        (basisValid_rename hxy ready.notMem hbT)
        hs'
        (by rw [Basis.sof_subst, hsofb0])
        (by rw [Basis.sof_subst, hsofb1])
        (by rw [Basis.sof_subst]; exact ihsv0 ready Psi' hes)
        (by rw [Basis.sof_subst]; exact ihsv1 ready Psi' hes)
        (ihsv ready Psi' hes) (ihsv' ready Psi' hes)
        (by rw [Basis.sof_subst]; exact ihsv1' ready Psi' hes)
        (ihcob ready Psi' hes) hembd' hproj'
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst] using hres
    case cobTermsRref =>
      intro Gamma Psi b b' e es env0 env1 sv tauv hbS hbT hbb hch hsv
        ihbb ihch ihsv ready Psi' hes
      have hch' := ihch (TermReady.empty ready) Psi' hes
      rw [Term.subst_dsumChain, Basis.subst_dsumChain] at hch'
      have hch'' : C.Term ∅ (renameNLCtx x y Gamma) Psi'
          (Term.dsumChain (Term.subst x (.var y) e)
            (es.map (Term.subst x (.var y))))
          (Basis.dsumChain (Basis.subst x (.var y) b')
            (es.map (Term.subst x (.var y))).length)
          (ValExpr.subst x arg env0) (ValTy.subst x arg tauv) := by
        rw [List.length_map]
        exact hch'
      have hres := C.Cob.terms_rref
        (b' := Basis.subst x (.var y) b')
        (e := Term.subst x (.var y) e)
        (es := es.map (Term.subst x (.var y)))
        (basisValid_rename hxy ready.notMem hbS)
        (by
          simpa only [Basis.subst, Space.subst, Basis.sof_subst,
            List.map_cons] using
            basisValid_rename hxy ready.notMem hbT)
        (ihbb ready Psi' hes) hch''
        (by rw [Basis.sof_subst]; exact ihsv ready Psi' hes)
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst, ValSpace.subst,
        Basis.sof_subst, List.map_cons, ValExpr.subst_reshapBase] using hres
    case cobRefl =>
      intro Gamma Psi b sv hb htof hsv ihsv ready Psi' hes
      have hres := C.Cob.refl
        (basisValid_rename hxy ready.notMem hb)
        (Basis.tof_space_subst x (.var y) htof)
        (by rw [Basis.sof_subst]; exact ihsv ready Psi' hes)
      simpa only [ValExpr.subst, ValTy.subst, ValSpace.subst] using hres
    case cobProjKerCokerCod =>
      intro Gamma Psi s0 s1 e s b0 b1 b1' env1 env3 sv0 sv sv'
        hbS hbT hs hsofb0 hsofb1 hsofb1' hsv0 hsv hsv' hembd hproj
        ihsv0 ihsv ihsv' ihembd ihproj ready Psi' hes
      have hs' : Space.subst x (.var y) s =
          .ker (Space.subst x (.var y) s0) (Space.subst x (.var y) s1)
            (Term.subst x (.var y) e) ∨
          Space.subst x (.var y) s =
          .coker (Space.subst x (.var y) s0) (Space.subst x (.var y) s1)
            (Term.subst x (.var y) e) :=
        hs.imp (fun h => by simp only [h, Space.subst])
          (fun h => by simp only [h, Space.subst])
      have hembd' := ihembd (TermReady.empty ready) Psi' hes
      have hproj' := ihproj (TermReady.empty ready) Psi' hes
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst] at hembd' hproj'
      have hres := C.Cob.proj_ker_coker_cod
        (basisValid_rename hxy ready.notMem hbS)
        (basisValid_rename hxy ready.notMem hbT) hs'
        (by rw [Basis.sof_subst, hsofb0])
        (by rw [Basis.sof_subst, hsofb1])
        (by rw [Basis.sof_subst, hsofb1'])
        (by rw [Basis.sof_subst]; exact ihsv0 ready Psi' hes)
        (ihsv ready Psi' hes) (ihsv' ready Psi' hes) hembd' hproj'
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst] using hres
    case cobProjImgCoimgDom =>
      intro Gamma Psi s0 s1 e s b0 b1 b0' env1 env3 sv1 sv sv'
        hbS hbT hs hsofb0 hsofb1 hsofb0' hsv1 hsv hsv' hembd hproj
        ihsv1 ihsv ihsv' ihembd ihproj ready Psi' hes
      have hs' : Space.subst x (.var y) s =
          .img (Space.subst x (.var y) s0) (Space.subst x (.var y) s1)
            (Term.subst x (.var y) e) ∨
          Space.subst x (.var y) s =
          .coimg (Space.subst x (.var y) s0) (Space.subst x (.var y) s1)
            (Term.subst x (.var y) e) :=
        hs.imp (fun h => by simp only [h, Space.subst])
          (fun h => by simp only [h, Space.subst])
      have hembd' := ihembd (TermReady.empty ready) Psi' hes
      have hproj' := ihproj (TermReady.empty ready) Psi' hes
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst] at hembd' hproj'
      have hres := C.Cob.proj_img_coimg_dom
        (basisValid_rename hxy ready.notMem hbS)
        (basisValid_rename hxy ready.notMem hbT) hs'
        (by rw [Basis.sof_subst, hsofb0])
        (by rw [Basis.sof_subst, hsofb1])
        (by rw [Basis.sof_subst, hsofb0'])
        (by rw [Basis.sof_subst]; exact ihsv1 ready Psi' hes)
        (ihsv ready Psi' hes) (ihsv' ready Psi' hes) hembd' hproj'
      simpa only [Basis.subst, ValExpr.subst, ValTy.subst] using hres
    case termVarLin =>
      intro Gamma Psi z b v s tauv hlookup htof hbv hτv ihτv
        ready Psi' hes
      by_cases hzx : z = x
      · subst z
        have hb : b = bX := hes.xonly b v hlookup
        subst b
        have hv : v = .var x tauVX := by
          exact (Option.some_inj.mp (hes.xbind.symm.trans hlookup)).symm
        subst v
        have htof' : Basis.tof (Basis.subst x (.var y) bX) =
            .space (Space.subst x (.var y) s) := by
          rw [Basis.tof_subst, htof]
          rfl
        have hres := C.Term.var_lin
          (opStep_var_lookup_of_cut harg hes.hcut) htof'
          (basisValid_rename hxy ready.notMemN hbv)
          (ihτv ready.toNL Psi' hes)
        rw [renameLCtx_singleton, Equiv.swap_apply_left]
        simpa [Term.subst, ValExpr.subst] using hres
      · have hzy : z ≠ y := by
          intro h
          subst z
          exact ready.notMemL (by simp)
        have htof' : Basis.tof (Basis.subst x (.var y) b) =
            .space (Space.subst x (.var y) s) := by
          rw [Basis.tof_subst, htof]
          rfl
        have hres := C.Term.var_lin (hes.fwd z b v hzx hlookup) htof'
          (basisValid_rename hxy ready.notMemN hbv)
          (ihτv ready.toNL Psi' hes)
        simpa only [renameLCtx_singleton,
          Equiv.swap_apply_of_ne_of_ne hzx hzy,
          Term.subst, if_neg (Ne.symm hzx)] using hres
    case termVarNlin =>
      intro Gamma Psi z b v tauv hlookup hGamma hbv hτv ihτv
        ready Psi' hes
      by_cases hzx : z = x
      · subst z
        have hb : b = bX := hes.xonly b v hlookup
        subst b
        have hv : v = .var x tauVX := by
          exact (Option.some_inj.mp (hes.xbind.symm.trans hlookup)).symm
        subst v
        have hGamma' : (renameNLCtx x y Gamma).lookup y =
            some (Basis.tof (Basis.subst x (.var y) bX)) := by
          rw [renameNLCtx_lookup, Equiv.swap_apply_right, hGamma,
            Basis.tof_subst]
          rfl
        have hres := C.Term.var_nlin
          (opStep_var_lookup_of_cut harg hes.hcut) hGamma'
          (basisValid_rename hxy ready.notMemN hbv)
          (ihτv ready.toNL Psi' hes)
        rw [renameLCtx_empty, Term.subst, if_pos rfl,
          ValExpr.subst, if_pos rfl]
        exact hres
      · have hzy : z ≠ y := by
          intro h
          subst z
          exact ready.notMemN (Finmap.mem_of_lookup_eq_some hGamma)
        have hGamma' : (renameNLCtx x y Gamma).lookup z =
            some (Basis.tof (Basis.subst x (.var y) b)) := by
          rw [renameNLCtx_lookup,
            Equiv.swap_apply_of_ne_of_ne hzx hzy, hGamma,
            Basis.tof_subst]
          rfl
        have hres := C.Term.var_nlin
          (hes.fwd z b v hzx hlookup) hGamma'
          (basisValid_rename hxy ready.notMemN hbv)
          (ihτv ready.toNL Psi' hes)
        simpa only [renameLCtx_empty,
          Equiv.swap_apply_of_ne_of_ne hzx hzy,
          Term.subst, if_neg (Ne.symm hzx)] using hres
    case termPromote =>
      intro Delta Gamma' Gamma'' Psi e b v tauv lin hdDelta hdGamma hfr hleP ht hbv
        hτv he ihτv ihe ready Psi' hes
      have hylinNL : y ∉ lin.toNL := notMem_union_left ready.notMemN
      have hylin : y ∉ lin := by
        intro hy
        exact hylinNL ((LCtx.mem_toNL_iff lin y).mpr hy)
      have hflin : LCtxFresh y lin :=
        NLCtxFresh.toLCtx ready.freshN.of_union_left
      have hfGamma'' : NLCtxFresh y Gamma'' :=
        NLCtxFresh.of_union_right hdGamma ready.freshN
      have hfGamma : NLCtxFresh y Gamma' := NLCtxFresh.of_incl hfGamma'' hleP
      have hdGamma' := renameNLCtx_disjoint (x := x) (y := y) hdGamma
      rw [renameLCtx_toNL] at hdGamma'
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      rw [renameNLCtx_union, renameLCtx_toNL] at ht'
      have hbv' := basisValid_rename hxy ready.notMemN hbv
      rw [renameNLCtx_union, renameLCtx_toNL] at hbv'
      have hτv' := ihτv ready.toNL Psi' hes
      rw [renameNLCtx_union, renameLCtx_toNL] at hτv'
      have he' := ihe ((ready.promoteInner hdDelta hdGamma).nl_smaller hleP) Psi' hes
      rw [renameLCtx_union] at he'
      have hres := C.Term.promote (renameLCtx x y lin)
        (renameLCtx_disjoint hdDelta) hdGamma'
        (promoteFresh_rename hxy hylin ready.freshL hflin hfGamma hfr)
        (NLCtxIncl.rename hleP)
        ht' hbv' hτv' he'
      simpa only [renameNLCtx_union, renameLCtx_toNL] using hres
    case termCob =>
      intro Delta Gamma Psi e b0 b1 v env0 sv tauv htof0 htof1 ht hbv
        hτv he hbb hs ihτv ihe ihbb ihs ready Psi' hes
      have hres := C.Term.cob
        (Basis.tof_space_subst x (.var y) htof0)
        (Basis.tof_space_subst x (.var y) htof1)
        (by
          have hr := ht.map (hasTypeBasis_rename hxy ready.notMemL
            ready.notMemN ready.disjoint)
          simpa only [renameLCtx_union, Term.subst, Basis.subst] using hr)
        (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes)
        (ihe ready Psi' hes) (ihbb ready.toNL Psi' hes)
        (by rw [Basis.sof_subst]; exact ihs ready.toNL Psi' hes)
      simpa only [Term.subst, ValExpr.subst, ValTy.subst,
        ValSpace.subst, ValExpr.subst_reshapBase] using hres
    case termReshape =>
      intro Delta Gamma Psi e b v tauv tauv' ht hbv hτv he
        ihτv ihe ready Psi' hes
      have hres := C.Term.reshape_cob
        (by
          have hr := ht.map (hasTypeBasis_rename hxy ready.notMemL
            ready.notMemN ready.disjoint)
          simpa only [renameLCtx_union, Term.subst, Basis.subst] using hr)
        (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes) (ihe ready Psi' hes)
      simpa only [ValExpr.subst] using hres
    case termScale =>
      intro Delta0 Delta1 Gamma Psi e0 e1 b v0 v1 sv hdisj htof ht hbv
        hτv he0 he1 ihτv ihe0 ihe1 ready Psi' hes
      have hres := C.Term.scale (renameLCtx_disjoint hdisj)
        (Basis.tof_space_subst x (.var y) htof)
        (by
          have hr := ht.map (hasTypeBasis_rename hxy ready.notMemL
            ready.notMemN ready.disjoint)
          simpa only [renameLCtx_union, Term.subst, Basis.subst] using hr)
        (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes)
        (ihe0 ready.of_union_left Psi' hes)
        (ihe1 (ready.of_union_right hdisj) Psi' hes)
      simpa only [renameLCtx_union, Term.subst, Basis.subst,
        ValExpr.subst, ValTy.subst, ValSpace.subst] using hres
    case termAdd =>
      intro Delta Gamma Psi e0 e1 b v0 v1 sv sv0 sv1 htof ht hbv hτv
        he0 he1 ihτv ihe0 ihe1 ready Psi' hes
      have hres := C.Term.add
        (Basis.tof_space_subst x (.var y) htof)
        (by
          have hr := ht.map (hasTypeBasis_rename hxy ready.notMemL
            ready.notMemN ready.disjoint)
          simpa only [renameLCtx_union, Term.subst, Basis.subst] using hr)
        (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes)
        (ihe0 ready Psi' hes) (ihe1 ready Psi' hes)
      simpa only [Term.subst, ValExpr.subst, ValTy.subst,
        ValSpace.subst] using hres
    case termDsum =>
      intro Delta Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 htof0 htof1 ht
        hbv hτv he0 he1 ihτv ihe0 ihe1 ready Psi' hes
      have hres := C.Term.dsumE
        (Basis.tof_space_subst x (.var y) htof0)
        (Basis.tof_space_subst x (.var y) htof1)
        (ht.map (hasTypeBasis_rename hxy ready.notMemL ready.notMemN
          ready.disjoint))
        (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes)
        (ihe0 ready Psi' hes) (ihe1 ready Psi' hes)
      simpa only [Term.subst, Basis.subst, ValExpr.subst,
        ValTy.subst, ValSpace.subst] using hres
    case termTprod =>
      intro Delta0 Delta1 Gamma Psi e0 e1 b0 b1 v0 v1 sv0 sv1 hdisj
        htof0 htof1 ht hbv hτv he0 he1 ihτv ihe0 ihe1 ready Psi' hes
      have hres := C.Term.tprodE (renameLCtx_disjoint hdisj)
        (Basis.tof_space_subst x (.var y) htof0)
        (Basis.tof_space_subst x (.var y) htof1)
        (by
          have hr := ht.map (hasTypeBasis_rename hxy ready.notMemL
            ready.notMemN ready.disjoint)
          simpa only [renameLCtx_union, Term.subst, Basis.subst] using hr)
        (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes)
        (ihe0 ready.of_union_left Psi' hes)
        (ihe1 (ready.of_union_right hdisj) Psi' hes)
      simpa only [renameLCtx_union, Term.subst, Basis.subst,
        ValExpr.subst, ValTy.subst, ValSpace.subst] using hres
    case termPinvTStd =>
      intro Gamma Psi b0 b1 e v sv0 sv1 hb0 hb1 ht hbv hτv he
        ihτv ihe ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst] at ht'
      have he' := ihe ready Psi' hes
      rw [renameLCtx_empty] at he'
      have hres := C.Term.pinvT_std
        ((Basis.isStd_subst x (.var y) b0).symm ▸ hb0)
        ((Basis.isStd_subst x (.var y) b1).symm ▸ hb1)
        ht' (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes) he'
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst, ValExpr.subst, ValTy.subst,
        ValSpace.subst] using hres
    case termPinvTGpinv =>
      intro Gamma Psi b0 b1 e v env0 env1 sv0 sv1 ht hbv hτv he hi0 hi1
        ihτv ihe ihi0 ihi1 ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst] at ht'
      have he' := ihe ready Psi' hes
      have hi0' := ihi0 ready Psi' hes
      have hi1' := ihi1 ready Psi' hes
      simp only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst] at he' hi0' hi1'
      have hres := C.Term.pinvT_gpinv ht'
        (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes) he' hi0' hi1'
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst, ValExpr.subst, ValTy.subst,
        ValSpace.subst] using hres
    case termPinvDStd =>
      intro Gamma Psi b0 b1 e v sv1 hsofb0 hb0 hb1 ht hbv hτv he
        ihτv ihe ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst] at ht'
      have he' := ihe ready Psi' hes
      rw [renameLCtx_empty] at he'
      have hres := C.Term.pinvD_std
        (by rw [Basis.sof_subst, hsofb0]; rfl)
        ((Basis.isStd_subst x (.var y) b0).symm ▸ hb0)
        ((Basis.isStd_subst x (.var y) b1).symm ▸ hb1)
        ht' (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes) he'
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst, ValExpr.subst, ValTy.subst,
        ValSpace.subst] using hres
    case termPinvDGpinv =>
      intro Gamma Psi b0 b1 e v env0 env1 sv1 hsofb0 hb0 ht hbv hτv he
        hi0 hi1 ihτv ihe ihi0 ihi1 ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst] at ht'
      have he' := ihe ready Psi' hes
      have hi0' := ihi0 ready Psi' hes
      have hi1' := ihi1 ready Psi' hes
      simp only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst] at he' hi0' hi1'
      have hres := C.Term.pinvD_gpinv
        (by rw [Basis.sof_subst, hsofb0]; rfl)
        ((Basis.isStd_subst x (.var y) b0).symm ▸ hb0)
        ht' (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes) he' hi0' hi1'
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst, ValExpr.subst, ValTy.subst,
        ValSpace.subst] using hres
    case termInnerStd =>
      intro Gamma Psi b0 s sv hb0 hsof ht hbv hτv hs
        ihτv ihs ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      rw [renameLCtx_empty] at ht'
      have hres := C.Term.inner_std
        ((Basis.isStd_subst x (.var y) b0).symm ▸ hb0)
        (by rw [Basis.sof_subst, hsof]) ht'
        (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes) (ihs ready.toNL Psi' hes)
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ← Basis.sof_subst, ValExpr.subst, ValTy.subst,
        ValSpace.subst] using hres
    case termEmbedKer =>
      intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
        hτv hi0 hi1 he ihτv ihi0 ihi1 ihe ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst, Basis.subst] at ht'
      have hτv' := ihτv ready.toNL Psi' hes
      simp only [Basis.subst, ValTy.subst, ValSpace.subst,
        ValExpr.subst_reshapBase] at hτv'
      have hi0' := ihi0 ready Psi' hes
      have hi1' := ihi1 ready Psi' hes
      have he' := ihe ready Psi' hes
      simp only [renameLCtx_empty, Term.subst, Basis.subst] at hi0' hi1' he'
      have hres := C.Term.embed_ker
        (by rw [Basis.sof_subst, hs0])
        (by rw [Basis.sof_subst, hs1]) ht'
        (basisValid_rename hxy ready.notMemN hbv) hτv'
        hi0' hi1' he'
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ValExpr.subst, ValTy.subst, ValSpace.subst,
        ValExpr.subst_reshapBase] using hres
    case termEmbedCoker =>
      intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
        hτv hi0 hi1 he ihτv ihi0 ihi1 ihe ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst, Basis.subst] at ht'
      have hτv' := ihτv ready.toNL Psi' hes
      simp only [Basis.subst, ValTy.subst, ValSpace.subst,
        ValExpr.subst_reshapBase] at hτv'
      have hi0' := ihi0 ready Psi' hes
      have hi1' := ihi1 ready Psi' hes
      have he' := ihe ready Psi' hes
      simp only [renameLCtx_empty, Term.subst, Basis.subst] at hi0' hi1' he'
      have hres := C.Term.embed_coker
        (by rw [Basis.sof_subst, hs0])
        (by rw [Basis.sof_subst, hs1]) ht'
        (basisValid_rename hxy ready.notMemN hbv) hτv'
        hi0' hi1' he'
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ValExpr.subst, ValTy.subst, ValSpace.subst,
        ValExpr.subst_reshapBase] using hres
    case termEmbedImg =>
      intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
        hτv hi0 hi1 he ihτv ihi0 ihi1 ihe ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst, Basis.subst] at ht'
      have hτv' := ihτv ready.toNL Psi' hes
      simp only [Basis.subst, ValTy.subst, ValSpace.subst,
        ValExpr.subst_reshapBase] at hτv'
      have hi0' := ihi0 ready Psi' hes
      have hi1' := ihi1 ready Psi' hes
      have he' := ihe ready Psi' hes
      simp only [renameLCtx_empty, Term.subst, Basis.subst] at hi0' hi1' he'
      have hres := C.Term.embed_img
        (by rw [Basis.sof_subst, hs0])
        (by rw [Basis.sof_subst, hs1]) ht'
        (basisValid_rename hxy ready.notMemN hbv) hτv'
        hi0' hi1' he'
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ValExpr.subst, ValTy.subst, ValSpace.subst,
        ValExpr.subst_reshapBase] using hres
    case termEmbedCoimg =>
      intro Gamma Psi b0 b1 e v env0 env1 s0 s1 sv0 sv1 hs0 hs1 ht hbv
        hτv hi0 hi1 he ihτv ihi0 ihi1 ihe ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst, Basis.subst] at ht'
      have hτv' := ihτv ready.toNL Psi' hes
      simp only [Basis.subst, ValTy.subst, ValSpace.subst,
        ValExpr.subst_reshapBase] at hτv'
      have hi0' := ihi0 ready Psi' hes
      have hi1' := ihi1 ready Psi' hes
      have he' := ihe ready Psi' hes
      simp only [renameLCtx_empty, Term.subst, Basis.subst] at hi0' hi1' he'
      have hres := C.Term.embed_coimg
        (by rw [Basis.sof_subst, hs0])
        (by rw [Basis.sof_subst, hs1]) ht'
        (basisValid_rename hxy ready.notMemN hbv) hτv'
        hi0' hi1' he'
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ValExpr.subst, ValTy.subst, ValSpace.subst,
        ValExpr.subst_reshapBase] using hres
    case termAppL =>
      intro Delta0 Delta1 Gamma Psi b0 b1 n0 n1 env0 env1 sv svOut
        svMat0 svMat1 svArg hdisj htof1 ht hbv hs hτv h0 h1
        ihs ihτv ih0 ih1 ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_union, Term.subst, Basis.subst,
        ← Basis.sof_subst] at ht'
      have hres := C.Term.appL_lin (renameLCtx_disjoint hdisj)
        (Basis.tof_space_subst x (.var y) htof1) ht'
        (basisValid_rename hxy ready.notMemN hbv)
        (by rw [Basis.sof_subst]; exact ihs ready.toNL Psi' hes)
        (ihτv ready.toNL Psi' hes)
        (ih0 ready.of_union_left Psi' hes)
        (ih1 (ready.of_union_right hdisj) Psi' hes)
      simpa only [renameLCtx_union, Term.subst, Basis.subst,
        ← Basis.sof_subst, ValExpr.subst, ValTy.subst,
        ValSpace.subst, ValExpr.subst_reshapBase] using hres
    case termAppI =>
      intro Delta0 Delta1 Gamma Psi b0 n0 n1 env0 env1 sv svFun svArg
        hdisj ht hs hτv h0 h1 ihs ihτv ih0 ih1 ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_union, Term.subst, Basis.subst,
        ← Basis.sof_subst] at ht'
      have hres := C.Term.appI_lin (renameLCtx_disjoint hdisj) ht'
        (by rw [Basis.sof_subst]; exact ihs ready.toNL Psi' hes)
        (by simpa only [Basis.subst, ValTy.subst, ValSpace.subst] using
          ihτv ready.toNL Psi' hes)
        (ih0 ready.of_union_left Psi' hes)
        (ih1 (ready.of_union_right hdisj) Psi' hes)
      simpa only [renameLCtx_union, Term.subst, Basis.subst,
        ← Basis.sof_subst, ValExpr.subst, ValTy.subst,
        ValSpace.subst] using hres
    case termNllam =>
      intro Gamma Psi b0 b1 tau0 tau1 e tauv0 tauv1 env hb0 hb1 ht hbv
        hτv h0 L he h1 ihτv ih0 ihe ih1 ready Psi' hes
      obtain ⟨_, _, _, _, htv⟩ := hbv.frame_inv
      have hyPi := freshTy_of_valid ready.notMemN (Classical.choice htv)
      have hyDom : y ∉ Ty.fv (Basis.tof b0) := by
        intro hm
        exact hyPi (by simp only [Ty.fv, Finset.mem_union]; exact Or.inl hm)
      have hy0 : y ∉ Ty.fv tau0 := by rwa [hb0] at hyDom
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst, Basis.subst] at ht'
      refine C.Term.nllam
        ((Basis.tof_subst x (.var y) b0).trans
          (congrArg (Ty.subst x (.var y)) hb0))
        ((Basis.tof_subst x (.var y) b1).trans
          (congrArg (Ty.subst x (.var y)) hb1))
        ht' (basisValid_rename hxy ready.notMemN hbv)
        (by simpa only [Basis.subst, ValTy.subst] using
          ihτv ready.toNL Psi' hes)
        (ih0 ready.toNL Psi' hes)
        (L ∪ {x, y} ∪ EvalCtx.avoid Psi ∪ EvalCtx.avoid Psi') ?_ ?_
      · intro z hz
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          not_or] at hz
        obtain ⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩ := hz
        have hes' := ESubst.extend (bz := b0) (tv0z := tauv0) hes hzx
          (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
        have hr := ihe z hzL
          (TermReady.empty (ready.toNL.insert (Ne.symm hzy) hy0)) _ hes'
        rw [renameLCtx_empty, renameNLCtx_insert,
          Equiv.swap_apply_of_ne_of_ne hzx hzy,
          Term.subst_openVar_ne_rename hzx,
          Basis.subst_openVar_ne_rename hzx,
          ValExpr.subst_openVar_ne_rename hes.lcarg hzx,
          ValTy.subst_openVar_ne_rename hes.lcarg hzx] at hr
        exact hr
      · intro z hz
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          not_or] at hz
        obtain ⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩ := hz
        have hes' := ESubst.extend (bz := b0) (tv0z := tauv0) hes hzx
          (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
        have hr := ih1 z hzL (ready.toNL.insert (Ne.symm hzy) hy0) _ hes'
        rw [renameNLCtx_insert,
          Equiv.swap_apply_of_ne_of_ne hzx hzy,
          Basis.subst_openVar_ne_rename hzx,
          ValTy.subst_openVar_ne_rename hes.lcarg hzx] at hr
        exact hr
    case termAppNVal =>
      intro Gamma Psi b0 b1 n0 n1 env0 env1 tauvFun0 tauvFun1 tauvArg
        tauOut ht hbv hτv h0 h1 ihτv ih0 ih1 ready Psi' hes
      have hinst : Basis.subst x (.var y) (Basis.instantiate n1 b1) =
          Basis.instantiate (Term.subst x (.var y) n1)
            (Basis.subst x (.var y) b1) :=
        Basis.subst_openRec x (.var y) Term.lc.var b1 0 n1
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [renameLCtx_empty, Term.subst] at ht'
      rw [hinst] at ht'
      have hbv' := basisValid_rename hxy ready.notMemN hbv
      rw [hinst] at hbv'
      have hτv' := ihτv ready.toNL Psi' hes
      rw [hinst] at hτv'
      have h0' := ih0 ready Psi' hes
      have h1' := ih1 ready Psi' hes
      simp only [renameLCtx_empty, Basis.subst, ValTy.subst] at h0' h1'
      have hres := C.Term.appN_val ht' hbv' hτv' h0' h1'
      simpa only [renameLCtx_empty, Term.subst, ValExpr.subst, hinst,
        ValExpr.subst_applyAt hes.lcarg
          (opStep_inferType_subst hes.lcarg h0.erase hes.htype)
          (opStep_inferType_subst hes.lcarg h1.erase hes.htype)] using hres
    case termFrameReanchor =>
      intro Gamma Psi b0 b0' b1 n0 leev env1 tauv0 tauv0' tauv1 tauv1'
        htof ht hbv hτv h0 hfn hdom L hx hcod
        ihτv ih0 ihfn ihdom ihx ihcod ready Psi' hes
      obtain ⟨_, _, _, _, htv⟩ := hbv.frame_inv
      have hyPi := freshTy_of_valid ready.notMemN (Classical.choice htv)
      have hyDom : y ∉ Ty.fv (Basis.tof b0) := by
        intro hm
        exact hyPi (by simp only [Ty.fv, Finset.mem_union]; exact Or.inl hm)
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      rw [renameLCtx_empty] at ht'
      have hfn' := ihfn ready Psi' hes
      simp only [renameLCtx_empty, Basis.subst, ValTy.subst] at hfn'
      simp only [ValExpr.subst, ValExpr.subst_applyValue
        (opStep_inferType_subst hes.lcarg hfn.erase hes.htype)
        (inferType_subst_reshap hes.lcarg)]
      refine C.Term.frame_reanchor
        (by
          rw [Basis.tof_subst, Basis.tof_subst]
          exact congrArg (Ty.subst x (.var y)) htof)
        ht' (basisValid_rename hxy ready.notMemN hbv)
        (by simpa only [Basis.subst, ValTy.subst] using
          ihτv ready.toNL Psi' hes)
        (ih0 ready.toNL Psi' hes) hfn'
        (ihdom ready.toNL Psi' hes)
        (L ∪ {x, y} ∪ EvalCtx.avoid Psi ∪ EvalCtx.avoid Psi') ?_ ?_
      · intro z hz
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          not_or] at hz
        obtain ⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩ := hz
        have hes' := ESubst.extend (bz := b0) (tv0z := tauv0) hes hzx
          (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
        have hr := ihx z hzL
          (TermReady.empty (ready.toNL.insert (Ne.symm hzy) hyDom)) _ hes'
        have hsrc : Term.subst x (.var y) (.var z) = .var z := by
          simp only [Term.subst, if_neg (Ne.symm hzx)]
        rw [renameLCtx_empty, renameNLCtx_insert,
          Equiv.swap_apply_of_ne_of_ne hzx hzy, hsrc,
          ValExpr.subst_openVar_ne_rename hes.lcarg hzx] at hr
        simpa only [Basis.tof_subst] using hr
      · intro z hz
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          not_or] at hz
        obtain ⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩ := hz
        have hes' := ESubst.extend (bz := b0) (tv0z := tauv0) hes hzx
          (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
        have hr := ihcod z hzL
          (ready.toNL.insert (Ne.symm hzy) hyDom) _ hes'
        rw [renameNLCtx_insert,
          Equiv.swap_apply_of_ne_of_ne hzx hzy,
          Basis.subst_openVar_ne_rename hzx,
          ValTy.subst_openVar_ne_rename hes.lcarg hzx] at hr
        simpa only [Basis.tof_subst] using hr
    case termFrameEta =>
      intro Gamma Psi b0 b1 n0 tauv0 tauv1 env ht hbv hτv h0 L he h1
        ihτv ih0 ihe ih1 ready Psi' hes
      obtain ⟨_, _, _, _, htv⟩ := hbv.frame_inv
      have hyPi := freshTy_of_valid ready.notMemN (Classical.choice htv)
      have hyDom : y ∉ Ty.fv (Basis.tof b0) := by
        intro hm
        exact hyPi (by simp only [Ty.fv, Finset.mem_union]; exact Or.inl hm)
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      rw [renameLCtx_empty] at ht'
      refine C.Term.frame_eta ht'
        (basisValid_rename hxy ready.notMemN hbv)
        (by simpa only [Basis.subst, ValTy.subst] using
          ihτv ready.toNL Psi' hes)
        (ih0 ready.toNL Psi' hes)
        (L ∪ {x, y} ∪ EvalCtx.avoid Psi ∪ EvalCtx.avoid Psi') ?_ ?_
      · intro z hz
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          not_or] at hz
        obtain ⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩ := hz
        have hes' := ESubst.extend (bz := b0) (tv0z := tauv0) hes hzx
          (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
        have hr := ihe z hzL
          (TermReady.empty (ready.toNL.insert (Ne.symm hzy) hyDom)) _ hes'
        have hsrc : Term.subst x (.var y) (.appN n0 (.var z)) =
            .appN (Term.subst x (.var y) n0) (.var z) := by
          simp only [Term.subst, if_neg (Ne.symm hzx)]
        rw [renameLCtx_empty, renameNLCtx_insert,
          Equiv.swap_apply_of_ne_of_ne hzx hzy, hsrc,
          Basis.subst_openVar_ne_rename hzx,
          ValExpr.subst_openVar_ne_rename hes.lcarg hzx,
          ValTy.subst_openVar_ne_rename hes.lcarg hzx] at hr
        simpa only [Basis.tof_subst] using hr
      · intro z hz
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          not_or] at hz
        obtain ⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩ := hz
        have hes' := ESubst.extend (bz := b0) (tv0z := tauv0) hes hzx
          (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
        have hr := ih1 z hzL
          (ready.toNL.insert (Ne.symm hzy) hyDom) _ hes'
        rw [renameNLCtx_insert,
          Equiv.swap_apply_of_ne_of_ne hzx hzy,
          Basis.subst_openVar_ne_rename hzx,
          ValTy.subst_openVar_ne_rename hes.lcarg hzx] at hr
        simpa only [Basis.tof_subst] using hr
    case termLlam =>
      intro Delta Gamma Psi b' b e sv' sv env htof' ht hbv hτv hsv'
        hsv L hfam ihτv ihsv' ihsv ihfam ready Psi' hes
      have hb' : BasisValid Gamma b' := hbv.tprod_inv.1.dual_inv
      have hyS : y ∉ Space.fv (Basis.sof b') :=
        freshSpace_of_valid ready.notMemN
          (Classical.choice (Basis.BasisValid.sof_valid hb'))
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst] at ht'
      have hdof : ValSpace.dofUB (ValSpace.subst x arg sv') =
          ValSpace.dofUB sv' := ValSpace.dofUB_subst x arg sv'
      let envT : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')) → ValExpr :=
        fun i => ValExpr.subst x arg (env (Fin.cast hdof i))
      have hres := C.Term.llam_assemble
        (env := envT)
        (Basis.tof_space_subst x (.var y) htof') ht'
        (basisValid_rename hxy ready.notMemN hbv)
        (by simpa only [Basis.subst, ValTy.subst, ValSpace.subst] using
          ihτv ready.toNL Psi' hes)
        (by rw [Basis.sof_subst]; exact ihsv' ready.toNL Psi' hes)
        (by rw [Basis.sof_subst]; exact ihsv ready.toNL Psi' hes)
        (L ∪ {x, y} ∪ EvalCtx.avoid Psi ∪ EvalCtx.avoid Psi' ∪ Gamma.keys)
        (fun z hz i => by
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
            not_or] at hz
          obtain ⟨⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩, hzG⟩ := hz
          have hzGamma : z ∉ Gamma := by
            intro hm
            exact hzG (Finmap.mem_keys.mpr hm)
          let j : Fin (ValSpace.dofUB sv') := Fin.cast hdof i
          have hes' := ESubst.extend_val (bz := b')
            (w := .delta j.val sv') hes hzx
            (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
            (by simp only [ValExpr.subst, ValExpr.inferSpace])
            (by rfl)
          have hr := ihfam z hzL j
            (ready.insertL (Ne.symm hzy) hyS hzGamma) _ hes'
          rw [renameLCtx_insert,
            Equiv.swap_apply_of_ne_of_ne hzx hzy,
            Term.subst_openVar_ne_rename hzx] at hr
          simpa only [envT, j, Fin.cast, Basis.sof_subst, ValTy.subst,
            ValSpace.subst] using hr)
      have hlist :
          List.ofFn (fun i : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')) =>
            ValExpr.tprodE (.delta i.val (ValSpace.subst x arg sv'))
              (.reshapBase (envT i) (ValSpace.subst x arg sv))) =
          List.ofFn (fun i : Fin (ValSpace.dofUB sv') =>
            ValExpr.tprodE (.delta i.val (ValSpace.subst x arg sv'))
              (.reshapBase (ValExpr.subst x arg (env i))
                (ValSpace.subst x arg sv))) := by
        rw [List.ofFn_congr hdof]
        congr 1
      rw [hlist] at hres
      simpa only [Function.comp_def, Term.subst, Basis.subst,
        envT, ValSpace.dofUB_subst, ← Basis.sof_subst,
        ValExpr.subst_sumAt, ValExpr.subst_reshapBase, ValExpr.subst,
        ValExpr.substList_eq_map, List.map_ofFn, ValSpace.subst,
        ValTy.subst] using hres
    case termLlamReal =>
      intro Delta Gamma Psi b' e sv' env htof' ht hbv hτv hsv'
        L hfam ihτv ihsv' ihfam ready Psi' hes
      have hb' : BasisValid Gamma b' := hbv.dual_inv
      have hyS : y ∉ Space.fv (Basis.sof b') :=
        freshSpace_of_valid ready.notMemN
          (Classical.choice (Basis.BasisValid.sof_valid hb'))
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [Term.subst, Basis.subst, ← Basis.sof_subst, Space.subst] at ht'
      have hdof : ValSpace.dofUB (ValSpace.subst x arg sv') =
          ValSpace.dofUB sv' := ValSpace.dofUB_subst x arg sv'
      let envT : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')) → ValExpr :=
        fun i => ValExpr.subst x arg (env (Fin.cast hdof i))
      have hres := C.Term.llam_assemble_real
        (env := envT)
        (Basis.tof_space_subst x (.var y) htof') ht'
        (basisValid_rename hxy ready.notMemN hbv)
        (by simpa only [Basis.subst, ValTy.subst, ValSpace.subst] using
          ihτv ready.toNL Psi' hes)
        (by rw [Basis.sof_subst]; exact ihsv' ready.toNL Psi' hes)
        (L ∪ {x, y} ∪ EvalCtx.avoid Psi ∪ EvalCtx.avoid Psi' ∪ Gamma.keys)
        (fun z hz i => by
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
            not_or] at hz
          obtain ⟨⟨⟨⟨hzL, hzx, hzy⟩, hzPsi⟩, hzPsi'⟩, hzG⟩ := hz
          have hzGamma : z ∉ Gamma := by
            intro hm
            exact hzG (Finmap.mem_keys.mpr hm)
          let j : Fin (ValSpace.dofUB sv') := Fin.cast hdof i
          have hes' := ESubst.extend_val (bz := b')
            (w := .delta j.val sv') hes hzx
            (EvalCtx.avoid_spec hzPsi).1 ((EvalCtx.avoid_spec hzPsi').1 _)
            (by simp only [ValExpr.subst, ValExpr.inferSpace])
            (by rfl)
          have hr := ihfam z hzL j
            (ready.insertL (Ne.symm hzy) hyS hzGamma) _ hes'
          rw [renameLCtx_insert,
            Equiv.swap_apply_of_ne_of_ne hzx hzy,
            Term.subst_openVar_ne_rename hzx] at hr
          simpa only [envT, j, Fin.cast, Basis.sof_subst, Basis.subst,
            ValTy.subst, ValSpace.subst] using hr)
      have hlist :
          List.ofFn (fun i : Fin (ValSpace.dofUB (ValSpace.subst x arg sv')) =>
            ValExpr.scale
              (.reshapBase (envT i) .real)
              (.delta i.val (ValSpace.subst x arg sv'))) =
          List.ofFn (fun i : Fin (ValSpace.dofUB sv') =>
            ValExpr.scale
              (.reshapBase (ValExpr.subst x arg (env i)) .real)
              (.delta i.val (ValSpace.subst x arg sv'))) := by
        rw [List.ofFn_congr hdof]
        congr 1
      rw [hlist] at hres
      simpa only [Function.comp_def, Term.subst, Basis.subst,
        envT, ValSpace.dofUB_subst, ← Basis.sof_subst, Space.subst,
        ValExpr.subst_sumAt, ValExpr.subst_reshapBase,
        ValExpr.subst, ValExpr.substList_eq_map, List.map_ofFn,
        ValSpace.subst, ValTy.subst] using hres
    case termZero =>
      intro Delta Gamma Psi b sv htof ht hbv hτv hs
        ihτv ihs ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      simp only [Term.subst, ← Basis.sof_subst] at ht'
      have hres := C.Term.zero
        (Basis.tof_space_subst x (.var y) htof)
        ht'
        (basisValid_rename hxy ready.notMemN hbv)
        (ihτv ready.toNL Psi' hes)
        (by rw [Basis.sof_subst]; exact ihs ready.toNL Psi' hes)
      simpa only [Term.subst, ← Basis.sof_subst, ValExpr.subst,
        ValTy.subst, ValSpace.subst] using hres
    case termRlit =>
      intro Gamma Psi r ht hτv ihτv ready Psi' hes
      have ht' := ht.map (hasTypeBasis_rename hxy ready.notMemL
        ready.notMemN ready.disjoint)
      rw [renameLCtx_empty] at ht'
      have hres := C.Term.rlit r ht'
        (by simpa only [Basis.subst, ValTy.subst, ValSpace.subst] using
          ihτv ready.toNL Psi' hes)
      simpa only [renameLCtx_empty, Term.subst, Basis.subst,
        ValExpr.subst, ValTy.subst, ValSpace.subst] using hres
    all_goals
      intros
      first | assumption))

set_option maxHeartbeats 1600000 in
theorem checkedRenameTyAtCore
    {x y : VName} {bX : Basis} {tauVX : ValTy} {arg : ValExpr}
    {Gamma : NLCtx} {Psi Psi' : EvalCtx} {b : Basis} {tauV : ValTy}
    (hxy : x ≠ y) (h : C.TyAt Gamma Psi b tauV)
    (ready : NLReady y Gamma)
    (harg : RenameCutValue arg)
    (hes : ESubst x bX tauVX (.var y) arg Psi Psi') :
    C.TyAt (renameNLCtx x y Gamma) Psi'
      (Basis.subst x (.var y) b) (ValTy.subst x arg tauV) := by
  have core : NLReady y Gamma -> forall Psi'',
      ESubst x bX tauVX (.var y) arg Psi Psi'' ->
      C.TyAt (renameNLCtx x y Gamma) Psi''
        (Basis.subst x (.var y) b) (ValTy.subst x arg tauV) := by
    solve_checked_rename(C.TyAt.rec, h, x, y, bX, tauVX, arg, hxy, harg)
  exact core ready Psi' hes

set_option maxHeartbeats 1600000 in
theorem checkedRenameTermCore
    {x y : VName} {bX : Basis} {tauVX : ValTy} {arg : ValExpr}
    {Delta : LCtx} {Gamma : NLCtx} {Psi Psi' : EvalCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hxy : x ≠ y) (h : C.Term Delta Gamma Psi e b v tauV)
    (ready : TermReady y Delta Gamma)
    (harg : RenameCutValue arg)
    (hes : ESubst x bX tauVX (.var y) arg Psi Psi') :
    C.Term (renameLCtx x y Delta) (renameNLCtx x y Gamma) Psi'
      (Term.subst x (.var y) e) (Basis.subst x (.var y) b)
      (ValExpr.subst x arg v) (ValTy.subst x arg tauV) := by
  have core : TermReady y Delta Gamma -> forall Psi'',
      ESubst x bX tauVX (.var y) arg Psi Psi'' ->
      C.Term (renameLCtx x y Delta) (renameNLCtx x y Gamma) Psi''
        (Term.subst x (.var y) e) (Basis.subst x (.var y) b)
        (ValExpr.subst x arg v) (ValTy.subst x arg tauV) := by
    solve_checked_rename(C.Term.rec, h, x, y, bX, tauVX, arg, hxy, harg)
  exact core ready Psi' hes

/-- The checked nonlinear and linear cofinite-renaming laws, obtained by
specializing the mutual transport above to the variable and delta cuts used
by the public interface. -/
theorem checkedRenameLaws : CheckedRenameLaws where
  tyAt_nl := by
    intro Gamma Psi x y tau0 tauV0 tauV b0 b hwf htau0 htof hbv
      hxGamma hyGamma hxy hes h
    obtain ⟨k, htau0⟩ := htau0
    have htau : TValid Gamma tau0 k := Classical.choice htau0
    have hxTau : x ∉ Ty.fv tau0 := freshTy_of_valid hxGamma htau
    have hyTau : y ∉ Ty.fv tau0 := freshTy_of_valid hyGamma htau
    have ready : NLReady y (Finmap.insert x tau0 Gamma) :=
      (NLReady.ofWF hwf hyGamma).insert (Ne.symm hxy) hyTau
    have hr := checkedRenameTyAtCore hxy h ready
      (Or.inl ⟨y, tauV0, rfl⟩) hes
    have hGamma : renameNLCtx x y Gamma = Gamma :=
      renameNLCtx_eq_self hxGamma hyGamma
        (nlctxFresh_of_ctxWF hwf hxGamma)
    have hTauSub : Ty.subst x (.var y) tau0 = tau0 :=
      Ty.subst_fresh x (.var y) tau0 hxTau
    simpa only [renameNLCtx_insert, Equiv.swap_apply_left, hTauSub,
      hGamma] using hr
  term_nl := by
    intro Gamma Psi x y tau0 tauV0 tauV e b0 b v hwf htau0 htof hbv
      hxGamma hyGamma hxy hes h
    obtain ⟨k, htau0⟩ := htau0
    have htau : TValid Gamma tau0 k := Classical.choice htau0
    have hxTau : x ∉ Ty.fv tau0 := freshTy_of_valid hxGamma htau
    have hyTau : y ∉ Ty.fv tau0 := freshTy_of_valid hyGamma htau
    have readyNL : NLReady y (Finmap.insert x tau0 Gamma) :=
      (NLReady.ofWF hwf hyGamma).insert (Ne.symm hxy) hyTau
    have hr := checkedRenameTermCore hxy h (TermReady.empty readyNL)
      (Or.inl ⟨y, tauV0, rfl⟩) hes
    have hGamma : renameNLCtx x y Gamma = Gamma :=
      renameNLCtx_eq_self hxGamma hyGamma
        (nlctxFresh_of_ctxWF hwf hxGamma)
    have hTauSub : Ty.subst x (.var y) tau0 = tau0 :=
      Ty.subst_fresh x (.var y) tau0 hxTau
    simpa only [renameLCtx_empty, renameNLCtx_insert,
      Equiv.swap_apply_left, hTauSub, hGamma] using hr
  term_delta := by
    intro Delta Gamma Psi x y s sv i tauV e b bout v hwf hs
      hxDelta hyDelta hxGamma hyGamma hxy hbeq hes h
    have hsv : SValid Gamma s := Classical.choice hs
    have hxS : x ∉ Space.fv s := freshSpace_of_valid hxGamma hsv
    have hyS : y ∉ Space.fv s := freshSpace_of_valid hyGamma hsv
    have ready : TermReady y (Finmap.insert x s Delta) Gamma :=
      (TermReady.ofWF hwf hyDelta hyGamma).insertL
        (Ne.symm hxy) hyS hxGamma
    have hr := checkedRenameTermCore hxy h ready
      (Or.inr ⟨i, sv, rfl⟩) hes
    have hDelta : renameLCtx x y Delta = Delta :=
      renameLCtx_eq_self hxDelta hyDelta
        (lctxFresh_of_ctxWF hwf hxGamma)
    have hGamma : renameNLCtx x y Gamma = Gamma :=
      renameNLCtx_eq_self hxGamma hyGamma
        (nlctxFresh_of_ctxWF hwf hxGamma)
    have hSpaceSub : Space.subst x (.var y) s = s :=
      Space.subst_fresh x (.var y) s hxS
    simpa only [renameLCtx_insert, Equiv.swap_apply_left, hSpaceSub,
      hDelta, hGamma] using hr

end RenameProof

end RawCertifiedOperational
end GLang
