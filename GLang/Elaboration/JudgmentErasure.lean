import GLang.Elaboration.ErasureLemmas

namespace GLang
set_option maxRecDepth 4096
mutual
  def SValid.toSurface {ε s} (h : SValid ε s) : Surface.SValid ε.erase s.erase :=
    match h with
    | .empty  => .empty
    | .real  => .real
    | .dual h => .dual h.toSurface
    | .dsum h g => .dsum h.toSurface g.toSurface
    | .tprod h g => .tprod h.toSurface g.toSurface
    | .ker a b h => .ker a.toSurface b.toSurface h.toSurface
    | .coker a b h => .coker a.toSurface b.toSurface h.toSurface
    | .img a b h => .img a.toSurface b.toSurface h.toSurface
    | .coimg a b h => .coimg a.toSurface b.toSurface h.toSurface
  termination_by structural h

  def TValid.toSurface {ε t k} (h : TValid ε t k) : Surface.TValid ε.erase t.erase k :=
    match h with
    | .space h => .space h.toSurface
    | .piTy L ha hb => by
        apply Surface.TValid.piTy L ha.toSurface
        intro y hy
        simpa [NLCtx.erase, sourceMap_insert, Ty.openVar, Surface.Ty.openVar, Ty.erase_openRec, Term.erase] using (hb y hy).toSurface
  termination_by structural h

  def SubType.toSurface {ε s t} (h : SubType ε s t) : Surface.SubType ε.erase s.erase t.erase :=
    match h with
    | .sub_ker a b h => .sub_ker a.toSurface b.toSurface h.toSurface
    | .sub_coker a b h => .sub_coker a.toSurface b.toSurface h.toSurface
    | .sub_img a b h => .sub_img a.toSurface b.toSurface h.toSurface
    | .sub_coimg a b h => .sub_coimg a.toSurface b.toSurface h.toSurface
  termination_by structural h

  def HasType.toSurface {Δ ε e t} (h : HasType Δ ε e t) : Surface.HasType Δ.erase ε.erase e.erase t.erase :=
    match h with
    | .zero h => .zero h.toSurface
    | .inner h => .inner h.toSurface
    | .real_lit r => .real_lit r
    | .smul h hd a b => by
        simpa only [LCtx.erase, NLCtx.erase, sourceMap_union, sourceMap_empty, sourceMap_insert, sourceMap_singleton, Term.erase, Ty.erase, Space.erase, Ty.instantiate, Ty.erase_openRec, Surface.Ty.instantiate] using Surface.HasType.smul h.toSurface (sourceMap_disjoint Space.erase hd) a.toSurface b.toSurface
    | .add h a b => .add h.toSurface a.toSurface b.toSurface
    | .app_linear ha hb hd a b => by
        simpa only [LCtx.erase, NLCtx.erase, sourceMap_union, sourceMap_empty, sourceMap_insert, sourceMap_singleton, Term.erase, Ty.erase, Space.erase, Ty.instantiate, Ty.erase_openRec, Surface.Ty.instantiate] using Surface.HasType.app_linear ha.toSurface hb.toSurface (sourceMap_disjoint Space.erase hd) a.toSurface b.toSurface
    | .app_inner h hd a b => by
        simpa only [LCtx.erase, NLCtx.erase, sourceMap_union, sourceMap_empty, sourceMap_insert, sourceMap_singleton, Term.erase, Ty.erase, Space.erase, Ty.instantiate, Ty.erase_openRec, Surface.Ty.instantiate] using Surface.HasType.app_inner h.toSurface (sourceMap_disjoint Space.erase hd) a.toSurface b.toSurface
    | .app_nonlinear a b => by
        simpa only [LCtx.erase, NLCtx.erase, sourceMap_union, sourceMap_empty, sourceMap_insert, sourceMap_singleton, Term.erase, Ty.erase, Space.erase, Ty.instantiate, Ty.erase_openRec, Surface.Ty.instantiate] using Surface.HasType.app_nonlinear a.toSurface b.toSurface
    | .var_lin  => by
        simpa only [LCtx.erase, NLCtx.erase, sourceMap_union, sourceMap_empty, sourceMap_insert, sourceMap_singleton, Term.erase, Ty.erase, Space.erase, Ty.instantiate, Ty.erase_openRec, Surface.Ty.instantiate] using (Surface.HasType.var_lin (ε := _))
    | .var_nlin h => by
        apply Surface.HasType.var_nlin
        simp [NLCtx.erase, h]
    | .pinv_tensor a b h => .pinv_tensor a.toSurface b.toSurface h.toSurface
    | .pinv_dual a h => .pinv_dual a.toSurface h.toSurface
    | .promote lin hd he hf h => by
        have hnew := Surface.HasType.promote lin.erase (sourceMap_disjoint _ hd)
          (by simpa only [← LCtx.erase_toNL] using sourceMap_disjoint Ty.erase he) hf.toSurface
          (by simpa only [LCtx.erase, sourceMap_union] using h.toSurface)
        simpa only [NLCtx.erase, sourceMap_union, LCtx.erase_toNL] using hnew
    | .dsumE a b h g => .dsumE a.toSurface b.toSurface h.toSurface g.toSurface
    | .tprodE a b hd h g => by
        simpa only [LCtx.erase, NLCtx.erase, sourceMap_union, sourceMap_empty, sourceMap_insert, sourceMap_singleton, Term.erase, Ty.erase, Space.erase, Ty.instantiate, Ty.erase_openRec, Surface.Ty.instantiate] using Surface.HasType.tprodE a.toSurface b.toSurface (sourceMap_disjoint Space.erase hd) h.toSurface g.toSurface
    | .llam_real L h hb => by
        apply Surface.HasType.llam_real L h.toSurface
        intro y hy
        simpa [LCtx.erase, sourceMap_insert, Term.openVar, Surface.Term.openVar, Term.erase_openRec, Term.erase, Ty.erase, Space.erase] using (hb y hy).toSurface
    | .llam_tensor L hn ha hb h => by
        apply Surface.HasType.llam_tensor L (by intro he; cases ‹Space› <;> simp_all [Space.erase]) ha.toSurface hb.toSurface
        intro y hy
        simpa [LCtx.erase, sourceMap_insert, Term.openVar, Surface.Term.openVar, Term.erase_openRec, Term.erase, Ty.erase] using (h y hy).toSurface
    | .embed h => .embed h.toSurface
    | .nllam L ht h => by
        apply Surface.HasType.nllam L ht.toSurface
        intro y hy
        simpa [LCtx.erase, NLCtx.erase, sourceMap_insert, sourceMap_empty, Term.openVar, Ty.openVar, Surface.Term.openVar, Surface.Ty.openVar, Term.erase_openRec, Ty.erase_openRec, Term.erase] using (h y hy).toSurface
  termination_by structural h

end

theorem Basis.BasisValid.toSurface {ε b} (h : Basis.BasisValid ε b) :
    Surface.Basis.BasisValid ε.erase b.erase := by
  induction h with
  | empty => exact .empty
  | one => exact .one
  | dual h he ih =>
      exact .dual ih (by simpa only [Basis.erase_tof, Ty.erase, Basis.erase_sof] using congrArg Ty.erase he)
  | dsum h g he hf ih ig =>
      exact .dsum ih ig
        (by simpa only [Basis.erase_tof, Ty.erase, Basis.erase_sof] using congrArg Ty.erase he)
        (by simpa only [Basis.erase_tof, Ty.erase, Basis.erase_sof] using congrArg Ty.erase hf)
  | tprod h g he hf ih ig =>
      exact .tprod ih ig
        (by simpa only [Basis.erase_tof, Ty.erase, Basis.erase_sof] using congrArg Ty.erase he)
        (by simpa only [Basis.erase_tof, Ty.erase, Basis.erase_sof] using congrArg Ty.erase hf)
  | proj_ker h g he hf ht ih ig =>
      exact .proj_ker ih ig
        (by simpa only [Basis.erase_tof, Ty.erase] using congrArg Ty.erase he)
        (by simpa only [Basis.erase_tof, Ty.erase] using congrArg Ty.erase hf)
        (ht.map fun ht => by simpa [LCtx.erase, Ty.erase, Space.erase] using ht.toSurface)
  | proj_coker h g he hf ht ih ig =>
      exact .proj_coker ih ig
        (by simpa only [Basis.erase_tof, Ty.erase] using congrArg Ty.erase he)
        (by simpa only [Basis.erase_tof, Ty.erase] using congrArg Ty.erase hf)
        (ht.map fun ht => by simpa [LCtx.erase, Ty.erase, Space.erase] using ht.toSurface)
  | proj_img h g he hf ht ih ig =>
      exact .proj_img ih ig
        (by simpa only [Basis.erase_tof, Ty.erase] using congrArg Ty.erase he)
        (by simpa only [Basis.erase_tof, Ty.erase] using congrArg Ty.erase hf)
        (ht.map fun ht => by simpa [LCtx.erase, Ty.erase, Space.erase] using ht.toSurface)
  | proj_coimg h g he hf ht ih ig =>
      exact .proj_coimg ih ig
        (by simpa only [Basis.erase_tof, Ty.erase] using congrArg Ty.erase he)
        (by simpa only [Basis.erase_tof, Ty.erase] using congrArg Ty.erase hf)
        (ht.map fun ht => by simpa [LCtx.erase, Ty.erase, Space.erase] using ht.toSurface)
  | image h he ht ih =>
      exact .image ih
        (by simpa only [Basis.erase_sof, Space.erase] using congrArg Space.erase he)
        (ht.map fun ht => by simpa [LCtx.erase, Ty.erase, Space.erase] using ht.toSurface)
  | terms h he hs ht hn ih =>
      apply Surface.Basis.BasisValid.terms ih
        (by simpa only [Basis.erase_tof, Ty.erase] using congrArg Ty.erase he)
        (hs.map SValid.toSurface)
      · intro e he
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact (ht e' he').map fun ht => by simpa [LCtx.erase, Ty.erase] using ht.toSurface
      · simpa using hn
  | frame L h hb ih ib =>
      apply Surface.Basis.BasisValid.frame L ih
      · intro y hy
        simpa [NLCtx.erase, sourceMap_insert, Basis.openVar, Surface.Basis.openVar,
          Basis.erase_openRec, Term.erase, Basis.erase_tof] using ib y hy

end GLang
