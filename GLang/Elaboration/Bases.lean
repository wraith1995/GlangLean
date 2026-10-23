import GLang.Elaboration.Existence
import GLang.Elaboration.Supporting.SourceBasisReconstruction

/-! Basis elaboration, and the complete six-part surface-to-internal theorem. -/
namespace GLang.SurfaceElaboration

private theorem basis_space_shape {b : Basis} {s : Surface.Space}
    (h : b.tof.erase = .space s) : b.tof = .space b.sof ∧ b.sof.erase = s := by
  cases ht : b.tof with
  | space S =>
    have hs := Basis.sof_eq_of_tof_eq_space ht
    exact ⟨by simpa only [hs] using ht, by simpa only [ht,Ty.erase,Surface.Ty.space.injEq,hs] using h⟩
  | piTy a c => simp [ht,Ty.erase] at h

private theorem lift_space_shape {E b B s} (hb : BasisLift E b B)
    (ht : b.tof = .space s) : B.tof = .space B.sof ∧ B.sof.erase = s := by
  apply basis_space_shape
  rw [Basis.erase_tof,hb.1,ht]

private theorem elaborateTermList {g E s S} (hw : Metatheory.SourceContextWF ∅ E)
    (hc : ContextEmbedding ∅ g ∅ E) (hvS : SValid E S) (heS : S.erase = s)
    (es : List Surface.Term)
    (hs : ∀ e ∈ es, Nonempty (Surface.HasType ∅ g e (.space s))) :
    ∃ xs : List Term, xs.map Term.erase = es ∧
      ∀ e ∈ xs, Nonempty (HasType ∅ E e (.space S)) := by
  induction es with
  | nil => exact ⟨[],rfl,by simp⟩
  | cons e es ih =>
    obtain ⟨⟨a,T⟩,ha,hT,⟨hv⟩⟩ := elaborateTerm (hs e (by simp)).some hw hc
    have ht := alignResult hw hv (.space hvS) (by simpa only [Ty.erase,heS] using hT)
    obtain ⟨xs,hxs,hvs⟩ := ih (fun e he => hs e (by simp [he]))
    refine ⟨a :: xs, by simp [ha,hxs], ?_⟩
    intro t hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact ⟨ht⟩
    · exact hvs t hmem

/-- Every valid surface basis elaborates, including term families and frames. -/
theorem elaborateBasis {g b} (h : Surface.Basis.BasisValid g b)
    {E : NLCtx} (hw : Metatheory.SourceContextWF ∅ E)
    (hc : ContextEmbedding ∅ g ∅ E) : ∃ B, BasisLift E b B := by
  induction h generalizing E with
  | empty => exact ⟨.empty,rfl,.empty⟩
  | one => exact ⟨.one,rfl,.one⟩
  | dual hb ht ih =>
    obtain ⟨B,hB,hvB⟩ := ih hw hc
    have hh := (lift_space_shape ⟨hB,hvB⟩ ht).1
    exact ⟨.dual B,congrArg Surface.Basis.dual hB,.dual hvB hh⟩
  | dsum ha hb ht hu iha ihb =>
    obtain ⟨A,hA,hvA⟩ := iha hw hc
    obtain ⟨B,hB,hvB⟩ := ihb hw hc
    exact ⟨.dsum A B,congrArg₂ Surface.Basis.dsum hA hB,
      .dsum hvA hvB (lift_space_shape ⟨hA,hvA⟩ ht).1 (lift_space_shape ⟨hB,hvB⟩ hu).1⟩
  | tprod ha hb ht hu iha ihb =>
    obtain ⟨A,hA,hvA⟩ := iha hw hc
    obtain ⟨B,hB,hvB⟩ := ihb hw hc
    exact ⟨.tprod A B,congrArg₂ Surface.Basis.tprod hA hB,
      .tprod hvA hvB (lift_space_shape ⟨hA,hvA⟩ ht).1 (lift_space_shape ⟨hB,hvB⟩ hu).1⟩
  | proj_ker ha hb ht hu he iha ihb =>
    obtain ⟨A,hA,hvA⟩ := iha hw hc
    obtain ⟨B,hB,hvB⟩ := ihb hw hc
    obtain ⟨htA,hsA⟩ := lift_space_shape ⟨hA,hvA⟩ ht
    obtain ⟨htB,hsB⟩ := lift_space_shape ⟨hB,hvB⟩ hu
    obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he.some hw hc
    have hte := alignResult hw hve
      (.space (.tprod (.dual hvA.sof_valid.some) hvB.sof_valid.some))
      (by simpa only [Ty.erase,Space.erase,hsA,hsB] using hT)
    refine ⟨.proj (.ker A.sof B.sof e) A B, ?_,.proj_ker hvA hvB htA htB ⟨hte⟩⟩
    simp only [Basis.erase,Space.erase,hA,hB,he']
  | proj_coker ha hb ht hu he iha ihb =>
    obtain ⟨A,hA,hvA⟩ := iha hw hc
    obtain ⟨B,hB,hvB⟩ := ihb hw hc
    obtain ⟨htA,hsA⟩ := lift_space_shape ⟨hA,hvA⟩ ht
    obtain ⟨htB,hsB⟩ := lift_space_shape ⟨hB,hvB⟩ hu
    obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he.some hw hc
    have hte := alignResult hw hve
      (.space (.tprod (.dual hvA.sof_valid.some) hvB.sof_valid.some))
      (by simpa only [Ty.erase,Space.erase,hsA,hsB] using hT)
    refine ⟨.proj (.coker A.sof B.sof e) A B, ?_,.proj_coker hvA hvB htA htB ⟨hte⟩⟩
    simp only [Basis.erase,Space.erase,hA,hB,he']
  | proj_img ha hb ht hu he iha ihb =>
    obtain ⟨A,hA,hvA⟩ := iha hw hc
    obtain ⟨B,hB,hvB⟩ := ihb hw hc
    obtain ⟨htA,hsA⟩ := lift_space_shape ⟨hA,hvA⟩ ht
    obtain ⟨htB,hsB⟩ := lift_space_shape ⟨hB,hvB⟩ hu
    obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he.some hw hc
    have hte := alignResult hw hve
      (.space (.tprod (.dual hvA.sof_valid.some) hvB.sof_valid.some))
      (by simpa only [Ty.erase,Space.erase,hsA,hsB] using hT)
    refine ⟨.proj (.img A.sof B.sof e) A B, ?_,.proj_img hvA hvB htA htB ⟨hte⟩⟩
    simp only [Basis.erase,Space.erase,hA,hB,he']
  | proj_coimg ha hb ht hu he iha ihb =>
    obtain ⟨A,hA,hvA⟩ := iha hw hc
    obtain ⟨B,hB,hvB⟩ := ihb hw hc
    obtain ⟨htA,hsA⟩ := lift_space_shape ⟨hA,hvA⟩ ht
    obtain ⟨htB,hsB⟩ := lift_space_shape ⟨hB,hvB⟩ hu
    obtain ⟨⟨e,T⟩,he',hT,⟨hve⟩⟩ := elaborateTerm he.some hw hc
    have hte := alignResult hw hve
      (.space (.tprod (.dual hvA.sof_valid.some) hvB.sof_valid.some))
      (by simpa only [Ty.erase,Space.erase,hsA,hsB] using hT)
    refine ⟨.proj (.coimg A.sof B.sof e) A B, ?_,.proj_coimg hvA hvB htA htB ⟨hte⟩⟩
    simp only [Basis.erase,Space.erase,hA,hB,he']
  | @image g b a c e hb hs he ih =>
    obtain ⟨B,hB,hvB⟩ := ih hw hc
    have herase : B.sof.erase = .coker e := by rw [Basis.erase_sof,hB,hs]
    have hvs := hvB.sof_valid.some
    cases hshape : B.sof <;> simp only [hshape,Space.erase,reduceCtorEq] at herase
    rename_i A C e'
    rw [hshape] at hvs
    cases hvs with
    | coker hA hC ht =>
      exact ⟨.image B,congrArg Surface.Basis.image hB,.image hvB hshape ⟨ht⟩⟩
  | terms hb ht hs hes hne ih =>
    obtain ⟨B,hB,hvB⟩ := ih hw hc
    obtain ⟨htB,hsB⟩ := lift_space_shape ⟨hB,hvB⟩ ht
    obtain ⟨es,hes',hves⟩ := elaborateTermList hw hc hvB.sof_valid.some hsB _ hes
    have hne' : es ≠ [] := fun h => hne (hes'.symm.trans (by simp [h]))
    refine ⟨.terms B.sof es B,?_,.terms hvB htB hvB.sof_valid hves hne'⟩
    simp only [Basis.erase,hes',hB]
  | @frame g a b L ha hb iha ihb =>
    obtain ⟨A,hA,hvA⟩ := iha hw hc
    obtain ⟨kA,htA⟩ := hvA.typeValid
    obtain ⟨x,hx⟩ := Infinite.exists_notMem_finset (L ∪ E.keys ∪ b.fv)
    simp only [Finset.mem_union,not_or] at hx
    have hxE : x ∉ E := fun h => hx.1.2 (Finmap.mem_keys.mpr h)
    have hw' := wf_insert_nonlinear hw Finmap.notMem_empty hxE htA
    have heA : A.tof.erase = a.tof := by rw [Basis.erase_tof,hA]
    obtain ⟨B,hB,hvB⟩ := ihb x hx.1.1 hw'
      (hc.insert_nonlinear (x := x) Finmap.notMem_empty heA)
    exact ⟨.frame A (Basis.closeRec 0 x B),
      congrArg₂ Surface.Basis.frame hA (Basis.erase_close_of_open hx.2 hB),
      hvA.close_frame hw hxE hvB⟩

/-- Basis-existence component of the joint theorem. -/
theorem basisExists : BasisExists := by
  intro Δ ε hw b h
  exact elaborateBasis h (wf_empty_linear hw.toSourceContextWF)
    (ContextEmbedding.refl Δ ε).with_empty_linear

/-- All six requested surface-to-internal existence results are proved. -/
theorem complete : Goals :=
  goals_of_judgments spaceExists typeExists subspaceExists termExists basisExists

end GLang.SurfaceElaboration
