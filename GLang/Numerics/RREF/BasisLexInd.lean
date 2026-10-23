/- Lexicographically earliest maximal independent subsequences.
`HSpace.lexInd` scans left to right, retaining vectors outside the span of
those already selected. The output is independent and spans the input;
independent input sequences are fixed points. -/

import GLang.Annotated.Denotation

namespace GLang

namespace HSpace

/-! ## Implementation -/

/-- Greedy filter helper: scans `vs` left-to-right, building up `acc`
    with each `v` kept iff `v ∉ span acc`. -/
noncomputable def lexIndAux {V : HSpace} (acc : List V.carrier) :
    List V.carrier → List V.carrier
  | [] => acc
  | v :: vs =>
      haveI := Classical.dec (v ∈ Submodule.span ℝ {w | w ∈ acc})
      if v ∈ Submodule.span ℝ {w | w ∈ acc} then
        lexIndAux acc vs
      else
        lexIndAux (acc ++ [v]) vs

noncomputable def lexInd (V : HSpace) (vs : List V.carrier) : List V.carrier :=
  lexIndAux [] vs

/-! ## Set-vs-Fin-range bridge -/

theorem mem_setOf_eq_range_get {V : HSpace} (L : List V.carrier) :
    ({w | w ∈ L} : Set V.carrier)
      = Set.range (fun i : Fin L.length => L.get i) := by
  ext w
  constructor
  · intro hw
    rcases List.mem_iff_get.mp hw with ⟨i, hi⟩
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    rw [← hi]
    exact List.get_mem _ _

theorem span_setOf_mem_eq_span_range_get {V : HSpace} (L : List V.carrier) :
    Submodule.span ℝ {w | w ∈ L}
      = Submodule.span ℝ (Set.range fun i : Fin L.length => L.get i) := by
  rw [mem_setOf_eq_range_get]

/-! ## Span invariant on `lexIndAux`. -/

theorem lexIndAux_span {V : HSpace} :
    ∀ (acc vs : List V.carrier),
      Submodule.span ℝ {w | w ∈ lexIndAux acc vs}
        = Submodule.span ℝ {w | w ∈ acc ++ vs}
  | acc, [] => by simp [lexIndAux]
  | acc, v :: vs => by
      unfold lexIndAux
      split_ifs with hv
      · -- v is in span acc, so span (acc ++ vs) = span (acc ++ v :: vs).
        rw [lexIndAux_span acc vs]
        -- Goal: span {w | w ∈ acc ++ vs} = span {w | w ∈ acc ++ v :: vs}.
        apply le_antisymm
        · -- (acc ++ vs) ⊆ (acc ++ v :: vs) at the set level.
          apply Submodule.span_mono
          intro x hx
          have : x ∈ acc ++ vs := hx
          have : x ∈ acc ∨ x ∈ vs := List.mem_append.mp this
          show x ∈ acc ++ v :: vs
          rw [List.mem_append, List.mem_cons]
          tauto
        · -- (acc ++ v :: vs) ⊆ span (acc ++ vs):
          --   any element is either in acc ⊆ span (acc ++ vs) directly,
          --   = v ∈ span acc ⊆ span (acc ++ vs),
          --   or in vs ⊆ span (acc ++ vs) directly.
          rw [Submodule.span_le]
          intro x hx
          have hx' : x ∈ acc ++ v :: vs := hx
          rcases List.mem_append.mp hx' with hxa | hxvvs
          · exact Submodule.subset_span (show x ∈ acc ++ vs by
              rw [List.mem_append]; exact Or.inl hxa)
          · rcases List.mem_cons.mp hxvvs with hxv | hxvs
            · rw [hxv]
              have h_sub : Submodule.span ℝ {w | w ∈ acc} ≤
                  Submodule.span ℝ {w | w ∈ acc ++ vs} := by
                apply Submodule.span_mono
                intro y hy
                show y ∈ acc ++ vs
                rw [List.mem_append]; exact Or.inl hy
              exact h_sub hv
            · exact Submodule.subset_span (show x ∈ acc ++ vs by
                rw [List.mem_append]; exact Or.inr hxvs)
      · -- v not in span acc; recurse with acc ++ [v].
        rw [lexIndAux_span (acc ++ [v]) vs]
        -- Goal: span {w | w ∈ (acc ++ [v]) ++ vs} = span {w | w ∈ acc ++ v :: vs}.
        congr 1
        ext w
        constructor
        · intro hw
          have hw' : w ∈ (acc ++ [v]) ++ vs := hw
          show w ∈ acc ++ v :: vs
          rcases List.mem_append.mp hw' with hw_av | hw_vs
          · rcases List.mem_append.mp hw_av with hw_a | hw_v
            · rw [List.mem_append]; exact Or.inl hw_a
            · rw [List.mem_append, List.mem_cons]
              rcases List.mem_singleton.mp hw_v with rfl
              exact Or.inr (Or.inl rfl)
          · rw [List.mem_append, List.mem_cons]; exact Or.inr (Or.inr hw_vs)
        · intro hw
          have hw' : w ∈ acc ++ v :: vs := hw
          show w ∈ (acc ++ [v]) ++ vs
          rcases List.mem_append.mp hw' with hw_a | hw_vvs
          · rw [List.mem_append]; exact Or.inl (List.mem_append.mpr (Or.inl hw_a))
          · rcases List.mem_cons.mp hw_vvs with rfl | hw_vs
            · rw [List.mem_append]
              exact Or.inl (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
            · rw [List.mem_append]; exact Or.inr hw_vs

/-! ## LI invariant on `lexIndAux`.

We need to show that if `acc.get` is LI and we extend by `[v]` with
`v ∉ span acc`, then `(acc ++ [v]).get` is LI. We work via `Fin.snoc`. -/

/-- The function `(acc ++ [v]).get` agrees with `Fin.snoc acc.get v`
    transported across `(acc ++ [v]).length = acc.length + 1`. -/
theorem get_append_singleton_eq_snoc {V : HSpace}
    (acc : List V.carrier) (v : V.carrier) (i : Fin (acc.length + 1)) :
    (acc ++ [v]).get (i.cast (by simp : acc.length + 1 = (acc ++ [v]).length))
      = @Fin.snoc acc.length (fun _ => V.carrier)
          (fun j : Fin acc.length => acc.get j) v i := by
  rcases lt_or_ge i.val acc.length with hi | hi
  · -- castSucc case: i = j.castSucc for some j : Fin acc.length.
    have h_lhs : (acc ++ [v]).get (i.cast (by simp : acc.length + 1 = (acc ++ [v]).length))
                  = acc.get ⟨i.val, hi⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem]
      exact List.getElem_append_left hi
    rw [h_lhs]
    -- For RHS: i.val < acc.length means i = (Fin.castLT i hi).castSucc.
    -- snoc f x i.castSucc = f i.
    have h_rhs : @Fin.snoc acc.length (fun _ => V.carrier)
                  (fun j : Fin acc.length => acc.get j) v i = acc.get ⟨i.val, hi⟩ := by
      have h_cs : i = (Fin.castLT i hi).castSucc := by
        ext; simp [Fin.castLT, Fin.castSucc, Fin.castAdd, Fin.castLE]
      conv_lhs => rw [h_cs]
      rw [Fin.snoc_castSucc]
      -- Goal: acc.get (i.castLT hi) = acc.get ⟨i.val, hi⟩.
      -- These are definitionally equal: i.castLT hi = ⟨i.val, hi⟩.
      rfl
    rw [h_rhs]
  · -- last case: i = Fin.last acc.length.
    have hi_eq : i.val = acc.length := by
      have := i.isLt; omega
    have hi_last : i = Fin.last acc.length := by
      ext; simp [Fin.last, hi_eq]
    rw [hi_last]
    -- LHS: (acc ++ [v]).get of (last).cast = (acc ++ [v]).get acc.length = v.
    have h_lhs : (acc ++ [v]).get
        ((Fin.last acc.length).cast (by simp : acc.length + 1 = (acc ++ [v]).length))
                  = v := by
      rw [List.get_eq_getElem]
      rw [List.getElem_append_right (by simp [Fin.last])]
      simp [Fin.last]
    rw [h_lhs]
    -- RHS: snoc f v (last) = v.
    -- Fin.snoc_last : snoc p x (last n) = x; implicit (n, α), explicit (x, p).
    have h_sl : @Fin.snoc acc.length (fun _ => V.carrier)
                  (fun j : Fin acc.length => acc.get j) v (Fin.last acc.length) = v :=
      @Fin.snoc_last acc.length (fun _ => V.carrier) v
                     (fun j : Fin acc.length => acc.get j)
    exact h_sl.symm

/-- LI under a transported family: if `f i = g (i.cast h)` for all `i`,
    then LI of `g` implies LI of `f` (and vice versa). -/
theorem li_of_eq_via_cast {V : HSpace} {n m : Nat} (h : n = m)
    (f : Fin n → V.carrier) (g : Fin m → V.carrier)
    (h_eq : ∀ i : Fin n, f i = g (i.cast h)) :
    LinearIndependent ℝ g → LinearIndependent ℝ f := by
  intro hg
  have h_fun : f = g ∘ (fun i : Fin n => i.cast h) := by funext i; exact h_eq i
  rw [h_fun]
  apply hg.comp
  intro i j hij
  ext
  exact Fin.mk.inj_iff.mp hij

/-- LI of `acc.get` and `v ∉ span acc` ⇒ LI of `(acc ++ [v]).get`. -/
theorem li_append_singleton {V : HSpace} {acc : List V.carrier}
    (h_acc : LinearIndependent ℝ (fun i : Fin acc.length => acc.get i))
    {v : V.carrier} (hv : v ∉ Submodule.span ℝ {w | w ∈ acc}) :
    LinearIndependent ℝ (fun i : Fin (acc ++ [v]).length => (acc ++ [v]).get i) := by
  -- Step 1: LI of Fin.snoc family.
  have h_snoc_li : LinearIndependent ℝ
      (fun i : Fin (acc.length + 1) =>
        @Fin.snoc acc.length (fun _ => V.carrier)
          (fun j : Fin acc.length => acc.get j) v i) := by
    rw [linearIndependent_fin_snoc]
    refine ⟨h_acc, ?_⟩
    rw [← span_setOf_mem_eq_span_range_get]
    exact hv
  -- Step 2: transport via length equality.
  -- We have f := (acc ++ [v]).get and want LI of f.
  -- Define f' on Fin (acc.length + 1) via f' i = f (i.cast _).
  -- get_append_singleton_eq_snoc gives f' = Fin.snoc-family.
  -- So LI of Fin.snoc family ⇒ LI of f'. We then convert LI of f' to LI of f.
  -- Note: f and f' are the same modulo Fin.cast. Use li_of_eq_via_cast with the *reverse* direction.
  have h_len : (acc ++ [v]).length = acc.length + 1 := by simp
  apply li_of_eq_via_cast h_len
      (g := fun i : Fin (acc.length + 1) =>
        @Fin.snoc acc.length (fun _ => V.carrier)
          (fun j : Fin acc.length => acc.get j) v i)
  · intro i
    -- f i = g (i.cast h_len) where f i = (acc ++ [v]).get i
    -- and g j = snoc ... j. Use get_append_singleton_eq_snoc.
    -- get_append_singleton_eq_snoc gives:
    --   (acc ++ [v]).get ((j : Fin (acc.length + 1)).cast _) = snoc f v j
    -- so we apply it with j := i.cast h_len, giving us:
    --   (acc ++ [v]).get ((i.cast h_len).cast _) = snoc f v (i.cast h_len).
    -- The double cast is the identity. Let's spell it out.
    have h_round_trip : (i.cast h_len).cast (by simp : acc.length + 1 = (acc ++ [v]).length) = i := by
      ext; rfl
    have := get_append_singleton_eq_snoc acc v (i.cast h_len)
    rw [h_round_trip] at this
    exact this
  · exact h_snoc_li

theorem lexIndAux_li {V : HSpace} :
    ∀ (acc vs : List V.carrier),
      LinearIndependent ℝ (fun i : Fin acc.length => acc.get i) →
      LinearIndependent ℝ (fun i : Fin (lexIndAux acc vs).length =>
        (lexIndAux acc vs).get i)
  | acc, [], h_acc => by simp only [lexIndAux]; exact h_acc
  | acc, v :: vs, h_acc => by
      haveI : Decidable (v ∈ Submodule.span ℝ {w | w ∈ acc}) := Classical.dec _
      by_cases hv : v ∈ Submodule.span ℝ {w | w ∈ acc}
      · have h_unfold : lexIndAux acc (v :: vs) = lexIndAux acc vs := by
          simp only [lexIndAux, hv, ↓reduceIte]
        rw [h_unfold]
        exact lexIndAux_li acc vs h_acc
      · have h_unfold : lexIndAux acc (v :: vs) = lexIndAux (acc ++ [v]) vs := by
          simp only [lexIndAux, hv, ↓reduceIte]
        rw [h_unfold]
        exact lexIndAux_li (acc ++ [v]) vs (li_append_singleton h_acc hv)

/-! ## Main property theorems -/

theorem lexInd_linearly_independent (V : HSpace) (vs : List V.carrier) :
    LinearIndependent ℝ (fun i : Fin (V.lexInd vs).length => (V.lexInd vs).get i) := by
  unfold lexInd
  apply lexIndAux_li
  have : IsEmpty (Fin ([] : List V.carrier).length) := by
    simp only [List.length_nil]; exact Fin.isEmpty'
  exact linearIndependent_empty_type

theorem lexInd_span_eq (V : HSpace) (vs : List V.carrier) :
    Submodule.span ℝ (Set.range fun i : Fin (V.lexInd vs).length => (V.lexInd vs).get i)
      = Submodule.span ℝ (Set.range fun i : Fin vs.length => vs.get i) := by
  rw [← span_setOf_mem_eq_span_range_get (V.lexInd vs),
      ← span_setOf_mem_eq_span_range_get vs]
  unfold lexInd
  -- lexIndAux_span: span {w | w ∈ lexIndAux [] vs} = span {w | w ∈ [] ++ vs}.
  -- And [] ++ vs = vs.
  simpa using lexIndAux_span [] vs

/-! ### `lexInd_of_li` -/

/-- If `(L₀ ++ L₁).get` is LI, then `L₀.get` is LI. -/
theorem li_prefix {V : HSpace} {L₀ L₁ : List V.carrier}
    (h : LinearIndependent ℝ (fun i : Fin (L₀ ++ L₁).length => (L₀ ++ L₁).get i)) :
    LinearIndependent ℝ (fun i : Fin L₀.length => L₀.get i) := by
  have h_le : L₀.length ≤ (L₀ ++ L₁).length := by simp
  let f : Fin L₀.length → Fin (L₀ ++ L₁).length := fun i =>
    ⟨i.val, lt_of_lt_of_le i.isLt h_le⟩
  have h_inj : Function.Injective f := by
    intro i j hij
    ext
    exact Fin.mk.inj_iff.mp hij
  have h_eq : (fun i : Fin L₀.length => L₀.get i) =
              (fun i : Fin (L₀ ++ L₁).length => (L₀ ++ L₁).get i) ∘ f := by
    funext i
    simp only [Function.comp_apply, f]
    have hi : i.val < L₀.length := i.isLt
    rw [List.get_eq_getElem, List.get_eq_getElem,
        List.getElem_append_left hi]
  rw [h_eq]
  exact h.comp f h_inj

/-- If `acc ++ [w]` is LI (as a Fin-indexed family), then `w ∉ span acc`. -/
theorem not_mem_span_of_li_append {V : HSpace} {acc : List V.carrier} {w : V.carrier}
    (h : LinearIndependent ℝ (fun i : Fin (acc ++ [w]).length => (acc ++ [w]).get i)) :
    w ∉ Submodule.span ℝ {x | x ∈ acc} := by
  -- Transport h to LI of Fin.snoc family, then apply linearIndependent_fin_snoc.
  have h_len : (acc ++ [w]).length = acc.length + 1 := by simp
  -- We have h on `Fin (acc ++ [w]).length`. We want LI on `Fin (acc.length + 1)` of snoc.
  -- Use li_of_eq_via_cast in reverse direction.
  have h_snoc : LinearIndependent ℝ
      (fun i : Fin (acc.length + 1) =>
        @Fin.snoc acc.length (fun _ => V.carrier)
          (fun j : Fin acc.length => acc.get j) w i) := by
    -- LI of (acc ++ [w]).get on Fin (acc ++ [w]).length, transported via Fin.cast h_len.symm.
    apply li_of_eq_via_cast h_len.symm
        (g := fun i : Fin (acc ++ [w]).length => (acc ++ [w]).get i)
    · intro i
      -- want: snoc f w i = (acc ++ [w]).get (i.cast h_len.symm).
      -- get_append_singleton_eq_snoc gives:
      --   (acc ++ [w]).get (i.cast _) = snoc f w i  for i : Fin (acc.length + 1).
      -- So the result is symm.
      exact (get_append_singleton_eq_snoc acc w i).symm
    · exact h
  rw [linearIndependent_fin_snoc] at h_snoc
  rw [span_setOf_mem_eq_span_range_get]
  exact h_snoc.2

theorem lexIndAux_of_li {V : HSpace} :
    ∀ (acc ws : List V.carrier),
      LinearIndependent ℝ (fun i : Fin (acc ++ ws).length => (acc ++ ws).get i) →
      lexIndAux acc ws = acc ++ ws
  | acc, [], _ => by simp [lexIndAux]
  | acc, w :: ws, h_li => by
      show lexIndAux acc (w :: ws) = acc ++ w :: ws
      have h_eq_list : acc ++ w :: ws = (acc ++ [w]) ++ ws := by simp
      have h_li' : LinearIndependent ℝ
          (fun i : Fin ((acc ++ [w]) ++ ws).length => ((acc ++ [w]) ++ ws).get i) := by
        rw [← h_eq_list]; exact h_li
      have h_li_pref : LinearIndependent ℝ
          (fun i : Fin (acc ++ [w]).length => (acc ++ [w]).get i) :=
        li_prefix h_li'
      have h_notin : w ∉ Submodule.span ℝ {x | x ∈ acc} :=
        not_mem_span_of_li_append h_li_pref
      simp only [lexIndAux, h_notin, ↓reduceIte]
      rw [h_eq_list]
      apply lexIndAux_of_li
      rw [← h_eq_list]
      exact h_li

theorem lexInd_of_li (V : HSpace) (vs : List V.carrier)
    (h : LinearIndependent ℝ (fun i : Fin vs.length => vs.get i)) :
    V.lexInd vs = vs := by
  unfold lexInd
  have h' : LinearIndependent ℝ (fun i : Fin ([] ++ vs).length => ([] ++ vs).get i) := by
    simpa using h
  simpa using lexIndAux_of_li [] vs h'

end HSpace

end GLang
