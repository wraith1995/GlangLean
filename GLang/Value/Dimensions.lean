import GLang.Value.Supporting.TotalDimensionSemantics

/-! Shape and dimension interpretation with explicit dimension errors. -/
namespace GLang

abbrev PartialFFSOracle := ValFFSProp → ValSpace → ValExpr → Except DimError Nat

mutual
  def ValSpace.shpOfPartial (orc : PartialFFSOracle) : ValSpace → Except DimError (List Nat)
    | .empty => .ok [0]
    | .real => .ok [1]
    | .dsum a b => do
        let m ← a.dofPartial orc
        let n ← b.dofPartial orc
        pure [m + n]
    | .tprod a b => do
        let m ← a.dofPartial orc
        let n ← b.dofPartial orc
        pure [m, n]
    | .ffs p s e => do
        let n ← orc p s e
        pure [n]

  def ValSpace.dofPartial (orc : PartialFFSOracle) (s : ValSpace) : Except DimError Nat := do
    let shape ← s.shpOfPartial orc
    pure (shape.foldr (· * ·) 1)
end

theorem ValSpace.shpOfPartial_success (orc : PartialFFSOracle) (total : FFSOracle)
    (h : ∀ p s e n, orc p s e = .ok n → total p s e = n) :
    ∀ (s : ValSpace) (sh : List Nat), s.shpOfPartial orc = .ok sh → s.shpOf total = sh := by
  intro s
  cases s with
  | empty => intro sh hs; simpa [shpOfPartial] using hs
  | real => intro sh hs; simpa [shpOfPartial] using hs
  | dsum a b =>
      have ia := shpOfPartial_success orc total h a
      have ib := shpOfPartial_success orc total h b
      intro sh hs
      simp only [shpOfPartial, dofPartial] at hs
      cases ha : shpOfPartial orc a <;> cases hb : shpOfPartial orc b <;>
        simp [ha, hb, bind, pure, Except.bind, Except.pure] at hs
      subst sh
      simp only [shpOf, dof, ia _ ha, ib _ hb]
  | tprod a b =>
      have ia := shpOfPartial_success orc total h a
      have ib := shpOfPartial_success orc total h b
      intro sh hs
      simp only [shpOfPartial, dofPartial] at hs
      cases ha : shpOfPartial orc a <;> cases hb : shpOfPartial orc b <;>
        simp [ha, hb, bind, pure, Except.bind, Except.pure] at hs
      subst sh
      simp only [shpOf, dof, ia _ ha, ib _ hb]
  | ffs p s e =>
      intro sh hs
      cases he : orc p s e <;> simp [shpOfPartial, he] at hs
      subst sh
      simp only [shpOf, h _ _ _ _ he]

termination_by s => sizeOf s

theorem ValSpace.dofPartial_success (orc : PartialFFSOracle) (total : FFSOracle)
    (h : ∀ p s e n, orc p s e = .ok n → total p s e = n)
    (s : ValSpace) (n : Nat) (hn : s.dofPartial orc = .ok n) : s.dof total = n := by
  cases hs : s.shpOfPartial orc <;> simp [dofPartial, hs] at hn
  subst n
  simp only [dof, shpOfPartial_success orc total h s _ hs]

/-- Strict finite-matrix rank: parent-shape failures, operand failures,
non-matrices, and wrong array lengths remain errors. -/
noncomputable def ffsOperandRankPartial (shape : Except DimError (List Nat))
    (operand : Except DimError ValValSem) : Except DimError Nat :=
  match shape with
  | .error e => .error e
  | .ok sh =>
    match operand with
    | .error e => .error e
    | .ok v =>
      match sh, v with
      | [m, n], .array a =>
          if a.length = m * n then .ok (denotAsMatrix m n a.get).rank
          else .error .mismatch
      | _, _ => .error .mismatch

@[simp] theorem ffsOperandRankPartial_error (sh : List Nat) (err : DimError) :
    ffsOperandRankPartial (.ok sh) (.error err) = .error err := rfl

@[simp] theorem ffsOperandRankPartial_shape_error (err : DimError)
    (operand : Except DimError ValValSem) :
    ffsOperandRankPartial (.error err) operand = .error err := rfl

/-- The four-fundamental-space query propagates rank failure unchanged. -/
noncomputable def ffsDimensionPartial (p : ValFFSProp)
    (shape : Except DimError (List Nat)) (operand : Except DimError ValValSem) :
    Except DimError Nat := do
  let sh ← shape
  let rank ← ffsOperandRankPartial (.ok sh) operand
  pure (ffsDim p sh rank)

@[simp] theorem ffsDimensionPartial_error (p : ValFFSProp) (sh : List Nat) (err : DimError) :
    ffsDimensionPartial p (.ok sh) (.error err) = .error err := rfl

/-- Wrong flat storage is rejected before computing the matrix rank. -/
theorem ffsOperandRankPartial_wrong_length (m n : Nat) (a : FlatArray)
    (ha : a.length ≠ m * n) :
    ffsOperandRankPartial (.ok [m, n]) (.ok (.array a)) = .error .mismatch := by
  simp only [ffsOperandRankPartial, if_neg ha]

/-- Exact matrix storage recovers the usual finite-matrix rank. -/
theorem ffsOperandRankPartial_matrix (m n : Nat) (a : FlatArray)
    (ha : a.length = m * n) :
    ffsOperandRankPartial (.ok [m, n]) (.ok (.array a)) =
      .ok (denotAsMatrix m n a.get).rank := by
  simp only [ffsOperandRankPartial, if_pos ha]

theorem ffsDimensionPartial_matrix (p : ValFFSProp) (m n : Nat) (a : FlatArray)
    (ha : a.length = m * n) :
    ffsDimensionPartial p (.ok [m, n]) (.ok (.array a)) =
      .ok (ffsDim p [m, n] (denotAsMatrix m n a.get).rank) := by
  simp [ffsDimensionPartial, ffsOperandRankPartial, ha, bind, pure, Except.bind, Except.pure]

/-- Successful shape interpretation determines dimension by its product. -/
theorem ValSpace.dofPartial_of_shape (orc : PartialFFSOracle) (s : ValSpace)
    (sh : List Nat) (h : s.shpOfPartial orc = .ok sh) :
    s.dofPartial orc = .ok (sh.foldr (· * ·) 1) := by
  simp [dofPartial, h]

/-- Shape failure cannot be converted to a zero dimension. -/
theorem ValSpace.dofPartial_of_error (orc : PartialFFSOracle) (s : ValSpace)
    (err : DimError) (h : s.shpOfPartial orc = .error err) :
    s.dofPartial orc = .error err := by
  simp [dofPartial, h]

end GLang
