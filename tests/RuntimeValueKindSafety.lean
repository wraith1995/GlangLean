import GLang.Proofs.Value.Runtime.RuntimeValueFormation
namespace GLang.RuntimeValue

-- An array cannot be called as a function, irrespective of argument/result type.
example {ε : ValCtx} {a : ValExpr} {τ : ValTy} :
    ¬ Nonempty (ValHasType ε (.appV (.rlit 0) a) τ) := by
  rintro ⟨h⟩
  cases h with
  | appV hf _ _ _ => cases hf

-- Actual operand typing remains independent of the declared source type.
-- The two declared types need only have the same recursive kind.
example : ValHasType ∅
    (.reshap (.rlit 0) (.space .real) (.space .empty)) (.space .real) :=
  .reshap (.rlit 0) (.space .empty) (.space .real)

-- A base-kind declared source cannot reshape to a function-kind target.
example : ¬ Nonempty (ValHasType ∅
    (.reshap (.rlit 0) (.piTy (.space .real) (.space .real)) (.space .real))
    (.piTy (.space .real) (.space .real))) := by
  rintro ⟨h⟩
  cases h with
  | reshap he hs ht => cases hs; cases ht

example : ¬ Nonempty (ValHasType ∅
    (.reshap (.rlit 0)
      (.piTy (.piTy (.space .real) (.space .real)) (.space .real))
      (.piTy (.space .real) (.space .real)))
    (.piTy (.piTy (.space .real) (.space .real)) (.space .real))) := by
  rintro ⟨h⟩
  cases h with
  | reshap _ hs ht =>
    have hk := hs.kind_eq_structural.symm.trans ht.kind_eq_structural
    cases hk

end GLang.RuntimeValue
