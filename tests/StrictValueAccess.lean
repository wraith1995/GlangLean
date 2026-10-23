import GLang.Proofs.Value.Typing.StrictValueAccess

open GLang

example : FlatArray.empty.readChecked 0 = .error .mismatch := by simp [FlatArray.readChecked, FlatArray.empty]
example : (FlatArray.zeros 2).readChecked 2 = .error .mismatch := by
  exact FlatArray.readChecked_of_ge _ _ (by decide)
example : (FlatArray.ofFn 3 (fun i => (i : ℝ))).readChecked 1 = .ok 1 := by
  rw [FlatArray.readChecked_of_lt _ _ (by decide)]
  simp [FlatArray.ofFn]
example : StrictValueAccess.lookup ([] : List Nat) 0 = .error .mismatch := rfl
example : StrictValueAccess.lookup [17, 23] 1 = .ok 23 := rfl
example : StrictValueAccess.lookup [17, 23] 2 = .error .mismatch := rfl
example (a : FlatArray) (i : Nat) (r : ℝ) (h : a.readChecked i = .ok r) :
    i < a.length := (FlatArray.readChecked_ok_iff a i r).mp h |>.choose
