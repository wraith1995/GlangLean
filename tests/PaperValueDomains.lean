import GLang.Value.ResultDomains
open GLang GLang.PaperValueDomains

-- The successful output really lives in the input-selected fibre.
def zerosByLength : Section Nat (fun n => SizedFlatArray n) :=
  .ok (fun n => .ok (SizedFlatArray.zeros n))
example : apply zerosByLength (.ok 3) = .ok ⟨3, SizedFlatArray.zeros 3⟩ := rfl
example : apply zerosByLength (.error .mismatch) = .error .mismatch := rfl
example : apply (.error .mismatch : Section Nat (fun n => SizedFlatArray n))
    (.ok 3) = .error .mismatch := rfl

-- A successfully constructed function can still fail when called.
def failedApplication : Section Nat (fun n => SizedFlatArray n) :=
  .ok (fun _ => .error .mismatch)
example : apply failedApplication (.ok 3) = .error .mismatch := rfl
#print axioms GLang.PaperValueDomains.array_membership
#print axioms GLang.PaperValueDomains.restrict_function
