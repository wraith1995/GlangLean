import GLang.Value.Supporting.TotalDimensionSemantics

open GLang

example (orc : FFSOracleSem) (rho : ValEnvSem) :
    denotValB_semS orc rho [] [] (.bvar 0) = .error .mismatch := by
  simp [denotValB_semS, StrictValueAccess.lookup]

example (A : Type) (f : A → Except DimError ValValSem) (i : Nat) :
    ValValSem.readChecked (.fn A f) i = .error .mismatch := rfl

example (i : Nat) :
    ValValSem.readResultChecked (.error .mismatch) i = .error .mismatch := rfl

example : ValValSem.readChecked (.array FlatArray.empty) 0 = .error .mismatch := rfl

example : ValValSem.toElDomainChecked (.space .real 1) (.array FlatArray.empty) =
    .error .mismatch := by
  exact ValValSem.toElChecked_space_of_length_ne _ _ _ (by decide)

example (a : FlatArray) (h : a.length = 1) :
    ValValSem.toElDomainChecked (.space .real 1) (.array a) = .ok a := by
  exact ValValSem.toElChecked_space_of_length _ _ _ h

example (A : Type) (fam : A → ValTypeSem) (v : ValValSem) :
    ValValSem.toElDomainChecked (.piTy A fam) v = ValValSem.toEl (.piTy A fam) v := rfl

/-- The stronger recursive decoder checks each returned fiber. It is deliberately
not substituted for the live higher-order application decoder. -/
example :
    (ValValSem.toElChecked (.piTy FlatArray (fun _ => .space .real 1))
      (.fn FlatArray (fun _ => .ok (.array FlatArray.empty)))).bind
        (fun f => f FlatArray.empty) = .error .mismatch := by
  simp [ValValSem.toElChecked, Except.bind, FlatArray.empty, FlatArray.ofFn]

example :
    (ValValSem.toEl (.piTy FlatArray (fun _ => .space .real 1))
      (.fn FlatArray (fun _ => .ok (.array FlatArray.empty)))).bind
        (fun f => f FlatArray.empty) = .ok FlatArray.empty := by
  simp [ValValSem.toEl, Except.bind]
example (orc : FFSOracleSem) (rho : ValEnvSem) :
    denotValB_semS orc rho [] [] (.delta 2 .real) =
      .ok (.array (FlatArray.zeros 1)) := by
  simp [denotValB_semS, ValExpr.inferSpaceCtx, ValSpace.dof, ValValSem.arrayOf,
    FlatArray.zeros]

example (orc : FFSOracleSem) :
    denotValB_semS orc (fun _ => .fn FlatArray (fun _ => .ok (.array (FlatArray.zeros 1))))
      [] [] (.appV (.var "f" (.piTy (.space .real) (.space .real))) (.zero .empty)) = .error .mismatch := by
  simp [denotValB_semS, ValExpr.inferTypeCtx, ValExpr.inferSpaceCtx, ValTy.domain,
    denotValTyS, ValSpace.dof, ValValSem.toElDomainChecked, ValValSem.toElChecked,
    ValValSem.arrayOf, FlatArray.ofFn]
