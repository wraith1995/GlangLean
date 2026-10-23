import GLang.Proofs.Value.Presentation.PaperValueSimpleOracle

open GLang GLang.PaperValueDomains

-- A genuinely evaluated lambda/application witness in a nonempty stack.
-- No premise states that this witness's results or oracle queries agree.
example (ε : VName → SimpleTy) (s : SimpleSpace) (w w' : World)
    (hw : w.types = [(SimpleTy.space s).toValTy])
    (hw' : w'.types = [(SimpleTy.space s).toValTy])
    (he : SimpleNamedRelated ε w.env w'.env)
    (hs : SimpleStackRelated [.space s] w.values w'.values)
    (p : ValFFSProp) :
    let e := ValExpr.appV
      (.vlam (.space s.toValSpace) (.space s.toValSpace) (.bvar 0))
      (.bvar 0)
    directOracle w.env w.types w.values p s.toValSpace e =
      directOracle w'.env w'.types w'.values p s.toValSpace e := by
  have ht : SimpleHasType ε [.space s]
      (.appV (.vlam (.space s.toValSpace) (.space s.toValSpace) (.bvar 0))
        (.bvar 0)) (.space s) := by
    exact SimpleHasType.app (s := .space s) (t := .space s)
      (SimpleHasType.lam (a := .space s) (b := .space s)
        (SimpleHasType.bvar (n := 0) rfl))
      (SimpleHasType.bvar (n := 0) rfl)
  exact ht.directOracle_related w w' hw hw' he hs p

#print axioms SimpleHasType.directOracle_related
#print axioms SimpleHasType.ffsLeaf_related
