import GLang.Proofs.Value.Presentation.PaperValueSimpleFundamental
import GLang.Proofs.Value.Presentation.PaperValueOracleExtensionality

/-! Oracle compatibility for evaluated higher-order witnesses in an independently typed fragment. -/
namespace GLang.PaperValueDomains

/-- A witness may use arbitrary nested simple arrows, applications, and
numerical primitives. Related inputs suffice to preserve its current FFS
query. This concerns the actual direct oracle, including nonempty stacks. -/
theorem SimpleHasType.directOracle_related
    {ε : VName → SimpleTy} {Γ : List SimpleTy}
    {e : ValExpr} {s : SimpleSpace}
    (h : SimpleHasType ε Γ e (.space s))
    (w w' : World)
    (hw : w.types = Γ.map SimpleTy.toValTy)
    (hw' : w'.types = Γ.map SimpleTy.toValTy)
    (hEnv : SimpleNamedRelated ε w.env w'.env)
    (hStack : SimpleStackRelated Γ w.values w'.values)
    (p : ValFFSProp) :
    directOracle w.env w.types w.values p s.toValSpace e =
      directOracle w'.env w'.types w'.values p s.toValSpace e := by
  apply directOracle_eq_of_same_query w w' p s.toValSpace e (hw.trans hw'.symm)
  · exact (leafAgreement_shapes _ _ _ (s.oracleAgreement _ _)).1
  · exact base_results_eq_of_related directOracle _ _ _ _ _
      (h.eval_runtime_related directOracle w w' hw hw' hEnv hStack)

/-- The corresponding dependent-space leaf obligation, suitable for a later
mutual typed-query proof. The witness itself is derived, not postulated related. -/
theorem SimpleHasType.ffsLeaf_related
    {ε : VName → SimpleTy} {Γ : List SimpleTy}
    {e : ValExpr} {s : SimpleSpace}
    (h : SimpleHasType ε Γ e (.space s))
    (w w' : World)
    (hw : w.types = Γ.map SimpleTy.toValTy)
    (hw' : w'.types = Γ.map SimpleTy.toValTy)
    (hEnv : SimpleNamedRelated ε w.env w'.env)
    (hStack : SimpleStackRelated Γ w.values w'.values)
    (p : ValFFSProp) :
    SpaceOracleAgreement (directOracle w.env w.types w.values)
      (directOracle w'.env w'.types w'.values) (.ffs p s.toValSpace e) :=
  h.directOracle_related w w' hw hw' hEnv hStack p

end GLang.PaperValueDomains
