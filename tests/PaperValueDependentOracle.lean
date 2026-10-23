import GLang.Proofs.Value.Presentation.PaperValueDependentOracle

open GLang GLang.PaperValueDomains

-- Two genuinely nested dependent dimensions, using original typing rules.
-- No global oracle agreement or witness-evaluation premise is supplied.
example (ε : ValCtx) (ρ ρ' : ValEnvSem)
    (hr : EnvironmentsRelated directOracle ε ρ ρ') (x y : VName)
    (p r : ValFFSProp)
    (hx : ε.lookup x = some (.space (.tprod .real .real)))
    (hy : ε.lookup y = some (.space (.tprod
      (.ffs p (.tprod .real .real) (.var x (.space (.tprod .real .real)))) .real))) :
    let s := ValSpace.ffs p (.tprod .real .real) (.var x (.space (.tprod .real .real)))
    SpaceOracleAgreement (directOracle ρ [] []) (directOracle ρ' [] [])
      (.ffs r (.tprod s .real) (.var y (.space (.tprod s .real)))) := by
  let s := ValSpace.ffs p (.tprod .real .real) (.var x (.space (.tprod .real .real)))
  have hs : GLang.ValSValid ε s := .ffs .real .real (.var hx)
  apply GLang.PaperValueDomains.ValSValid.oracleAgreement_namedQueries
    (GLang.ValSValid.ffs hs .real (.var hy)) ρ ρ' hr
  intro q hq
  simp [spaceQueries, s] at hq
  rcases hq with rfl | rfl
  · exact ⟨y, rfl⟩
  · exact ⟨x, rfl⟩

#print axioms original_ffs_oracle_step
#print axioms GLang.PaperValueDomains.ValSValid.query_typed
#print axioms GLang.PaperValueDomains.ValSValid.oracleAgreement_namedQueries
