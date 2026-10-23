import GLang.Proofs.Value.Presentation.PaperValueCoherentFamily

open GLang GLang.PaperValueDomains

-- Arbitrary dependent types, including higher-order fibres.
example (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w)
    (a b c : (w.denot orc τ).El)
    (hab : Related orc τ w w a b) (hbc : Related orc τ w w b c) :
    Related orc τ w w a c :=
  (coherentFamily_laws orc τ (fun _ : Unit => w) (fun _ _ => hc)).trans
    () () () a b c hab hbc

example (orc : FFSOracleSem) (τ : ValTy) (w : World)
    (hc : TypeCoherent orc τ w w) (v v' v'' : ValValSem)
    (h : RuntimeRelated orc τ w w v v') (h' : RuntimeRelated orc τ w w v' v'') :
    RuntimeRelated orc τ w w v v'' :=
  coherentFamily_runtime_trans orc τ (fun _ : Unit => w) (fun _ _ => hc)
    () () () v v' v'' h h'

#print axioms coherentFamily_laws
#print axioms coherentFamily_fiber
#print axioms coherentFamily_runtime_transport
#print axioms coherentFamily_runtime_trans
