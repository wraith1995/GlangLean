import GLang.Proofs.Value.Runtime.RuntimeValueInfer
import GLang.Proofs.Value.Runtime.RuntimeValueInstantiation
import GLang.Proofs.Value.Runtime.RuntimeValueResultAnnotations
import GLang.Proofs.Value.Binding.ValueBetaOracle

namespace GLang

private def matrix : ValSpace := .tprod .real .real

-- The argument enters the codomain by ordinary dependent substitution.
example : ValExpr.inferType
    (.appV (.vlam (.space matrix) (.space (.ffs .image matrix (.bvar 0)))
      (.zero matrix)) (.zero matrix)) =
    .space (.ffs .image matrix (.zero matrix)) := rfl

-- An argument referring to an outer binder must remain free under a returned function.
example : ValTy.applyCodomain (.bvar 0)
    (.piTy (.space .real) (.space (.ffs .image matrix (.bvar 1)))) =
    .piTy (.space .real) (.space (.ffs .image matrix (.bvar 1))) := rfl

-- Eliminating the function parameter removes its slot from outer references.
example : ValTy.applyCodomain (.rlit 3) (.space (.ffs .image matrix (.bvar 1))) =
    .space (.ffs .image matrix (.bvar 0)) := rfl

example {ε : ValCtx} {f a : ValExpr} {d c : ValTy} {k : ValKind}
    (hf : RuntimeValue.ValHasType ε f (.piTy d c))
    (ha : RuntimeValue.ValHasType ε a d)
    (hc : RuntimeValue.ValTValid ε (ValTy.applyCodomain a c) k) :
    RuntimeValue.ValHasType ε (.appV f a) (ValTy.applyCodomain a c) :=
  .appV hf ha rfl hc

example {ε : ValCtx} {f a : ValExpr} {d c : ValTy} {k : ValKind}
    (hf : RuntimeValue.ValHasType ε f (.piTy d c))
    (ha : RuntimeValue.ValHasType ε a d)
    (hc : RuntimeValue.ValTValid ε (ValTy.applyCodomain a c) k) :
    ValExpr.inferType (.appV f a) = ValTy.applyCodomain a c :=
  RuntimeValue.ValHasType.inferType_eq_of_typed (.appV hf ha rfl hc)

#print axioms ValTy.subst_applyCodomain
#print axioms ValTy.openRec_applyCodomain
#print axioms FFSOracle.substBound_respect

-- Output formation is obtained from function formation and argument typing.
noncomputable example {ε : ValCtx} {a : ValExpr} {d c : ValTy} {kd kc : ValKind}
    (hctx : RuntimeValue.ValCtxValid ε)
    (hp : RuntimeValue.ValTValid ε (.piTy d c) (.arrow kd kc))
    (ha : RuntimeValue.ValHasType ε a d) :
    RuntimeValue.ValTValid ε (ValTy.applyCodomain a c) kc :=
  hp.applyCodomain hctx ha

#print axioms RuntimeValue.ValHasType.resultAnnotations
#print axioms RuntimeValue.ValTValid.applyCodomain

end GLang
