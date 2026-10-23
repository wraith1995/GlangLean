import GLang.Proofs.Adequacy.Partial.Functions.PartialSourceAbstraction
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceInferred
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceTypeConstructors
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceElementary
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceSpaceConstructors
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCobConstructors
import GLang.Proofs.Value.Partial.PartialValuePrimitiveSized

-- Inspect the actual theorem closures, not only their module dependencies.
#print axioms GLang.PartialAdequacy.Agree.checked
#print axioms GLang.PartialAdequacy.reshape_result
#print axioms GLang.PartialAdequacy.ResultAgree.valueOpenPush
#print axioms GLang.PartialAdequacy.mTyAt_holds
#print axioms GLang.PartialAdequacy.arm_nllam
#print axioms GLang.PartialAdequacy.arm_space_ffs
#print axioms GLang.PartialAdequacy.arm_add
#print axioms GLang.PartialAdequacy.arm_scale
#print axioms GLang.PartialAdequacy.arm_dsumE
#print axioms GLang.PartialAdequacy.arm_tprodE
#print axioms GLang.PartialAdequacy.arm_cob_inverse
#print axioms GLang.PartialAdequacy.arm_cob_trans
#print axioms GLang.PartialAdequacy.arm_cob_tprod
#print axioms GLang.PartialAdequacy.arm_cob_dsum
#print axioms GLang.PartialValueDomains.partial_arrayPrimitive_sized
#print axioms GLang.PartialValueDomains.partial_arrayPrimitive_related_of_eval_eq
