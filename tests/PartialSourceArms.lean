import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCobProducts
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCanonical
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceGPinv
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourcePinvConstructors
import GLang.Proofs.Adequacy.Partial.Source.PartialSourceMatrixReadback
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCanonicalBlocks
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceGPinvConstructors
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceGPinvDual
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceEmbeddings
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceEmbeddingShapes
import GLang.Proofs.Adequacy.Partial.Functions.PartialSourceLinearApply
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceCobSpecial
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceProjectionCore
import GLang.Proofs.Adequacy.Partial.LinearAlgebra.PartialSourceProjections
import Lean

open Lean Elab Command
elab "check_partial_source_arms_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``GLang.PartialAdequacy.zero, ``GLang.PartialAdequacy.real,
      ``GLang.PartialAdequacy.add, ``GLang.PartialAdequacy.scale,
      ``GLang.PartialAdequacy.dsum, ``GLang.PartialAdequacy.tprod,
      ``GLang.PartialAdequacy.inner, ``GLang.PartialAdequacy.reshape_space,
      ``GLang.PartialAdequacy.ffs_oracle, ``GLang.PartialAdequacy.ffs_shape,
      ``GLang.PartialAdequacy.space_real, ``GLang.PartialAdequacy.space_empty,
      ``GLang.PartialAdequacy.space_dual, ``GLang.PartialAdequacy.space_dsum,
      ``GLang.PartialAdequacy.space_tprod,
      ``GLang.PartialAdequacy.cob_inverse, ``GLang.PartialAdequacy.cob_trans,
      ``GLang.PartialAdequacy.cob_apply, ``GLang.PartialAdequacy.cob_refl,
      ``GLang.PartialAdequacy.cob_reshape, ``GLang.PartialAdequacy.cob_tprod,
      ``GLang.PartialAdequacy.cob_dsum,
      ``GLang.PartialAdequacy.pinv_tensor, ``GLang.PartialAdequacy.pinv_dual,
      ``GLang.PartialAdequacy.gpinv_tensor,
      ``GLang.PartialAdequacy.canonical_dimensions,
      ``GLang.PartialAdequacy.canonical_transpose_direct,
      ``GLang.PartialAdequacy.embedding_of_columns,
      ``GLang.PartialAdequacy.arm_pinvT_std_facts,
      ``GLang.PartialAdequacy.arm_pinvD_std_facts,
      ``GLang.PartialAdequacy.arm_pinvT_gpinv_facts,
      ``GLang.PartialAdequacy.gpinv_dual,
      ``GLang.PartialAdequacy.trace_witness_matrix,
      ``GLang.PartialAdequacy.trace_inner_matrix,
      ``GLang.PartialAdequacy.eval_vtrans_canonicalUI,
      ``GLang.PartialAdequacy.eval_vtrans_canonicalU,
      ``GLang.PartialAdequacy.eval_vtrans_canonicalV,
      ``GLang.PartialAdequacy.eval_vtrans_canonicalVI,
      ``GLang.PartialAdequacy.arm_embed_kernel,
      ``GLang.PartialAdequacy.arm_embed_kernel_facts,
      ``GLang.PartialAdequacy.arm_embed_cokernel_facts,
      ``GLang.PartialAdequacy.arm_embed_image_facts,
      ``GLang.PartialAdequacy.arm_embed_coimage_facts,
      ``GLang.PartialAdequacy.arm_pinvD_gpinv_facts,
      ``GLang.PartialAdequacy.arm_appL_lin,
      ``GLang.PartialAdequacy.arm_appI_lin,
      ``GLang.PartialAdequacy.arm_cob_dual_std_facts,
      ``GLang.PartialAdequacy.arm_cob_image_facts,
      ``GLang.PartialAdequacy.arm_cob_facts_proj_ker_coker,
      ``GLang.PartialAdequacy.arm_cob_facts_proj_ker_coker_cod,
      ``GLang.PartialAdequacy.arm_cob_facts_proj_img_coimg_dom,
      ``GLang.PartialAdequacy.arm_cob_facts_proj_img_coimg] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected partial source arm axiom {n}: {ax}"
  logInfo "Partial primitive and FFS source-agreement arms use no new axioms."
check_partial_source_arms_axioms
