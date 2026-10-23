import GLang.Proofs.Adequacy.Raw.RawAgreement
import GLang.Proofs.Adequacy.Foundations.FvIrrel

/-!
# Environment transport for raw agreement

These are the source- and value-environment weakening facts needed to carry a
raw consistency entry from its creation prefix to a later telescope.  The
higher-order clauses deliberately retain the identical untyped runtime
argument; no decode/re-encode round trip occurs.
-/

namespace GLang

/-! ## Source-environment transport -/

/-- `srcShp` reads a source environment only at the free variables of the
source space. -/
private theorem rawSrcShp_agree {sigma1 sigma2 : DEnv} (Ds : List DVal) :
    forall (s : Space), sigma1.AgreeOn sigma2 (Space.fv s) ->
      srcShp sigma1 Ds s = srcShp sigma2 Ds s
  | .empty, _ => rfl
  | .real, _ => rfl
  | .dual s, h => by
      simp only [Space.fv] at h
      simp only [srcShp]
      exact rawSrcShp_agree Ds s h
  | .dsum s0 s1, h => by
      simp only [Space.fv] at h
      simp only [srcShp]
      rw [denotSpaceAux_agree Ds s0 h.of_union_left,
        denotSpaceAux_agree Ds s1 h.of_union_right]
  | .tprod s0 s1, h => by
      simp only [Space.fv] at h
      simp only [srcShp]
      rw [denotSpaceAux_agree Ds s0 h.of_union_left,
        denotSpaceAux_agree Ds s1 h.of_union_right]
  | .ker s0 s1 e, h => by
      simp only [srcShp]
      rw [denotSpaceAux_agree Ds (.ker s0 s1 e) h]
  | .coker s0 s1 e, h => by
      simp only [srcShp]
      rw [denotSpaceAux_agree Ds (.coker s0 s1 e) h]
  | .img s0 s1 e, h => by
      simp only [srcShp]
      rw [denotSpaceAux_agree Ds (.img s0 s1 e) h]
  | .coimg s0 s1 e, h => by
      simp only [srcShp]
      rw [denotSpaceAux_agree Ds (.coimg s0 s1 e) h]

/-- Raw agreement is invariant under source environments agreeing on the free
variables of the source type. -/
theorem RawAgree.agreeOn {orc : FFSOracleSem} {sigma1 sigma2 : DEnv}
    (rho : ValEnvSem) :
    forall (tau : Ty) (tauv : ValTy) (Ds : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (B : BasisDenot)
      (x : DVal) (yv : ValValSem),
      sigma1.AgreeOn sigma2 (Ty.fv tau) ->
      (RawAgree orc sigma1 rho Ds Gv Dv tau tauv B x yv <->
        RawAgree orc sigma2 rho Ds Gv Dv tau tauv B x yv)
  | .space s, .space sv, Ds, Gv, Dv, B, x, .array a, h => by
      simp only [Ty.fv] at h
      simp only [RawAgree, LegacyAgree]
      rw [denotSpaceAux_agree Ds s h]
  | .space _, .space _, _, _, _, _, _, .fn _ _, _ => by
      simp only [RawAgree]
  | .piTy tau0 tau1, .piTy tauv0 tauv1, Ds, Gv, Dv, B, x, yv, h => by
      simp only [Ty.fv] at h
      simp only [RawAgree]
      rw [denotTyAux_agree Ds tau0 h.of_union_left]
      exact exists_congr fun f => and_congr Iff.rfl
        (forall_congr' fun x' => forall_congr' fun argVal =>
          forall_congr' fun arg =>
            imp_congr Iff.rfl
              (imp_congr
                (RawAgree.agreeOn rho tau0 tauv0 Ds Gv Dv
                  B.domainBasis _ argVal h.of_union_left)
                (exists_congr fun out => and_congr Iff.rfl
                  (RawAgree.agreeOn rho tau1 tauv1
                    ((denotTyAux sigma2 Ds tau0).embed x' :: Ds)
                    (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')
                    (x.applyEl x') out h.of_union_right))))
  | .space _, .piTy _ _, _, _, _, _, _, _, _ => by
      simp only [RawAgree]
  | .piTy _ _, .space _, _, _, _, _, _, _, _ => by
      simp only [RawAgree]

/-- Exact-basis dimensions have the same source free-variable footprint as
raw agreement. -/
theorem RawAgreeDimsAt.agreeOn {orc : FFSOracleSem}
    {sigma1 sigma2 : DEnv} (rho : ValEnvSem) :
    forall (tau : Ty) (tauv : ValTy) (Ds : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (B : BasisDenot),
      sigma1.AgreeOn sigma2 (Ty.fv tau) ->
      (RawAgreeDimsAt orc sigma1 rho Ds Gv Dv tau tauv B <->
        RawAgreeDimsAt orc sigma2 rho Ds Gv Dv tau tauv B)
  | .space s, .space sv, Ds, Gv, Dv, B, h => by
      simp only [Ty.fv] at h
      simp only [RawAgreeDimsAt]
      rw [rawSrcShp_agree Ds s h]
  | .piTy tau0 tau1, .piTy tauv0 tauv1, Ds, Gv, Dv, B, h => by
      simp only [Ty.fv] at h
      simp only [RawAgreeDimsAt]
      rw [denotTyAux_agree Ds tau0 h.of_union_left]
      exact and_congr
        (RawAgreeDimsAt.agreeOn rho tau0 tauv0 Ds Gv Dv
          B.domainBasis h.of_union_left)
        (forall_congr' fun x' => forall_congr' fun argVal =>
          forall_congr' fun arg =>
            imp_congr Iff.rfl
              (imp_congr
                (RawAgree.agreeOn rho tau0 tauv0 Ds Gv Dv
                  B.domainBasis _ argVal h.of_union_left)
                (RawAgreeDimsAt.agreeOn rho tau1 tauv1
                  ((denotTyAux sigma2 Ds tau0).embed x' :: Ds)
                  (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')
                  h.of_union_right)))
  | .space _, .piTy _ _, _, _, _, _, _ => by
      simp only [RawAgreeDimsAt]
  | .piTy _ _, .space _, _, _, _, _, _ => by
      simp only [RawAgreeDimsAt]

/-! ## Value-environment transport -/

/-- Updating a name outside a value type's free variables does not affect raw
agreement.  The Pi case preserves `argVal` verbatim. -/
theorem RawAgree.update_of_not_mem_fv {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc) (sigma : DEnv) (rho : ValEnvSem)
    (y : VName) (w : ValValSem) :
    forall (tau : Ty) (tauv : ValTy) (Ds : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (B : BasisDenot)
      (x : DVal) (yv : ValValSem),
      ValTyCtxFresh y Gv -> y ∉ ValTy.fv tauv ->
      (RawAgree orc sigma (rho.update y w) Ds Gv Dv tau tauv B x yv <->
        RawAgree orc sigma rho Ds Gv Dv tau tauv B x yv)
  | .space s, .space sv, Ds, Gv, Dv, B, x, .array a, hGv, hy => by
      simp only [RawAgree]
      exact LegacyAgree.update_of_not_mem_fv hirr sigma rho y w
        (.space s) (.space sv) Ds Gv Dv B x (.array a) hGv hy
  | .space _, .space _, _, _, _, _, _, .fn _ _, _, _ => by
      simp only [RawAgree]
  | .piTy tau0 tau1, .piTy tauv0 tauv1, Ds, Gv, Dv, B, x, yv, hGv, hy => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      simp only [RawAgree]
      rw [denotValTyS_update_of_not_mem_fv hirr rho y w tauv0 Gv Dv hGv hy.1]
      exact exists_congr fun f => and_congr Iff.rfl
        (forall_congr' fun x' => forall_congr' fun argVal =>
          forall_congr' fun arg =>
            imp_congr Iff.rfl
              (imp_congr
                (RawAgree.update_of_not_mem_fv hirr sigma rho y w
                  tau0 tauv0 Ds Gv Dv B.domainBasis _ argVal hGv hy.1)
                (exists_congr fun out => and_congr Iff.rfl
                  (RawAgree.update_of_not_mem_fv hirr sigma rho y w
                    tau1 tauv1
                    ((denotTyAux sigma Ds tau0).embed x' :: Ds)
                    (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')
                    (x.applyEl x') out (ValTyCtxFresh.cons hy.1 hGv) hy.2))))
  | .space _, .piTy _ _, _, _, _, _, _, _, _, _ => by
      simp only [RawAgree]
  | .piTy _ _, .space _, _, _, _, _, _, _, _, _ => by
      simp only [RawAgree]

/-- Value-environment transport for exact-basis raw dimensions. -/
theorem RawAgreeDimsAt.update_of_not_mem_fv {orc : FFSOracleSem}
    (hirr : OracleFvIrrel orc) (sigma : DEnv) (rho : ValEnvSem)
    (y : VName) (w : ValValSem) :
    forall (tau : Ty) (tauv : ValTy) (Ds : List DVal)
      (Gv : List ValTy) (Dv : List ValValSem) (B : BasisDenot),
      ValTyCtxFresh y Gv -> y ∉ ValTy.fv tauv ->
      (RawAgreeDimsAt orc sigma (rho.update y w) Ds Gv Dv tau tauv B <->
        RawAgreeDimsAt orc sigma rho Ds Gv Dv tau tauv B)
  | .space s, .space sv, Ds, Gv, Dv, B, hGv, hy => by
      simp only [ValTy.fv] at hy
      simp only [RawAgreeDimsAt]
      rw [ValSpace.shpOf_update_of_not_mem_fv hirr rho y w Gv Dv hGv sv hy]
  | .piTy tau0 tau1, .piTy tauv0 tauv1, Ds, Gv, Dv, B, hGv, hy => by
      simp only [ValTy.fv, Finset.mem_union, not_or] at hy
      simp only [RawAgreeDimsAt]
      rw [denotValTyS_update_of_not_mem_fv hirr rho y w tauv0 Gv Dv hGv hy.1]
      exact and_congr
        (RawAgreeDimsAt.update_of_not_mem_fv hirr sigma rho y w
          tau0 tauv0 Ds Gv Dv B.domainBasis hGv hy.1)
        (forall_congr' fun x' => forall_congr' fun argVal =>
          forall_congr' fun arg =>
            imp_congr Iff.rfl
              (imp_congr
                (RawAgree.update_of_not_mem_fv hirr sigma rho y w
                  tau0 tauv0 Ds Gv Dv B.domainBasis _ argVal hGv hy.1)
                (RawAgreeDimsAt.update_of_not_mem_fv hirr sigma rho y w
                  tau1 tauv1
                  ((denotTyAux sigma Ds tau0).embed x' :: Ds)
                  (tauv0 :: Gv) (argVal :: Dv) (B.applyEl x')
                  (ValTyCtxFresh.cons hy.1 hGv) hy.2)))
  | .space _, .piTy _ _, _, _, _, _, _, _ => by
      simp only [RawAgreeDimsAt]
  | .piTy _ _, .space _, _, _, _, _, _, _ => by
      simp only [RawAgreeDimsAt]

end GLang
