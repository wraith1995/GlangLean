import GLang.Proofs.Adequacy.Partial.Evaluation.PartialDirectAssembly
import GLang.Proofs.Adequacy.Raw.RawReification

/-! Source agreement for error-preserving value semantics. Dimensions are
successful partial observations, never the numeric fallback of an oracle.
Function agreement uses the actual raw argument in each dependent fiber. -/
namespace GLang.PartialAdequacy

noncomputable def Agree (orc : PartialFFSOracleSem) (σ : DEnv) (ρ : ValEnvSem) :
    List DVal → List ValTy → List ValValSem →
    Ty → ValTy → BasisDenot → DVal → ValValSem → Prop
  | Ds, Γ, Δ, .space s, .space sv, B, x, .array a =>
      let V := denotSpaceAux σ Ds s
      let vs := B.atSpace V
      ∃ n, sv.dofPartial (orc ρ Γ Δ) = .ok n ∧
        vs.length = n ∧ a.length = n ∧
        x.atSpace V = ∑ i : Fin n, a.get i.val • vs.getD i.val 0
  | _, _, _, .space _, .space _, _, _, .fn _ _ => False
  | Ds, Γ, Δ, .piTy d c, .piTy dv cv, B, x, v =>
      let T := denotTyAux σ Ds d
      ∃ D : PartialValType dv, denotValTyPartial orc ρ Γ Δ dv = .ok D ∧
      ∃ f : dv.carrierEl → Except DimError ValValSem,
        v = .fn dv.carrierEl f ∧
        ∀ (a : T.El) (raw : ValValSem) (arg : dv.carrierEl),
          dv.carrierFromVal raw = .ok arg →
          Agree orc σ ρ Ds Γ Δ d dv B.domainBasis (T.embed a) raw →
          ∃ out, f arg = .ok out ∧
            Agree orc σ ρ (T.embed a :: Ds) (dv :: Γ) (raw :: Δ)
              c cv (B.applyEl a) (x.applyEl a) out
  | _, _, _, .space _, .piTy _ _, _, _, _ => False
  | _, _, _, .piTy _ _, .space _, _, _, _ => False
termination_by _ _ _ t tv _ _ _ => Ty.size t + ValTy.kindSize tv
decreasing_by all_goals simp only [Ty.size, ValTy.kindSize_piTy]; omega

def ResultAgree (orc : PartialFFSOracleSem) (σ : DEnv) (ρ : ValEnvSem)
    (Ds : List DVal) (Γ : List ValTy) (Δ : List ValValSem)
    (t : Ty) (tv : ValTy) (B : BasisDenot) (x : DVal)
    (r : Except DimError ValValSem) : Prop :=
  ∃ v, r = .ok v ∧ Agree orc σ ρ Ds Γ Δ t tv B x v

/-- Dimension agreement includes a successful shape observation at every
source-admissible fiber. Unsupported raw arguments are not silently repaired. -/
noncomputable def DimsAt (orc : PartialFFSOracleSem) (σ : DEnv) (ρ : ValEnvSem) :
    List DVal → List ValTy → List ValValSem → Ty → ValTy → BasisDenot → Prop
  | Ds, Γ, Δ, .space s, .space sv, _ =>
      sv.shpOfPartial (orc ρ Γ Δ) = .ok (srcShp σ Ds s)
  | Ds, Γ, Δ, .piTy d c, .piTy dv cv, B =>
      let T := denotTyAux σ Ds d
      DimsAt orc σ ρ Ds Γ Δ d dv B.domainBasis ∧
      ∀ (a : T.El) (raw : ValValSem) (arg : dv.carrierEl),
        dv.carrierFromVal raw = .ok arg →
        Agree orc σ ρ Ds Γ Δ d dv B.domainBasis (T.embed a) raw →
        DimsAt orc σ ρ (T.embed a :: Ds) (dv :: Γ) (raw :: Δ) c cv (B.applyEl a)
  | _, _, _, .space _, .piTy _ _, _ => False
  | _, _, _, .piTy _ _, .space _, _ => False
termination_by _ _ _ t tv _ => Ty.size t + ValTy.kindSize tv
decreasing_by all_goals simp only [Ty.size, ValTy.kindSize_piTy]; omega

end GLang.PartialAdequacy
