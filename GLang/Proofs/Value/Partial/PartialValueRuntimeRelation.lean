import GLang.Proofs.Value.Partial.PartialValueCarrier
import GLang.Proofs.Value.Soundness.ValueSoundVals

/-! Runtime membership for the partial logical relation. Environments constrain
only their declared bindings, and no evaluator property is included in the
contract. Structural decoding retains raw higher-order argument identity. -/
namespace GLang.PartialValueDomains
open PaperValueDomains

/-- Runtime functions preserve related raw outputs as well as typed arguments;
a malformed successful output cannot masquerade as a decoded error. -/
def PartialRuntimeRelated : (τ : ValTy) → Except DimError (PartialValType τ) →
    Except DimError (PartialValType τ) → ValValSem → ValValSem → Prop
  | .space s, T, U, .array a, .array b => PartialRelated (.space s) T U a b
  | .piTy d c, .ok (D,F), .ok (E,G), .fn A f, .fn B g =>
      ∃ hA : A = d.carrierEl, ∃ hB : B = d.carrierEl,
        ∀ a b, PartialRelated d (.ok D) (.ok E) (hA ▸ a) (hB ▸ b) →
          PartialRel (PartialRuntimeRelated c (F (hA ▸ a)) (G (hB ▸ b))) (f a) (g b)
  | _, _, _, _, _ => False

/-- Partial value-environment membership, independent of any evaluator
fundamental theorem. A failed declared type cannot have a successful entry. -/
def PartialEnvironmentsRelated (orc : PartialFFSOracleSem) (ε : ValCtx)
    (ρ ρ' : ValEnvSem) : Prop :=
  ∀ x τ, ε.lookup x = some τ →
    PartialRuntimeRelated τ (denotValTyPartial orc ρ [] [] τ)
      (denotValTyPartial orc ρ' [] [] τ) (ρ x) (ρ' x)

def PartialEnvWF (orc : PartialFFSOracleSem) (ε : ValCtx) (ρ : ValEnvSem) : Prop :=
  Nonempty (ValCtxValid ε) ∧ PartialEnvironmentsRelated orc ε ρ ρ

theorem PartialEnvWF.empty (orc : PartialFFSOracleSem) (ρ : ValEnvSem) : PartialEnvWF orc ∅ ρ := by
  constructor
  · exact ⟨fun x τ hx => by simp at hx⟩
  · intro x τ hx
    simp at hx

/-- Reification produces related raw values, preserving latent errors. -/
theorem partial_reify_related (τ : ValTy) (T U : Except DimError (PartialValType τ))
    (a b : τ.carrierEl) (h : PartialRelated τ T U a b) :
    PartialRuntimeRelated τ T U (τ.carrierToVal a) (τ.carrierToVal b) := by
  cases τ with
  | space s => exact h
  | piTy d c =>
    cases T <;> cases U <;> try exact False.elim h
    rename_i T U
    rcases T with ⟨D,F⟩
    rcases U with ⟨E,G⟩
    refine ⟨rfl,rfl,?_⟩
    intro x y hxy
    exact PartialRel.map _ _ (fun u v huv => partial_reify_related c _ _ u v huv) (h x y hxy)
termination_by sizeOf τ

/-- Extract successful typed representatives without altering callback inputs. -/
theorem partial_extract_related (τ : ValTy) (T U : Except DimError (PartialValType τ))
    (v w : ValValSem) (h : PartialRuntimeRelated τ T U v w) :
    ∃ a b, τ.carrierFromVal v = .ok a ∧ τ.carrierFromVal w = .ok b ∧
      PartialRelated τ T U a b := by
  cases τ with
  | space s =>
    cases v <;> cases w <;> try exact False.elim h
    exact ⟨_,_,rfl,rfl,h⟩
  | piTy d c =>
    cases T <;> cases U <;> cases v <;> cases w <;> try exact False.elim h
    rename_i T U A f B g
    rcases T with ⟨D,F⟩
    rcases U with ⟨E,G⟩
    obtain ⟨hA,hB,hfg⟩ := h
    subst A; subst B
    simp only [ValTy.carrierFromVal, dif_pos rfl]
    refine ⟨_,_,rfl,rfl,?_⟩
    intro a b hab
    have ho := hfg a b hab
    cases hf : f a <;> cases hg : g b <;> simp only [hf,hg,PartialRel] at ho ⊢
    obtain ⟨x,y,hx,hy,hxy⟩ := partial_extract_related c _ _ _ _ ho
    simpa only [hx,hy] using hxy
termination_by sizeOf τ

/-- Related runtime computations decode to related structural results. -/
theorem partial_extract_results {τ : ValTy} {T U : Except DimError (PartialValType τ)}
    {r s : Except DimError ValValSem} (h : PartialRel (PartialRuntimeRelated τ T U) r s) :
    PartialRel (PartialRelated τ T U) (r.bind τ.carrierFromVal) (s.bind τ.carrierFromVal) := by
  cases r with
  | error e =>
    cases s with
    | error e' => exact h
    | ok b => exact False.elim h
  | ok v =>
    cases s with
    | error e => exact False.elim h
    | ok w =>
      obtain ⟨a,b,ha,hb,hab⟩ := partial_extract_related τ T U v w h
      simpa only [Except.bind,ha,hb] using hab

/-- Successful structural decoding commutes with actual raw application. -/
theorem carrier_apply {d c : ValTy} {v : ValValSem}
    {f : (.piTy d c : ValTy).carrierEl}
    (h : (.piTy d c : ValTy).carrierFromVal v = .ok f) (a : d.carrierEl) :
    (v.applyTyped a).bind c.carrierFromVal = f a := by
  cases v with
  | array v => cases h
  | fn A g =>
    simp only [ValTy.carrierFromVal] at h
    split at h
    · rename_i hA
      subst A
      cases h
      simp only [ValValSem.applyTyped_fn]
      cases g a <;> rfl
    · cases h

/-- Domain decoding accepts a supported argument with exactly its original
structural representative. It never normalizes a function argument. -/
theorem decodeDomain_related_left (orc : PartialFFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (d : ValTy)
    (U : Except DimError (PartialValType d)) (v : ValValSem) (a b : d.carrierEl)
    (hv : d.carrierFromVal v = .ok a)
    (h : PartialRelated d (denotValTyPartial orc ρ Γ Δ d) U a b) :
    PartialValueEval.decodeDomain orc ρ Γ Δ d v = .ok a := by
  cases d with
  | space s =>
    cases hT : denotValTyPartial orc ρ Γ Δ (.space s) <;>
      cases U <;> rw [hT] at h <;> try exact False.elim h
    simp only [PartialValueEval.decodeDomain,hT,hv,if_pos h.2.1]
  | piTy d c =>
    cases hT : denotValTyPartial orc ρ Γ Δ (.piTy d c) <;>
      cases U <;> rw [hT] at h <;> try exact False.elim h
    simp only [PartialValueEval.decodeDomain,hT,hv]

end GLang.PartialValueDomains
