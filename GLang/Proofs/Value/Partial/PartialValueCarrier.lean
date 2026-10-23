import GLang.Proofs.Value.Partial.PartialValueCheckedRelation

/-! Exact structural-carrier codecs. Neither direction resizes arrays or
validates function arguments, so higher-order callback identity is preserved. -/
namespace GLang.PartialValueDomains
open PaperValueDomains

/-- Structural reification followed by decoding is literally the identity,
including every suspended error of a higher-order callback. -/
theorem carrier_roundtrip (τ : ValTy) (a : τ.carrierEl) :
    τ.carrierFromVal (τ.carrierToVal a) = .ok a := by
  cases τ with
  | space s => rfl
  | piTy d c =>
    simp only [ValTy.carrierToVal, ValTy.carrierFromVal, dif_pos rfl]
    apply congrArg Except.ok
    funext x
    cases hx : a x with
    | error e => rfl
    | ok b => simpa only [Except.map] using carrier_roundtrip c b
termination_by sizeOf τ

/-- Reified partial results decode with exactly the same success or error. -/
theorem carrier_result_roundtrip (τ : ValTy) (r : Except DimError τ.carrierEl) :
    (r.map τ.carrierToVal).bind τ.carrierFromVal = r := by
  cases r with
  | error e => rfl
  | ok a => exact carrier_roundtrip τ a

end GLang.PartialValueDomains
