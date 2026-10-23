import GLang.Proofs.Value.Binding.ValueLN
import Mathlib.Data.Finmap

/-! The shared value-variable typing context. -/
namespace GLang

abbrev ValCtx := @Finmap VName (fun _ => ValTy)

end GLang
