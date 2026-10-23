import GLang.Value.Inference
import GLang.Value.Arrays

/-! Runtime contracts for finite-array primitives. -/

namespace GLang.ValueShape

def scale (q : FFSOracle) (s : ValSpace) (a b : FlatArray) : Prop :=
  a.length = 1 ∧ b.length = ValSpace.dof q s

def pair (q : FFSOracle) (s t : ValSpace) (a b : FlatArray) : Prop :=
  a.length = ValSpace.dof q s ∧ b.length = ValSpace.dof q t

def tensor (q : FFSOracle) (s : ValSpace) (a : FlatArray) : Prop :=
  match s with
  | .tprod s0 s1 => a.length = ValSpace.dof q s0 * ValSpace.dof q s1
  | _ => False

def matrices (q : FFSOracle) (s t : ValSpace) (a b : FlatArray) : Prop :=
  tensor q s a ∧ tensor q t b

def ttv (q : FFSOracle) (contract s t : ValSpace) (a b : FlatArray) : Prop :=
  pair q s t a b ∧
    match s with
    | .tprod domain _ =>
        ValSpace.dof q domain = ValSpace.dof q contract ∧
          ValSpace.dof q t = ValSpace.dof q contract
    | _ => ValSpace.dof q s = ValSpace.dof q contract ∧
        ValSpace.dof q t = ValSpace.dof q contract

def mtm (q : FFSOracle) (contract s t : ValSpace) (a b : FlatArray) : Prop :=
  matrices q s t a b ∧
    match s, t with
    | .tprod domain _, .tprod _ codomain =>
        ValSpace.dof q domain = ValSpace.dof q contract ∧
          ValSpace.dof q codomain = ValSpace.dof q contract
    | _, _ => False

/-- A bounded family has exactly one successfully evaluated array per active
index, each at the result dimension. Inactive candidates are not evaluated. -/
def family (count width : Nat) (arrays : List FlatArray) : Prop :=
  arrays.length = count ∧ ∀ a ∈ arrays, a.length = width

instance (q : FFSOracle) (s : ValSpace) (a b : FlatArray) :
    Decidable (scale q s a b) := inferInstanceAs (Decidable (_ ∧ _))
instance (q : FFSOracle) (s t : ValSpace) (a b : FlatArray) :
    Decidable (pair q s t a b) := inferInstanceAs (Decidable (_ ∧ _))
instance (q : FFSOracle) (s : ValSpace) (a : FlatArray) :
    Decidable (tensor q s a) := by cases s <;> unfold tensor <;> infer_instance
instance (q : FFSOracle) (s t : ValSpace) (a b : FlatArray) :
    Decidable (matrices q s t a b) := inferInstanceAs (Decidable (_ ∧ _))
instance (q : FFSOracle) (c s t : ValSpace) (a b : FlatArray) :
    Decidable (ttv q c s t a b) := by cases s <;> unfold ttv <;> infer_instance
instance (q : FFSOracle) (c s t : ValSpace) (a b : FlatArray) :
    Decidable (mtm q c s t a b) := by
  cases s <;> cases t <;> unfold mtm <;> infer_instance
instance (count width : Nat) (arrays : List FlatArray) :
    Decidable (family count width arrays) := by unfold family; infer_instance

end GLang.ValueShape
