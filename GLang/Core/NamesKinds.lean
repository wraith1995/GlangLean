
namespace GLang

abbrev Name := String

/-- Kinds. -/
inductive Kind : Type
  | base
  | arrow : Kind → Kind → Kind
  deriving Repr, Inhabited

end GLang
