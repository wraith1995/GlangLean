import GLang.Proofs.Value.Presentation.PaperValueTypedQueries

namespace GLang.PaperValueDomains

def primitiveAnnotationSpaces : ValExpr → List ValSpace
  | .zero s | .delta _ s | .idelta s | .vadd s _ _ | .vsum s _ => [s]
  | .ttv s _ _ => [s]
  | .mtm _ _ s t _ _ => [s,t]
  | _ => []

end GLang.PaperValueDomains
