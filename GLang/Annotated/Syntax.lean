

import GLang.Core.NamesKinds
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic

namespace GLang

mutual

  /-- Spaces (the carriers of vectors / linear maps). -/
  inductive Space : Type
    | empty                                  -- ⊥
    | real                                   -- ℝ
    | dual    : Space → Space                -- s*
    | dsum    : Space → Space → Space        -- s ⊕ s
    | tprod   : Space → Space → Space

    | ker     : Space → Space → Term → Space  -- Ker_{s₀,s₁}(e)
    | coker   : Space → Space → Term → Space  -- CoKer_{s₀,s₁}(e)
    | img     : Space → Space → Term → Space  -- Img_{s₀,s₁}(e)
    | coimg   : Space → Space → Term → Space  -- CoImg_{s₀,s₁}(e)

  /-- Types: spaces (as types) plus dependent function types. -/
  inductive Ty : Type
    | space : Space → Ty
    | piTy  : Ty → Ty → Ty                   -- (_ : τ₀) → τ₁   (codomain uses bvar 0)

  /-- Terms (vectors / dependent functions). -/
  inductive Term : Type
    | bvar    : Nat → Term                            -- de Bruijn index (bound var)
    | zero    : Space → Term                          -- 0_s
    | smul    : Term → Term → Term                    -- r · e
    | real    : ℝ → Term                              -- r
    | add     : Term → Term → Term                    -- e + e
    | inner   : Space → Term                          -- ⟨·, ·⟩_s
    | appL    : Space → Space → Term → Term → Term    -- e₀(e₁) at s₀*⊗s₁ × s₀ ⇒ s₁
    | appI    : Space → Term → Term → Term            -- e₀(e₁) at s* × s ⇒ ℝ
    | appN    : Term → Term → Term                    -- e₀(e₁) at (x:τ₀)→τ₁ × τ₀
    | llam    : Space → Space → Term → Term           -- λ(_:s₀) ⊸ e with body in s (body uses bvar 0)
    | nllam   : Ty → Term → Term                      -- λ(_:τ) ⇒ e          (body uses bvar 0)
    | var     : Name → Term                           -- free var x
    | pinvT   : Space → Space → Term → Term           -- e† at s₀*⊗s₁ ⇒ s₁*⊗s₀
    | pinvD   : Space → Term → Term                   -- e† at s* ⇒ ℝ*⊗s
    | dsumE   : Term → Term → Term                    -- e ⊕ e
    | tprodE  : Term → Term → Term                    -- e ⊗ e
    | embed   : Space → Term                          -- embed_s   (inclusion of subspace s)

end

inductive Basis : Type
  | empty   : Basis                                 -- ⌊⌋
  | one     : Basis                                 -- ⌊1⌋
  | dual    : Basis → Basis                         -- b*
  | dsum    : Basis → Basis → Basis                 -- b₀ ⊕ b₁
  | tprod   : Basis → Basis → Basis                 -- b₀ ⊗ b₁
  | proj    : Space → Basis → Basis → Basis         -- projected basis P{s}{b₀,b₁}
  | image   : Basis → Basis                         -- I(b)
  | terms   : Space → List Term → Basis → Basis

  | frame   : Basis → Basis → Basis                 -- frame _:b₀.b₁  (b₁ uses bvar 0)

instance : Inhabited Space  := ⟨Space.empty⟩
instance : Inhabited Ty     := ⟨Ty.space Space.empty⟩
instance : Inhabited Term   := ⟨Term.zero Space.empty⟩
instance : Inhabited Basis  := ⟨Basis.empty⟩

end GLang
