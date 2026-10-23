/- GLang.ValueWeakening — EvalCtx weakening (monotonicity under a fresh-key
extension). -/
import GLang.Operational.Ordinary

namespace GLang

section EvalWeaken
variable {x₀ : VName} {bᵢ : Basis} {v₀ : ValExpr}

/-- Discharge a source-`allNames` sub-freshness goal from a parent one. The
parent `h` bounds the conclusion's names; every sub-term/sub-basis is a syntactic
sub-part, so `simp`-unfolding both + `tauto` picks the right conjunct. Opaque
atoms (`Space.allNames (sof b)`, `Basis.allNames b`) are carried through. -/
local macro "frs" h:ident : term => `(by
  first
  | exact $h:ident
  | (simp only [Space.allNames, Ty.allNames, Term.allNames, Basis.allNames,
       Finset.mem_union, Finset.mem_insert, not_or, Finset.notMem_empty] at $h:ident ⊢ <;>
     tauto))

/-- `x₀ ∉ Space.allNames (sof b)` from `x₀ ∉ Basis.allNames b` (closure lemma). -/
local macro "sofFresh" h:ident : term =>
  `(fun hm => $h (Basis.allNames_sof_subset _ hm))

/-- Inserting the weakening key `(x₀, bᵢ)` commutes with a binder extension
`(x, b)` when the keys differ — the `EvalCtx` insert-commute that lets the
`nllam`/`piTy` binder arms move the fresh key under the binder. -/
theorem evalctx_extend_comm {Ψ : EvalCtx} {x : VName} {b : Basis} {v : ValExpr}
    (hne : (x₀, bᵢ) ≠ (x, b)) :
    Finmap.insert (x₀, bᵢ) v₀ (EvalCtx.extend Ψ x b v)
      = EvalCtx.extend (Finmap.insert (x₀, bᵢ) v₀ Ψ) x b v := by
  simp only [EvalCtx.extend]
  exact Finmap.insert_insert_of_ne Ψ hne.symm

set_option maxHeartbeats 1600000 in
mutual
def evalS_wk : {Ψ : EvalCtx} → {s : Space} → {sv : ValSpace} →
    ValSpace.EvalS Ψ s sv → (x₀, bᵢ) ∉ Ψ →
    ValSpace.EvalS (Finmap.insert (x₀, bᵢ) v₀ Ψ) s sv
  | _, _, _, .real, _ => .real
  | _, _, _, .empty, _ => .empty
  | _, _, _, .dual h, hΨ => .dual (evalS_wk h hΨ)

  | _, _, _, .ker he hb hcompat hsvb, hΨ =>
      .ker (opStep_wk he hΨ) hb hcompat (evalS_wk hsvb hΨ)
  | _, _, _, .coker he hb hcompat hsvb, hΨ =>
      .coker (opStep_wk he hΨ) hb hcompat (evalS_wk hsvb hΨ)
  | _, _, _, .img he hb hcompat hsvb, hΨ =>
      .img (opStep_wk he hΨ) hb hcompat (evalS_wk hsvb hΨ)
  | _, _, _, .coimg he hb hcompat hsvb, hΨ =>
      .coimg (opStep_wk he hΨ) hb hcompat (evalS_wk hsvb hΨ)
  | _, _, _, .tprod h₀ h₁, hΨ => .tprod (evalS_wk h₀ hΨ) (evalS_wk h₁ hΨ)
  | _, _, _, .dsum h₀ h₁, hΨ => .dsum (evalS_wk h₀ hΨ) (evalS_wk h₁ hΨ)

def evalT_wk : {Ψ : EvalCtx} → {τ : Ty} → {τv : ValTy} →
    ValTy.EvalT Ψ τ τv → (x₀, bᵢ) ∉ Ψ →
    ValTy.EvalT (Finmap.insert (x₀, bᵢ) v₀ Ψ) τ τv
  | _, _, _, .space h, hΨ => .space (evalS_wk h hΨ)

  | Ψ, _, _, @ValTy.EvalT.piTy _ b₀ τ₀ τ₁ τv₀ τv₁ h₀ hb L h₁, hΨ =>
      .piTy (evalT_wk h₀ hΨ) hb (L ∪ {x₀}) (fun y hy => by
        have hyne : y ≠ x₀ := fun h =>
          hy (by rw [h]; exact Finset.mem_union_right L (Finset.mem_singleton_self x₀))
        have hyx₀ : (x₀, bᵢ) ≠ (y, b₀) := fun heq => hyne (congrArg Prod.fst heq).symm
        have hy' : y ∉ L := fun h => hy (Finset.mem_union_left _ h)
        have hΨ_ext : (x₀, bᵢ) ∉ EvalCtx.extend Ψ y b₀ (.var y τv₀) := by
          rw [EvalCtx.extend]; exact fun h => (Finmap.mem_insert.mp h).elim hyx₀ hΨ
        exact evalctx_extend_comm hyx₀ ▸ evalT_wk (h₁ y hy') hΨ_ext)

def evalBB_wk : {Ψ : EvalCtx} → {b : Basis} → {env : ValExpr} → {b' : Basis} →
    Basis.EvalBB Ψ b env b' → (x₀, bᵢ) ∉ Ψ →
    Basis.EvalBB (Finmap.insert (x₀, bᵢ) v₀ Ψ) b env b'
  | _, _, _, _, .inverse h, hΨ => .inverse (evalBB_wk h hΨ)

  | _, _, _, _, .trans h₀ h₁ hsv, hΨ =>
      .trans (evalBB_wk h₀ hΨ) (evalBB_wk h₁ hΨ) (evalS_wk hsv hΨ)
  | _, _, _, _, .tprod h₀ h₁, hΨ => .tprod (evalBB_wk h₀ hΨ) (evalBB_wk h₁ hΨ)
  | _, _, _, _, .dsum h₀ h₁, hΨ => .dsum (evalBB_wk h₀ hΨ) (evalBB_wk h₁ hΨ)
  | _, _, _, _, .image hcoker h, hΨ => .image hcoker (evalBB_wk h hΨ)
  | _, _, _, _, .image_svds hs₀ hs₁ hb₀ hb₁ he hsvb, hΨ =>
      .image_svds hs₀ hs₁ hb₀ hb₁ (opStep_wk he hΨ) (evalS_wk hsvb hΨ)
  | _, _, _, _, .dual_std htof hb₁, hΨ => .dual_std htof (evalBB_wk hb₁ hΨ)
  | _, _, _, _,
      .proj_ker_coker hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₀' hcob hembd hproj, hΨ =>
      .proj_ker_coker hs hsofb₀ hsofb₁ (evalS_wk hsv₀ hΨ) (evalS_wk hsv₁ hΨ)
        (evalS_wk hsv hΨ) (evalS_wk hsv' hΨ) (evalS_wk hsv₀' hΨ)
        (evalBB_wk hcob hΨ) (opStep_wk hembd hΨ) (opStep_wk hproj hΨ)
  | _, _, _, _,
      .proj_img_coimg hs hsofb₀ hsofb₁ hsv₀ hsv₁ hsv hsv' hsv₁' hcob hembd hproj, hΨ =>
      .proj_img_coimg hs hsofb₀ hsofb₁ (evalS_wk hsv₀ hΨ) (evalS_wk hsv₁ hΨ)
        (evalS_wk hsv hΨ) (evalS_wk hsv' hΨ) (evalS_wk hsv₁' hΨ)
        (evalBB_wk hcob hΨ) (opStep_wk hembd hΨ) (opStep_wk hproj hΨ)
  -- `terms_rref` (fresh-key): the chain term/basis are pure indices.
  | _, _, _, _, .terms_rref hbb hch hsv, hΨ =>
      .terms_rref (evalBB_wk hbb hΨ) (opStep_wk hch hΨ) (evalS_wk hsv hΨ)
  -- `refl` (erratum-fix reflexivity): the basis is a pure index; the
  -- realization weakens.
  | _, _, _, _, .refl htof hsv, hΨ => .refl htof (evalS_wk hsv hΨ)
  -- `proj_ker_coker_cod` (P6a codomain-side proj conversion): pure indices +
  -- recursive premises, same shape as `proj_ker_coker` minus the COB factor.
  | _, _, _, _,
      .proj_ker_coker_cod hs hsofb₀ hsofb₁ hsofb₁' hsv₀ hsv hsv' hembd hproj, hΨ =>
      .proj_ker_coker_cod hs hsofb₀ hsofb₁ hsofb₁' (evalS_wk hsv₀ hΨ)
        (evalS_wk hsv hΨ) (evalS_wk hsv' hΨ)
        (opStep_wk hembd hΨ) (opStep_wk hproj hΨ)
  -- `proj_img_coimg_dom` (P6a domain-side img/coimg conversion): mirror of
  -- `proj_ker_coker_cod` through the codomain ambient `b₁`.
  | _, _, _, _,
      .proj_img_coimg_dom hs hsofb₀ hsofb₁ hsofb₀' hsv₁ hsv hsv' hembd hproj, hΨ =>
      .proj_img_coimg_dom hs hsofb₀ hsofb₁ hsofb₀' (evalS_wk hsv₁ hΨ)
        (evalS_wk hsv hΨ) (evalS_wk hsv' hΨ)
        (opStep_wk hembd hΨ) (opStep_wk hproj hΨ)

def opStep_wk : {Ψ : EvalCtx} → {e : Term} → {b : Basis} → {v : ValExpr} →
    ValExpr.OpStep Ψ e b v → (x₀, bᵢ) ∉ Ψ →
    ValExpr.OpStep (Finmap.insert (x₀, bᵢ) v₀ Ψ) e b v
  -- `var`: the looked-up key is IN `Ψ`, the inserted key is NOT, so they differ.
  | _, .var x, b, _, .var h, hΨ =>
      have hmem := Finmap.mem_of_lookup_eq_some h
      have hne : (x, b) ≠ (x₀, bᵢ) := fun heq => hΨ (heq ▸ hmem)
      .var (by rw [EvalCtx.lookup, Finmap.lookup_insert_of_ne _ hne]; exact h)

  | _, _, _, _, .cob htof₀ htof₁ he hbb hes, hΨ =>
      .cob htof₀ htof₁ (opStep_wk he hΨ) (evalBB_wk hbb hΨ) (evalS_wk hes hΨ)
  | _, _, _, _, .reshape_cob he hsrc htgt, hΨ =>
      .reshape_cob (opStep_wk he hΨ) (evalT_wk hsrc hΨ) (evalT_wk htgt hΨ)
  | _, _, _, _, .scale he₀ he₁, hΨ => .scale (opStep_wk he₀ hΨ) (opStep_wk he₁ hΨ)
  | _, _, _, _, .add htof hsv he₀ he₁, hΨ =>
      .add htof (evalS_wk hsv hΨ) (opStep_wk he₀ hΨ) (opStep_wk he₁ hΨ)
  | _, _, _, _, .dsumE he₀ he₁ htof₀ htof₁, hΨ =>
      .dsumE (opStep_wk he₀ hΨ) (opStep_wk he₁ hΨ) htof₀ htof₁
  | _, _, _, _, .tprodE he₀ he₁ htof₀ htof₁, hΨ =>
      .tprodE (opStep_wk he₀ hΨ) (opStep_wk he₁ hΨ) htof₀ htof₁
  | _, _, _, _, .pinvT_std he hb₀ hb₁, hΨ => .pinvT_std (opStep_wk he hΨ) hb₀ hb₁
  | _, _, _, _, .pinvD_std he hsofb₀ hb₀ hb₁ hsv₁, hΨ =>
      .pinvD_std (opStep_wk he hΨ) hsofb₀ hb₀ hb₁ (evalS_wk hsv₁ hΨ)
  | _, _, _, _, .inner_std hb₀ hsv hsof, hΨ => .inner_std hb₀ (evalS_wk hsv hΨ) hsof
  | _, _, _, _, .embed_ker hs₀ hs₁ hi₀ hi₁ he, hΨ =>
      .embed_ker hs₀ hs₁ (opStep_wk hi₀ hΨ) (opStep_wk hi₁ hΨ) (opStep_wk he hΨ)
  | _, _, _, _, .embed_coker hs₀ hs₁ hi₀ hi₁ he, hΨ =>
      .embed_coker hs₀ hs₁ (opStep_wk hi₀ hΨ) (opStep_wk hi₁ hΨ) (opStep_wk he hΨ)
  | _, _, _, _, .embed_img hs₀ hs₁ hi₀ hi₁ he, hΨ =>
      .embed_img hs₀ hs₁ (opStep_wk hi₀ hΨ) (opStep_wk hi₁ hΨ) (opStep_wk he hΨ)
  | _, _, _, _, .embed_coimg hs₀ hs₁ hi₀ hi₁ he, hΨ =>
      .embed_coimg hs₀ hs₁ (opStep_wk hi₀ hΨ) (opStep_wk hi₁ hΨ) (opStep_wk he hΨ)
  | _, _, _, _, .pinvT_gpinv he hi₀ hi₁, hΨ =>
      .pinvT_gpinv (opStep_wk he hΨ) (opStep_wk hi₀ hΨ) (opStep_wk hi₁ hΨ)
  | _, _, _, _, .pinvD_gpinv he hsofb₀ hb₀ hi₀ hi₁ hsv₁, hΨ =>
      .pinvD_gpinv (opStep_wk he hΨ) hsofb₀ hb₀
        (opStep_wk hi₀ hΨ) (opStep_wk hi₁ hΨ)
        (evalS_wk hsv₁ hΨ)

  | _, _, _, _, .appL_lin h₀ hsv₀ h₁ hsv₁ htof₁, hΨ =>
      .appL_lin (opStep_wk h₀ hΨ) (evalS_wk hsv₀ hΨ)
        (opStep_wk h₁ hΨ) (evalS_wk hsv₁ hΨ) htof₁
  | _, _, _, _, .appI_lin h₀ hsv h₁, hΨ =>
      .appI_lin (opStep_wk h₀ hΨ) (evalS_wk hsv hΨ) (opStep_wk h₁ hΨ)
  -- `appN_val` (fresh-key): the frame/instantiated bases are pure indices; the
  -- result-type premise weakens via `evalT_wk`.
  | _, _, _, _, .appN_val h₀ h₁ hout, hΨ =>
      .appN_val (opStep_wk h₀ hΨ) (opStep_wk h₁ hΨ) (evalT_wk hout hΨ)
  -- BINDER (`frame_reanchor`, §9.23 cofinite): structural premises weaken
  -- directly; the two under-binder premises re-instantiate at `y ∉ L ∪ {x₀}`
  -- and insert-commute, as `nllam`.
  | Ψ, _, _, _,
      @ValExpr.OpStep.frame_reanchor _ b₀ b₀' b₁ n₀ leev env₁ τv₀ τv₀' τv₁'
        h₀ htof hfn hdom L hx hcod, hΨ =>
      .frame_reanchor (evalT_wk h₀ hΨ) htof (opStep_wk hfn hΨ) (evalT_wk hdom hΨ)
        (L ∪ {x₀})
        (fun y hy => by
          have hyne : y ≠ x₀ := fun h =>
            hy (by rw [h]; exact Finset.mem_union_right L (Finset.mem_singleton_self x₀))
          have hyx₀ : (x₀, bᵢ) ≠ (y, b₀) := fun heq => hyne (congrArg Prod.fst heq).symm
          have hΨ_ext : (x₀, bᵢ) ∉ EvalCtx.extend Ψ y b₀ (.var y τv₀) := by
            rw [EvalCtx.extend]; exact fun h => (Finmap.mem_insert.mp h).elim hyx₀ hΨ
          exact evalctx_extend_comm hyx₀ ▸
            opStep_wk (hx y (fun h => hy (Finset.mem_union_left _ h))) hΨ_ext)
        (fun y hy => by
          have hyne : y ≠ x₀ := fun h =>
            hy (by rw [h]; exact Finset.mem_union_right L (Finset.mem_singleton_self x₀))
          have hyx₀ : (x₀, bᵢ) ≠ (y, b₀) := fun heq => hyne (congrArg Prod.fst heq).symm
          have hΨ_ext : (x₀, bᵢ) ∉ EvalCtx.extend Ψ y b₀ (.var y τv₀) := by
            rw [EvalCtx.extend]; exact fun h => (Finmap.mem_insert.mp h).elim hyx₀ hΨ
          exact evalctx_extend_comm hyx₀ ▸
            evalT_wk (hcod y (fun h => hy (Finset.mem_union_left _ h))) hΨ_ext)
  -- BINDER (`frame_eta`, §9.23 cofinite): as `nllam`.
  | Ψ, _, _, _,
      @ValExpr.OpStep.frame_eta _ b₀ b₁ n₀ τv₀ τv₁ env h₀ L he h₁, hΨ =>
      .frame_eta (evalT_wk h₀ hΨ) (L ∪ {x₀})
        (fun y hy => by
          have hyne : y ≠ x₀ := fun h =>
            hy (by rw [h]; exact Finset.mem_union_right L (Finset.mem_singleton_self x₀))
          have hyx₀ : (x₀, bᵢ) ≠ (y, b₀) := fun heq => hyne (congrArg Prod.fst heq).symm
          have hΨ_ext : (x₀, bᵢ) ∉ EvalCtx.extend Ψ y b₀ (.var y τv₀) := by
            rw [EvalCtx.extend]; exact fun h => (Finmap.mem_insert.mp h).elim hyx₀ hΨ
          exact evalctx_extend_comm hyx₀ ▸
            opStep_wk (he y (fun h => hy (Finset.mem_union_left _ h))) hΨ_ext)
        (fun y hy => by
          have hyne : y ≠ x₀ := fun h =>
            hy (by rw [h]; exact Finset.mem_union_right L (Finset.mem_singleton_self x₀))
          have hyx₀ : (x₀, bᵢ) ≠ (y, b₀) := fun heq => hyne (congrArg Prod.fst heq).symm
          have hΨ_ext : (x₀, bᵢ) ∉ EvalCtx.extend Ψ y b₀ (.var y τv₀) := by
            rw [EvalCtx.extend]; exact fun h => (Finmap.mem_insert.mp h).elim hyx₀ hΨ
          exact evalctx_extend_comm hyx₀ ▸
            evalT_wk (h₁ y (fun h => hy (Finset.mem_union_left _ h))) hΨ_ext)
  -- BINDER (`nllam`, §9.23 cofinite): re-instantiate each cofinite premise at a
  -- fresh `y ∉ L ∪ {x₀}`, weaken past `(x₀,bᵢ)`, insert-commute under the binder.
  | Ψ, _, _, _,
      @ValExpr.OpStep.nllam _ b₀ b₁ τ₀ τ₁ e τv₀ τv₁ env hb₀ hb₁ h₀ L he h₁, hΨ =>
      .nllam hb₀ hb₁ (evalT_wk h₀ hΨ) (L ∪ {x₀})
        (fun y hy => by
          have hyne : y ≠ x₀ := fun h =>
            hy (by rw [h]; exact Finset.mem_union_right L (Finset.mem_singleton_self x₀))
          have hyx₀ : (x₀, bᵢ) ≠ (y, b₀) := fun heq => hyne (congrArg Prod.fst heq).symm
          have hΨ_ext : (x₀, bᵢ) ∉ EvalCtx.extend Ψ y b₀ (.var y τv₀) := by
            rw [EvalCtx.extend]; exact fun h => (Finmap.mem_insert.mp h).elim hyx₀ hΨ
          exact evalctx_extend_comm hyx₀ ▸
            opStep_wk (he y (fun h => hy (Finset.mem_union_left _ h))) hΨ_ext)
        (fun y hy => by
          have hyne : y ≠ x₀ := fun h =>
            hy (by rw [h]; exact Finset.mem_union_right L (Finset.mem_singleton_self x₀))
          have hyx₀ : (x₀, bᵢ) ≠ (y, b₀) := fun heq => hyne (congrArg Prod.fst heq).symm
          have hΨ_ext : (x₀, bᵢ) ∉ EvalCtx.extend Ψ y b₀ (.var y τv₀) := by
            rw [EvalCtx.extend]; exact fun h => (Finmap.mem_insert.mp h).elim hyx₀ hΨ
          exact evalctx_extend_comm hyx₀ ▸
            evalT_wk (h₁ y (fun h => hy (Finset.mem_union_left _ h))) hΨ_ext)
  -- BINDER + FAMILY (`llam_assemble`, §9.23 cofinite × fixed `Fin (dofUB sv')` family):
  -- the family premise re-instantiates at `y ∉ L ∪ {x₀}` per `i`; the binding
  -- value `.delta i sv'` is key-irrelevant to `evalctx_extend_comm`.
  | Ψ, _, _, _,
      @ValExpr.OpStep.llam_assemble _ b' b e sv' sv env htof' hsv' hsv L hfam, hΨ =>
      .llam_assemble htof' (evalS_wk hsv' hΨ) (evalS_wk hsv hΨ) (L ∪ {x₀})
        (fun y hy i => by
          have hyne : y ≠ x₀ := fun h =>
            hy (by rw [h]; exact Finset.mem_union_right L (Finset.mem_singleton_self x₀))
          have hyx₀ : (x₀, bᵢ) ≠ (y, b') := fun heq => hyne (congrArg Prod.fst heq).symm
          have hΨ_ext : (x₀, bᵢ) ∉ EvalCtx.extend Ψ y b' (.delta i.val sv') := by
            rw [EvalCtx.extend]; exact fun h => (Finmap.mem_insert.mp h).elim hyx₀ hΨ
          exact evalctx_extend_comm hyx₀ ▸
            opStep_wk (hfam y (fun h => hy (Finset.mem_union_left _ h)) i) hΨ_ext)
  | Ψ, _, _, _,
      @ValExpr.OpStep.llam_assemble_real _ b' e sv' env htof' hsv' L hfam, hΨ =>
      .llam_assemble_real htof' (evalS_wk hsv' hΨ) (L ∪ {x₀})
        (fun y hy i => by
          have hyne : y ≠ x₀ := fun h =>
            hy (by rw [h]; exact Finset.mem_union_right L (Finset.mem_singleton_self x₀))
          have hyx₀ : (x₀, bᵢ) ≠ (y, b') := fun heq => hyne (congrArg Prod.fst heq).symm
          have hΨ_ext : (x₀, bᵢ) ∉ EvalCtx.extend Ψ y b' (.delta i.val sv') := by
            rw [EvalCtx.extend]; exact fun h => (Finmap.mem_insert.mp h).elim hyx₀ hΨ
          exact evalctx_extend_comm hyx₀ ▸
            opStep_wk (hfam y (fun h => hy (Finset.mem_union_left _ h)) i) hΨ_ext)
  -- `zero` (erratum-fix literal): the basis is a pure index; the realization weakens.
  | _, _, _, _, .zero htof hsv, hΨ => .zero htof (evalS_wk hsv hΨ)
  -- `rlit` (erratum-fix literal): no premises, context-free.
  | _, _, _, _, .rlit r, _hΨ => .rlit r
end

end EvalWeaken

end GLang
