import GLang.Metatheory

namespace GLang.PaperOperationalResults

/-- Ordinary preservation with its original common-kinding witnesses retained. -/
theorem preservationWithKinding
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx} {GammaV : ValCtx}
    {e : Term} {b : Basis} {v : ValExpr}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (htyped : HasType Delta Gamma e (Basis.tof b))
    (hbvalid : Basis.BasisValid Gamma b)
    (hstep : Operational.Unchecked.OpStep Psi e b v) :
    ∃ tauV k, ValTy.EvalT Psi (Basis.tof b) tauV ∧
      Nonempty (RuntimeValue.ValTValid GammaV (ValExpr.inferType v) k) ∧
      Nonempty (RuntimeValue.ValTValid GammaV tauV k) ∧
      Nonempty (RuntimeValue.ValHasType GammaV v (ValExpr.inferType v)) ∧
      (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ Psi.keyNames) := by
  obtain ⟨tauV,heval,hkind,_hok,hfv,hv⟩ := Metatheory.preservation hhistory htyped hbvalid hstep
  obtain ⟨k,hk⟩ := hv.some.regular hhistory.valueContextValid.some
  have ht := (RuntimeValue.preservation_mutual.2.1 heval GammaV hhistory.evalContext).some
  have hke : k = tauV.structuralKind := hk.kind_eq_structural.trans hkind
  exact ⟨tauV,k,heval,⟨hk⟩,⟨hke.symm ▸ ht⟩,hv,hfv⟩

theorem typePreservationWithKinding
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {tau : Ty} {tauV : ValTy} {k : Kind}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (hvalid : TValid Gamma tau k)
    (hstep : ValTy.EvalT Psi tau tauV) :
    ∃ kV, Nonempty (RuntimeValue.ValTValid GammaV tauV kV) ∧
      ValTy.fv tauV ⊆ Psi.keyNames := by
  have hplus : V2.EvalCtxValidPlus Psi := hhistory.erase.evalCtxValidPlus
  obtain ⟨⟨kV, hkind⟩, hfvs⟩ :=
    V2.preservation_master.2.1 hstep Delta Gamma Psi.keyNames k
      hplus hplus.rhoValid_keyNames (V2.keyScope_keyNames Psi) hvalid
  exact ⟨tauV.structuralKind, RuntimeValue.preservation_mutual.2.1 hstep GammaV hhistory.evalContext, hfvs⟩

theorem checkedPreservationOfHistory
    {Psi : EvalCtx} {Delta : LCtx} {Gamma : NLCtx}
    {e : Term} {b : Basis} {v : ValExpr} {tauV : ValTy}
    (hhistory : Operational.ContextHistory Delta Gamma GammaV Psi)
    (hstep : Operational.Term Delta Gamma Psi e b v tauV) :
    Operational.TyAt Gamma Psi b tauV /\
      ValTy.EvalT Psi (Basis.tof b) tauV /\
      (ValExpr.inferType v).structuralKind = tauV.structuralKind /\
      (ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ Psi.keyNames) := by
  obtain ⟨hat, hty, hkind, _hann, hfv⟩ :=
    Metatheory.checkedPreservation hhistory.erase.evalCtxValidPlus
      (V2.keyScope_keyNames Psi) hstep
  exact ⟨hat, hty, hkind, hfv⟩

theorem preservation
    {Δ : LCtx} {ε : NLCtx} {Γv : ValCtx} {Ψ : EvalCtx}
    (hctx : Operational.ContextHistory Δ ε Γv Ψ) :
    (∀ {T Tv k}, TValid ε T k → Operational.Unchecked.EvalT Ψ T Tv →
      ∃ kv, Nonempty (RuntimeValue.ValTValid Γv Tv kv) ∧
        ValTy.fv Tv ⊆ Ψ.keyNames) ∧
    (∀ {t b v}, HasType Δ ε t (Basis.tof b) → Basis.BasisValid ε b →
      Operational.Unchecked.OpStep Ψ t b v →
      Nonempty (RuntimeValue.ValHasType Γv v (ValExpr.inferType v)) ∧
      (∃ kv, Nonempty (RuntimeValue.ValTValid Γv (ValExpr.inferType v) kv)) ∧
      ValTy.fv (ValExpr.inferType v) ∪ ValExpr.fv v ⊆ Ψ.keyNames) ∧
    (∀ {b₀ b₁ v}, Basis.BasisValid ε b₀ →
      Operational.Unchecked.EvalBB Ψ b₀ v b₁ →
      ∃ s₀ s₁ sv₀ sv₁,
        Nonempty (RuntimeValue.ValHasType Γv v (.space (.tprod sv₀ sv₁))) ∧
        ValExpr.inferType v = .space (.tprod sv₀ sv₁) ∧
        Operational.Unchecked.EvalS Ψ s₀ sv₀ ∧
        Operational.Unchecked.EvalS Ψ s₁ sv₁ ∧
        ValExpr.fv v ⊆ Ψ.keyNames) := by
  refine ⟨fun ht he => typePreservationWithKinding hctx ht he, ?_, ?_⟩
  · intro t b v ht hb he
    obtain ⟨_, k, _, hk, _, hv, hfv⟩ := preservationWithKinding hctx ht hb he
    exact ⟨hv, ⟨k, hk⟩, hfv⟩
  · intro b₀ b₁ v hb he
    obtain ⟨⟨⟨s₀, s₁, sv₀, sv₁, hinfer, hs₀, hs₁⟩, _, hfv⟩, hv⟩ :=
      Metatheory.cobPreservation hctx hb he
    exact ⟨s₀, s₁, sv₀, sv₁, hinfer ▸ hv, hinfer, hs₀, hs₁, hfv⟩

theorem progress
    {Δ : LCtx} {ε : NLCtx} {Γv : ValCtx} {Ψ : EvalCtx}
    (hctx : Operational.ContextHistory Δ ε Γv Ψ) :
    (∀ {s}, SValid ε s → ∃ sv, Operational.Space ε Ψ s sv) ∧
    (∀ {t b}, HasType Δ ε t (Basis.tof b) → Basis.BasisValid ε b →
      ∃ v Tv, Operational.Term Δ ε Ψ t b v Tv ∧ ValExpr.inferType v = Tv) ∧
    (∀ {b₀ b₁ s}, Basis.BasisValid ε b₀ → Basis.BasisValid ε b₁ →
      Basis.tof b₀ = .space s → Basis.tof b₁ = .space s →
      ∃ v, Operational.Cob ε Ψ b₀ v b₁) := by
  refine ⟨fun hs => Metatheory.checkedSpaceProgress hctx hs, ?_, ?_⟩
  · intro t b ht hb
    obtain ⟨v, Tv, he, hinfer, _⟩ := Metatheory.progress hctx ht hb
    exact ⟨v, Tv, he, hinfer⟩
  · intro b₀ b₁ s hb₀ hb₁ hs₀ hs₁
    exact Metatheory.checkedCobProgress hctx hb₀ hb₁
      (hs₀.trans (congrArg Ty.space (Basis.sof_eq_of_tof_eq_space hs₀)).symm)
      (hs₀.trans hs₁.symm)

end GLang.PaperOperationalResults
