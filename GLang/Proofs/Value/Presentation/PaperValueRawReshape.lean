import GLang.Proofs.Value.Presentation.PaperValueRawPresentation

namespace GLang.PaperValueDomains
open ValSoundOfDenot DirectOracleReshape

/-- Exact paired-context reshape congruence. The codomain hypotheses apply to
identical arbitrary raw arguments, including the checked/reshaped values that
this evaluator actually pushes. -/
theorem rawPresentation_reshape (orc : FFSOracleSem)
    (target source target' source' : ValTy) (ρ ρ' : ValEnvSem)
    (Γt Γt' Γs Γs' : List ValTy) (Δt Δt' Δs Δs' : List ValValSem)
    (ht : RawTypePresentation orc target target' ⟨ρ,Γt,Δt⟩ ⟨ρ',Γt',Δt'⟩)
    (hs : RawTypePresentation orc source source' ⟨ρ,Γs,Δs⟩ ⟨ρ',Γs',Δs'⟩)
    (v : ValValSem) :
    reshapDenotSemBetweenS orc ρ Γt Δt Γs Δs v target source =
      reshapDenotSemBetweenS orc ρ' Γt' Δt' Γs' Δs' v target' source' := by
  cases target <;> cases target' <;> cases source <;> cases source'
  case space.space.space.space st st' ss ss' =>
    change ValSpace.dof _ st = ValSpace.dof _ st' at ht
    change ValSpace.dof _ ss = ValSpace.dof _ ss' at hs
    cases v <;> simp only [reshapDenotSemBetweenS, reshapArrayBetweenS, ht, hs]
  case space.space.piTy.piTy => cases v <;> simp [reshapDenotSemBetweenS, reshapArrayBetweenS]
  case piTy.piTy.space.space => simp [reshapDenotSemBetweenS]
  case piTy.piTy.piTy.piTy td tc td' tc' sd sc sd' sc' =>
    have htt := ht.1.sameShape orc td td' _ _
    have hss := hs.1.sameShape orc sd sd' _ _
    have he := presentation_carrier orc htt ⟨ρ,Γt,Δt⟩ ⟨ρ',Γt',Δt'⟩
    rw [reshapDenotSemBetweenS.eq_3, reshapDenotSemBetweenS.eq_3]
    apply congrArg Except.ok
    apply ValValSem.fn_congr _ _ he
    intro a
    dsimp only
    have hcheck := presentation_fromElChecked orc td td' htt
      ⟨ρ,Γt,Δt⟩ ⟨ρ',Γt',Δt'⟩ (ht.1.toPresentation orc td td' _ _)
      a (he ▸ a) (cast_heq he a).symm
    rw [hcheck]
    generalize hchk : ValValSem.fromElChecked (denotValTyS orc ρ' Γt' Δt' td')
      (he ▸ a) = chk
    cases chk with
    | error err => rfl
    | ok argT =>
      simp only
      rw [rawPresentation_reshape orc sd td sd' td' ρ ρ'
        Γs Γs' Γt Γt' Δs Δs' Δt Δt' hs.1 ht.1 argT]
      generalize harg : reshapDenotSemBetweenS orc ρ' Γs' Δs' Γt' Δt' argT sd' td' = ar
      cases ar with
      | error err => rfl
      | ok argS =>
        simp only
        have hmatch := toEl_match_denotValTyS_sameShape_raw_local orc sd sd' hss
          ρ ρ' Γs Γs' Δs Δs' argS
          (fun a => match v.applyTyped a with
            | .error err => .error err
            | .ok res => reshapDenotSemBetweenS orc ρ (td::Γt) (argT::Δt)
                (sd::Γs) (argS::Δs) res tc sc)
          (fun a' => match v.applyTyped a' with
            | .error err => .error err
            | .ok res => reshapDenotSemBetweenS orc ρ' (td'::Γt') (argT::Δt')
                (sd'::Γs') (argS::Δs') res tc' sc') (by
          intro a a' haa
          have happ := applyTyped_heq_local
            (presentation_carrier orc hss ⟨ρ,Γs,Δs⟩ ⟨ρ',Γs',Δs'⟩) v a a' haa
          dsimp only
          rw [happ]
          generalize hh : v.applyTyped a' = r
          cases r with
          | error err => rfl
          | ok res =>
            exact rawPresentation_reshape orc tc sc tc' sc' ρ ρ'
              (td::Γt) (td'::Γt') (sd::Γs) (sd'::Γs')
              (argT::Δt) (argT::Δt') (argS::Δs) (argS::Δs') (ht.2 argT) (hs.2 argS) res)
        generalize hl : ValValSem.toEl (denotValTyS orc ρ Γs Δs sd) argS = l at hmatch ⊢
        generalize hr : ValValSem.toEl (denotValTyS orc ρ' Γs' Δs' sd') argS = r at hmatch ⊢
        cases l <;> cases r <;> simpa only using hmatch
  all_goals first | exact ht.elim | exact hs.elim
termination_by sizeOf target + sizeOf source

/-- The actual reshape expression commutes with exact presentation changes. -/
theorem rawPresentation_eval_reshape (orc : FFSOracleSem) (w u : World)
    (e e' : ValExpr) (target source target' source' : ValTy)
    (ht : RawTypePresentation orc target target' w u)
    (hs : RawTypePresentation orc source source' w u)
    (he : denotValB_semS orc w.env w.types w.values e =
      denotValB_semS orc u.env u.types u.values e') :
    denotValB_semS orc w.env w.types w.values (.reshap e target source) =
      denotValB_semS orc u.env u.types u.values (.reshap e' target' source') := by
  rw [denotValB_semS.eq_17, denotValB_semS.eq_17, he]
  cases denotValB_semS orc u.env u.types u.values e' with
  | error err => rfl
  | ok v =>
    simp only [reshapDenotSemS_eq_between]
    exact rawPresentation_reshape orc target source target' source' w.env u.env
      w.types u.types w.types u.types w.values u.values w.values u.values ht hs v

end GLang.PaperValueDomains
