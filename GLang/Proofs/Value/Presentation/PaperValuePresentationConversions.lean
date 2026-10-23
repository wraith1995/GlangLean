import GLang.Proofs.Value.Presentation.PaperValueTypePresentation
import GLang.Proofs.Value.Presentation.PaperValueTypedCorrespondence
import GLang.Proofs.Value.Presentation.PaperValueOpenPush

/-! Exact conversion transport for typed substitution. These results use the
algebraic type presentation on every carrier input, so they preserve raw
callbacks and partial failures without assuming an evaluation theorem. -/
namespace GLang.PaperValueDomains
open ValSoundOfDenot

/-- Reverse an exact change of type presentation. -/
theorem TypePresentation.symm (orc : FFSOracleSem) (τ υ : ValTy)
    (hs : ValTy.SameShape τ υ) (w w' u u' : World)
    (hp : TypePresentation orc τ υ w w' u u') :
    TypePresentation orc υ τ u u' w w' := by
  cases τ <;> cases υ
  case space.space s t => exact ⟨hp.1.symm, hp.2.symm⟩
  case space.piTy => exact hs.elim
  case piTy.space => exact hs.elim
  case piTy.piTy d c d' c' =>
    refine ⟨TypePresentation.symm orc d d' hs.1 w w' u u' hp.1, ?_⟩
    intro a b a' b' ha hb
    exact TypePresentation.symm orc c c' hs.2 _ _ _ _ (hp.2 a' b' a b ha.symm hb.symm)
termination_by sizeOf τ

/-- Compose two exact changes of dependent presentation. -/
theorem TypePresentation.trans (orc : FFSOracleSem) (τ υ ζ : ValTy)
    (hs : ValTy.SameShape τ υ) (ht : ValTy.SameShape υ ζ)
    (w w' u u' z z' : World)
    (hp : TypePresentation orc τ υ w w' u u')
    (hq : TypePresentation orc υ ζ u u' z z') :
    TypePresentation orc τ ζ w w' z z' := by
  cases τ <;> cases υ <;> cases ζ
  case space.space.space s t r => exact ⟨hp.1.trans hq.1, hp.2.trans hq.2⟩
  case piTy.piTy.piTy d c d' c' d'' c'' =>
    refine ⟨TypePresentation.trans orc d d' d'' hs.1 ht.1 _ _ _ _ _ _ hp.1 hq.1, ?_⟩
    intro a b a'' b'' ha hb
    let a' := cast (presentation_carrier orc hs.1 w u) a
    let b' := cast (presentation_carrier orc hs.1 w' u') b
    have haa : HEq a a' := (cast_heq _ a).symm
    have hbb : HEq b b' := (cast_heq _ b).symm
    exact TypePresentation.trans orc c c' c'' hs.2 ht.2 _ _ _ _ _ _
      (hp.2 a b a' b' haa hbb)
      (hq.2 a' b' a'' b'' (haa.symm.trans ha) (hbb.symm.trans hb))
  all_goals first | exact hs.elim | exact ht.elim
termination_by sizeOf τ

/-- Pair independently proved left and right changes of presentation. -/
theorem TypePresentation.pair (orc : FFSOracleSem) (τ υ : ValTy)
    (hs : ValTy.SameShape τ υ) (w w' u u' : World)
    (hl : TypePresentation orc τ υ w w u u)
    (hr : TypePresentation orc τ υ w' w' u' u') :
    TypePresentation orc τ υ w w' u u' := by
  cases τ <;> cases υ
  case space.space s t => exact ⟨hl.1, hr.1⟩
  case space.piTy => exact hs.elim
  case piTy.space => exact hs.elim
  case piTy.piTy d c d' c' =>
    refine ⟨TypePresentation.pair orc d d' hs.1 _ _ _ _ hl.1 hr.1, ?_⟩
    intro a b a' b' ha hb
    exact TypePresentation.pair orc c c' hs.2 _ _ _ _
      (hl.2 a a a' a' ha ha) (hr.2 b b b' b' hb hb)
termination_by sizeOf τ

/-- Reification depends on the finite dimensions and recursive fibres, not on
the syntactic spelling of their space annotations. -/
theorem presentation_fromEl (orc : FFSOracleSem) (τ υ : ValTy)
    (hs : ValTy.SameShape τ υ) (w u : World)
    (hp : TypePresentation orc τ υ w w u u)
    (a : (w.denot orc τ).El) (b : (u.denot orc υ).El) (hab : HEq a b) :
    ValValSem.fromEl (w.denot orc τ) a = ValValSem.fromEl (u.denot orc υ) b := by
  cases τ <;> cases υ
  case space.space s t =>
    obtain rfl := eq_of_heq hab
    simp only [denotValTyS, ValValSem.fromEl, hp.1]
  case space.piTy => exact hs.elim
  case piTy.space => exact hs.elim
  case piTy.piTy d c d' c' =>
    have hd := presentation_carrier orc hs.1 w u
    have hfamilies : HEq
        (fun x : (w.denot orc d).El => Except DimError ((w.push orc d x).denot orc c).El)
        (fun y : (u.denot orc d').El => Except DimError ((u.push orc d' y).denot orc c').El) := by
      refine Function.hfunext hd ?_
      intro x y _
      exact heq_of_eq (congrArg (Except DimError)
        (presentation_carrier orc hs.2 (w.push orc d x) (u.push orc d' y)))
    simp only [denotValTyS, ValValSem.fromEl]
    apply ValValSem.fn_congr _ _ hd
    intro x
    let y := cast hd x
    have hxy : HEq x y := (cast_heq hd x).symm
    have hout : HEq (a x) (b y) := heq_app_dep hd hfamilies hab hxy
    apply except_map_heq_congr
      (presentation_carrier orc hs.2 (w.push orc d x) (u.push orc d' y))
      (a x) (b y) hout
    intro r r' hr
    exact presentation_fromEl orc c c' hs.2 (w.push orc d x) (u.push orc d' y)
      (hp.2 x x y y hxy hxy) r r' hr
termination_by sizeOf τ

/-- The non-resizing reifier also transports, retaining every error. -/
theorem presentation_fromElChecked (orc : FFSOracleSem) (τ υ : ValTy)
    (hs : ValTy.SameShape τ υ) (w u : World)
    (hp : TypePresentation orc τ υ w w u u)
    (a : (w.denot orc τ).El) (b : (u.denot orc υ).El) (hab : HEq a b) :
    ValValSem.fromElChecked (w.denot orc τ) a = ValValSem.fromElChecked (u.denot orc υ) b := by
  cases τ <;> cases υ
  case space.space s t =>
    obtain rfl := eq_of_heq hab
    simp only [denotValTyS, ValValSem.fromElChecked, hp.1]
  case space.piTy => exact hs.elim
  case piTy.space => exact hs.elim
  case piTy.piTy d c d' c' =>
    have hd := presentation_carrier orc hs.1 w u
    have hfamilies : HEq
        (fun x : (w.denot orc d).El => Except DimError ((w.push orc d x).denot orc c).El)
        (fun y : (u.denot orc d').El => Except DimError ((u.push orc d' y).denot orc c').El) := by
      refine Function.hfunext hd ?_
      intro x y _
      exact heq_of_eq (congrArg (Except DimError)
        (presentation_carrier orc hs.2 (w.push orc d x) (u.push orc d' y)))
    simp only [denotValTyS, ValValSem.fromElChecked]
    apply congrArg Except.ok
    apply ValValSem.fn_congr _ _ hd
    intro x
    let y := cast hd x
    have hxy : HEq x y := (cast_heq hd x).symm
    have hout : HEq (a x) (b y) := heq_app_dep hd hfamilies hab hxy
    apply except_bind_heq_congr
      (presentation_carrier orc hs.2 (w.push orc d x) (u.push orc d' y))
      (a x) (b y) hout
    intro r r' hr
    exact presentation_fromElChecked orc c c' hs.2 (w.push orc d x) (u.push orc d' y)
      (hp.2 x x y y hxy hxy) r r' hr
termination_by sizeOf τ

/-- The application's domain decoder respects an exact type presentation.
The immediate base length check remains present. -/
theorem presentation_toElDomainChecked (orc : FFSOracleSem) (τ υ : ValTy)
    (hs : ValTy.SameShape τ υ) (w u : World)
    (hp : TypePresentation orc τ υ w w u u) (v : ValValSem) :
    HEq (ValValSem.toElDomainChecked (w.denot orc τ) v)
      (ValValSem.toElDomainChecked (u.denot orc υ) v) := by
  cases τ <;> cases υ
  case space.space s t =>
    cases v <;> simp only [denotValTyS, ValValSem.toElDomainChecked,
      ValValSem.toElChecked, hp.1] <;> rfl
  case space.piTy => exact hs.elim
  case piTy.space => exact hs.elim
  case piTy.piTy d c d' c' =>
    simpa only [World.denot, denotValTyS, ValValSem.toElDomainChecked] using
      toEl_denotValTyS_sameShape_raw orc (.piTy d c) (.piTy d' c') hs
        w.env u.env w.types u.types w.values u.values v

/-- Exact binary-application congruence for corresponding inferred domains. This is the
application arm of named substitution, with both operand failures included. -/
theorem presentation_eval_appV (orc : FFSOracleSem) (w u : World)
    (f a f' a' : ValExpr)
    (hs : ValTy.SameShape (ValExpr.inferTypeCtx w.types f).domain
      (ValExpr.inferTypeCtx u.types f').domain)
    (hp : TypePresentation orc (ValExpr.inferTypeCtx w.types f).domain
      (ValExpr.inferTypeCtx u.types f').domain w w u u)
    (hf : denotValB_semS orc w.env w.types w.values f =
      denotValB_semS orc u.env u.types u.values f')
    (ha : denotValB_semS orc w.env w.types w.values a =
      denotValB_semS orc u.env u.types u.values a') :
    denotValB_semS orc w.env w.types w.values (.appV f a) =
      denotValB_semS orc u.env u.types u.values (.appV f' a') := by
  rw [denotValB_semS.eq_28, denotValB_semS.eq_28, hf, ha]
  cases hfr : denotValB_semS orc u.env u.types u.values f' with
  | error err => rfl
  | ok v =>
    cases v with
    | array arr => rfl
    | fn T fn =>
      cases har : denotValB_semS orc u.env u.types u.values a' with
      | error err => rfl
      | ok arg =>
        exact valSound_appV_match_congr_domainChecked (.fn T fn) arg arg
          (presentation_carrier orc hs w u)
          (presentation_toElDomainChecked orc _ _ hs w u hp arg)

/-- Fresh-name lambda congruence for the actual current evaluator. The
premise is the opened body's ordinary induction hypothesis for each stored
argument, so it can be supplied by named substitution under a fresh binder. -/
theorem presentation_eval_vlam_open (ρ ρ' : ValEnvSem) (x : VName)
    (d c d' c' : ValTy) (body body' : ValExpr)
    (hs : ValTy.SameShape d d')
    (hp : TypePresentation directOracle d d' ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ ⟨ρ',[],[]⟩)
    (hd : ValTy.lc d) (hd' : ValTy.lc d')
    (hxd : x ∉ ValTy.fv d) (hxd' : x ∉ ValTy.fv d')
    (hxb : x ∉ ValExpr.fv body) (hxb' : x ∉ ValExpr.fv body')
    (hbody : ∀ v,
      denotValB_semS directOracle (ρ.update x v) [] [] (ValExpr.openVar x d body) =
      denotValB_semS directOracle (ρ'.update x v) [] [] (ValExpr.openVar x d' body')) :
    denotValB_semS directOracle ρ [] [] (.vlam d c body) =
      denotValB_semS directOracle ρ' [] [] (.vlam d' c' body') := by
  rw [denotValB_semS, denotValB_semS]
  apply congrArg Except.ok
  have he := presentation_carrier directOracle hs ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩
  apply ValValSem.fn_congr _ _ he
  intro a
  have hraw := presentation_fromEl directOracle d d' hs ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ hp
    a (cast he a) (cast_heq he a).symm
  have h := hbody (ValValSem.fromEl (denotValTyS directOracle ρ [] [] d) a)
  rw [original_eval_openVar ρ x d _ body hd hxd hxb,
    original_eval_openVar ρ' x d' _ body' hd' hxd' hxb'] at h
  simpa only [hraw] using h

/-- A cofinite named codomain induction hypothesis yields exact dependent
arrow presentation. This is the type-binder arm for semantic substitution. -/
theorem presentation_pi_open (ρ ρ' : ValEnvSem) (x : VName)
    (d c d' c' : ValTy) (hdshape : ValTy.SameShape d d') (hcshape : ValTy.SameShape c c')
    (hp : TypePresentation directOracle d d' ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ ⟨ρ',[],[]⟩)
    (hd : ValTy.lc d) (hd' : ValTy.lc d')
    (hxd : x ∉ ValTy.fv d) (hxd' : x ∉ ValTy.fv d')
    (hxc : x ∉ ValTy.fv c) (hxc' : x ∉ ValTy.fv c')
    (hbody : ∀ v, TypePresentation directOracle (ValTy.openVar x d c) (ValTy.openVar x d' c')
      ⟨ρ.update x v,[],[]⟩ ⟨ρ.update x v,[],[]⟩
      ⟨ρ'.update x v,[],[]⟩ ⟨ρ'.update x v,[],[]⟩) :
    TypePresentation directOracle (.piTy d c) (.piTy d' c')
      ⟨ρ,[],[]⟩ ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ ⟨ρ',[],[]⟩ := by
  have fibre : ∀ a b, HEq a b →
      TypePresentation directOracle c c'
        ((World.mk ρ [] []).push directOracle d a) ((World.mk ρ [] []).push directOracle d a)
        ((World.mk ρ' [] []).push directOracle d' b) ((World.mk ρ' [] []).push directOracle d' b) := by
    intro a b hab
    let p := ValValSem.fromEl (denotValTyS directOracle ρ [] [] d) a
    let p' := ValValSem.fromEl (denotValTyS directOracle ρ' [] [] d') b
    have heq : p = p' := presentation_fromEl directOracle d d' hdshape
      ⟨ρ,[],[]⟩ ⟨ρ',[],[]⟩ hp a b hab
    let W : DirectOracleReshape.OpenPushWorld directOracle :=
      ⟨ρ,x,d,p,[],[],rfl,hd,hxd,by simp⟩
    let U : DirectOracleReshape.OpenPushWorld directOracle :=
      ⟨ρ',x,d',p',[],[],rfl,hd',hxd',by simp⟩
    have h₁ := openPush_presentation c W W rfl rfl hxc hxc
    have h₃ := openPush_presentation c' U U rfl rfl hxc' hxc'
    have s₁ := ValTy.SameShape_openRec 0 (.var x d) c
    have s₃ := ValTy.SameShape_openRec 0 (.var x d') c'
    have sm := s₁.trans (hcshape.trans s₃.symm)
    have hm : TypePresentation directOracle (ValTy.openVar x d c) (ValTy.openVar x d' c')
        W.namedWorld W.namedWorld U.namedWorld U.namedWorld := by
      simpa only [W,U,DirectOracleReshape.OpenPushWorld.namedWorld,
        DirectOracleReshape.OpenPushWorld.namedRho,DirectOracleReshape.OpenPushWorld.namedG,
        DirectOracleReshape.OpenPushWorld.namedD,ValTy.closePrefix,heq] using hbody p
    have h₁' := h₁.symm directOracle _ _ s₁ _ _ _ _
    have h₂ := h₁'.trans directOracle _ _ _ s₁.symm sm _ _ _ _ _ _ hm
    have h₄ := h₂.trans directOracle _ _ _ (hcshape.trans s₃.symm) s₃ _ _ _ _ _ _ h₃
    simpa only [W,U,DirectOracleReshape.OpenPushWorld.pushedWorld,
      DirectOracleReshape.OpenPushWorld.pushedRho,DirectOracleReshape.OpenPushWorld.pushedG,
      DirectOracleReshape.OpenPushWorld.pushedD,List.nil_append,World.push,p,p'] using h₄
  refine ⟨hp, ?_⟩
  intro a b a' b' ha hb
  exact TypePresentation.pair directOracle c c' hcshape _ _ _ _ (fibre a a' ha) (fibre b b' hb)

end GLang.PaperValueDomains
