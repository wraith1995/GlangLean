import GLang.Proofs.Value.Presentation.PaperValueSimpleTypes
import GLang.Proofs.Value.Presentation.PaperValueCheckedExtensionality
import GLang.Proofs.Value.Presentation.PaperValuePrimitiveLocality
import GLang.Proofs.Value.Presentation.PaperValuePrimitiveSized
import GLang.Proofs.Value.Presentation.PaperValueSimpleReshape

/-! A fundamental theorem for the actual error-capable evaluator on the
simply typed variables, lambdas, applications, and fixed-shape numerical fragment. Its premises describe only
related input environments and stacks, not evaluation of the term or its body. -/
namespace GLang.PaperValueDomains

/-- Typing for a fragment of the existing value syntax. Named bindings retain
their annotations; de Bruijn variables must occur in the local context. -/
inductive SimpleHasType (ε : VName → SimpleTy) : List SimpleTy → ValExpr → SimpleTy → Prop
  | var (Γ : List SimpleTy) (x : VName) :
      SimpleHasType ε Γ (.var x (ε x).toValTy) (ε x)
  | bvar {Γ : List SimpleTy} {n : Nat} {t : SimpleTy} (h : Γ[n]? = some t) :
      SimpleHasType ε Γ (.bvar n) t
  | lam {Γ : List SimpleTy} {body : ValExpr} {a b : SimpleTy}
      (h : SimpleHasType ε (a :: Γ) body b) :
      SimpleHasType ε Γ (.vlam a.toValTy b.toValTy body) (.arrow a b)
  | app {Γ : List SimpleTy} {f a : ValExpr} {s t : SimpleTy}
      (hf : SimpleHasType ε Γ f (.arrow s t)) (ha : SimpleHasType ε Γ a s) :
      SimpleHasType ε Γ (.appV f a) t

  | reshape {Γ : List SimpleTy} {e : ValExpr} {source target : SimpleTy}
      (hkind : source.kind = target.kind)
      (h : SimpleHasType ε Γ e source) :
      SimpleHasType ε Γ (.reshap e target.toValTy source.toValTy) target
  | primitive {Γ : List SimpleTy} {e : ValExpr} {s : SimpleSpace}
      (operandSpace : ValExpr → SimpleSpace)
      (hp : ArrayPrimitive e)
      (ht : ValExpr.inferTypeCtx (Γ.map SimpleTy.toValTy) e = .space s.toValSpace)
      (hspace : ValExpr.inferSpaceCtx (Γ.map SimpleTy.toValTy) e = s.toValSpace)
      (hq : ∀ q ∈ primitiveQuerySpaces (Γ.map SimpleTy.toValTy) e,
        ∃ r : SimpleSpace, q = r.toValSpace)
      (children : ∀ a ∈ primitiveOperands e, SimpleHasType ε Γ a (.space (operandSpace a))) :
      SimpleHasType ε Γ e (.space s)

@[simp] theorem SimpleSpace.raise (s : SimpleSpace) (n k : Nat) :
    ValSpace.raise n k s.toValSpace = s.toValSpace := by
  induction s <;> simp_all [toValSpace, ValSpace.raise]

@[simp] theorem SimpleTy.raise (t : SimpleTy) (n k : Nat) :
    ValTy.raise n k t.toValTy = t.toValTy := by
  induction t generalizing k with
  | space s => simp [toValTy, ValTy.raise]
  | arrow a b ha hb => simp [toValTy, ValTy.raise, ha, hb]

@[simp] theorem SimpleSpace.substBound (s : SimpleSpace) (a : ValExpr) (k : Nat) :
    ValSpace.substBound k a s.toValSpace = s.toValSpace := by
  induction s <;> simp_all [toValSpace, ValSpace.substBound]

@[simp] theorem SimpleTy.substBound (t : SimpleTy) (a : ValExpr) (k : Nat) :
    ValTy.substBound k a t.toValTy = t.toValTy := by
  induction t generalizing k with
  | space s => simp [toValTy, ValTy.substBound]
  | arrow d c hd hc => simp [toValTy, ValTy.substBound, hd, hc]

theorem SimpleHasType.infer {ε : VName → SimpleTy} {Γ : List SimpleTy}
    {e : ValExpr} {t : SimpleTy} (h : SimpleHasType ε Γ e t) :
    ValExpr.inferTypeCtx (Γ.map SimpleTy.toValTy) e = t.toValTy := by
  induction h with
  | var => rfl
  | bvar h => simp [ValExpr.inferTypeCtx, ValTyCtx.lookupUse, List.getD, List.getElem?_map, h]
  | lam => rfl
  | app hf ha ihf iha => simp [ValExpr.inferTypeCtx, ihf, SimpleTy.toValTy, ValTy.applyCodomain]
  | reshape => rfl
  | primitive _ _ ht _ _ _ _ => exact ht

theorem SimpleSpace.oracleAgreement (s : SimpleSpace) (q q' : FFSOracle) :
    SpaceOracleAgreement q q' s.toValSpace := by
  induction s <;> simp_all [toValSpace, SpaceOracleAgreement]

/-- Input contracts constrain only the supplied variables. -/
def SimpleNamedRelated (ε : VName → SimpleTy) (ρ ρ' : ValEnvSem) : Prop :=
  ∀ x, (ε x).runtimeRel (ρ x) (ρ' x)

def SimpleStackRelated (Γ : List SimpleTy) (Δ Δ' : List ValValSem) : Prop :=
  ∀ (n : Nat) (t : SimpleTy), Γ[n]? = some t → ∃ v v', Δ[n]? = some v ∧ Δ'[n]? = some v' ∧ t.runtimeRel v v'

theorem SimpleStackRelated.cons {Γ : List SimpleTy} {Δ Δ' : List ValValSem}
    {t : SimpleTy} {v v' : ValValSem} (h : SimpleStackRelated Γ Δ Δ')
    (hv : t.runtimeRel v v') : SimpleStackRelated (t :: Γ) (v :: Δ) (v' :: Δ') := by
  intro n u hn
  cases n with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hn; subst u; exact ⟨v,v',rfl,rfl,hv⟩
  | succ n => exact h n u (by simpa using hn)

/-- Evaluation of every typed fragment term preserves the relation, including
matching operand failures. Arrow nesting and higher-order arguments are unrestricted. -/
theorem SimpleHasType.eval_related {ε : VName → SimpleTy} {Γ : List SimpleTy}
    {e : ValExpr} {t : SimpleTy} (h : SimpleHasType ε Γ e t)
    (orc : FFSOracleSem) (w w' : World)
    (hw : w.types = Γ.map SimpleTy.toValTy) (hw' : w'.types = Γ.map SimpleTy.toValTy)
    (hEnv : SimpleNamedRelated ε w.env w'.env)
    (hStack : SimpleStackRelated Γ w.values w'.values) :
    PartialRel t.runtimeRel
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semS orc w'.env w'.types w'.values e) := by
  induction h generalizing w w' with
  | var Γ x => simpa only [denotValB_semS, PartialRel] using hEnv x
  | bvar hn =>
      obtain ⟨v,v',hv,hv',hr⟩ := hStack _ _ hn
      simpa only [denotValB_semS, StrictValueAccess.lookup, hv, hv', PartialRel] using hr
  | @lam Γ body a b ht ih =>
      apply (SimpleTy.resultRelated_iff (.arrow a b) orc w w' _ _).1
      apply eval_lambda_related
      intro x y hxy
      apply (b.resultRelated_iff orc _ _ _ _).2
      apply ih
      · simpa [World.push] using congrArg (List.cons a.toValTy) hw
      · simpa [World.push] using congrArg (List.cons a.toValTy) hw'
      · exact hEnv
      · apply hStack.cons
        exact (a.runtimeRelated_iff orc w w' _ _).1 (reify_related orc a.toValTy w w' x y hxy)
  | @app Γ ef ea s t hf ha ihf iha =>
      have hF := ihf w w' hw hw' hEnv hStack
      have hA := iha w w' hw hw' hEnv hStack
      cases hfl : denotValB_semS orc w.env w.types w.values ef with
      | error err =>
          cases hfr : denotValB_semS orc w'.env w'.types w'.values ef with
          | error err' =>
              have he : err = err' := by simpa only [hfl,hfr,PartialRel] using hF
              subst err'
              simp only [denotValB_semS.eq_28, hfl, hfr, PartialRel]
          | ok f' => simp only [hfl,hfr,PartialRel] at hF
      | ok f =>
          cases hfr : denotValB_semS orc w'.env w'.types w'.values ef with
          | error err => simp only [hfl,hfr,PartialRel] at hF
          | ok g =>
              have hfg : RuntimeRelated orc (.piTy s.toValTy t.toValTy) w w' f g :=
                ((SimpleTy.arrow s t).runtimeRelated_iff orc w w' f g).2
                  (by simpa only [hfl,hfr,PartialRel] using hF)
              cases f with
              | array arr => cases g <;> exact hfg.elim
              | fn T f =>
                cases g with
                | array arr => exact hfg.elim
                | fn U g =>
                  cases hal : denotValB_semS orc w.env w.types w.values ea with
                  | error err =>
                      cases har : denotValB_semS orc w'.env w'.types w'.values ea with
                      | error err' =>
                          have he : err = err' := by simpa only [hal,har,PartialRel] using hA
                          subst err'
                          simp only [denotValB_semS.eq_28,hfl,hfr,hal,har,PartialRel]
                      | ok a' => simp only [hal,har,PartialRel] at hA
                  | ok a =>
                      cases har : denotValB_semS orc w'.env w'.types w'.values ea with
                      | error err => simp only [hal,har,PartialRel] at hA
                      | ok b =>
                          have hab := (s.runtimeRelated_iff orc w w' a b).2
                            (by simpa only [hal,har,PartialRel] using hA)
                          have hdom : (ValExpr.inferTypeCtx w.types ef).domain = s.toValTy := by
                            rw [hw,hf.infer]; rfl
                          have hdom' : (ValExpr.inferTypeCtx w'.types ef).domain = s.toValTy := by
                            rw [hw',hf.infer]; rfl
                          obtain ⟨x,y,_hx,_hy,_hxy,hr⟩ := eval_appV_related orc s.toValTy t.toValTy
                            t.toValTy t.toValTy w w' ef ea ef ea (.fn T f) (.fn U g) a b
                            hdom hdom' hfl hfr hal har hfg hab
                          exact (t.resultRelated_iff orc _ _ _ _).1 hr
  | @reshape Γ e source target hkind ht ih =>
      exact SimpleTy.eval_reshape_related target source orc w w' e e
        (ih w w' hw hw' hEnv hStack)
  | @primitive Γ e s operandSpace hp ht hspace hq children ih =>
      apply ((SimpleTy.space s).resultRelated_iff orc w w' _ _).1
      apply arrayPrimitive_related_of_eval_eq orc w w' e s.toValSpace hp
      · have hs : ValExpr.inferSpaceCtx w.types e = s.toValSpace := by
          rw [hw, hspace]
        rw [hs]
      · have hs : ValExpr.inferSpaceCtx w'.types e = s.toValSpace := by
          rw [hw', hspace]
        rw [hs]
      · apply arrayPrimitive_eval_congr_local orc e w w' hp (hw.trans hw'.symm)
        · intro q hmem
          obtain ⟨r, rfl⟩ := hq q (by simpa only [hw] using hmem)
          exact r.oracleAgreement _ _
        · intro a ha
          exact base_results_eq
            (((SimpleTy.space (operandSpace a)).resultRelated_iff orc w w' _ _).2
              (ih a ha w w' hw hw' hEnv hStack))

theorem SimpleHasType.eval_runtime_related {ε : VName → SimpleTy} {Γ : List SimpleTy}
    {e : ValExpr} {t : SimpleTy} (h : SimpleHasType ε Γ e t)
    (orc : FFSOracleSem) (w w' : World)
    (hw : w.types = Γ.map SimpleTy.toValTy) (hw' : w'.types = Γ.map SimpleTy.toValTy)
    (hEnv : SimpleNamedRelated ε w.env w'.env)
    (hStack : SimpleStackRelated Γ w.values w'.values) :
    PartialRel (RuntimeRelated orc t.toValTy w w')
      (denotValB_semS orc w.env w.types w.values e)
      (denotValB_semS orc w'.env w'.types w'.values e) :=
  (t.resultRelated_iff orc w w' _ _).2 (h.eval_related orc w w' hw hw' hEnv hStack)

/-- The live evaluator followed by checked extraction and the proved simple
carrier identification. Errors are retained at both stages. -/
noncomputable def SimpleTy.interpret (t : SimpleTy) (orc : FFSOracleSem)
    (w : World) (e : ValExpr) : Except DimError t.El :=
  t.encodeResult orc w ((denotValB_semS orc w.env w.types w.values e).bind
    (ValValSem.toElChecked (w.denot orc t.toValTy)))

theorem SimpleHasType.interpret_related {ε : VName → SimpleTy} {Γ : List SimpleTy}
    {e : ValExpr} {t : SimpleTy} (h : SimpleHasType ε Γ e t)
    (orc : FFSOracleSem) (w w' : World)
    (hw : w.types = Γ.map SimpleTy.toValTy) (hw' : w'.types = Γ.map SimpleTy.toValTy)
    (hEnv : SimpleNamedRelated ε w.env w'.env)
    (hStack : SimpleStackRelated Γ w.values w'.values) :
    PartialRel t.per.rel (t.interpret orc w e) (t.interpret orc w' e) :=
  (t.encodedPartialRelated_iff orc w w' _ _).1
    (extract_checked_results_related orc t.toValTy w w' _ _
      (h.eval_runtime_related orc w w' hw hw' hEnv hStack))

/-- A self-related input world supplies an actual supported output quotient
class. No choice of a function's behavior on malformed arguments is exposed. -/
noncomputable def SimpleHasType.interpretClass {ε : VName → SimpleTy} {Γ : List SimpleTy}
    {e : ValExpr} {t : SimpleTy} (h : SimpleHasType ε Γ e t)
    (orc : FFSOracleSem) (w : World) (hw : w.types = Γ.map SimpleTy.toValTy)
    (hEnv : SimpleNamedRelated ε w.env w.env)
    (hStack : SimpleStackRelated Γ w.values w.values) : t.per.result.Domain :=
  Quotient.mk _ ⟨t.interpret orc w e, h.interpret_related orc w w hw hw hEnv hStack⟩

/-- Equivalent supported input worlds yield the same interpreted quotient
result, including the error class when evaluation fails. -/
theorem SimpleHasType.interpretClass_eq {ε : VName → SimpleTy} {Γ : List SimpleTy}
    {e : ValExpr} {t : SimpleTy} (h : SimpleHasType ε Γ e t)
    (orc : FFSOracleSem) (w w' : World)
    (hw : w.types = Γ.map SimpleTy.toValTy) (hw' : w'.types = Γ.map SimpleTy.toValTy)
    (hEnvSelf : SimpleNamedRelated ε w.env w.env)
    (hEnvSelf' : SimpleNamedRelated ε w'.env w'.env)
    (hStackSelf : SimpleStackRelated Γ w.values w.values)
    (hStackSelf' : SimpleStackRelated Γ w'.values w'.values)
    (hEnv : SimpleNamedRelated ε w.env w'.env)
    (hStack : SimpleStackRelated Γ w.values w'.values) :
    h.interpretClass orc w hw hEnvSelf hStackSelf =
      h.interpretClass orc w' hw' hEnvSelf' hStackSelf' :=
  Quotient.sound (h.interpret_related orc w w' hw hw' hEnv hStack)

end GLang.PaperValueDomains
