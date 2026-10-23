import GLang.Value.Supporting.TotalDimensionSemantics

namespace GLang.PaperValueDomains

universe u v w x

/-- Relate partial results, including *matching* failure. -/
def PartialRel {A : Type u} {B : Type v} (R : A → B → Prop) : Except DimError A → Except DimError B → Prop
  | .error e, .error e' => e = e'
  | .ok a, .ok b => R a b
  | _, _ => False

theorem PartialRel.symm {A : Type u} {B : Type v} {R : A → B → Prop} {S : B → A → Prop}
    (hs : ∀ a b, R a b → S b a) {a : Except DimError A} {b : Except DimError B}
    (h : PartialRel R a b) : PartialRel S b a := by
  cases a <;> cases b <;> simp_all [PartialRel]

theorem PartialRel.map {A : Type u} {B : Type v} {C : Type w} {D : Type x} {R : A → B → Prop} {S : C → D → Prop}
    (f : A → C) (g : B → D) (hfg : ∀ a b, R a b → S (f a) (g b))
    {a : Except DimError A} {b : Except DimError B} (h : PartialRel R a b) :
    PartialRel S (a.map f) (b.map g) := by
  cases a <;> cases b <;> simp_all [PartialRel, Except.map]

theorem PartialRel.bind {A : Type u} {B : Type v} {C : Type w} {D : Type x} {R : A → B → Prop} {S : C → D → Prop}
    (f : A → Except DimError C) (g : B → Except DimError D)
    (hfg : ∀ a b, R a b → PartialRel S (f a) (g b))
    {a : Except DimError A} {b : Except DimError B} (h : PartialRel R a b) :
    PartialRel S (a.bind f) (b.bind g) := by
  cases a <;> cases b <;> simp_all [PartialRel, Except.bind]

/-- A semantic world contains the named environment and the actual local stack. -/
structure World where
  env : ValEnvSem
  types : List ValTy
  values : List ValValSem

noncomputable abbrev World.denot (w : World) (orc : FFSOracleSem) (τ : ValTy) :=
  denotValTyS orc w.env w.types w.values τ

noncomputable def World.push (w : World) (orc : FFSOracleSem) (τ : ValTy)
    (a : (w.denot orc τ).El) : World :=
  ⟨w.env, τ :: w.types, ValValSem.fromEl (w.denot orc τ) a :: w.values⟩

/-- Cross-world relation on typed representatives. At arrows this is a genuine
relational contract: related inputs must give related successes or equal errors.
It does not quantify over malformed/unrelated inputs. -/
def Related (orc : FFSOracleSem) : (τ : ValTy) → (w w' : World) →
    (w.denot orc τ).El → (w'.denot orc τ).El → Prop
  | .space s, w, w', a, b => a = b ∧
      a.length = ValSpace.dof (orc w.env w.types w.values) s ∧
      b.length = ValSpace.dof (orc w'.env w'.types w'.values) s
  | .piTy τ₀ τ₁, w, w', f, g =>
      ∀ a b, Related orc τ₀ w w' a b →
        PartialRel (Related orc τ₁ (w.push orc τ₀ a) (w'.push orc τ₀ b)) (f a) (g b)

/-- Runtime version of the same relation. Retaining the actual callback-domain
equalities allows a proved bridge to the evaluator's typed conversions. -/
def RuntimeRelated (orc : FFSOracleSem) :
    ValTy → World → World → ValValSem → ValValSem → Prop
  | .space s, w, w', .array a, .array b => Related orc (.space s) w w' a b
  | .piTy τ₀ τ₁, w, w', .fn T f, .fn U g =>
      ∃ hT : T = (w.denot orc τ₀).El,
      ∃ hU : U = (w'.denot orc τ₀).El,
        ∀ a b, Related orc τ₀ w w' (hT ▸ a) (hU ▸ b) →
          PartialRel (RuntimeRelated orc τ₁
            (w.push orc τ₀ (hT ▸ a)) (w'.push orc τ₀ (hU ▸ b))) (f a) (g b)
  | _, _, _, _, _ => False

/-- Relatedness is symmetric even when the two environments and fibres differ. -/
theorem related_symm (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (a : (w.denot orc τ).El) (b : (w'.denot orc τ).El)
    (h : Related orc τ w w' a b) : Related orc τ w' w b a := by
  cases τ with
  | space s => exact ⟨h.1.symm, h.2.2, h.2.1⟩
  | piTy τ₀ τ₁ =>
    intro x y hxy
    exact PartialRel.symm (fun u v huv => related_symm orc τ₁ _ _ u v huv)
      (h y x (related_symm orc τ₀ _ _ x y hxy))
termination_by sizeOf τ

private theorem resize_self {a : FlatArray} {n : Nat} (h : a.length = n) :
    a.resize n = a := by
  apply FlatArray.ext h.symm
  intro i
  simp [FlatArray.resize, FlatArray.ofFn, FlatArray.get, h]

/-- Ordinary reification preserves the strengthened relation, recursively and
with the exact reified argument worlds used by dependent codomains. -/
theorem reify_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (a : (w.denot orc τ).El) (b : (w'.denot orc τ).El)
    (h : Related orc τ w w' a b) :
    RuntimeRelated orc τ w w'
      (ValValSem.fromEl (w.denot orc τ) a)
      (ValValSem.fromEl (w'.denot orc τ) b) := by
  cases τ with
  | space s =>
    change Related orc (.space s) w w' (a.resize _) (b.resize _)
    rw [resize_self h.2.1, resize_self h.2.2]
    exact h
  | piTy τ₀ τ₁ =>
    refine ⟨rfl, rfl, ?_⟩
    intro x y hxy
    exact PartialRel.map _ _
      (fun u v huv => reify_related orc τ₁ _ _ u v huv) (h x y hxy)
termination_by sizeOf τ

/-- Typed extraction of related runtime values succeeds on both sides and
preserves the full relation, including latent callback errors. -/
theorem extract_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (v v' : ValValSem) (h : RuntimeRelated orc τ w w' v v') :
    ∃ a b, ValValSem.toEl (w.denot orc τ) v = .ok a ∧
      ValValSem.toEl (w'.denot orc τ) v' = .ok b ∧ Related orc τ w w' a b := by
  classical
  cases τ with
  | space s =>
    cases v <;> cases v' <;> try exact h.elim
    exact ⟨_, _, rfl, rfl, h⟩
  | piTy τ₀ τ₁ =>
    cases v <;> cases v' <;> try exact h.elim
    rename_i T f U g
    obtain ⟨hT, hU, hfg⟩ := h
    subst T; subst U
    simp only [World.denot, denotValTyS, ValValSem.toEl, dite_true]
    let f' : (w.denot orc (.piTy τ₀ τ₁)).El := fun y => match f y with
      | .error e => .error e
      | .ok v => ValValSem.toEl ((w.push orc τ₀ y).denot orc τ₁) v
    let g' : (w'.denot orc (.piTy τ₀ τ₁)).El := fun y => match g y with
      | .error e => .error e
      | .ok v => ValValSem.toEl ((w'.push orc τ₀ y).denot orc τ₁) v
    refine ⟨f', g', rfl, rfl, ?_⟩
    intro x y hxy
    have hres := hfg x y hxy
    cases hx : f x <;> cases hy : g y <;> simp only [hx, hy, PartialRel] at hres
    · simp [f', g', hx, hy, PartialRel]
    · obtain ⟨a, b, ha, hb, hab⟩ := extract_related orc τ₁ _ _ _ _ hres
      simpa only [f', g', hx, hy, ha, hb, PartialRel] using hab
termination_by sizeOf τ

/-- The live typed-application primitive respects related functions and inputs.
Its result relation is indexed by the exact two argument-selected fibres. -/
theorem applyTyped_related (orc : FFSOracleSem) (τ₀ τ₁ : ValTy) (w w' : World)
    (f g : ValValSem) (hf : RuntimeRelated orc (.piTy τ₀ τ₁) w w' f g)
    (a : (w.denot orc τ₀).El) (b : (w'.denot orc τ₀).El)
    (hab : Related orc τ₀ w w' a b) :
    PartialRel (RuntimeRelated orc τ₁ (w.push orc τ₀ a) (w'.push orc τ₀ b))
      (ValValSem.applyTyped f a) (ValValSem.applyTyped g b) := by
  classical
  cases f <;> cases g <;> try exact hf.elim
  rename_i T f U g
  obtain ⟨hT, hU, hfg⟩ := hf
  subst T; subst U
  simpa only [ValValSem.applyTyped, dite_true] using hfg a b hab

/-- Extraction preserves related partial results as well as successful values. -/
theorem extract_results_related (orc : FFSOracleSem) (τ : ValTy) (w w' : World)
    (r r' : Except DimError ValValSem) (h : PartialRel (RuntimeRelated orc τ w w') r r') :
    PartialRel (Related orc τ w w')
      (r.bind (ValValSem.toEl (w.denot orc τ)))
      (r'.bind (ValValSem.toEl (w'.denot orc τ))) := by
  apply PartialRel.bind _ _ ?_ h
  intro v v' hv
  obtain ⟨a, b, ha, hb, hab⟩ := extract_related orc τ w w' v v' hv
  simpa only [ha, hb, PartialRel] using hab

/-- For first-order functions the relational contract is exactly equality on
valid array inputs, with equal errors and exact-size successful outputs. -/
theorem firstOrder_related_iff (orc : FFSOracleSem) (w : World) (s t : ValSpace)
    (f g : (w.denot orc (.piTy (.space s) (.space t))).El) :
    Related orc (.piTy (.space s) (.space t)) w w f g ↔
      ∀ a, a.length = ValSpace.dof (orc w.env w.types w.values) s →
        PartialRel (Related orc (.space t)
          (w.push orc (.space s) a) (w.push orc (.space s) a)) (f a) (g a) := by
  constructor
  · intro h a ha
    exact h a a ⟨rfl, ha, ha⟩
  · intro h a b hab
    obtain ⟨rfl, ha, _⟩ := hab
    exact h a ha

/-- Named environments satisfy the strengthened contract at declared entries.
This is additional relational data, not implied by the current unary EnvWF. -/
def EnvironmentsRelated (orc : FFSOracleSem) (ε : ValCtx) (ρ ρ' : ValEnvSem) : Prop :=
  ∀ x τ, ε.lookup x = some τ →
    RuntimeRelated orc τ ⟨ρ, [], []⟩ ⟨ρ', [], []⟩ (ρ x) (ρ' x)

/-- The actual lambda evaluator satisfies the relational contract whenever its
body satisfies the relation in the two pushed worlds (the induction premise of
a future whole-language fundamental theorem). -/
theorem eval_lambda_related (orc : FFSOracleSem) (τ₀ τ₁ : ValTy) (w w' : World)
    (body body' : ValExpr)
    (hbody : ∀ a b, Related orc τ₀ w w' a b →
      PartialRel (RuntimeRelated orc τ₁ (w.push orc τ₀ a) (w'.push orc τ₀ b))
        (denotValB_semS orc (w.push orc τ₀ a).env (w.push orc τ₀ a).types
          (w.push orc τ₀ a).values body)
        (denotValB_semS orc (w'.push orc τ₀ b).env (w'.push orc τ₀ b).types
          (w'.push orc τ₀ b).values body')) :
    PartialRel (RuntimeRelated orc (.piTy τ₀ τ₁) w w')
      (denotValB_semS orc w.env w.types w.values (.vlam τ₀ τ₁ body))
      (denotValB_semS orc w'.env w'.types w'.values (.vlam τ₀ τ₁ body')) := by
  simp only [denotValB_semS, PartialRel]
  exact ⟨rfl, rfl, hbody⟩

/-- The variable case follows from the strengthened environment contract. -/
theorem eval_var_related (orc : FFSOracleSem) (ε : ValCtx) (ρ ρ' : ValEnvSem)
    (hρ : EnvironmentsRelated orc ε ρ ρ') (x : VName) (τ : ValTy)
    (hx : ε.lookup x = some τ) :
    PartialRel (RuntimeRelated orc τ ⟨ρ, [], []⟩ ⟨ρ', [], []⟩)
      (denotValB_semS orc ρ [] [] (.var x τ))
      (denotValB_semS orc ρ' [] [] (.var x τ)) := by
  simpa only [denotValB_semS, PartialRel] using hρ x τ hx

/-- Only the primitive oracle observations actually used by this space's shape.
This permits a later typed-query theorem without requiring agreement on arbitrary
ill-typed oracle queries. -/
def SpaceOracleAgreement (left right : FFSOracle) : ValSpace → Prop
  | .empty | .real => True
  | .dsum s t | .tprod s t =>
      SpaceOracleAgreement left right s ∧ SpaceOracleAgreement left right t
  | .ffs p s e => left p s e = right p s e

/-- Agreement on a space's primitive FFS leaves suffices for both its derived
shape and flattened dimension. No evaluator or numerical assumption is used. -/
theorem leafAgreement_shapes (left right : FFSOracle) (s : ValSpace)
    (h : SpaceOracleAgreement left right s) :
    ValSpace.shpOf left s = ValSpace.shpOf right s ∧
    ValSpace.dof left s = ValSpace.dof right s := by
  have hs : ValSpace.shpOf left s = ValSpace.shpOf right s := by
    cases s with
    | empty => simp only [ValSpace.shpOf]
    | real => simp only [ValSpace.shpOf]
    | dsum s t =>
      simp only [ValSpace.shpOf, (leafAgreement_shapes left right s h.1).2,
        (leafAgreement_shapes left right t h.2).2]
    | tprod s t =>
      simp only [ValSpace.shpOf, (leafAgreement_shapes left right s h.1).2,
        (leafAgreement_shapes left right t h.2).2]
    | ffs p s e => simpa only [ValSpace.shpOf] using congrArg (fun n => [n]) h
  exact ⟨hs, by simpa only [ValSpace.dof] using congrArg (fun ns => ns.foldr (· * ·) 1) hs⟩
termination_by sizeOf s

/-- Compatibility obligations for an independently supplied relation on worlds.
The oracle field requires equality of primitive FFS observations; the push field
ensures related inputs select related dependent worlds. Neither is an axiom. -/
structure WorldCompatibility (orc : FFSOracleSem) (W : World → World → Prop) : Prop where
  oracle : ∀ w w', W w w' → ∀ p s e,
    orc w.env w.types w.values p s e = orc w'.env w'.types w'.values p s e
  push : ∀ w w', W w w' → ∀ τ a b, Related orc τ w w' a b →
    W (w.push orc τ a) (w'.push orc τ b)

/-- Equal primitive oracle observations imply equal derived shapes and sizes.
This covers all space syntax, including dependent FFS expressions. -/
theorem compatible_shapes {orc : FFSOracleSem} {W : World → World → Prop}
    (hW : WorldCompatibility orc W) {w w' : World} (h : W w w') (s : ValSpace) :
    ValSpace.shpOf (orc w.env w.types w.values) s =
      ValSpace.shpOf (orc w'.env w'.types w'.values) s ∧
    ValSpace.dof (orc w.env w.types w.values) s =
      ValSpace.dof (orc w'.env w'.types w'.values) s := by
  have heq : orc w.env w.types w.values = orc w'.env w'.types w'.values :=
    funext fun p => funext fun t => funext fun e => hW.oracle w w' h p t e
  rw [heq]
  exact ⟨rfl, rfl⟩

/-- Dependent shape/size equality after applying related arguments. -/
theorem compatible_fibre_shapes {orc : FFSOracleSem} {W : World → World → Prop}
    (hW : WorldCompatibility orc W) {w w' : World} (h : W w w')
    (τ : ValTy) (a : (w.denot orc τ).El) (b : (w'.denot orc τ).El)
    (hab : Related orc τ w w' a b) (s : ValSpace) :
    ValSpace.shpOf (orc (w.push orc τ a).env (w.push orc τ a).types
      (w.push orc τ a).values) s =
      ValSpace.shpOf (orc (w'.push orc τ b).env (w'.push orc τ b).types
        (w'.push orc τ b).values) s :=
  (compatible_shapes hW (hW.push w w' h τ a b hab) s).1

/-- World-independent oracles satisfy the world compatibility conditions. -/
theorem constantOracle_compatible (q : FFSOracle) :
    WorldCompatibility (FFSOracleSem.const q) (fun _ _ => True) := by
  constructor
  · intros; rfl
  · intros; trivial

end GLang.PaperValueDomains
