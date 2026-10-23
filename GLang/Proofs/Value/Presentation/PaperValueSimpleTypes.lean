import GLang.Proofs.Value.Presentation.PaperValueQuotient

/-! Nondependent finite-array simple types: arbitrary arrow nesting, no FFS
queries. Their logical relation is exactly the supported PER interpretation.
No statement about all definable terms or arbitrary dependent types is assumed. -/
namespace GLang.PaperValueDomains
open ExtensionalQuotient
universe u v

inductive SimpleSpace where
  | empty | real
  | dsum (s t : SimpleSpace)
  | tprod (s t : SimpleSpace)

def SimpleSpace.toValSpace : SimpleSpace → ValSpace
  | .empty => .empty
  | .real => .real
  | .dsum s t => .dsum s.toValSpace t.toValSpace
  | .tprod s t => .tprod s.toValSpace t.toValSpace

def SimpleSpace.dim : SimpleSpace → Nat
  | .empty => 0
  | .real => 1
  | .dsum s t => s.dim + t.dim
  | .tprod s t => s.dim * t.dim

@[simp] theorem SimpleSpace.dof (s : SimpleSpace) (q : FFSOracle) :
    ValSpace.dof q s.toValSpace = s.dim := by
  induction s <;> simp_all [toValSpace, dim]

inductive SimpleTy where
  | space (s : SimpleSpace)
  | arrow (a b : SimpleTy)

def SimpleTy.toValTy : SimpleTy → ValTy
  | .space s => .space s.toValSpace
  | .arrow a b => .piTy a.toValTy b.toValTy

def SimpleTy.kind : SimpleTy → ValKind
  | .space _ => .base
  | .arrow a b => .arrow a.kind b.kind

def SimpleTy.El : SimpleTy → Type
  | .space _ => FlatArray
  | .arrow a b => a.El → Except DimError b.El

def SimpleTy.per : (t : SimpleTy) → PER t.El
  | .space s => PER.arrays s.dim
  | .arrow a b => a.per.arrow b.per

theorem SimpleTy.carrier_eq (t : SimpleTy) (orc : FFSOracleSem) (w : World) :
    (w.denot orc t.toValTy).El = t.El := by
  induction t generalizing w with
  | space s => rfl
  | arrow a b ha hb =>
      change ((x : (w.denot orc a.toValTy).El) →
        Except DimError ((w.push orc a.toValTy x).denot orc b.toValTy).El) =
        (a.El → Except DimError b.El)
      have hc : (fun x : (w.denot orc a.toValTy).El =>
          Except DimError ((w.push orc a.toValTy x).denot orc b.toValTy).El) =
          (fun _ => Except DimError b.El) :=
        funext fun x => congrArg (Except DimError) (hb (w.push orc a.toValTy x))
      exact (congrArg (fun F : (w.denot orc a.toValTy).El → Type =>
        (x : (w.denot orc a.toValTy).El) → F x) hc).trans
        (congrArg (fun A : Type => A → Except DimError b.El) (ha w))

def SimpleTy.encode (t : SimpleTy) (orc : FFSOracleSem) (w : World)
    (v : (w.denot orc t.toValTy).El) : t.El := cast (t.carrier_eq orc w) v

def SimpleTy.encodeResult (t : SimpleTy) (orc : FFSOracleSem) (w : World)
    (v : Except DimError (w.denot orc t.toValTy).El) : Except DimError t.El :=
  cast (congrArg (Except DimError) (t.carrier_eq orc w)) v

private theorem cast_apply {A B C : Type} {D : A → Type}
    (hA : A = B) (hD : ∀ a, D a = C)
    (hF : ((a : A) → Except DimError (D a)) = (B → Except DimError C))
    (f : (a : A) → Except DimError (D a)) (a : A) :
    cast (congrArg (Except DimError) (hD a)) (f a) = (cast hF f) (cast hA a) := by
  cases hA
  have hD' : D = fun _ => C := funext hD
  cases hD'
  rfl

@[simp] theorem SimpleTy.encode_apply (a b : SimpleTy) (orc : FFSOracleSem) (w : World)
    (f : (w.denot orc (SimpleTy.arrow a b).toValTy).El)
    (x : (w.denot orc a.toValTy).El) :
    (SimpleTy.arrow a b).encode orc w f (a.encode orc w x) =
      b.encodeResult orc (w.push orc a.toValTy x) (f x) :=
  (cast_apply (a.carrier_eq orc w)
    (fun x => b.carrier_eq orc (w.push orc a.toValTy x))
    ((SimpleTy.arrow a b).carrier_eq orc w) f x).symm

private theorem cast_except_ok {A B : Type} (h : A = B) (a : A) :
    cast (congrArg (Except DimError) h) (.ok a) = .ok (cast h a) := by
  cases h
  rfl

private theorem cast_except_error {A B : Type} (h : A = B) (e : DimError) :
    cast (congrArg (Except DimError) h) (.error e) = .error e := by
  cases h
  rfl

@[simp] theorem SimpleTy.encodeResult_ok (t : SimpleTy) (orc : FFSOracleSem) (w : World)
    (v : (w.denot orc t.toValTy).El) :
    t.encodeResult orc w (.ok v) = .ok (t.encode orc w v) :=
  cast_except_ok _ _

@[simp] theorem SimpleTy.encodeResult_error (t : SimpleTy) (orc : FFSOracleSem) (w : World)
    (e : DimError) : t.encodeResult orc w (.error e) = .error e :=
  cast_except_error (t.carrier_eq orc w) e

def SimpleTy.decode (t : SimpleTy) (orc : FFSOracleSem) (w : World)
    (v : t.El) : (w.denot orc t.toValTy).El := cast (t.carrier_eq orc w).symm v

@[simp] theorem SimpleTy.encode_decode (t : SimpleTy) (orc : FFSOracleSem) (w : World)
    (v : t.El) : t.encode orc w (t.decode orc w v) = v := by
  simp [encode, decode]

private theorem partial_encode_iff (t : SimpleTy) (orc : FFSOracleSem) (w w' : World)
    (ih : ∀ a b, Related orc t.toValTy w w' a b ↔
      t.per.rel (t.encode orc w a) (t.encode orc w' b))
    (r : Except DimError (w.denot orc t.toValTy).El)
    (r' : Except DimError (w'.denot orc t.toValTy).El) :
    PartialRel (Related orc t.toValTy w w') r r' ↔
      PartialRel t.per.rel (t.encodeResult orc w r) (t.encodeResult orc w' r') := by
  cases r <;> cases r' <;> simp only [SimpleTy.encodeResult_ok,
    SimpleTy.encodeResult_error, PartialRel]
  exact ih _ _

/-- Arbitrarily nested simple types have the same PER interpretation in every
world, even for a world-dependent oracle: their shapes make no oracle queries. -/
theorem SimpleTy.related_iff (t : SimpleTy) (orc : FFSOracleSem)
    (w w' : World) (a : (w.denot orc t.toValTy).El)
    (b : (w'.denot orc t.toValTy).El) :
    Related orc t.toValTy w w' a b ↔
      t.per.rel (t.encode orc w a) (t.encode orc w' b) := by
  induction t generalizing w w' with
  | space s =>
      have ha : (space s).encode orc w a = a := eq_of_heq (cast_heq _ a)
      have hb : (space s).encode orc w' b = b := eq_of_heq (cast_heq _ b)
      simp only [toValTy, Related, per, PER.arrays, SimpleSpace.dof, ha, hb]
      rfl
  | arrow dom cod ihDom ihCod =>
      constructor
      · intro h x y hxy
        let x' := dom.decode orc w x
        let y' := dom.decode orc w' y
        have hx : dom.encode orc w x' = x := dom.encode_decode orc w x
        have hy : dom.encode orc w' y' = y := dom.encode_decode orc w' y
        have harg : Related orc dom.toValTy w w' x' y' :=
          (ihDom w w' x' y').2 (by simpa only [hx, hy] using hxy)
        have hr := h x' y' harg
        change PartialRel cod.per.rel
          ((SimpleTy.arrow dom cod).encode orc w a x)
          ((SimpleTy.arrow dom cod).encode orc w' b y)
        rw [← hx, ← hy, encode_apply, encode_apply]
        exact (partial_encode_iff cod orc _ _ (ihCod _ _) _ _).1 hr
      · intro h x y hxy
        have harg := (ihDom w w' x y).1 hxy
        have hr := h (dom.encode orc w x) (dom.encode orc w' y) harg
        rw [encode_apply, encode_apply] at hr
        exact (partial_encode_iff cod orc _ _ (ihCod _ _) _ _).2 hr

/-- Unlike arbitrary dependent worlds, simple-type relatedness composes across
any three worlds. All dimensions and higher-order fibres are fixed by syntax. -/
theorem SimpleTy.related_trans (t : SimpleTy) (orc : FFSOracleSem)
    (w₀ w₁ w₂ : World) (a : (w₀.denot orc t.toValTy).El)
    (b : (w₁.denot orc t.toValTy).El) (c : (w₂.denot orc t.toValTy).El)
    (hab : Related orc t.toValTy w₀ w₁ a b)
    (hbc : Related orc t.toValTy w₁ w₂ b c) :
    Related orc t.toValTy w₀ w₂ a c :=
  (t.related_iff orc w₀ w₂ a c).2
    (t.per.trans ((t.related_iff orc w₀ w₁ a b).1 hab)
      ((t.related_iff orc w₁ w₂ b c).1 hbc))

def SimpleTy.semanticPER (t : SimpleTy) (orc : FFSOracleSem) (w : World) :
    PER (w.denot orc t.toValTy).El where
  rel := Related orc t.toValTy w w
  symm := fun h => related_symm orc _ w w _ _ h
  trans := fun h k => t.related_trans orc w w w _ _ _ h k

/-- World-independent runtime version of the simple-type PER. -/
def SimpleTy.runtimeRel : SimpleTy → ValValSem → ValValSem → Prop
  | .space s, .array a, .array b => (PER.arrays s.dim).rel a b
  | .arrow dom cod, .fn T f, .fn U g =>
      ∃ hT : T = dom.El, ∃ hU : U = dom.El,
        ∀ x y, dom.per.rel (hT ▸ x) (hU ▸ y) →
          PartialRel cod.runtimeRel (f x) (g y)
  | _, _, _ => False

private theorem partialRel_congr {A : Type u} {B : Type v} {R S : A → B → Prop}
    (h : ∀ a b, R a b ↔ S a b) (a : Except DimError A) (b : Except DimError B) :
    PartialRel R a b ↔ PartialRel S a b := by
  cases a <;> cases b <;> simp only [PartialRel]
  exact h _ _

private theorem encode_cast (t : SimpleTy) (orc : FFSOracleSem) (w : World)
    {A : Type} (h : A = (w.denot orc t.toValTy).El) (k : A = t.El) (a : A) :
    t.encode orc w (h ▸ a) = k ▸ a := by
  exact eq_of_heq ((cast_heq (t.carrier_eq orc w) (h ▸ a)).trans
    ((cast_heq h a).trans (cast_heq k a).symm))

/-- Actual runtime relatedness at simple types is independent of both worlds.
This is the fibre-transport step needed by a compositional application proof. -/
theorem SimpleTy.runtimeRelated_iff (t : SimpleTy) (orc : FFSOracleSem)
    (w w' : World) (v v' : ValValSem) :
    RuntimeRelated orc t.toValTy w w' v v' ↔ t.runtimeRel v v' := by
  induction t generalizing w w' v v' with
  | space s =>
      cases v <;> cases v' <;>
        simp [toValTy, RuntimeRelated, runtimeRel, Related, PER.arrays, SimpleSpace.dof]
      tauto
  | arrow dom cod ihDom ihCod =>
      cases v <;> cases v' <;> try exact Iff.rfl
      rename_i T f U g
      constructor
      · rintro ⟨hT, hU, hf⟩
        refine ⟨hT.trans (dom.carrier_eq orc w), hU.trans (dom.carrier_eq orc w'), ?_⟩
        intro x y hxy
        apply (partialRel_congr (ihCod _ _) _ _).1
        apply hf x y
        apply (dom.related_iff orc w w' _ _).2
        rw [encode_cast dom orc w hT (hT.trans (dom.carrier_eq orc w)) x,
          encode_cast dom orc w' hU (hU.trans (dom.carrier_eq orc w')) y]
        exact hxy
      · rintro ⟨hT, hU, hf⟩
        refine ⟨hT.trans (dom.carrier_eq orc w).symm,
          hU.trans (dom.carrier_eq orc w').symm, ?_⟩
        intro x y hxy
        apply (partialRel_congr (ihCod _ _) _ _).2
        apply hf x y
        have h := (dom.related_iff orc w w' _ _).1 hxy
        rw [encode_cast dom orc w _ hT x, encode_cast dom orc w' _ hU y] at h
        exact h

theorem SimpleTy.runtimeRelated_world_irrel (t : SimpleTy) (orc : FFSOracleSem)
    (w w' u u' : World) (v v' : ValValSem) :
    RuntimeRelated orc t.toValTy w w' v v' ↔ RuntimeRelated orc t.toValTy u u' v v' :=
  (t.runtimeRelated_iff orc w w' v v').trans (t.runtimeRelated_iff orc u u' v v').symm

theorem SimpleTy.resultRelated_iff (t : SimpleTy) (orc : FFSOracleSem)
    (w w' : World) (r r' : Except DimError ValValSem) :
    PartialRel (RuntimeRelated orc t.toValTy w w') r r' ↔
      PartialRel t.runtimeRel r r' :=
  partialRel_congr (t.runtimeRelated_iff orc w w') r r'

theorem SimpleTy.encodedPartialRelated_iff (t : SimpleTy) (orc : FFSOracleSem)
    (w w' : World) (r : Except DimError (w.denot orc t.toValTy).El)
    (r' : Except DimError (w'.denot orc t.toValTy).El) :
    PartialRel (Related orc t.toValTy w w') r r' ↔
      PartialRel t.per.rel (t.encodeResult orc w r) (t.encodeResult orc w' r') :=
  partial_encode_iff t orc w w' (t.related_iff orc w w') r r'

end GLang.PaperValueDomains
