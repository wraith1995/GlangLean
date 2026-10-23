import GLang.Value.SemanticValues

/-! Type and expression interpretation using total dimension queries. -/
namespace GLang

noncomputable def denotValTyS (orc : FFSOracleSem) :
    ValEnvSem → List ValTy → List ValValSem → ValTy → ValTypeSem
  | ρ, Γ, Δ, .space s => .space s (ValSpace.dof (orc ρ Γ Δ) s)
  | ρ, Γ, Δ, .piTy τ₀ τ₁ =>
      let τ₀_sem := denotValTyS orc ρ Γ Δ τ₀
      .piTy τ₀_sem.El (fun (v : τ₀_sem.El) =>
        denotValTyS orc ρ (τ₀ :: Γ) (ValValSem.fromEl τ₀_sem v :: Δ) τ₁)

@[simp] theorem denotValTyS_space (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (s : ValSpace) :
    denotValTyS orc ρ Γ Δ (.space s)
      = .space s (ValSpace.dof (orc ρ Γ Δ) s) := rfl

/-! Higher-order reshape by recursion on kind size. Function arguments
are converted to the source domain and results to the target codomain. -/
/-- Base-space reshape is a checked reinterpretation of one flat array.
The array must first be a complete representation of the declared source
space, and the source and target spaces must have the same dimension in their
respective contexts.  Keeping this check in a helper preserves the public
four-equation interface of the higher-order reshape functions. -/
noncomputable def reshapArrayBetweenS (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γt : List ValTy) (Δt : List ValValSem)
    (Γs : List ValTy) (Δs : List ValValSem)
    (a : FlatArray) (st : ValSpace) (τ_src : ValTy) :
    Except DimError ValValSem :=
  match τ_src with
  | .space ss =>
      let ns := ValSpace.dof (orc ρ Γs Δs) ss
      let nt := ValSpace.dof (orc ρ Γt Δt) st
      if a.length = ns then
        if ns = nt then .ok (.array a) else .error .mismatch
      else .error .mismatch
  | .piTy _ _ => .error .mismatch

/-- Paired-context implementation of higher-order reshape.  Target and source
contexts coincide at the public entry point, but differ beneath a Π: the
target codomain is interpreted after pushing the original target argument,
while the source codomain is interpreted after pushing the reshaped source
argument.  This is essential for dependent FFS dimensions observed by
`FFSOracleSem`.

The result stays untyped.  At a Π, the callback first canonicalizes its typed
target argument, recursively reshapes that raw value to the source domain,
decodes the exact resulting raw source value, applies the source function, and
then recursively reshapes the result under the two correctly extended
contexts. -/
noncomputable def reshapDenotSemBetweenS (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γt : List ValTy) (Δt : List ValValSem)
    (Γs : List ValTy) (Δs : List ValValSem) :
    ValValSem → ValTy → ValTy → Except DimError ValValSem
  | .array a, .space st, τ_src =>
      reshapArrayBetweenS orc ρ Γt Δt Γs Δs a st τ_src
  | .fn _ _, .space _, _ => .error .mismatch
  | v, .piTy τt₀ τt₁, .piTy τs₀ τs₁ =>
      let Tt₀ := denotValTyS orc ρ Γt Δt τt₀
      let Ts₀ := denotValTyS orc ρ Γs Δs τs₀
      .ok (.fn Tt₀.El (fun (a : Tt₀.El) =>
        match ValValSem.fromElChecked Tt₀ a with
        | .error e => .error e
        | .ok argT =>
            match reshapDenotSemBetweenS orc ρ Γs Δs Γt Δt argT τs₀ τt₀ with
            | .error e => .error e
            | .ok argS =>
                match ValValSem.toEl Ts₀ argS with
                | .error e => .error e
                | .ok argEl =>
                    match v.applyTyped argEl with
                    | .error e => .error e
                    | .ok res =>
                        reshapDenotSemBetweenS orc ρ
                          (τt₀ :: Γt) (argT :: Δt)
                          (τs₀ :: Γs) (argS :: Δs)
                          res τt₁ τs₁))
  | _v, .piTy _ _, .space _ =>
      .error .mismatch
  termination_by _v τt τs => ValTy.kindSize τt + ValTy.kindSize τs
  decreasing_by
    all_goals (simp only [ValTy.kindSize_piTy]; omega)

/-- Higher-order reshape. Function binders use separate source and target value contexts. -/
noncomputable def reshapDenotSemS (orc : FFSOracleSem) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) :
    ValValSem → ValTy → ValTy → Except DimError ValValSem
  | .array a, .space st, τ_src =>
      reshapArrayBetweenS orc ρ Γ Δ Γ Δ a st τ_src
  | .fn _ _, .space _, _ => .error .mismatch
  | v, .piTy τt₀ τt₁, .piTy τs₀ τs₁ =>
      let Tt₀ := denotValTyS orc ρ Γ Δ τt₀
      let Ts₀ := denotValTyS orc ρ Γ Δ τs₀
      .ok (.fn Tt₀.El (fun (a : Tt₀.El) =>
        match ValValSem.fromElChecked Tt₀ a with
        | .error e => .error e
        | .ok argT =>
            match reshapDenotSemBetweenS orc ρ Γ Δ Γ Δ argT τs₀ τt₀ with
            | .error e => .error e
            | .ok argS =>
                match ValValSem.toEl Ts₀ argS with
                | .error e => .error e
                | .ok argEl =>
                    match v.applyTyped argEl with
                    | .error e => .error e
                    | .ok res =>
                        reshapDenotSemBetweenS orc ρ
                          (τt₀ :: Γ) (argT :: Δ)
                          (τs₀ :: Γ) (argS :: Δ)
                          res τt₁ τs₁))
  | _v, .piTy _ _, .space _ => .error .mismatch

/-- Candidate columns for `RREFRep`.  `termCoords` is the row-major
concatenation of `K` vectors in an `N`-dimensional basis.  RREF sees those
vectors as columns, followed by the full coordinate basis; the identity tail
ensures that the candidate family spans the ambient space. -/
def termsCandidateMatrix (N K : Nat) (termCoords : Nat -> Real) :
    Matrix (Fin N) (Fin (K + N)) Real :=
  fun i j =>
    if j.val < K then
      termCoords (j.val * N + i.val)
    else if i.val = j.val - K then 1 else 0

/-- Matrix computed by `RREFRep`. -/
noncomputable def termsRREFRepMatrix (N K : Nat)
    (termCoords oldCob : Nat -> Real) : Matrix (Fin N) (Fin N) Real :=
  let A := termsCandidateMatrix N K termCoords
  let C := denotAsMatrix N N oldCob
  C * (matrixRREF A).E_inv.transpose

/-- Flat row-major form of `termsRREFRepMatrix`. -/
noncomputable def termsRREFRepDenot (N K : Nat)
    (termCoords oldCob : Nat -> Real) : Nat -> Real :=
  matrixAsDenot (termsRREFRepMatrix N K termCoords oldCob)

noncomputable def denotValB_semS (orc : FFSOracleSem) :
    ValEnvSem → List ValTy → List ValValSem → ValExpr → Except DimError ValValSem
  | _ρ, _Γ, Δ, .bvar n      => StrictValueAccess.lookup Δ n
  | ρ, _Γ, _Δ, .var x _     => .ok (ρ x)
  | ρ, Γ, Δ, whole@(.rlit r) =>
      .ok (.arrayOf (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole))
        (fun i => if i = 0 then r else 0))
  | ρ, Γ, Δ, whole@(.zero _) =>
      .ok (.arrayOf (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole))
        (fun _ => 0))
  | ρ, Γ, Δ, whole@(.scale e₀ e₁)  =>
      ValValSem.bindArrays (denotValB_semS orc ρ Γ Δ e₀)
        (denotValB_semS orc ρ Γ Δ e₁) fun a₀ a₁ =>
          if ValueShape.scale (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
            .ok (.arrayOf
              (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole))
              (fun i => a₀.get 0 * a₁.get i))
          else .error .mismatch
  | ρ, Γ, Δ, .vadd s e₀ e₁   =>
      ValValSem.bindArrays (denotValB_semS orc ρ Γ Δ e₀)
        (denotValB_semS orc ρ Γ Δ e₁) fun a₀ a₁ =>
          let n := ValSpace.dof (orc ρ Γ Δ) s
          if h₀ : a₀.length = n then
            if h₁ : a₁.length = n then
              .ok (.array (FlatArray.zipWith n (fun x y => x + y) a₀ a₁ h₀ h₁))
            else .error .mismatch
          else .error .mismatch
  | ρ, Γ, Δ, whole@(.delta n s)   =>
      .ok (.arrayOf (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole))
        (fun i => if i = n ∧ n < ValSpace.dof (orc ρ Γ Δ) s then 1 else 0))
  | ρ, Γ, Δ, whole@(.idelta s)    =>
      .ok (.arrayOf (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
        let d := ValSpace.dof (orc ρ Γ Δ) s
        if d = 0 then 0
        else if i < d * d then
          let r := i / d
          let c := i % d
          if r = c ∧ r < d then 1 else 0
        else 0))
  | ρ, Γ, Δ, whole@(.tprodE e₀ e₁) =>
      ValValSem.bindArrays (denotValB_semS orc ρ Γ Δ e₀)
        (denotValB_semS orc ρ Γ Δ e₁) fun a₀ a₁ =>
          if ValueShape.pair (orc ρ Γ Δ)
              (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
            .ok (.arrayOf
              (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                let d₁ := ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ e₁)
                let i₀ := i / d₁
                let i₁ := i % d₁
                a₀.get i₀ * a₁.get i₁))
          else .error .mismatch
  | ρ, Γ, Δ, whole@(.dsumE e₀ e₁)  =>
      ValValSem.bindArrays (denotValB_semS orc ρ Γ Δ e₀)
        (denotValB_semS orc ρ Γ Δ e₁) fun a₀ a₁ =>
          if ValueShape.pair (orc ρ Γ Δ)
              (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
            .ok (.arrayOf
              (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                let d₀ := ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ e₀)
                if i < d₀ then a₀.get i else a₁.get (i - d₀)))
          else .error .mismatch
  | ρ, Γ, Δ, whole@(.vtrans e)     =>
      ValValSem.bindArray (denotValB_semS orc ρ Γ Δ e) fun a =>
        if ValueShape.tensor (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ e) a then
          .ok (.arrayOf
            (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
              match ValExpr.inferSpaceCtx Γ e with
              | .tprod s0 s1 =>
                  let d₀ := ValSpace.dof (orc ρ Γ Δ) s0
                  let d₁ := ValSpace.dof (orc ρ Γ Δ) s1
                  if i ≥ d₁ * d₀ then 0
                  else
                    let r := i / d₀
                    let c := i % d₀
                    a.get (d₁ * c + r)
              | _ => 0))
        else .error .mismatch
  | ρ, Γ, Δ, whole@(.ttv s e₀ e₁)  =>
      ValValSem.bindArrays (denotValB_semS orc ρ Γ Δ e₀)
        (denotValB_semS orc ρ Γ Δ e₁) fun a₀ a₁ =>
          if ValueShape.ttv (orc ρ Γ Δ) s
              (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
            .ok (.arrayOf
              (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                let d_contract := ValSpace.dof (orc ρ Γ Δ) s
                match ValExpr.inferSpaceCtx Γ e₀ with
                | .tprod _ s_out =>
                    let d_out := ValSpace.dof (orc ρ Γ Δ) s_out
                    if i ≥ d_out then 0
                    else (Finset.range d_contract).sum fun j =>
                      a₀.get (d_out * j + i) * a₁.get j
                | _ =>
                    if i = 0 then (Finset.range d_contract).sum fun j =>
                      a₀.get j * a₁.get j
                    else 0))
          else .error .mismatch
  | ρ, Γ, Δ, whole@(.mtm _ _ s_contract _ e₀ e₁) =>
      ValValSem.bindArrays (denotValB_semS orc ρ Γ Δ e₀)
        (denotValB_semS orc ρ Γ Δ e₁) fun a₀ a₁ =>
          if ValueShape.mtm (orc ρ Γ Δ) s_contract
              (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
            .ok (.arrayOf
              (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                let d_contract := ValSpace.dof (orc ρ Γ Δ) s_contract
                match ValExpr.inferSpaceCtx Γ e₀, ValExpr.inferSpaceCtx Γ e₁ with
                | .tprod _ s_0, .tprod s_target _ =>
                    let d_0 := ValSpace.dof (orc ρ Γ Δ) s_0
                    let d_target := ValSpace.dof (orc ρ Γ Δ) s_target
                    if i ≥ d_target * d_0 then 0
                    else
                      let r := i / d_0
                      let c := i % d_0
                      (Finset.range d_contract).sum fun k =>
                        a₀.get (d_0 * k + c) * a₁.get (d_contract * r + k)
                | _, _ => 0))
          else .error .mismatch
  | ρ, Γ, Δ, whole@(.vkrn e e')    =>
      ValValSem.bindArrays (denotValB_semS orc ρ Γ Δ e)
        (denotValB_semS orc ρ Γ Δ e') fun a a' =>
          if ValueShape.matrices (orc ρ Γ Δ)
              (ValExpr.inferSpaceCtx Γ e) (ValExpr.inferSpaceCtx Γ e') a a' then
            .ok (.arrayOf
              (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                match ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ e' with
                | .tprod _ s2, .tprod s1 s3 =>
                    let d_1 := ValSpace.dof (orc ρ Γ Δ) s1
                    let d_2 := ValSpace.dof (orc ρ Γ Δ) s2
                    let d_3 := ValSpace.dof (orc ρ Γ Δ) s3
                    let d_right_out := d_2 * d_3
                    let i_left := i / d_right_out
                    let i_right := i % d_right_out
                    let i_0 := i_left / d_1
                    let i_1 := i_left % d_1
                    let j_0 := i_right / d_3
                    let j_1 := i_right % d_3
                    a.get (d_2 * i_0 + j_0) * a'.get (d_3 * i_1 + j_1)
                | _, _ => 0))
          else .error .mismatch
  | ρ, Γ, Δ, whole@(.vblk e e')    =>
      ValValSem.bindArrays (denotValB_semS orc ρ Γ Δ e)
        (denotValB_semS orc ρ Γ Δ e') fun a a' =>
          if ValueShape.matrices (orc ρ Γ Δ)
              (ValExpr.inferSpaceCtx Γ e) (ValExpr.inferSpaceCtx Γ e') a a' then
            .ok (.arrayOf
              (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                match ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ e' with
                | .tprod s0 s2, .tprod _ s3 =>
                    let d_0 := ValSpace.dof (orc ρ Γ Δ) s0
                    let d_2 := ValSpace.dof (orc ρ Γ Δ) s2
                    let d_3 := ValSpace.dof (orc ρ Γ Δ) s3
                    let d_right_out := d_2 + d_3
                    let i_left := i / d_right_out
                    let i_right := i % d_right_out
                    if i_left < d_0 then
                      if i_right < d_2 then a.get (d_2 * i_left + i_right) else 0
                    else if i_right < d_2 then 0
                    else a'.get (d_3 * (i_left - d_0) + (i_right - d_2))
                | _, _ => 0))
          else .error .mismatch
  -- A bounded sum evaluates exactly its semantic index range. A syntactic
  -- family may supply extra inactive candidates (the compiler uses dofUB),
  -- but may not omit an active index or supply an incorrectly sized summand.
  | ρ, Γ, Δ, whole@(.vsum s es)    =>
      let count := ValSpace.dof (orc ρ Γ Δ) s
      if count ≤ es.length then
        let active := es.take count
        let rs := active.attach.map fun e => denotValB_semS orc ρ Γ Δ e.1
        match ValValSem.sequenceArrays rs with
        | .error err => .error err
        | .ok arrays =>
            let width := ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)
            if ValueShape.family count width arrays then
              .ok (.arrayOf width (fun j =>
                (Finset.range count).sum fun i =>
                  match arrays[i]? with
                  | some a => a.get j
                  | none => 0))
            else .error .mismatch
      else .error .mismatch

  | ρ, Γ, Δ, .reshap e τ τ₀ =>
      match denotValB_semS orc ρ Γ Δ e with
      | .error err => .error err
      | .ok v => reshapDenotSemS orc ρ Γ Δ v τ τ₀
  -- `.pinv` — routes through `matrixSVDPinv`.  Flat arrays carry their
  -- runtime length separately from the inferred operand space, so check that
  -- length before converting to a matrix.  This prevents `denotAsMatrix` from
  -- silently zero-padding a short operand or truncating a long one.
  | ρ, Γ, Δ, whole@(.pinv e)       =>
      ValValSem.bindArray (denotValB_semS orc ρ Γ Δ e) fun a =>
        match ValExpr.inferSpaceCtx Γ e with
        | .tprod s0 s1 =>
            let d0 := ValSpace.dof (orc ρ Γ Δ) s0
            let d1 := ValSpace.dof (orc ρ Γ Δ) s1
            if a.length = d0 * d1 then
              .ok (.arrayOf
                (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let M : Matrix (Fin d0) (Fin d1) ℝ := denotAsMatrix d0 d1 a.get
                  matrixAsDenot (matrixSVDPinv M) i))
            else .error .mismatch
        | s =>
            let d := ValSpace.dof (orc ρ Γ Δ) s
            if a.length = d then
              .ok (.arrayOf
                (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let M : Matrix (Fin d) (Fin 1) ℝ := fun j _ => a.get j.val
                  matrixAsDenot (matrixSVDPinv M) i))
            else .error .mismatch

  | ρ, Γ, Δ, whole@(.gsvdS e a b) =>
      ValValSem.bindArrays3 (denotValB_semS orc ρ Γ Δ e)
        (denotValB_semS orc ρ Γ Δ a) (denotValB_semS orc ρ Γ Δ b)
        fun ae aa ab =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof (orc ρ Γ Δ) s0
              let d1 := ValSpace.dof (orc ρ Γ Δ) s1
              match ValueCanonicalFSV.evalSigma d0 d1 ae aa ab with
              | .error err => .error err
              | .ok r =>
                  if r.rows * r.cols =
                      ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole) then
                    .ok (.array r.flatten)
                  else .error .mismatch
          | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gsvdU e a b) =>
      ValValSem.bindArrays3 (denotValB_semS orc ρ Γ Δ e)
        (denotValB_semS orc ρ Γ Δ a) (denotValB_semS orc ρ Γ Δ b)
        fun ae aa ab =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof (orc ρ Γ Δ) s0
              let d1 := ValSpace.dof (orc ρ Γ Δ) s1
              match ValueCanonicalFSV.eval .cokernel d0 d1 ae aa ab with
              | .error err => .error err
              | .ok r =>
                  if r.rows * r.cols =
                      ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole) then
                    .ok (.array r.flatten)
                  else .error .mismatch
          | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gsvdUI e a b) =>
      ValValSem.bindArrays3 (denotValB_semS orc ρ Γ Δ e)
        (denotValB_semS orc ρ Γ Δ a) (denotValB_semS orc ρ Γ Δ b)
        fun ae aa ab =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof (orc ρ Γ Δ) s0
              let d1 := ValSpace.dof (orc ρ Γ Δ) s1
              match ValueCanonicalFSV.eval .kernel d0 d1 ae aa ab with
              | .error err => .error err
              | .ok r =>
                  if r.rows * r.cols =
                      ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole) then
                    .ok (.array r.flatten)
                  else .error .mismatch
          | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gsvdV e a b) =>
      ValValSem.bindArrays3 (denotValB_semS orc ρ Γ Δ e)
        (denotValB_semS orc ρ Γ Δ a) (denotValB_semS orc ρ Γ Δ b)
        fun ae aa ab =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof (orc ρ Γ Δ) s0
              let d1 := ValSpace.dof (orc ρ Γ Δ) s1
              match ValueCanonicalFSV.eval .image d0 d1 ae aa ab with
              | .error err => .error err
              | .ok r =>
                  if r.rows * r.cols =
                      ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole) then
                    .ok (.array r.flatten)
                  else .error .mismatch
          | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gsvdVI e a b) =>
      ValValSem.bindArrays3 (denotValB_semS orc ρ Γ Δ e)
        (denotValB_semS orc ρ Γ Δ a) (denotValB_semS orc ρ Γ Δ b)
        fun ae aa ab =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof (orc ρ Γ Δ) s0
              let d1 := ValSpace.dof (orc ρ Γ Δ) s1
              match ValueCanonicalFSV.eval .coimage d0 d1 ae aa ab with
              | .error err => .error err
              | .ok r =>
                  if r.rows * r.cols =
                      ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole) then
                    .ok (.array r.flatten)
                  else .error .mismatch
          | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gpinv e a b)  =>
      ValValSem.bindArrays3 (denotValB_semS orc ρ Γ Δ e)
        (denotValB_semS orc ρ Γ Δ a) (denotValB_semS orc ρ Γ Δ b)
        fun ae aa ab =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof (orc ρ Γ Δ) s0
              let d1 := ValSpace.dof (orc ρ Γ Δ) s1
              if GSVDInputsShape d0 d1 ae aa ab then
                .ok (.arrayOf
                  (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let M : Matrix (Fin d1) (Fin d0) ℝ :=
                    (denotAsMatrix d0 d1 ae.get).transpose
                  let MW : Matrix (Fin d0) (Fin d0) ℝ := denotAsMatrix d0 d0 aa.get
                  let MV : Matrix (Fin d1) (Fin d1) ℝ := denotAsMatrix d1 d1 ab.get
                  let P : Matrix (Fin d0) (Fin d1) ℝ := matrixGSVDPinv M MW MV
                  matrixAsDenot (m := d1) (n := d0) P.transpose i))
              else .error .mismatch
          | _ => .error .mismatch

  | ρ, Γ, Δ, whole@(.inv e)        =>
      ValValSem.bindArray (denotValB_semS orc ρ Γ Δ e) fun a =>
        match ValExpr.inferSpaceCtx Γ e with
        | .tprod s0 s1 =>
            let d0 := ValSpace.dof (orc ρ Γ Δ) s0
            let d1 := ValSpace.dof (orc ρ Γ Δ) s1
            if a.length = d0 * d1 then
              .ok (.arrayOf
                (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let M : Matrix (Fin d0) (Fin d1) ℝ := denotAsMatrix d0 d1 a.get
                  matrixAsDenot (matrixSVDPinv M) i))
            else .error .mismatch
        | s =>
            let d := ValSpace.dof (orc ρ Γ Δ) s
            if a.length = d then
              .ok (.arrayOf
                (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let M : Matrix (Fin d) (Fin 1) ℝ := fun j _ => a.get j.val
                  matrixAsDenot (matrixSVDPinv M) i))
            else .error .mismatch

  | ρ, Γ, Δ, whole@(.svds e)       =>
      ValValSem.bindArray (denotValB_semS orc ρ Γ Δ e) fun a =>
        match ValExpr.inferSpaceCtx Γ e with
        | .tprod s0 s1 =>
            let d0 := ValSpace.dof (orc ρ Γ Δ) s0
            let d1 := ValSpace.dof (orc ρ Γ Δ) s1
            if a.length = d0 * d1 then
              .ok (.arrayOf
                (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let M : Matrix (Fin d1) (Fin d0) ℝ :=
                    (denotAsMatrix d0 d1 a.get).transpose
                  let g := ValueCanonicalFSV.standard M
                  matrixAsDenot (m := g.r) (n := g.r) g.sMat i))
            else .error .mismatch
        | _ => .error .mismatch

  | ρ, Γ, Δ, .vlam τ₀ _τ₁ body =>
      -- LN (D1): push the domain value onto the local env; recurse STRUCTURALLY
      -- on `body` (so `ValExpr.size` termination is preserved).
      let τ₀_sem : ValTypeSem := denotValTyS orc ρ Γ Δ τ₀
      .ok (.fn τ₀_sem.El (fun (v : τ₀_sem.El) =>
        denotValB_semS orc ρ (τ₀ :: Γ) (ValValSem.fromEl τ₀_sem v :: Δ) body))

  | ρ, Γ, Δ, .appV e₀ e₁ =>
      let τ₀_sem : ValTypeSem :=
        denotValTyS orc ρ Γ Δ (ValExpr.inferTypeCtx Γ e₀).domain
      match denotValB_semS orc ρ Γ Δ e₀ with
      | .error err => .error err
      | .ok (.array _) => .error .mismatch
      | .ok (.fn T f) =>
          match denotValB_semS orc ρ Γ Δ e₁ with
          | .error err => .error err
          | .ok v₁ =>
              haveI := Classical.dec (T = τ₀_sem.El)
              if h : T = τ₀_sem.El then
                match ValValSem.toElDomainChecked τ₀_sem v₁ with
                | .error err => .error err
                | .ok arg => f (h ▸ arg)
              else .error .mismatch

  | ρ, Γ, Δ, whole@(.rrefRep e₀ e₁) =>
      ValValSem.bindArrays (denotValB_semS orc ρ Γ Δ e₀)
        (denotValB_semS orc ρ Γ Δ e₁) fun a₀ a₁ =>
          match ValExpr.inferSpaceCtx Γ e₁ with
          | .tprod s_p0 s_p1 =>
              let d_p0 := ValSpace.dof (orc ρ Γ Δ) s_p0
              let d_p1 := ValSpace.dof (orc ρ Γ Δ) s_p1
              let K := a₀.length / d_p0
              if d_p0 = d_p1 ∧
                  a₀.length = K * d_p0 ∧
                  a₁.length = d_p0 * d_p0 then
                .ok (.arrayOf
                  (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ whole))
                  (termsRREFRepDenot d_p0 K a₀.get a₁.get))
              else .error .mismatch
          | _ => .error .mismatch
termination_by _ρ _Γ _Δ e => ValExpr.size e
decreasing_by
  all_goals
    first
    | (have hmem : (e.1 : ValExpr) ∈ es := List.mem_of_mem_take e.2
       have hle := ValExpr.size_le_sizeList hmem
       simp only [ValExpr.size]
       omega)
    | (simp [ValExpr.size]; omega)
    | (simp only [ValExpr.size]; omega)

/-- Uniform derived selector equation for the four SVD blocks. -/
theorem denotValB_semS_canonicalFSV (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (which : ValFFSProp) (e a b : ValExpr) :
    denotValB_semS orc ρ Γ Δ (.canonicalFSV which e a b) =
      ValValSem.bindArrays3 (denotValB_semS orc ρ Γ Δ e)
        (denotValB_semS orc ρ Γ Δ a) (denotValB_semS orc ρ Γ Δ b)
        fun ae aa ab =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof (orc ρ Γ Δ) s0
              let d1 := ValSpace.dof (orc ρ Γ Δ) s1
              match ValueCanonicalFSV.eval which d0 d1 ae aa ab with
              | .error err => .error err
              | .ok r =>
                  if r.rows * r.cols =
                      ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ (.canonicalFSV which e a b)) then
                    .ok (.array r.flatten)
                  else .error .mismatch
          | _ => .error .mismatch := by
  cases which <;> simp only [ValExpr.canonicalFSV, denotValB_semS] <;> rfl

/-- Successful canonical FSV evaluation returns the exact selected finite matrix. -/
theorem denotValB_semS_canonicalFSV_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (which : ValFFSProp)
    (e a b : ValExpr) (ae aa ab : FlatArray) (s0 s1 : ValSpace)
    (r : ValueCanonicalFSV.ResultMatrix)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hr : ValueCanonicalFSV.eval which (ValSpace.dof (orc ρ Γ Δ) s0)
      (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab = .ok r)
    (hlen : r.rows * r.cols = ValSpace.dof (orc ρ Γ Δ)
      (ValExpr.inferSpaceCtx Γ (.canonicalFSV which e a b))) :
    denotValB_semS orc ρ Γ Δ (.canonicalFSV which e a b) = .ok (.array r.flatten) := by
  rw [denotValB_semS_canonicalFSV, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray, hinfer, hr, if_pos hlen]

/-! ### Checked addition boundary lemmas. -/

/-- A typed addition succeeds when both recursive denotations are arrays of
exactly the dimension declared by the result-space annotation. -/
theorem denotValB_semS_vadd_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (s : ValSpace) (e₀ e₁ : ValExpr)
    (a₀ a₁ : FlatArray)
    (hv₀ : denotValB_semS orc ρ Γ Δ e₀ = .ok (.array a₀))
    (hv₁ : denotValB_semS orc ρ Γ Δ e₁ = .ok (.array a₁))
    (h₀ : a₀.length = ValSpace.dof (orc ρ Γ Δ) s)
    (h₁ : a₁.length = ValSpace.dof (orc ρ Γ Δ) s) :
    denotValB_semS orc ρ Γ Δ (.vadd s e₀ e₁) =
      .ok (.array (FlatArray.zipWith (ValSpace.dof (orc ρ Γ Δ) s)
        (fun x y => x + y) a₀ a₁ h₀ h₁)) := by
  rw [denotValB_semS.eq_6]
  simp only [ValValSem.bindArrays, ValValSem.bindArray, hv₀, hv₁,
    h₀, h₁, ↓reduceDIte]

/-- A successful pair of array operands still fails when the left operand does
not have the annotated result dimension. -/
theorem denotValB_semS_vadd_left_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (s : ValSpace) (e₀ e₁ : ValExpr)
    (a₀ a₁ : FlatArray)
    (hv₀ : denotValB_semS orc ρ Γ Δ e₀ = .ok (.array a₀))
    (hv₁ : denotValB_semS orc ρ Γ Δ e₁ = .ok (.array a₁))
    (h₀ : a₀.length ≠ ValSpace.dof (orc ρ Γ Δ) s) :
    denotValB_semS orc ρ Γ Δ (.vadd s e₀ e₁) = .error .mismatch := by
  rw [denotValB_semS.eq_6]
  simp only [ValValSem.bindArrays, ValValSem.bindArray, hv₀, hv₁,
    h₀, ↓reduceDIte]

/-- If the left operand has the declared dimension but the right does not,
checked addition also fails. -/
theorem denotValB_semS_vadd_right_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (s : ValSpace) (e₀ e₁ : ValExpr)
    (a₀ a₁ : FlatArray)
    (hv₀ : denotValB_semS orc ρ Γ Δ e₀ = .ok (.array a₀))
    (hv₁ : denotValB_semS orc ρ Γ Δ e₁ = .ok (.array a₁))
    (h₀ : a₀.length = ValSpace.dof (orc ρ Γ Δ) s)
    (h₁ : a₁.length ≠ ValSpace.dof (orc ρ Γ Δ) s) :
    denotValB_semS orc ρ Γ Δ (.vadd s e₀ e₁) = .error .mismatch := by
  rw [denotValB_semS.eq_6]
  simp only [ValValSem.bindArrays, ValValSem.bindArray, hv₀, hv₁,
    h₀, h₁, ↓reduceDIte]

/-- `gsvdS` succeeds only after the map and both metrics have their required
runtime lengths. -/
theorem denotValB_semS_gsvdS_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (e a b : ValExpr) (ae aa ab : FlatArray) (s0 s1 : ValSpace)
    (r : ValueCanonicalFSV.ResultMatrix)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hr : ValueCanonicalFSV.evalSigma (ValSpace.dof (orc ρ Γ Δ) s0)
      (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab = .ok r)
    (hlen : r.rows * r.cols = ValSpace.dof (orc ρ Γ Δ)
      (ValExpr.inferSpaceCtx Γ (.gsvdS e a b))) :
    denotValB_semS orc ρ Γ Δ (.gsvdS e a b) = .ok (.array r.flatten) := by
  rw [denotValB_semS.eq_19, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray, hinfer, hr, if_pos hlen]

theorem denotValB_semS_gsvdS_shape_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (s0 s1 : ValSpace)
    (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hshape : ¬ GSVDInputsShape
      (ValSpace.dof (orc ρ Γ Δ) s0) (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab) :
    denotValB_semS orc ρ Γ Δ (.gsvdS e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_19, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray, hinfer]
  rw [ValueCanonicalFSV.evalSigma_shape_mismatch _ _ _ _ _ hshape]

/-- `gsvdU` succeeds under the shared GSVD runtime-shape contract. -/
theorem denotValB_semS_gsvdU_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (e a b : ValExpr) (ae aa ab : FlatArray) (s0 s1 : ValSpace)
    (r : ValueCanonicalFSV.ResultMatrix)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hr : ValueCanonicalFSV.eval .cokernel (ValSpace.dof (orc ρ Γ Δ) s0)
      (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab = .ok r)
    (hlen : r.rows * r.cols = ValSpace.dof (orc ρ Γ Δ)
      (ValExpr.inferSpaceCtx Γ (.gsvdU e a b))) :
    denotValB_semS orc ρ Γ Δ (.gsvdU e a b) = .ok (.array r.flatten) := by
  exact denotValB_semS_canonicalFSV_ok orc ρ Γ Δ .cokernel e a b ae aa ab s0 s1 r he ha hb hinfer hr hlen

/-- `gsvdU` rejects a malformed represented map or metric array. -/
theorem denotValB_semS_gsvdU_shape_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (s0 s1 : ValSpace)
    (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hshape : ¬ GSVDInputsShape
      (ValSpace.dof (orc ρ Γ Δ) s0) (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab) :
    denotValB_semS orc ρ Γ Δ (.gsvdU e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_20, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray, hinfer]
  rw [ValueCanonicalFSV.eval_shape_mismatch _ _ _ _ _ _ hshape]

/-- `gsvdUI` succeeds under the shared GSVD runtime-shape contract. -/
theorem denotValB_semS_gsvdUI_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (e a b : ValExpr) (ae aa ab : FlatArray) (s0 s1 : ValSpace)
    (r : ValueCanonicalFSV.ResultMatrix)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hr : ValueCanonicalFSV.eval .kernel (ValSpace.dof (orc ρ Γ Δ) s0)
      (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab = .ok r)
    (hlen : r.rows * r.cols = ValSpace.dof (orc ρ Γ Δ)
      (ValExpr.inferSpaceCtx Γ (.gsvdUI e a b))) :
    denotValB_semS orc ρ Γ Δ (.gsvdUI e a b) = .ok (.array r.flatten) := by
  exact denotValB_semS_canonicalFSV_ok orc ρ Γ Δ .kernel e a b ae aa ab s0 s1 r he ha hb hinfer hr hlen

/-- `gsvdUI` rejects a malformed represented map or metric array. -/
theorem denotValB_semS_gsvdUI_shape_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (s0 s1 : ValSpace)
    (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hshape : ¬ GSVDInputsShape
      (ValSpace.dof (orc ρ Γ Δ) s0) (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab) :
    denotValB_semS orc ρ Γ Δ (.gsvdUI e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_21, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray, hinfer]
  rw [ValueCanonicalFSV.eval_shape_mismatch _ _ _ _ _ _ hshape]

/-- `gsvdV` succeeds under the shared GSVD runtime-shape contract. -/
theorem denotValB_semS_gsvdV_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (e a b : ValExpr) (ae aa ab : FlatArray) (s0 s1 : ValSpace)
    (r : ValueCanonicalFSV.ResultMatrix)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hr : ValueCanonicalFSV.eval .image (ValSpace.dof (orc ρ Γ Δ) s0)
      (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab = .ok r)
    (hlen : r.rows * r.cols = ValSpace.dof (orc ρ Γ Δ)
      (ValExpr.inferSpaceCtx Γ (.gsvdV e a b))) :
    denotValB_semS orc ρ Γ Δ (.gsvdV e a b) = .ok (.array r.flatten) := by
  exact denotValB_semS_canonicalFSV_ok orc ρ Γ Δ .image e a b ae aa ab s0 s1 r he ha hb hinfer hr hlen

/-- `gsvdV` rejects a malformed represented map or metric array. -/
theorem denotValB_semS_gsvdV_shape_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (s0 s1 : ValSpace)
    (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hshape : ¬ GSVDInputsShape
      (ValSpace.dof (orc ρ Γ Δ) s0) (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab) :
    denotValB_semS orc ρ Γ Δ (.gsvdV e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_22, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray, hinfer]
  rw [ValueCanonicalFSV.eval_shape_mismatch _ _ _ _ _ _ hshape]

/-- `gsvdVI` succeeds under the shared GSVD runtime-shape contract. -/
theorem denotValB_semS_gsvdVI_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem)
    (e a b : ValExpr) (ae aa ab : FlatArray) (s0 s1 : ValSpace)
    (r : ValueCanonicalFSV.ResultMatrix)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hr : ValueCanonicalFSV.eval .coimage (ValSpace.dof (orc ρ Γ Δ) s0)
      (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab = .ok r)
    (hlen : r.rows * r.cols = ValSpace.dof (orc ρ Γ Δ)
      (ValExpr.inferSpaceCtx Γ (.gsvdVI e a b))) :
    denotValB_semS orc ρ Γ Δ (.gsvdVI e a b) = .ok (.array r.flatten) := by
  exact denotValB_semS_canonicalFSV_ok orc ρ Γ Δ .coimage e a b ae aa ab s0 s1 r he ha hb hinfer hr hlen

/-- `gsvdVI` rejects a malformed represented map or metric array. -/
theorem denotValB_semS_gsvdVI_shape_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (s0 s1 : ValSpace)
    (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hshape : ¬ GSVDInputsShape
      (ValSpace.dof (orc ρ Γ Δ) s0) (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab) :
    denotValB_semS orc ρ Γ Δ (.gsvdVI e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_23, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray, hinfer]
  rw [ValueCanonicalFSV.eval_shape_mismatch _ _ _ _ _ _ hshape]

/-- `gpinv` succeeds under the same runtime-shape contract as the five GSVD
component operations. -/
theorem denotValB_semS_gpinv_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (s0 s1 : ValSpace)
    (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hshape : GSVDInputsShape
      (ValSpace.dof (orc ρ Γ Δ) s0) (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab) :
    denotValB_semS orc ρ Γ Δ (.gpinv e a b) =
      .ok (.arrayOf
        (ValSpace.dof (orc ρ Γ Δ) (ValExpr.inferSpaceCtx Γ (.gpinv e a b))) (fun i =>
          let d0 := ValSpace.dof (orc ρ Γ Δ) s0
          let d1 := ValSpace.dof (orc ρ Γ Δ) s1
          let M : Matrix (Fin d1) (Fin d0) ℝ :=
            (denotAsMatrix d0 d1 ae.get).transpose
          let MW : Matrix (Fin d0) (Fin d0) ℝ := denotAsMatrix d0 d0 aa.get
          let MV : Matrix (Fin d1) (Fin d1) ℝ := denotAsMatrix d1 d1 ab.get
          let P : Matrix (Fin d0) (Fin d1) ℝ := matrixGSVDPinv M MW MV
          matrixAsDenot (m := d1) (n := d0) P.transpose i)) := by
  rw [denotValB_semS.eq_24, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray, hinfer]
  rw [if_pos hshape]

/-- `gpinv` rejects a malformed represented map or metric array. -/
theorem denotValB_semS_gpinv_shape_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (s0 s1 : ValSpace)
    (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ValExpr.inferSpaceCtx Γ e = .tprod s0 s1)
    (hshape : ¬ GSVDInputsShape
      (ValSpace.dof (orc ρ Γ Δ) s0) (ValSpace.dof (orc ρ Γ Δ) s1) ae aa ab) :
    denotValB_semS orc ρ Γ Δ (.gpinv e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_24, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray, hinfer]
  rw [if_neg hshape]

/-- A GSVD component cannot interpret a non-tensor inferred map space. -/
theorem denotValB_semS_gsvdS_non_tensor_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ∀ s0 s1, ValExpr.inferSpaceCtx Γ e ≠ .tprod s0 s1) :
    denotValB_semS orc ρ Γ Δ (.gsvdS e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_19, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray]

/-- `gsvdU` cannot interpret a non-tensor inferred map space. -/
theorem denotValB_semS_gsvdU_non_tensor_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ∀ s0 s1, ValExpr.inferSpaceCtx Γ e ≠ .tprod s0 s1) :
    denotValB_semS orc ρ Γ Δ (.gsvdU e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_20, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray]

/-- `gsvdUI` cannot interpret a non-tensor inferred map space. -/
theorem denotValB_semS_gsvdUI_non_tensor_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ∀ s0 s1, ValExpr.inferSpaceCtx Γ e ≠ .tprod s0 s1) :
    denotValB_semS orc ρ Γ Δ (.gsvdUI e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_21, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray]

/-- `gsvdV` cannot interpret a non-tensor inferred map space. -/
theorem denotValB_semS_gsvdV_non_tensor_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ∀ s0 s1, ValExpr.inferSpaceCtx Γ e ≠ .tprod s0 s1) :
    denotValB_semS orc ρ Γ Δ (.gsvdV e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_22, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray]

/-- `gsvdVI` cannot interpret a non-tensor inferred map space. -/
theorem denotValB_semS_gsvdVI_non_tensor_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ∀ s0 s1, ValExpr.inferSpaceCtx Γ e ≠ .tprod s0 s1) :
    denotValB_semS orc ρ Γ Δ (.gsvdVI e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_23, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray]

/-- `gpinv` cannot interpret a non-tensor inferred map space. -/
theorem denotValB_semS_gpinv_non_tensor_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e a b : ValExpr) (ae aa ab : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array ae))
    (ha : denotValB_semS orc ρ Γ Δ a = .ok (.array aa))
    (hb : denotValB_semS orc ρ Γ Δ b = .ok (.array ab))
    (hinfer : ∀ s0 s1, ValExpr.inferSpaceCtx Γ e ≠ .tprod s0 s1) :
    denotValB_semS orc ρ Γ Δ (.gpinv e a b) = .error .mismatch := by
  rw [denotValB_semS.eq_24, he, ha, hb]
  simp only [ValValSem.bindArrays3, ValValSem.bindArray]

/-- A base-kind reshape preserves the computed flat array exactly when it is
    a complete source-space representation and the source and target spaces
    have equal dimensions.  In particular, reshape neither manufactures a
    padded/truncated source nor silently changes its dimension. -/
theorem denotValB_semS_reshap_spaces_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e : ValExpr) (st ss : ValSpace)
    (a : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array a))
    (hlen : a.length = ValSpace.dof (orc ρ Γ Δ) ss)
    (hdim : ValSpace.dof (orc ρ Γ Δ) ss =
      ValSpace.dof (orc ρ Γ Δ) st) :
    denotValB_semS orc ρ Γ Δ (.reshap e (.space st) (.space ss)) =
      .ok (.array a) := by
  rw [denotValB_semS.eq_17, he]
  simp only
  rw [reshapDenotSemS.eq_1]
  simp only [reshapArrayBetweenS, hlen, hdim, ↓reduceIte]

/-- Identity specialization used by `reshapBase`. -/
theorem denotValB_semS_reshap_space_ok (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e : ValExpr) (s : ValSpace)
    (a : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array a))
    (hlen : a.length = ValSpace.dof (orc ρ Γ Δ) s) :
    denotValB_semS orc ρ Γ Δ (.reshap e (.space s) (.space s)) =
      .ok (.array a) :=
  denotValB_semS_reshap_spaces_ok orc ρ Γ Δ e s s a he hlen rfl

/-- A base-kind reshape fails explicitly when the computed flat array does not
    have the target dimension.  Adequacy is responsible for ruling this branch
    out for well-typed operational evaluations. -/
theorem denotValB_semS_reshap_space_mismatch (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e : ValExpr) (s : ValSpace)
    (τ_src : ValTy) (a : FlatArray)
    (he : denotValB_semS orc ρ Γ Δ e = .ok (.array a))
    (hlen : a.length ≠ ValSpace.dof (orc ρ Γ Δ) s) :
    denotValB_semS orc ρ Γ Δ (.reshap e (.space s) τ_src) = .error .mismatch := by
  rw [denotValB_semS.eq_17, he]
  simp only
  cases τ_src <;> simp only [reshapDenotSemS, reshapArrayBetweenS]
  split <;> rename_i hs
  · split <;> rename_i hd
    · exact (hlen (hs.trans hd)).elim
    · rfl
  · rfl

noncomputable def denotValTy (orc : FFSOracle) :
    ValEnvSem → List ValValSem → ValTy → ValTypeSem
  | _ρ, _Δ, .space s => .space s (ValSpace.dof orc s)
  | ρ,  Δ,  .piTy τ₀ τ₁ =>
      let τ₀_sem := denotValTy orc ρ Δ τ₀
      .piTy τ₀_sem.El (fun (v : τ₀_sem.El) =>
        denotValTy orc ρ (ValValSem.fromEl τ₀_sem v :: Δ) τ₁)

noncomputable def reshapDenotSem (orc : FFSOracle) (v : ValValSem) (τ_tgt τ_src : ValTy) :
    Except DimError ValValSem :=
  reshapDenotSemS (.const orc) ValEnvSem.empty [] [] v τ_tgt τ_src

noncomputable def denotValB_sem (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e : ValExpr) : Except DimError ValValSem :=
  denotValB_semS (.const orc) ρ Γ Δ e

theorem denotValTy_eq_denotValTyS (orc : FFSOracle) (ρ : ValEnvSem) :
    ∀ (τ : ValTy) (Γ : List ValTy) (Δ : List ValValSem),
      denotValTy orc ρ Δ τ = denotValTyS (.const orc) ρ Γ Δ τ
  | .space _, _, _ => rfl
  | .piTy τ₀ τ₁, Γ, Δ => by
      rw [denotValTy, denotValTyS, denotValTy_eq_denotValTyS orc ρ τ₀ Γ Δ]
      exact congrArg _ (funext fun v => denotValTy_eq_denotValTyS orc ρ τ₁ _ _)

/-- At a constant oracle family the type denotation does not depend on `Γ`. -/
theorem denotValTyS_const_gamma (orc : FFSOracle) (ρ : ValEnvSem) (τ : ValTy)
    (Γ Γ' : List ValTy) (Δ : List ValValSem) :
    denotValTyS (.const orc) ρ Γ Δ τ = denotValTyS (.const orc) ρ Γ' Δ τ :=
  (denotValTy_eq_denotValTyS orc ρ τ Γ Δ).symm.trans (denotValTy_eq_denotValTyS orc ρ τ Γ' Δ)

/-- At a constant oracle family the complete type denotation is independent
of all semantic and local environments. -/
theorem denotValTyS_const_env (orc : FFSOracle) :
    ∀ (τ : ValTy) (ρ ρ' : ValEnvSem) (Γ Γ' : List ValTy)
      (Δ Δ' : List ValValSem),
      denotValTyS (.const orc) ρ Γ Δ τ =
        denotValTyS (.const orc) ρ' Γ' Δ' τ
  | .space _, _, _, _, _, _, _ => rfl
  | .piTy τ₀ τ₁, ρ, ρ', Γ, Γ', Δ, Δ' => by
      rw [denotValTyS, denotValTyS,
        denotValTyS_const_env orc τ₀ ρ ρ' Γ Γ' Δ Δ']
      exact congrArg _ (funext fun a =>
        denotValTyS_const_env orc τ₁ ρ ρ'
          (τ₀ :: Γ) (τ₀ :: Γ')
          (ValValSem.fromEl (denotValTyS (.const orc) ρ' Γ' Δ' τ₀) a :: Δ)
          (ValValSem.fromEl (denotValTyS (.const orc) ρ' Γ' Δ' τ₀) a :: Δ'))

/-- The paired reshape is environment-independent for a constant oracle. -/
theorem reshapDenotSemBetweenS_const_env (orc : FFSOracle) :
    ∀ (v : ValValSem) (τ_tgt τ_src : ValTy)
      (ρ ρ' : ValEnvSem)
      (Γt Γt' Γs Γs' : List ValTy)
      (Δt Δt' Δs Δs' : List ValValSem),
      reshapDenotSemBetweenS (.const orc) ρ Γt Δt Γs Δs v τ_tgt τ_src =
        reshapDenotSemBetweenS (.const orc) ρ' Γt' Δt' Γs' Δs' v τ_tgt τ_src
  | .array a, .space st, ts, ρ, ρ', Γt, Γt', Γs, Γs', Δt, Δt', Δs, Δs' => by
      cases ts <;> simp [reshapDenotSemBetweenS, reshapArrayBetweenS]
  | .fn T f, .space s, src, ρ, ρ', Γt, Γt', Γs, Γs', Δt, Δt', Δs, Δs' => by
      rw [reshapDenotSemBetweenS.eq_2, reshapDenotSemBetweenS.eq_2]
  | v, .piTy τt₀ τt₁, .piTy τs₀ τs₁,
      ρ, ρ', Γt, Γt', Γs, Γs', Δt, Δt', Δs, Δs' => by
      rw [reshapDenotSemBetweenS.eq_3, reshapDenotSemBetweenS.eq_3]
      rw [denotValTyS_const_env orc τt₀ ρ ρ' Γt Γt' Δt Δt',
        denotValTyS_const_env orc τs₀ ρ ρ' Γs Γs' Δs Δs']
      apply congrArg Except.ok
      apply congrArg _
      funext a
      dsimp only
      generalize hcheck : ValValSem.fromElChecked
        (denotValTyS (.const orc) ρ' Γt' Δt' τt₀) a = checkResult
      cases checkResult with
      | error _ => simp [hcheck]
      | ok argT =>
          simp only [hcheck]
          rw [reshapDenotSemBetweenS_const_env orc argT
            τs₀ τt₀ ρ ρ' Γs Γs' Γt Γt' Δs Δs' Δt Δt']
          generalize harg : reshapDenotSemBetweenS (.const orc) ρ' Γs' Δs' Γt' Δt'
            argT τs₀ τt₀ = argResult
          cases argResult with
          | error _ => simp
          | ok argS =>
              generalize hdecode : ValValSem.toEl
                (denotValTyS (.const orc) ρ' Γs' Δs' τs₀) argS = decodeResult
              cases decodeResult with
              | error _ => simp [hdecode]
              | ok argEl =>
                  generalize happ : v.applyTyped argEl = appResult
                  cases appResult with
                  | error _ => simp [hdecode, happ]
                  | ok res =>
                      simpa [hdecode, happ] using
                        reshapDenotSemBetweenS_const_env orc res τt₁ τs₁ ρ ρ'
                        (τt₀ :: Γt) (τt₀ :: Γt') (τs₀ :: Γs) (τs₀ :: Γs')
                        (argT :: Δt) (argT :: Δt')
                        (argS :: Δs) (argS :: Δs')
  | v, .piTy τt₀ τt₁, .space s,
      ρ, ρ', Γt, Γt', Γs, Γs', Δt, Δt', Δs, Δs' => by
      rw [reshapDenotSemBetweenS.eq_4, reshapDenotSemBetweenS.eq_4]
  termination_by v τt τs _ _ _ _ _ _ _ _ _ _ =>
    ValTy.kindSize τt + ValTy.kindSize τs
  decreasing_by all_goals simp only [ValTy.kindSize_piTy]; omega

/-- The public wrapper is the paired implementation started from one shared
context. -/
theorem reshapDenotSemS_eq_between (orc : FFSOracleSem) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (v : ValValSem)
    (τ_tgt τ_src : ValTy) :
    reshapDenotSemS orc ρ Γ Δ v τ_tgt τ_src =
      reshapDenotSemBetweenS orc ρ Γ Δ Γ Δ v τ_tgt τ_src := by
  cases v <;> cases τ_tgt <;> cases τ_src <;>
    simp [reshapDenotSemS, reshapDenotSemBetweenS]

/-- At a constant oracle family the higher-kinded reshape does not depend on
    the environments `(ρ, Γ, Δ)` (only consumed by the oracle). -/
theorem reshapDenotSemS_const_env (orc : FFSOracle) (ρ ρ' : ValEnvSem) (Γ Γ' : List ValTy)
    (Δ Δ' : List ValValSem) :
    ∀ (v : ValValSem) (τ_tgt τ_src : ValTy),
      reshapDenotSemS (.const orc) ρ Γ Δ v τ_tgt τ_src
        = reshapDenotSemS (.const orc) ρ' Γ' Δ' v τ_tgt τ_src := by
  intro v τ_tgt τ_src
  rw [reshapDenotSemS_eq_between, reshapDenotSemS_eq_between]
  exact reshapDenotSemBetweenS_const_env orc v τ_tgt τ_src ρ ρ'
    Γ Γ' Γ Γ' Δ Δ' Δ Δ'

@[simp] theorem denotValTy_space (orc : FFSOracle) (ρ : ValEnvSem)
    (Δ : List ValValSem) (s : ValSpace) :
    denotValTy orc ρ Δ (.space s)
      = .space s (ValSpace.dof orc s) := rfl

theorem reshapDenotSem_eq_space (orc : FFSOracle) (v : ValValSem) (τ_src : ValTy)
    (s : ValSpace) :
    reshapDenotSem orc v (.space s) τ_src =
      reshapDenotSemS (.const orc) ValEnvSem.empty [] [] v (.space s) τ_src := rfl

theorem reshapDenotSem_eq_piTy (orc : FFSOracle) (v : ValValSem)
    (τ₂ τ₃ τ₄ τ₅ : ValTy) :
    reshapDenotSem orc v (.piTy τ₂ τ₃) (.piTy τ₄ τ₅) =
      reshapDenotSemS (.const orc) ValEnvSem.empty [] [] v
        (.piTy τ₂ τ₃) (.piTy τ₄ τ₅) := rfl

theorem reshapDenotSem_eq_piTy_space (orc : FFSOracle) (v : ValValSem)
    (τ₂ τ₃ : ValTy) (s : ValSpace) :
    reshapDenotSem orc v (.piTy τ₂ τ₃) (.space s) =
      reshapDenotSemS (.const orc) ValEnvSem.empty [] [] v
        (.piTy τ₂ τ₃) (.space s) := rfl

attribute [eqns reshapDenotSem_eq_space reshapDenotSem_eq_piTy
  reshapDenotSem_eq_piTy_space] reshapDenotSem

theorem denotValB_sem_eq_bvar (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (n : Nat) :
    denotValB_sem orc ρ Γ Δ (.bvar n) =
      denotValB_semS (.const orc) ρ Γ Δ (.bvar n) := rfl

theorem denotValB_sem_eq_var (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (x : VName) (τ : ValTy) :
    denotValB_sem orc ρ Γ Δ (.var x τ) =
      denotValB_semS (.const orc) ρ Γ Δ (.var x τ) := rfl

theorem denotValB_sem_eq_rlit (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (r : ℝ) :
    denotValB_sem orc ρ Γ Δ (.rlit r) =
      denotValB_semS (.const orc) ρ Γ Δ (.rlit r) := rfl

theorem denotValB_sem_eq_zero (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (s : ValSpace) :
    denotValB_sem orc ρ Γ Δ (.zero s) =
      denotValB_semS (.const orc) ρ Γ Δ (.zero s) := rfl

theorem denotValB_sem_eq_scale (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e₀ e₁ : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.scale e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.scale e₀ e₁) := rfl

theorem denotValB_sem_eq_vadd (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (s : ValSpace) (e₀ e₁ : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.vadd s e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.vadd s e₀ e₁) := rfl

theorem denotValB_sem_eq_delta (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (n : Nat) (s : ValSpace) :
    denotValB_sem orc ρ Γ Δ (.delta n s) =
      denotValB_semS (.const orc) ρ Γ Δ (.delta n s) := rfl

theorem denotValB_sem_eq_idelta (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (s : ValSpace) :
    denotValB_sem orc ρ Γ Δ (.idelta s) =
      denotValB_semS (.const orc) ρ Γ Δ (.idelta s) := rfl

theorem denotValB_sem_eq_tprodE (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e₀ e₁ : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.tprodE e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.tprodE e₀ e₁) := rfl

theorem denotValB_sem_eq_dsumE (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e₀ e₁ : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.dsumE e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.dsumE e₀ e₁) := rfl

theorem denotValB_sem_eq_vtrans (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.vtrans e) =
      denotValB_semS (.const orc) ρ Γ Δ (.vtrans e) := rfl

theorem denotValB_sem_eq_ttv (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (s : ValSpace) (e₀ e₁ : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.ttv s e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.ttv s e₀ e₁) := rfl

theorem denotValB_sem_eq_mtm (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (n₀ n₁ : Nat) (s₀ s₁ : ValSpace) (e₀ e₁ : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.mtm n₀ n₁ s₀ s₁ e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.mtm n₀ n₁ s₀ s₁ e₀ e₁) := rfl

theorem denotValB_sem_eq_vkrn (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e₀ e₁ : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.vkrn e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.vkrn e₀ e₁) := rfl

theorem denotValB_sem_eq_vblk (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e₀ e₁ : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.vblk e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.vblk e₀ e₁) := rfl

theorem denotValB_sem_eq_vsum (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (s : ValSpace) (es : List ValExpr) :
    denotValB_sem orc ρ Γ Δ (.vsum s es) =
      denotValB_semS (.const orc) ρ Γ Δ (.vsum s es) := rfl

theorem denotValB_sem_eq_reshap_space (orc : FFSOracle) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e : ValExpr) (s : ValSpace) (τ_src : ValTy) :
    denotValB_sem orc ρ Γ Δ (.reshap e (.space s) τ_src) =
      denotValB_semS (.const orc) ρ Γ Δ (.reshap e (.space s) τ_src) := rfl

theorem denotValB_sem_eq_reshap_piTy (orc : FFSOracle) (ρ : ValEnvSem)
    (Γ : List ValTy) (Δ : List ValValSem) (e : ValExpr) (τ₀ τ₁ τ_src : ValTy) :
    denotValB_sem orc ρ Γ Δ (.reshap e (.piTy τ₀ τ₁) τ_src) =
      denotValB_semS (.const orc) ρ Γ Δ
        (.reshap e (.piTy τ₀ τ₁) τ_src) := rfl

theorem denotValB_sem_eq_pinv (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.pinv e) =
      denotValB_semS (.const orc) ρ Γ Δ (.pinv e) := rfl

theorem denotValB_sem_eq_gsvdS (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e a b : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.gsvdS e a b) =
      denotValB_semS (.const orc) ρ Γ Δ (.gsvdS e a b) := rfl

theorem denotValB_sem_eq_gsvdU (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e a b : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.gsvdU e a b) =
      denotValB_semS (.const orc) ρ Γ Δ (.gsvdU e a b) := rfl

theorem denotValB_sem_eq_gsvdUI (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e a b : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.gsvdUI e a b) =
      denotValB_semS (.const orc) ρ Γ Δ (.gsvdUI e a b) := rfl

theorem denotValB_sem_eq_gsvdV (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e a b : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.gsvdV e a b) =
      denotValB_semS (.const orc) ρ Γ Δ (.gsvdV e a b) := rfl

theorem denotValB_sem_eq_gsvdVI (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e a b : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.gsvdVI e a b) =
      denotValB_semS (.const orc) ρ Γ Δ (.gsvdVI e a b) := rfl

theorem denotValB_sem_eq_gpinv (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e a b : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.gpinv e a b) =
      denotValB_semS (.const orc) ρ Γ Δ (.gpinv e a b) := rfl

theorem denotValB_sem_eq_inv (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.inv e) =
      denotValB_semS (.const orc) ρ Γ Δ (.inv e) := rfl

theorem denotValB_sem_eq_svds (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.svds e) =
      denotValB_semS (.const orc) ρ Γ Δ (.svds e) := rfl

theorem denotValB_sem_eq_vlam (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (τ₀ τ₁ : ValTy) (body : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.vlam τ₀ τ₁ body) =
      denotValB_semS (.const orc) ρ Γ Δ (.vlam τ₀ τ₁ body) := rfl

theorem denotValB_sem_eq_appV (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e₀ e₁ : ValExpr) (τ : ValTy) :
    denotValB_sem orc ρ Γ Δ (.appV e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.appV e₀ e₁) := rfl

theorem denotValB_sem_eq_rrefRep (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (e₀ e₁ : ValExpr) :
    denotValB_sem orc ρ Γ Δ (.rrefRep e₀ e₁) =
      denotValB_semS (.const orc) ρ Γ Δ (.rrefRep e₀ e₁) := rfl

attribute [eqns
  denotValB_sem_eq_bvar denotValB_sem_eq_var denotValB_sem_eq_rlit denotValB_sem_eq_zero
  denotValB_sem_eq_scale denotValB_sem_eq_vadd denotValB_sem_eq_delta denotValB_sem_eq_idelta
  denotValB_sem_eq_tprodE denotValB_sem_eq_dsumE denotValB_sem_eq_vtrans denotValB_sem_eq_ttv
  denotValB_sem_eq_mtm denotValB_sem_eq_vkrn denotValB_sem_eq_vblk denotValB_sem_eq_vsum
  denotValB_sem_eq_reshap_space denotValB_sem_eq_reshap_piTy denotValB_sem_eq_pinv
  denotValB_sem_eq_gsvdS denotValB_sem_eq_gsvdU denotValB_sem_eq_gsvdUI denotValB_sem_eq_gsvdV
  denotValB_sem_eq_gsvdVI denotValB_sem_eq_gpinv denotValB_sem_eq_inv denotValB_sem_eq_svds
  denotValB_sem_eq_vlam denotValB_sem_eq_appV denotValB_sem_eq_rrefRep] denotValB_sem

def ffsDim : ValFFSProp → List Nat → Nat → Nat
  | .kernel,   [d₀, _], r => d₀ - r
  | .cokernel, [_, _],  r => r
  | .image,    [_, _],  r => r
  | .coimage,  [_, d₁], r => d₁ - r
  | _, _, _ => 0

/-- Rank of the FFS operand `w` read as a matrix. The parent space `s` is
    expected to be `s₀ ⊗ s₁` with `shpOf s = [d₀, d₁]`; the flat array
    `denotValB_semS orc ρ Γ Δ w` is read through the SAME bridge as the
    `.gsvd*`/`.pinv` arms of `denotValB_semS`, `denotAsMatrix d₀ d₁`
    (`ValueSVD.lean`: rows = first tensor factor `s₀`, row-major). The GSVD
    arms then use its transpose `d₁ × d₀`; `Matrix.rank` is
    transpose-invariant (`Matrix.rank_transpose`), so the orientation is
    immaterial for `r`. Non-2-element shapes yield rank `0`. -/
noncomputable def ffsOperandRank (orc : FFSOracleSem) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) (s : ValSpace) (w : ValExpr) : Nat :=
  match ValSpace.shpOf (orc ρ Γ Δ) s with
  | [d₀, d₁] =>
      match denotValB_semS orc ρ Γ Δ w with
      | .ok (.array a) => (denotAsMatrix d₀ d₁ a.get).rank
      | _ => 0
  | _ => 0

def OracleSpecPre (orc : FFSOracleSem) : Prop :=
  ∀ (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem) (p : ValFFSProp) (s : ValSpace)
    (w : ValExpr),
    orc ρ Γ Δ p s w = ffsDim p (ValSpace.shpOf (orc ρ Γ Δ) s) (ffsOperandRank orc ρ Γ Δ s w)

/-- Ambient upper bound of the FFS dimension from the parent shape `[d₀, d₁]`: a kernel or
    cokernel dimension is at most the domain factor `d₀`, an image or coimage dimension at
    most the codomain factor `d₁` (rank ≤ either). Non-2-element shapes yield `0`, like
    `ffsDim`. `ffsDim p shp r ≤ ffsDimUB p shp` whenever `r ≤ d₀` and `r ≤ d₁`. -/
def ffsDimUB : ValFFSProp → List Nat → Nat
  | .kernel,   [d₀, _] => d₀
  | .cokernel, [d₀, _] => d₀
  | .image,    [_, d₁] => d₁
  | .coimage,  [_, d₁] => d₁
  | _, _ => 0

structure OracleSpec (orc : FFSOracleSem) : Prop where
  /-- Rank ≤ ambient, unconditionally. -/
  bound : ∀ (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem) (p : ValFFSProp)
    (s : ValSpace) (w : ValExpr),
    orc ρ Γ Δ p s w ≤ ffsDimUB p (ValSpace.shpOf (orc ρ Γ Δ) s)

  rank : ∀ (ρ : ValEnvSem) (p : ValFFSProp) (s : ValSpace) (w : ValExpr),
    ValExpr.inferSpaceCtx [] w = s →
    ValueQueryDependencies.Finite (.space [] (.ffs p s w)) →
    orc ρ [] [] p s w = ffsDim p (ValSpace.shpOf (orc ρ [] []) s) (ffsOperandRank orc ρ [] [] s w)
  /-- The oracle reads `ρ` only at the free names of the parent, the witness, and the
      de Bruijn type context consulted by the witness. -/
  fvIrrel : ∀ (ρ : ValEnvSem) (y : VName) (v : ValValSem) (Γ : List ValTy)
    (Δ : List ValValSem) (p : ValFFSProp) (s : ValSpace) (w : ValExpr),
    (∀ τ ∈ Γ, y ∉ ValTy.fv τ) →
    y ∉ ValSpace.fv s → y ∉ ValExpr.fv w →
    orc (ρ.update y v) Γ Δ p s w = orc ρ Γ Δ p s w

/-- `ffsDimUB` on a non-2-element shape is `0` (the fallback arm). -/
theorem ffsDimUB_singleton (p : ValFFSProp) (d : Nat) : ffsDimUB p [d] = 0 := by
  cases p <;> rfl

/-- `ffsDim ≤ ffsDimUB` on a 2-element shape when the rank is bounded by both factors. -/
theorem ffsDim_le_ffsDimUB (p : ValFFSProp) (d₀ d₁ r : Nat) (h₀ : r ≤ d₀) (h₁ : r ≤ d₁) :
    ffsDim p [d₀, d₁] r ≤ ffsDimUB p [d₀, d₁] := by
  cases p <;> simp only [ffsDim, ffsDimUB] <;> omega

theorem denotValB_sem_appV_fn (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem)
    (e₀ e₁ : ValExpr) (τ_out d : ValTy)
    (fam : (denotValTyS (.const orc) ρ Γ Δ d).El → Except DimError ValValSem)
    (v₁ : ValValSem) (arg : (denotValTyS (.const orc) ρ Γ Δ d).El)
    (hd : (ValExpr.inferTypeCtx Γ e₀).domain = d)
    (hv₀ : denotValB_sem orc ρ Γ Δ e₀ =
      .ok (.fn (denotValTyS (.const orc) ρ Γ Δ d).El fam))
    (hv₁ : denotValB_sem orc ρ Γ Δ e₁ = .ok v₁)
    (hto : ValValSem.toElDomainChecked (denotValTyS (.const orc) ρ Γ Δ d) v₁ = .ok arg) :
    denotValB_sem orc ρ Γ Δ (.appV e₀ e₁)
      = fam arg := by
  subst d
  delta denotValB_sem at hv₀ hv₁ ⊢
  rw [denotValB_semS.eq_28]
  simp only [hv₀, hv₁, ↓reduceDIte, hto]

/-! ## Sanity-check `@[simp]` lemmas. -/

@[simp] theorem denotValB_sem_zero (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem) (s : ValSpace) :
    denotValB_sem orc ρ Γ Δ (.zero s) =
      .ok (.arrayOf (ValSpace.dof orc s) (fun _ => 0)) :=
  by
    delta denotValB_sem
    rw [denotValB_semS.eq_4]
    rfl

@[simp] theorem denotValB_sem_rlit (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem) (r : ℝ) :
    denotValB_sem orc ρ Γ Δ (.rlit r)
      = .ok (.arrayOf (ValSpace.dof orc (ValExpr.inferSpaceCtx Γ (.rlit r)))
          (fun i => if i = 0 then r else 0)) :=
  by
    delta denotValB_sem
    rw [denotValB_semS.eq_3]

@[simp] theorem denotValB_sem_delta (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (n : Nat) (s : ValSpace) :
    denotValB_sem orc ρ Γ Δ (.delta n s)
      = .ok (.arrayOf (ValSpace.dof orc s)
          (fun i => if i = n ∧ n < ValSpace.dof orc s then 1 else 0)) :=
  by
    delta denotValB_sem
    rw [denotValB_semS.eq_7]
    rfl

@[simp] theorem denotValB_sem_idelta (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (s : ValSpace) :
    denotValB_sem orc ρ Γ Δ (.idelta s)
      = .ok (.arrayOf (ValSpace.dof orc (ValExpr.inferSpaceCtx Γ (.idelta s))) (fun i =>
          let d := ValSpace.dof orc s
          if d = 0 then 0
          else if i < d * d then
            let r := i / d
            let c := i % d
            if r = c ∧ r < d then 1 else 0
          else 0)) :=
  by
    delta denotValB_sem
    rw [denotValB_semS.eq_8]

section VSumLinearLambdaValidation

/-- The DISTINCT-`env_i` summand family `[ δ₀ ⊗ env₀ , δ₁ ⊗ env₁ ]`
    (`δ_i = env_i = .delta i ℝ`). -/
def vsum_linearLambda_summands : List ValExpr :=
  [ .tprodE (.delta 0 .real) (.delta 0 .real)
  , .tprodE (.delta 1 .real) (.delta 1 .real) ]

/-- The linear-λ-style current value `Σ^ℝ [ δ₀ ⊗ env₀ , δ₁ ⊗ env₁ ]`. -/
def vsum_linearLambda_example : ValExpr :=
  .vsum .real vsum_linearLambda_summands

-- The DISTINCT-summand value form exists and elaborates.
#check (vsum_linearLambda_example : ValExpr)
example : vsum_linearLambda_summands.length = 2 := rfl

/-- A single-summand instance `Σ^ℝ [ δ ⊗ env ]`, used for the well-typed +
    denotable theorems (a singleton list lets the `Type`-valued per-summand
    typing be built by Eq-substitution on `List.mem_singleton`, avoiding the
    blocked `Or`/`List.Mem` large-elimination). The two-summand value above
    establishes representability of distinct families. -/
def vsum_linearLambda_singleton : ValExpr :=
  .vsum .real [ .tprodE (.delta 0 .real) (.delta 0 .real) ]

/-- **Well-typed.** The singleton current types at `.space (ℝ ⊗ ℝ)`. -/
def vsum_linearLambda_wellTyped (ε : ValCtx) :
    ValHasType ε vsum_linearLambda_singleton (.space (.tprod .real .real)) :=
  ValHasType.vsum ValSValid.real
    (fun e hmem =>
      -- `e ∈ [a]` ⇒ `e = a` (Eq, large-eliminable into `Type`).
      (List.mem_singleton.mp hmem) ▸
        ValHasType.tprodE (ValHasType.delta ValSValid.real)
          (ValHasType.delta ValSValid.real))
    (.tprod .real .real)
    -- nonempty list ⇒ determinism premise `es = [] → s = .empty` is vacuous.
    (by intro h; exact absurd h (by simp [vsum_linearLambda_singleton]))

#check (vsum_linearLambda_wellTyped : (ε : ValCtx) →
  ValHasType ε vsum_linearLambda_singleton (.space (.tprod .real .real)))

/-- The partial wrapper agrees definitionally with the active semantic-family
evaluator on the representability example. -/
theorem vsum_linearLambda_denot (orc : FFSOracle) (ρ : ValEnvSem) (Γ : List ValTy)
    (Δ : List ValValSem) :
    denotValB_sem orc ρ Γ Δ vsum_linearLambda_example =
      denotValB_semS (.const orc) ρ Γ Δ vsum_linearLambda_example := rfl

end VSumLinearLambdaValidation

end GLang
