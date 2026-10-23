import GLang.Value.EvaluationHelpers

/-! The live error-preserving value interpretation. Guards remain explicit
in each clause. Application is binary; reshape checks function fibers recursively. -/
namespace GLang

noncomputable def denotValB_partial (orc : PartialFFSOracleSem) :
    ValEnvSem → List ValTy → List ValValSem → ValExpr → Except DimError ValValSem
  | _ρ, _Γ, Δ, .bvar n      => StrictValueAccess.lookup Δ n
  | ρ, _Γ, _Δ, .var x _     => .ok (ρ x)
  | ρ, Γ, Δ, whole@(.rlit r) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ whole] fun q =>
        .ok (.arrayOf (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole))
          (fun i => if i = 0 then r else 0))
  | ρ, Γ, Δ, whole@(.zero _) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ whole] fun q =>
        .ok (.arrayOf (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole))
          (fun _ => 0))
  | ρ, Γ, Δ, whole@(.scale e₀ e₁)  =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e₁] fun q =>
        ValValSem.bindArrays (denotValB_partial orc ρ Γ Δ e₀)
          (denotValB_partial orc ρ Γ Δ e₁) fun a₀ a₁ =>
            if ValueShape.scale q (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
              .ok (.arrayOf
                (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole))
                (fun i => a₀.get 0 * a₁.get i))
            else .error .mismatch
  | ρ, Γ, Δ, .vadd s e₀ e₁   =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [s] fun q =>
        ValValSem.bindArrays (denotValB_partial orc ρ Γ Δ e₀)
          (denotValB_partial orc ρ Γ Δ e₁) fun a₀ a₁ =>
            let n := ValSpace.dof q s
            if h₀ : a₀.length = n then
              if h₁ : a₁.length = n then
                .ok (.array (FlatArray.zipWith n (fun x y => x + y) a₀ a₁ h₀ h₁))
              else .error .mismatch
            else .error .mismatch
  | ρ, Γ, Δ, whole@(.delta n s)   =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [s] fun q =>
        .ok (.arrayOf (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole))
          (fun i => if i = n ∧ n < ValSpace.dof q s then 1 else 0))
  | ρ, Γ, Δ, whole@(.idelta s)    =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [s] fun q =>
        .ok (.arrayOf (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
          let d := ValSpace.dof q s
          if d = 0 then 0
          else if i < d * d then
            let r := i / d
            let c := i % d
            if r = c ∧ r < d then 1 else 0
          else 0))
  | ρ, Γ, Δ, whole@(.tprodE e₀ e₁) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e₀, ValExpr.inferSpaceCtx Γ e₁] fun q =>
        ValValSem.bindArrays (denotValB_partial orc ρ Γ Δ e₀)
          (denotValB_partial orc ρ Γ Δ e₁) fun a₀ a₁ =>
            if ValueShape.pair q
                (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
              .ok (.arrayOf
                (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let d₁ := ValSpace.dof q (ValExpr.inferSpaceCtx Γ e₁)
                  let i₀ := i / d₁
                  let i₁ := i % d₁
                  a₀.get i₀ * a₁.get i₁))
            else .error .mismatch
  | ρ, Γ, Δ, whole@(.dsumE e₀ e₁)  =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e₀, ValExpr.inferSpaceCtx Γ e₁] fun q =>
        ValValSem.bindArrays (denotValB_partial orc ρ Γ Δ e₀)
          (denotValB_partial orc ρ Γ Δ e₁) fun a₀ a₁ =>
            if ValueShape.pair q
                (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
              .ok (.arrayOf
                (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let d₀ := ValSpace.dof q (ValExpr.inferSpaceCtx Γ e₀)
                  if i < d₀ then a₀.get i else a₁.get (i - d₀)))
            else .error .mismatch
  | ρ, Γ, Δ, whole@(.vtrans e)     =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArray (denotValB_partial orc ρ Γ Δ e) fun a =>
          if ValueShape.tensor q (ValExpr.inferSpaceCtx Γ e) a then
            .ok (.arrayOf
              (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                match ValExpr.inferSpaceCtx Γ e with
                | .tprod s0 s1 =>
                    let d₀ := ValSpace.dof q s0
                    let d₁ := ValSpace.dof q s1
                    if i ≥ d₁ * d₀ then 0
                    else
                      let r := i / d₀
                      let c := i % d₀
                      a.get (d₁ * c + r)
                | _ => 0))
          else .error .mismatch
  | ρ, Γ, Δ, whole@(.ttv s e₀ e₁)  =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [s, ValExpr.inferSpaceCtx Γ e₀, ValExpr.inferSpaceCtx Γ e₁, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays (denotValB_partial orc ρ Γ Δ e₀)
          (denotValB_partial orc ρ Γ Δ e₁) fun a₀ a₁ =>
            if ValueShape.ttv q s
                (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
              .ok (.arrayOf
                (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let d_contract := ValSpace.dof q s
                  match ValExpr.inferSpaceCtx Γ e₀ with
                  | .tprod _ s_out =>
                      let d_out := ValSpace.dof q s_out
                      if i ≥ d_out then 0
                      else (Finset.range d_contract).sum fun j =>
                        a₀.get (d_out * j + i) * a₁.get j
                  | _ =>
                      if i = 0 then (Finset.range d_contract).sum fun j =>
                        a₀.get j * a₁.get j
                      else 0))
            else .error .mismatch
  | ρ, Γ, Δ, whole@(.mtm _ _ s_contract _ e₀ e₁) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [s_contract, ValExpr.inferSpaceCtx Γ e₀, ValExpr.inferSpaceCtx Γ e₁, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays (denotValB_partial orc ρ Γ Δ e₀)
          (denotValB_partial orc ρ Γ Δ e₁) fun a₀ a₁ =>
            if ValueShape.mtm q s_contract
                (ValExpr.inferSpaceCtx Γ e₀) (ValExpr.inferSpaceCtx Γ e₁) a₀ a₁ then
              .ok (.arrayOf
                (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  let d_contract := ValSpace.dof q s_contract
                  match ValExpr.inferSpaceCtx Γ e₀, ValExpr.inferSpaceCtx Γ e₁ with
                  | .tprod _ s_0, .tprod s_target _ =>
                      let d_0 := ValSpace.dof q s_0
                      let d_target := ValSpace.dof q s_target
                      if i ≥ d_target * d_0 then 0
                      else
                        let r := i / d_0
                        let c := i % d_0
                        (Finset.range d_contract).sum fun k =>
                          a₀.get (d_0 * k + c) * a₁.get (d_contract * r + k)
                  | _, _ => 0))
            else .error .mismatch
  | ρ, Γ, Δ, whole@(.vkrn e e')    =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ e', ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays (denotValB_partial orc ρ Γ Δ e)
          (denotValB_partial orc ρ Γ Δ e') fun a a' =>
            if ValueShape.matrices q
                (ValExpr.inferSpaceCtx Γ e) (ValExpr.inferSpaceCtx Γ e') a a' then
              .ok (.arrayOf
                (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  match ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ e' with
                  | .tprod _ s2, .tprod s1 s3 =>
                      let d_1 := ValSpace.dof q s1
                      let d_2 := ValSpace.dof q s2
                      let d_3 := ValSpace.dof q s3
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
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ e', ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays (denotValB_partial orc ρ Γ Δ e)
          (denotValB_partial orc ρ Γ Δ e') fun a a' =>
            if ValueShape.matrices q
                (ValExpr.inferSpaceCtx Γ e) (ValExpr.inferSpaceCtx Γ e') a a' then
              .ok (.arrayOf
                (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                  match ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ e' with
                  | .tprod s0 s2, .tprod _ s3 =>
                      let d_0 := ValSpace.dof q s0
                      let d_2 := ValSpace.dof q s2
                      let d_3 := ValSpace.dof q s3
                      let d_right_out := d_2 + d_3
                      let i_left := i / d_right_out
                      let i_right := i % d_right_out
                      if i_left < d_0 then
                        if i_right < d_2 then a.get (d_2 * i_left + i_right) else 0
                      else if i_right < d_2 then 0
                      else a'.get (d_3 * (i_left - d_0) + (i_right - d_2))
                  | _, _ => 0))
            else .error .mismatch
  | ρ, Γ, Δ, whole@(.vsum s es)    =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [s, ValExpr.inferSpaceCtx Γ whole] fun q =>
        let count := ValSpace.dof q s
        if count ≤ es.length then
          let active := es.take count
          let rs := active.attach.map fun e => denotValB_partial orc ρ Γ Δ e.1
          match ValValSem.sequenceArrays rs with
          | .error err => .error err
          | .ok arrays =>
              let width := ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)
              if ValueShape.family count width arrays then
                .ok (.arrayOf width (fun j =>
                  (Finset.range count).sum fun i =>
                    match arrays[i]? with
                    | some a => a.get j
                    | none => 0))
              else .error .mismatch
        else .error .mismatch
  | ρ, Γ, Δ, .reshap e τ τ₀ =>
      match denotValB_partial orc ρ Γ Δ e with
      | .error err => .error err
      | .ok v => PartialValueEval.reshapeInferred orc ρ Γ Δ v τ τ₀ (ValExpr.inferTypeCtx Γ e)
  | ρ, Γ, Δ, whole@(.pinv e)       =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArray (denotValB_partial orc ρ Γ Δ e) fun a =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof q s0
              let d1 := ValSpace.dof q s1
              if a.length = d0 * d1 then
                .ok (.arrayOf
                  (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                    let M : Matrix (Fin d0) (Fin d1) ℝ := denotAsMatrix d0 d1 a.get
                    matrixAsDenot (matrixSVDPinv M) i))
              else .error .mismatch
          | s =>
              let d := ValSpace.dof q s
              if a.length = d then
                .ok (.arrayOf
                  (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                    let M : Matrix (Fin d) (Fin 1) ℝ := fun j _ => a.get j.val
                    matrixAsDenot (matrixSVDPinv M) i))
              else .error .mismatch
  | ρ, Γ, Δ, whole@(.gsvdS e a b) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ a, ValExpr.inferSpaceCtx Γ b, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays3 (denotValB_partial orc ρ Γ Δ e)
          (denotValB_partial orc ρ Γ Δ a) (denotValB_partial orc ρ Γ Δ b)
          fun ae aa ab =>
            match ValExpr.inferSpaceCtx Γ e with
            | .tprod s0 s1 =>
                let d0 := ValSpace.dof q s0
                let d1 := ValSpace.dof q s1
                match ValueCanonicalFSV.evalSigma d0 d1 ae aa ab with
                | .error err => .error err
                | .ok r =>
                    if r.rows * r.cols =
                        ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole) then
                      .ok (.array r.flatten)
                    else .error .mismatch
            | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gsvdU e a b) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ a, ValExpr.inferSpaceCtx Γ b, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays3 (denotValB_partial orc ρ Γ Δ e)
          (denotValB_partial orc ρ Γ Δ a) (denotValB_partial orc ρ Γ Δ b)
          fun ae aa ab =>
            match ValExpr.inferSpaceCtx Γ e with
            | .tprod s0 s1 =>
                let d0 := ValSpace.dof q s0
                let d1 := ValSpace.dof q s1
                match ValueCanonicalFSV.eval .cokernel d0 d1 ae aa ab with
                | .error err => .error err
                | .ok r =>
                    if r.rows * r.cols =
                        ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole) then
                      .ok (.array r.flatten)
                    else .error .mismatch
            | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gsvdUI e a b) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ a, ValExpr.inferSpaceCtx Γ b, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays3 (denotValB_partial orc ρ Γ Δ e)
          (denotValB_partial orc ρ Γ Δ a) (denotValB_partial orc ρ Γ Δ b)
          fun ae aa ab =>
            match ValExpr.inferSpaceCtx Γ e with
            | .tprod s0 s1 =>
                let d0 := ValSpace.dof q s0
                let d1 := ValSpace.dof q s1
                match ValueCanonicalFSV.eval .kernel d0 d1 ae aa ab with
                | .error err => .error err
                | .ok r =>
                    if r.rows * r.cols =
                        ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole) then
                      .ok (.array r.flatten)
                    else .error .mismatch
            | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gsvdV e a b) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ a, ValExpr.inferSpaceCtx Γ b, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays3 (denotValB_partial orc ρ Γ Δ e)
          (denotValB_partial orc ρ Γ Δ a) (denotValB_partial orc ρ Γ Δ b)
          fun ae aa ab =>
            match ValExpr.inferSpaceCtx Γ e with
            | .tprod s0 s1 =>
                let d0 := ValSpace.dof q s0
                let d1 := ValSpace.dof q s1
                match ValueCanonicalFSV.eval .image d0 d1 ae aa ab with
                | .error err => .error err
                | .ok r =>
                    if r.rows * r.cols =
                        ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole) then
                      .ok (.array r.flatten)
                    else .error .mismatch
            | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gsvdVI e a b) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ a, ValExpr.inferSpaceCtx Γ b, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays3 (denotValB_partial orc ρ Γ Δ e)
          (denotValB_partial orc ρ Γ Δ a) (denotValB_partial orc ρ Γ Δ b)
          fun ae aa ab =>
            match ValExpr.inferSpaceCtx Γ e with
            | .tprod s0 s1 =>
                let d0 := ValSpace.dof q s0
                let d1 := ValSpace.dof q s1
                match ValueCanonicalFSV.eval .coimage d0 d1 ae aa ab with
                | .error err => .error err
                | .ok r =>
                    if r.rows * r.cols =
                        ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole) then
                      .ok (.array r.flatten)
                    else .error .mismatch
            | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.gpinv e a b)  =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ a, ValExpr.inferSpaceCtx Γ b, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays3 (denotValB_partial orc ρ Γ Δ e)
          (denotValB_partial orc ρ Γ Δ a) (denotValB_partial orc ρ Γ Δ b)
          fun ae aa ab =>
            match ValExpr.inferSpaceCtx Γ e with
            | .tprod s0 s1 =>
                let d0 := ValSpace.dof q s0
                let d1 := ValSpace.dof q s1
                if GSVDInputsShape d0 d1 ae aa ab then
                  .ok (.arrayOf
                    (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                    let M : Matrix (Fin d1) (Fin d0) ℝ :=
                      (denotAsMatrix d0 d1 ae.get).transpose
                    let MW : Matrix (Fin d0) (Fin d0) ℝ := denotAsMatrix d0 d0 aa.get
                    let MV : Matrix (Fin d1) (Fin d1) ℝ := denotAsMatrix d1 d1 ab.get
                    let P : Matrix (Fin d0) (Fin d1) ℝ := matrixGSVDPinv M MW MV
                    matrixAsDenot (m := d1) (n := d0) P.transpose i))
                else .error .mismatch
            | _ => .error .mismatch
  | ρ, Γ, Δ, whole@(.inv e)        =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArray (denotValB_partial orc ρ Γ Δ e) fun a =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof q s0
              let d1 := ValSpace.dof q s1
              if a.length = d0 * d1 then
                .ok (.arrayOf
                  (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                    let M : Matrix (Fin d0) (Fin d1) ℝ := denotAsMatrix d0 d1 a.get
                    matrixAsDenot (matrixSVDPinv M) i))
              else .error .mismatch
          | s =>
              let d := ValSpace.dof q s
              if a.length = d then
                .ok (.arrayOf
                  (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                    let M : Matrix (Fin d) (Fin 1) ℝ := fun j _ => a.get j.val
                    matrixAsDenot (matrixSVDPinv M) i))
              else .error .mismatch
  | ρ, Γ, Δ, whole@(.svds e)       =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArray (denotValB_partial orc ρ Γ Δ e) fun a =>
          match ValExpr.inferSpaceCtx Γ e with
          | .tprod s0 s1 =>
              let d0 := ValSpace.dof q s0
              let d1 := ValSpace.dof q s1
              if a.length = d0 * d1 then
                .ok (.arrayOf
                  (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole)) (fun i =>
                    let M : Matrix (Fin d1) (Fin d0) ℝ :=
                      (denotAsMatrix d0 d1 a.get).transpose
                    let g := ValueCanonicalFSV.standard M
                    matrixAsDenot (m := g.r) (n := g.r) g.sMat i))
              else .error .mismatch
          | _ => .error .mismatch
  | ρ, Γ, Δ, .vlam d _c body =>
      match denotValTyPartial orc ρ Γ Δ d with
      | .error e => .error e
      | .ok _ => .ok (.fn d.carrierEl (fun a =>
          denotValB_partial orc ρ (d :: Γ) (d.carrierToVal a :: Δ) body))
  | ρ, Γ, Δ, .appV f a =>
      match ValExpr.inferTypeCtx Γ f with
      | .space _ => .error .mismatch
      | .piTy domain _codomain =>
        PartialValueEval.applyDomainChecked orc ρ Γ Δ domain
          (denotValB_partial orc ρ Γ Δ f) (denotValB_partial orc ρ Γ Δ a)
  | ρ, Γ, Δ, whole@(.rrefRep e₀ e₁) =>
      PartialValueEval.withDimensions (orc ρ Γ Δ)
        [ValExpr.inferSpaceCtx Γ e₁, ValExpr.inferSpaceCtx Γ whole] fun q =>
        ValValSem.bindArrays (denotValB_partial orc ρ Γ Δ e₀)
          (denotValB_partial orc ρ Γ Δ e₁) fun a₀ a₁ =>
            match ValExpr.inferSpaceCtx Γ e₁ with
            | .tprod s_p0 s_p1 =>
                let d_p0 := ValSpace.dof q s_p0
                let d_p1 := ValSpace.dof q s_p1
                let K := a₀.length / d_p0
                if d_p0 = d_p1 ∧
                    a₀.length = K * d_p0 ∧
                    a₁.length = d_p0 * d_p0 then
                  .ok (.arrayOf
                    (ValSpace.dof q (ValExpr.inferSpaceCtx Γ whole))
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

/-- Evaluate with partial dimensions, decode the structural carrier, then
validate the result in the partial dependent interpretation. -/
noncomputable def denotValB_partialCheckedAt (orc : PartialFFSOracleSem)
    (ρ : ValEnvSem) (Γ : List ValTy) (Δ : List ValValSem)
    (τ : ValTy) (e : ValExpr) : Except DimError τ.carrierEl :=
  match denotValB_partial orc ρ Γ Δ e with
  | .error err => .error err
  | .ok v =>
      match τ.carrierFromVal v with
      | .error err => .error err
      | .ok a => checkValTyPartial orc ρ Γ Δ τ a

end GLang
