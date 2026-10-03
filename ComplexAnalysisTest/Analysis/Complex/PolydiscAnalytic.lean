/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ComplexAnalysis.Analysis.Complex.PolydiscAnalytic

/-! # Vector-valued analyticity on closed polydiscs -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

example (v : ℂ × ℂ) : AnalyticAt ℂ (fun _ : Fin 0 → ℂ => v) 0 := by
  exact (differentiable_const v).differentiableOn.analyticAt_zero_of_polydisc
    (R := 1) (by norm_num)

example : AnalyticAt ℂ (fun z : Fin 2 → ℂ => (z 0 * z 1 + 1, z 1 ^ 2)) 0 := by
  have hf : DifferentiableOn ℂ (fun z : Fin 2 → ℂ => (z 0 * z 1 + 1, z 1 ^ 2))
      {z | ∀ i, ‖z i‖ ≤ (1 : ℝ)} := by
    apply Differentiable.differentiableOn
    fun_prop
  exact hf.analyticAt_zero_of_polydisc (by norm_num)
