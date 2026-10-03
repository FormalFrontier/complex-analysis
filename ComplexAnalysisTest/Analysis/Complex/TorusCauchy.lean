/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ComplexAnalysis.Analysis.Complex.TorusCauchy

/-! # Examples of the Cauchy formula on a polydisc -/

@[expose] public section

open Complex
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

example (v : ℂ × ℂ) :
    (∯ w in T((0 : Fin 0 → ℂ), (fun _ => (1 : ℝ))),
      (∏ i, (w i)⁻¹) • v) = v := by
  have h := (differentiable_const v).differentiableOn.torusIntegral_cauchy
    (c := (0 : Fin 0 → ℂ)) (z := 0) (R := fun _ => 1)
    (by intro i; exact Fin.elim0 i)
  simpa only [Pi.zero_apply, sub_zero, pow_zero, one_smul] using h

example :
    (∯ w in T((0 : Fin 2 → ℂ), (fun _ => (1 : ℝ))),
      (∏ i, (w i)⁻¹) • (w 0 + 1, w 1 ^ 2 + 1)) =
      (2 * (Real.pi : ℂ) * I) ^ 2 • ((1 : ℂ), (1 : ℂ)) := by
  have hf : Differentiable ℂ (fun w : Fin 2 → ℂ => (w 0 + 1, w 1 ^ 2 + 1)) := by
    fun_prop
  simpa using hf.differentiableOn.torusIntegral_cauchy
    (c := 0) (z := 0) (R := fun _ => 1) (by intro i; simp)

example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℂ → F} {c w : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (hw : w ∈ Metric.ball c R) :
    (∮ ζ in C(c, R), (ζ - w)⁻¹ • f ζ) = (2 * (Real.pi : ℂ) * I) • f w := by
  have hg : DifferentiableOn ℂ (fun y : Fin 1 → ℂ => f (y 0))
      {y | ∀ i, y i ∈ Metric.closedBall c R} :=
    hf.fun_comp (differentiable_apply 0).differentiableOn (fun y hy => hy 0)
  simpa [torusIntegral_dim1] using hg.torusIntegral_cauchy
    (c := fun _ => c) (z := fun _ => w) (R := fun _ => R) (fun _ => hw)
