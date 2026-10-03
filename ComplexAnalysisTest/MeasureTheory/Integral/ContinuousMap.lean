/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.MeasureTheory.Integral.ContinuousMap

/-!
# Angular-cube integration examples

The zero-dimensional angular cube and a product-valued integrand exercise normalization and
constant preservation without imposing finite-dimensionality on the operator's target.
-/

set_option warningAsError true

@[expose] public section

open ContinuousMap

example (value : ℂ × ℂ) :
    cubeAverageCLM 0 (ContinuousMap.const (angularCube 0) value) = value := by
  simp

example (f : C(angularCube 0, ℂ × ℂ)) :
    cubeAverageCLM 0 f = ∫ θ : angularCube 0, f θ := by
  simp [cubeAverageCLM_apply]

example (value : ℂ × ℂ) :
    (((((2 * Real.pi) ^ 2)⁻¹ : ℝ) : ℂ)) •
      ∫ θ : angularCube 2, (ContinuousMap.const (angularCube 2) value) θ = value := by
  simpa only [cubeAverageCLM_apply] using
    (cubeAverageCLM_const 2 value)
