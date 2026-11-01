/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.MeasureTheory.Integral.Kernel

/-!
# A constant imaginary kernel

A purely imaginary constant kernel has the same, rather than conjugate, phase
in its output. This also checks agreement with integration on continuous inputs.
-/

open MeasureTheory
open scoped ENNReal

universe uX uY

variable {X : Type uX} [TopologicalSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [CompactSpace Y]
variable [MeasurableSpace Y] [BorelSpace Y]

local instance : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The constant imaginary kernel sends the constant unit input to its mass times `Complex.I`. -/
public theorem ContinuousMap.kernelOperator_const_I_toLp_one (μ : Measure Y) [IsFiniteMeasure μ] :
    ContinuousMap.kernelOperator μ (ContinuousMap.const (X × Y) Complex.I)
        (ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ (ContinuousMap.const Y 1)) =
      ContinuousMap.const X (μ.real Set.univ • Complex.I) := by
  ext x
  rw [ContinuousMap.kernelOperator_toLp_apply]
  have h : (ContinuousMap.const (X × Y) Complex.I).curry x *
      ContinuousMap.const Y (1 : ℂ) = ContinuousMap.const Y Complex.I := by
    ext y
    simp
  rw [h, ContinuousMap.integralCLM_const]
  rfl
