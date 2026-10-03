/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.Analysis.Complex.PolydiscKernel

/-!
# Tests for analytic Cauchy kernels

A two-coordinate kernel on a two-point compact space has genuinely varying boundary
values. At distinct nonzero coordinate inputs its quotient formula gives different
values at the two points. On a zero-dimensional coordinate space the product is
identically one, and a fixed vector-valued multiplier remains analytic.
-/

set_option warningAsError true

@[expose] public section

namespace ContinuousMap

example :
    ∃ (boundary : Fin 2 → C(Fin 2, ℂ)) (input : Fin 2 → ℂ),
      (∀ i x, boundary i x = if i = x then (1 : ℂ) else -1) ∧
      input 0 = 1 / 2 ∧ input 1 = 1 / 3 ∧
      cauchyKernelProd (fun i => Ring.inverse (boundary i)) Finset.univ input 0 = 3 / 2 ∧
      cauchyKernelProd (fun i => Ring.inverse (boundary i)) Finset.univ input 1 = 1 ∧
      cauchyKernelProd (fun i => Ring.inverse (boundary i)) Finset.univ input 0 ≠
        cauchyKernelProd (fun i => Ring.inverse (boundary i)) Finset.univ input 1 ∧
      AnalyticAt ℂ
        (fun z : Fin 2 → ℂ =>
          smulRightCLM (ContinuousMap.const (Fin 2) ((1 : ℂ), Complex.I))
            (cauchyKernelProd (fun i => Ring.inverse (boundary i)) Finset.univ z)) 0 ∧
      (smulRightCLM (ContinuousMap.const (Fin 2) ((1 : ℂ), Complex.I))
        (cauchyKernelProd (fun i => Ring.inverse (boundary i)) Finset.univ input))
          (0 : Fin 2) = ((3 / 2 : ℂ), (3 / 2 : ℂ) * Complex.I) ∧
      (smulRightCLM (ContinuousMap.const (Fin 2) ((1 : ℂ), Complex.I))
        (cauchyKernelProd (fun i => Ring.inverse (boundary i)) Finset.univ input))
          (1 : Fin 2) = ((1 : ℂ), Complex.I) := by
  let boundary : Fin 2 → C(Fin 2, ℂ) := fun i =>
    ⟨(fun x => if i = x then (1 : ℂ) else -1), continuous_of_discreteTopology⟩
  let input : Fin 2 → ℂ := fun i => if i = 0 then 1 / 2 else 1 / 3
  have boundary_norm (i x : Fin 2) : ‖boundary i x‖ = 1 := by
    by_cases h : i = x <;> simp [boundary, h]
  have input_norm (i : Fin 2) : ‖input i‖ < 1 := by
    fin_cases i <;> norm_num [input]
  have kernel_zero :
      cauchyKernelProd (fun i => Ring.inverse (boundary i)) Finset.univ input 0 = 3 / 2 := by
    rw [cauchyKernelProd_boundary_apply boundary Finset.univ input
      (show (0 : ℝ) < 1 by norm_num)
      (by intro i _ x; exact boundary_norm i x)
      (by intro i _; exact input_norm i) (0 : Fin 2)]
    norm_num [Fin.prod_univ_two, boundary, input]
  have kernel_one :
      cauchyKernelProd (fun i => Ring.inverse (boundary i)) Finset.univ input 1 = 1 := by
    rw [cauchyKernelProd_boundary_apply boundary Finset.univ input
      (show (0 : ℝ) < 1 by norm_num)
      (by intro i _ x; exact boundary_norm i x)
      (by intro i _; exact input_norm i) (1 : Fin 2)]
    norm_num [Fin.prod_univ_two, boundary, input]
  refine ⟨boundary, input, ?_, ?_, ?_, kernel_zero, kernel_one, ?_, ?_, ?_, ?_⟩
  · intro i x
    rfl
  · norm_num [input]
  · norm_num [input]
  · rw [kernel_zero, kernel_one]
    norm_num
  · exact analyticAt_cauchyKernelProd_smul _ _ _
  · rw [smulRightCLM_apply, kernel_zero]
    simp
  · rw [smulRightCLM_apply, kernel_one]
    simp

example :
    AnalyticAt ℂ
      (cauchyKernelProd (fun _ : Fin 0 => (1 : C(Fin 2, ℂ))) Finset.univ) 0 ∧
    ∀ z : Fin 0 → ℂ,
      cauchyKernelProd (fun _ : Fin 0 => (1 : C(Fin 2, ℂ))) Finset.univ z = 1 := by
  constructor
  · exact analyticAt_cauchyKernelProd _ Finset.univ
  · intro z
    simp [cauchyKernelProd]

example :
    AnalyticAt ℂ
      (fun z : Fin 0 → ℂ =>
        smulRightCLM (ContinuousMap.const (Fin 2) ((1 : ℂ), Complex.I))
          (cauchyKernelProd (fun _ : Fin 0 => (1 : C(Fin 2, ℂ))) Finset.univ z)) 0 ∧
    ∀ z : Fin 0 → ℂ,
      (smulRightCLM (ContinuousMap.const (Fin 2) ((1 : ℂ), Complex.I))
        (cauchyKernelProd (fun _ : Fin 0 => (1 : C(Fin 2, ℂ))) Finset.univ z))
          (0 : Fin 2) =
        ((1 : ℂ), Complex.I) := by
  constructor
  · exact analyticAt_cauchyKernelProd_smul _ _ _
  · intro z
    simp [cauchyKernelProd, smulRightCLM_apply]

end ContinuousMap
