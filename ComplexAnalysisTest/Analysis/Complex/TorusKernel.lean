/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.Analysis.Complex.TorusKernel

/-!
# Examples of normalized torus integration

The empty torus and a positive-dimensional zero-centered torus exercise the
normalization for vector-valued and scalar-valued functions, respectively.
-/

set_option warningAsError true

@[expose] public section

open Complex Set MeasureTheory
open scoped Real

/-- The angular integral in dimension zero returns a vector-valued function's
value at the unique point, with no assumptions on the function. -/
example (f : (Fin 0 → ℂ) → (Fin 2 → ℂ)) (R : Fin 0 → ℝ) :
    (∫ θ : Fin 0 → ℝ in Icc (0 : Fin 0 → ℝ) (fun _ => 2 * π),
      (∏ i, torusMap 0 R θ i / (torusMap 0 R θ i - (0 : Fin 0 → ℂ) i)) •
        f (torusMap 0 R θ)) = f 0 := by
  have h := torusIntegral_prod_inv_normalized_zero f (0 : Fin 0 → ℂ) R
  simpa only [pow_zero, ofReal_one, inv_one, one_smul, Fin.prod_univ_zero,
    torusIntegral_dim0] using h.symm

/-- A two-dimensional zero-centered torus admits the same normalization for an
unrestricted scalar boundary function, including vanishing radii. -/
example (f : (Fin 2 → ℂ) → ℂ) (z : Fin 2 → ℂ) (R : Fin 2 → ℝ) :
    ((2 * (π : ℂ) * I) ^ 2)⁻¹ *
        torusIntegral (fun w => ((w 0 - z 0) * (w 1 - z 1))⁻¹ * f w) 0 R =
      (((2 * π : ℝ) ^ 2 : ℝ) : ℂ)⁻¹ *
        ∫ θ : Fin 2 → ℝ in Icc (0 : Fin 2 → ℝ) (fun _ => 2 * π),
          (torusMap 0 R θ 0 / (torusMap 0 R θ 0 - z 0) *
            (torusMap 0 R θ 1 / (torusMap 0 R θ 1 - z 1))) *
            f (torusMap 0 R θ) := by
  simpa only [smul_eq_mul, Fin.prod_univ_two, mul_inv_rev, mul_comm] using
    torusIntegral_prod_inv_normalized_zero f z R

end
