/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.MeasureTheory.Integral.TorusIntegral

/-!
# Normalizing torus integrals with inverse coordinate kernels

The Jacobian in `torusIntegral` cancels a product of inverse coordinate differences
pointwise, leaving an angular integral of boundary ratios. The identity requires no
integrability, completeness, or nonzero-radius assumptions on the complex normed target.
-/

set_option warningAsError true

@[expose] public section

open Complex Set MeasureTheory
open scoped Real

universe u

variable {n : ℕ} {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem torus_jacobian_mul_prod_inv (c z : Fin n → ℂ) (R θ : Fin n → ℝ) :
    (∏ i, R i * exp (θ i * I) * I : ℂ) *
        (∏ i, (torusMap c R θ i - z i)⁻¹) =
      I ^ n * ∏ i, (torusMap c R θ i - c i) / (torusMap c R θ i - z i) := by
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ i, (R i * exp (θ i * I) * I : ℂ) * (torusMap c R θ i - z i)⁻¹) =
        ∏ i, I * ((torusMap c R θ i - c i) / (torusMap c R θ i - z i)) := by
          apply Finset.prod_congr rfl
          intro i _
          simp only [torusMap, add_sub_cancel_left, div_eq_mul_inv]
          ring
    _ = I ^ n * ∏ i, (torusMap c R θ i - c i) / (torusMap c R θ i - z i) := by
      rw [Finset.prod_mul_distrib, Fin.prod_const]

/-- The inverse-coordinate kernel turns the torus Jacobian into the product of
boundary ratios, up to the factor `I ^ n`. This holds even when some radii vanish. -/
theorem torusIntegral_prod_inv (f : (Fin n → ℂ) → F) (c z : Fin n → ℂ)
    (R : Fin n → ℝ) :
    torusIntegral (fun w => (∏ i, (w i - z i)⁻¹) • f w) c R =
      I ^ n • ∫ θ : Fin n → ℝ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π),
        (∏ i, (torusMap c R θ i - c i) / (torusMap c R θ i - z i)) •
          f (torusMap c R θ) := by
  rw [torusIntegral, ← integral_smul]
  congr 1
  funext θ
  simp only [smul_smul]
  rw [torus_jacobian_mul_prod_inv]

private theorem normalized_factor (n : ℕ) :
    ((2 * (π : ℂ) * I) ^ n)⁻¹ * I ^ n = (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ := by
  have h : 2 * (π : ℂ) * I = ((2 * π : ℝ) : ℂ) * I := by push_cast; rfl
  rw [h, mul_pow, mul_inv_rev]
  calc
    (I ^ n)⁻¹ * (((2 * π : ℝ) : ℂ) ^ n)⁻¹ * I ^ n =
        (((2 * π : ℝ) : ℂ) ^ n)⁻¹ * ((I ^ n)⁻¹ * I ^ n) := by ring
    _ = (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ := by
      rw [inv_mul_cancel₀ (pow_ne_zero n I_ne_zero), mul_one]
      norm_cast

/-- Normalized torus integration of an inverse-coordinate kernel is the angular
integral of the corresponding boundary ratios, normalized by the cube volume. -/
theorem torusIntegral_prod_inv_normalized (f : (Fin n → ℂ) → F)
    (c z : Fin n → ℂ) (R : Fin n → ℝ) :
    ((2 * (π : ℂ) * I) ^ n)⁻¹ •
        torusIntegral (fun w => (∏ i, (w i - z i)⁻¹) • f w) c R =
      (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ •
        ∫ θ : Fin n → ℝ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π),
          (∏ i, (torusMap c R θ i - c i) / (torusMap c R θ i - z i)) •
            f (torusMap c R θ) := by
  rw [torusIntegral_prod_inv, smul_smul, normalized_factor]

/-- For a torus centered at zero, the boundary ratios have numerator `torusMap 0 R θ i`. -/
theorem torusIntegral_prod_inv_normalized_zero (f : (Fin n → ℂ) → F)
    (z : Fin n → ℂ) (R : Fin n → ℝ) :
    ((2 * (π : ℂ) * I) ^ n)⁻¹ •
        torusIntegral (fun w => (∏ i, (w i - z i)⁻¹) • f w) 0 R =
      (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ •
        ∫ θ : Fin n → ℝ in Icc (0 : Fin n → ℝ) (fun _ => 2 * π),
          (∏ i, torusMap 0 R θ i / (torusMap 0 R θ i - z i)) •
            f (torusMap 0 R θ) := by
  simpa only [Pi.zero_apply, sub_zero] using torusIntegral_prod_inv_normalized f 0 z R

end
