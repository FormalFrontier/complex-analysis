/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.Analysis.Complex.PolynomialBoundary
public import PolynomialRootStability.ScaleRoots

/-!
# Exterior root-scaling homotopies of complex polynomials

For a fixed complex polynomial `p` nonvanishing at every complex number of norm
at least one, root scaling over the real unit interval gives a homotopy from the
normalized leading monomial `p.leadingCoeff • X ^ p.natDegree` to the normalized
polynomial boundary map. Its characteristic value at real `t ∈ I` and `z : Circle`
is `NormedSpace.normalize ((p.scaleRoots (t : ℂ)).eval (z : ℂ))`.

Mathlib's division-free `scaleRoots` family is defined at zero scaling: its zero
endpoint is `p.leadingCoeff • X ^ p.natDegree`, and its one endpoint is `p`.
The normalized maps are unbased, retaining the leading coefficient's arbitrary
phase, including for nonzero constants. The ambient zero endpoint is
`NormedSpace.normalize p.leadingCoeff * (z : ℂ) ^ p.natDegree`.

The exterior degree statement identifies the normalized boundary degree with
`p.natDegree`. Its degree route uses the constant and `X` calculations, products,
powers and homotopy invariance, not the fundamental theorem of algebra or the
interior-root multiplicity formula. The disk family obtained by evaluating
`p(t*z)` is a separate construction.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §7,
  proof of the fundamental theorem of algebra, pp. 10–11, for the exterior
  root-scaling homotopy and its degree, before the Problems. Problem (1), p. 11,
  is the separate degree and root-multiplicity identity.
* Mathlib supplies the root-scaling operation, polynomial continuity and the
  complex circle. Polynomial Root Stability supplies joint continuity and
  scale-relative nonvanishing of Mathlib's root-scaling operation.
* `PolynomialBoundary` supplies normalized polynomial boundary maps and the
  constant and linear-factor degree calculations. Sphere Topology supplies
  normalization of nowhere-zero continuous maps and integer degree with the
  positive circle generator, including product, power and homotopy APIs.
-/

@[expose] public section

noncomputable section

namespace Polynomial

open scoped unitInterval

/-- Root scaling gives a homotopy from the normalized leading monomial to the
normalized polynomial boundary map when the polynomial has no zero of norm at
least one. The parameter is real and the circle maps need not preserve `1`.
This is the exterior homotopy in May, Chapter 1, §7, pp. 10–11. -/
def normalizedCircleMapScaleRootsHomotopy (p : ℂ[X])
    (hOutside : ∀ w : ℂ, 1 ≤ ‖w‖ → p.eval w ≠ 0) :
    ContinuousMap.Homotopy
      ((p.leadingCoeff • X ^ p.natDegree : ℂ[X]).normalizedCircleMap
        (fun z => by
          simpa only [scaleRoots_zero] using
            p.scaleRoots_eval_ne_zero_of_norm_le hOutside
              (t := (0 : ℂ)) (z := (z : ℂ)) (by simp) z.coe_ne_zero))
      (p.normalizedCircleMap (fun z => hOutside z (by simp))) := by
  let V : C(I × Circle, ℂ) :=
    ⟨fun q => (p.scaleRoots (q.1 : ℂ)).eval (q.2 : ℂ),
      p.continuous_eval_scaleRoots.comp
        ((Complex.continuous_ofReal.comp
          (continuous_subtype_val.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd))⟩
  have hV : ∀ q, V q ≠ 0 := by
    intro q
    apply p.scaleRoots_eval_ne_zero_of_norm_le hOutside _ q.2.coe_ne_zero
    simpa only [Complex.norm_real, Real.norm_of_nonneg q.1.2.1,
      Circle.norm_coe] using q.1.2.2
  let N := ContinuousMap.normalizeOfNoZero V hV
  exact
    { toFun q := ⟨N q, mem_sphere_zero_iff_norm.mpr
        (ContinuousMap.norm_normalizeOfNoZero V hV q)⟩
      continuous_toFun := N.continuous.subtype_mk _
      map_zero_left z := by
        apply Subtype.ext
        change NormedSpace.normalize ((p.scaleRoots (0 : ℂ)).eval (z : ℂ)) =
          NormedSpace.normalize
            ((p.leadingCoeff • X ^ p.natDegree : ℂ[X]).eval (z : ℂ))
        rw [scaleRoots_zero]
      map_one_left z := by
        apply Subtype.ext
        change NormedSpace.normalize ((p.scaleRoots (1 : ℂ)).eval (z : ℂ)) =
          NormedSpace.normalize (p.eval (z : ℂ))
        rw [scaleRoots_one] }

/-- Ambient evaluation of the root-scaling homotopy, including at zero scaling.
The polynomial family is division-free throughout the real unit interval. -/
@[simp]
theorem normalizedCircleMapScaleRootsHomotopy_apply (p : ℂ[X])
    (hOutside : ∀ w : ℂ, 1 ≤ ‖w‖ → p.eval w ≠ 0) (t : I) (z : Circle) :
    (p.normalizedCircleMapScaleRootsHomotopy hOutside (t, z) : ℂ) =
      NormedSpace.normalize ((p.scaleRoots (t : ℂ)).eval (z : ℂ)) := rfl

/-- The zero endpoint is the canonical normalized leading-monomial boundary map. -/
theorem normalizedCircleMapScaleRootsHomotopy_apply_zero (p : ℂ[X])
    (hOutside : ∀ w : ℂ, 1 ≤ ‖w‖ → p.eval w ≠ 0) (z : Circle) :
    p.normalizedCircleMapScaleRootsHomotopy hOutside (0, z) =
      (p.leadingCoeff • X ^ p.natDegree : ℂ[X]).normalizedCircleMap
        (fun w => by
          simpa only [scaleRoots_zero] using
            p.scaleRoots_eval_ne_zero_of_norm_le hOutside
              (t := (0 : ℂ)) (z := (w : ℂ)) (by simp) w.coe_ne_zero) z :=
  (p.normalizedCircleMapScaleRootsHomotopy hOutside).apply_zero z

/-- The one endpoint is the canonical normalized polynomial boundary map. -/
theorem normalizedCircleMapScaleRootsHomotopy_apply_one (p : ℂ[X])
    (hOutside : ∀ w : ℂ, 1 ≤ ‖w‖ → p.eval w ≠ 0) (z : Circle) :
    p.normalizedCircleMapScaleRootsHomotopy hOutside (1, z) =
      p.normalizedCircleMap (fun w => hOutside w (by simp)) z :=
  (p.normalizedCircleMapScaleRootsHomotopy hOutside).apply_one z

/-- The ambient zero endpoint retains the leading coefficient's arbitrary phase. -/
theorem normalizedCircleMapScaleRootsHomotopy_apply_zero_coe (p : ℂ[X])
    (hOutside : ∀ w : ℂ, 1 ≤ ‖w‖ → p.eval w ≠ 0) (z : Circle) :
    (p.normalizedCircleMapScaleRootsHomotopy hOutside (0, z) : ℂ) =
      NormedSpace.normalize p.leadingCoeff * (z : ℂ) ^ p.natDegree := by
  rw [normalizedCircleMapScaleRootsHomotopy_apply]
  change NormedSpace.normalize ((p.scaleRoots (0 : ℂ)).eval (z : ℂ)) = _
  simp only [scaleRoots_zero, eval_smul, eval_pow, eval_X, smul_eq_mul,
    NormedSpace.normalize, norm_mul, norm_pow, Circle.norm_coe, one_pow,
    mul_one, smul_mul_assoc]

/-- A complex polynomial nonvanishing at every point of norm at least one has
normalized boundary degree equal to its natural degree, including for nonzero
constants with arbitrary phase. This is the exterior degree calculation in
May, Chapter 1, §7, pp. 10–11. -/
theorem degree_normalizedCircleMap_of_nonvanishing_outside (p : ℂ[X])
    (hOutside : ∀ w : ℂ, 1 ≤ ‖w‖ → p.eval w ≠ 0) :
    Circle.degree (p.normalizedCircleMap (fun z => hOutside z (by simp))) =
      (p.natDegree : ℤ) := by
  let H := p.normalizedCircleMapScaleRootsHomotopy hOutside
  let c : Circle := H (0, 1)
  have hc : (c : ℂ) = NormedSpace.normalize p.leadingCoeff := by
    simpa only [Circle.coe_one, one_pow, mul_one] using
      p.normalizedCircleMapScaleRootsHomotopy_apply_zero_coe hOutside 1
  have hzero (z : Circle) : H (0, z) = c * z ^ p.natDegree := by
    apply Circle.ext
    simpa only [Circle.coe_mul, Circle.coe_pow, hc] using
      p.normalizedCircleMapScaleRootsHomotopy_apply_zero_coe hOutside z
  rw [← Circle.degree_eq_of_homotopic ⟨H⟩]
  calc
    _ = Circle.degree
        (ContinuousMap.const Circle c * (ContinuousMap.id Circle) ^ p.natDegree) := by
      apply congrArg Circle.degree
      apply ContinuousMap.ext
      intro z
      exact (H.apply_zero z).symm.trans (hzero z)
    _ = (p.natDegree : ℤ) := by
      rw [Circle.degree_mul, Circle.degree_const, zero_add]
      simpa only [zpow_natCast] using Circle.degree_zpow (p.natDegree : ℤ)

end Polynomial
