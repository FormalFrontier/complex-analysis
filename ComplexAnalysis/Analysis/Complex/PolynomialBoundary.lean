/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Homotopy.Basic
public import SphereTopology.Homotopy.CircleDegree
public import SphereTopology.Homotopy.Sphere
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Normalized boundary maps of complex polynomials

A complex polynomial with no zeros on the unit circle gives a continuous circle
self-map by normalizing its values. This is an unbased map: its value at `1` is
not required to be `1`. The ambient evaluation formula is
`‖p.eval (z : ℂ)‖⁻¹ • p.eval (z : ℂ)`.

For a polynomial with no zeros on the closed unit disk, normalizing `p(tz)`
gives a homotopy from the constant phase of `p(0)` to its boundary map. The
parameter precedes the circle point, following Mathlib's homotopy convention.

The boundary degree counts roots strictly inside the unit disk with their
multiset multiplicities. The root-count proof uses the constant and linear-factor
calculations, additivity of circle degree under pointwise multiplication, and
Mathlib's algebraic closedness of `ℂ` to induct on split polynomials. Thus the
root-count identity retains the existing fundamental theorem of algebra as an
input; this module does not construct the exterior polynomial homotopy.

## References

* J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §7,
  p. 10 (PDF p. 18), for the disk-scaling homotopy in the proof of the
  fundamental theorem of algebra; Problem (1), p. 11, for the degree and
  root-multiplicity identity.
* Mathlib supplies polynomial continuity, root multisets, split-polynomial
  induction, the fundamental theorem of algebra and the complex circle.
  Sphere Topology supplies normalization of nowhere-zero continuous maps and
  integer degree with the positive circle generator, including additivity under
  pointwise multiplication.
-/

@[expose] public section

noncomputable section

namespace Polynomial

/-- The normalized boundary map of a complex polynomial with no zeros on the
unit circle. No condition on its value at `1` is imposed. -/
def normalizedCircleMap (p : ℂ[X])
    (h : ∀ z : Circle, p.eval (z : ℂ) ≠ 0) : C(Circle, Circle) := by
  let V : C(Circle, ℂ) :=
    ⟨fun z => p.eval (z : ℂ), p.continuous.comp continuous_subtype_val⟩
  let N := ContinuousMap.normalizeOfNoZero V h
  exact
    { toFun z := ⟨N z, mem_sphere_zero_iff_norm.mpr
        (ContinuousMap.norm_normalizeOfNoZero V h z)⟩
      continuous_toFun := N.continuous.subtype_mk _ }

/-- Ambient evaluation of the normalized polynomial boundary map. -/
@[simp]
theorem normalizedCircleMap_apply (p : ℂ[X])
    (h : ∀ z : Circle, p.eval (z : ℂ) ≠ 0) (z : Circle) :
    (p.normalizedCircleMap h z : ℂ) =
      ‖p.eval (z : ℂ)‖⁻¹ • p.eval (z : ℂ) := rfl

/-- Normalization carries a product of boundary-nonvanishing polynomials to
the pointwise product of their normalized boundary maps. -/
theorem normalizedCircleMap_mul (p q : ℂ[X])
    (hp : ∀ z : Circle, p.eval (z : ℂ) ≠ 0)
    (hq : ∀ z : Circle, q.eval (z : ℂ) ≠ 0) :
    (p * q).normalizedCircleMap
        (fun z => by simpa only [eval_mul] using mul_ne_zero (hp z) (hq z)) =
      p.normalizedCircleMap hp * q.normalizedCircleMap hq := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  simp only [ContinuousMap.mul_apply, Circle.coe_mul, normalizedCircleMap_apply,
    eval_mul, norm_mul, mul_inv, smul_mul_smul_comm]

/-- The normalized boundary map of a constant polynomial has degree zero,
with no restriction on its phase. -/
theorem degree_normalizedCircleMap_C (c : ℂ)
    (h : ∀ z : Circle, (C c : ℂ[X]).eval (z : ℂ) ≠ 0) :
    Circle.degree ((C c : ℂ[X]).normalizedCircleMap h) = 0 := by
  have heq : (C c : ℂ[X]).normalizedCircleMap h =
      ContinuousMap.const Circle ((C c : ℂ[X]).normalizedCircleMap h 1) := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    simp only [ContinuousMap.const_apply, normalizedCircleMap_apply, eval_C]
  exact (congrArg Circle.degree heq).trans (Circle.degree_const _)

open scoped unitInterval

/-- The disk-scaling homotopy of a polynomial with no zeros on the closed unit
disk, from the constant phase of its value at zero to its normalized boundary
map. This is May's family in Chapter 1, §7, p. 10, with time as the first
coordinate. No basedness condition is imposed. -/
def normalizedCircleMapDiskHomotopy (p : ℂ[X])
    (hClosed : ∀ w : ℂ, ‖w‖ ≤ 1 → p.eval w ≠ 0) :
    ContinuousMap.Homotopy
      (ContinuousMap.const Circle
        (⟨NormedSpace.normalize (p.eval 0), mem_sphere_zero_iff_norm.mpr
          (NormedSpace.norm_normalize
            (hClosed 0 ((norm_zero : ‖(0 : ℂ)‖ = 0).le.trans zero_le_one)))⟩ : Circle))
      (p.normalizedCircleMap (fun z => hClosed (z : ℂ) (le_of_eq z.norm_coe))) := by
  let V : C(I × Circle, ℂ) :=
    ⟨fun q => p.eval (((q.1 : ℝ) : ℂ) * (q.2 : ℂ)),
      p.continuous.comp
        ((Complex.continuous_ofReal.comp
          (continuous_subtype_val.comp continuous_fst)).mul
          (continuous_subtype_val.comp continuous_snd))⟩
  have hV : ∀ q, V q ≠ 0 := by
    intro q
    apply hClosed
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg q.1.2.1,
      Circle.norm_coe, mul_one]
    exact q.1.2.2
  let N := ContinuousMap.normalizeOfNoZero V hV
  exact
    { toFun q := ⟨N q, mem_sphere_zero_iff_norm.mpr
        (ContinuousMap.norm_normalizeOfNoZero V hV q)⟩
      continuous_toFun := N.continuous.subtype_mk _
      map_zero_left z := by
        apply Subtype.ext
        change N (0, z) = NormedSpace.normalize (p.eval 0)
        rw [ContinuousMap.normalizeOfNoZero_apply]
        change NormedSpace.normalize (p.eval (((0 : ℝ) : ℂ) * (z : ℂ))) = _
        simp only [Complex.ofReal_zero, zero_mul]
      map_one_left z := by
        apply Subtype.ext
        change N (1, z) = (p.normalizedCircleMap _ z : ℂ)
        rw [ContinuousMap.normalizeOfNoZero_apply, normalizedCircleMap_apply]
        change NormedSpace.normalize (p.eval (((1 : ℝ) : ℂ) * (z : ℂ))) = _
        simp only [Complex.ofReal_one, one_mul, NormedSpace.normalize] }

/-- Ambient evaluation of the polynomial disk-scaling homotopy at every time
and circle point, including time zero. -/
@[simp]
theorem normalizedCircleMapDiskHomotopy_apply (p : ℂ[X])
    (hClosed : ∀ w : ℂ, ‖w‖ ≤ 1 → p.eval w ≠ 0) (t : I) (z : Circle) :
    ((p.normalizedCircleMapDiskHomotopy hClosed).toContinuousMap (t, z) : ℂ) =
      ‖p.eval (((t : ℝ) : ℂ) * (z : ℂ))‖⁻¹ •
        p.eval (((t : ℝ) : ℂ) * (z : ℂ)) := rfl

/-- A polynomial with no zeros on the closed unit disk has normalized boundary
degree zero, as in May, Chapter 1, §7, p. 10. -/
theorem degree_normalizedCircleMap_eq_zero_of_forall_norm_le_one (p : ℂ[X])
    (hClosed : ∀ w : ℂ, ‖w‖ ≤ 1 → p.eval w ≠ 0) :
    Circle.degree
      (p.normalizedCircleMap (fun z => hClosed (z : ℂ) (le_of_eq z.norm_coe))) = 0 := by
  exact (Circle.degree_eq_of_homotopic
    ⟨p.normalizedCircleMapDiskHomotopy hClosed⟩).symm.trans (Circle.degree_const _)

private theorem degree_normalizedCircleMap_X_sub_C_of_norm_lt (a : ℂ)
    (h : ∀ z : Circle, (X - C a : ℂ[X]).eval (z : ℂ) ≠ 0) (ha : ‖a‖ < 1) :
    Circle.degree ((X - C a : ℂ[X]).normalizedCircleMap h) = 1 := by
  let V : C(I × Circle, ℂ) :=
    ⟨fun q => (q.2 : ℂ) - (q.1 : ℝ) • a,
      (continuous_subtype_val.comp continuous_snd).sub
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)⟩
  have hV : ∀ q, V q ≠ 0 := by
    intro q hq
    have hnorm : ‖(q.1 : ℝ) • a‖ < 1 := calc
      ‖(q.1 : ℝ) • a‖ = (q.1 : ℝ) * ‖a‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg q.1.2.1]
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right q.1.2.2 (norm_nonneg a)
      _ = ‖a‖ := one_mul _
      _ < 1 := ha
    have heq : (q.2 : ℂ) = (q.1 : ℝ) • a := sub_eq_zero.mp hq
    rw [← heq, Circle.norm_coe] at hnorm
    exact (lt_irrefl 1) hnorm
  let N := ContinuousMap.normalizeOfNoZero V hV
  let H : ContinuousMap.Homotopy (ContinuousMap.id Circle)
      ((X - C a : ℂ[X]).normalizedCircleMap h) :=
    { toFun q := ⟨N q, mem_sphere_zero_iff_norm.mpr
        (ContinuousMap.norm_normalizeOfNoZero V hV q)⟩
      continuous_toFun := N.continuous.subtype_mk _
      map_zero_left z := by
        apply Subtype.ext
        change N (0, z) = (z : ℂ)
        rw [ContinuousMap.normalizeOfNoZero_apply]
        change NormedSpace.normalize ((z : ℂ) - (0 : ℝ) • a) = (z : ℂ)
        simpa only [zero_smul, sub_zero] using
          (NormedSpace.normalize_eq_self_of_norm_eq_one z.norm_coe)
      map_one_left z := by
        apply Subtype.ext
        change N (1, z) = (((X - C a : ℂ[X]).normalizedCircleMap h z) : ℂ)
        rw [ContinuousMap.normalizeOfNoZero_apply, normalizedCircleMap_apply]
        change NormedSpace.normalize ((z : ℂ) - (1 : ℝ) • a) =
          ‖(X - C a : ℂ[X]).eval (z : ℂ)‖⁻¹ • (X - C a : ℂ[X]).eval (z : ℂ)
        simp only [one_smul, NormedSpace.normalize, eval_sub, eval_X, eval_C] }
  exact (Circle.degree_eq_of_homotopic ⟨H⟩).symm.trans Circle.degree_id

private theorem degree_normalizedCircleMap_X_sub_C_of_one_lt_norm (a : ℂ)
    (h : ∀ z : Circle, (X - C a : ℂ[X]).eval (z : ℂ) ≠ 0) (ha : 1 < ‖a‖) :
    Circle.degree ((X - C a : ℂ[X]).normalizedCircleMap h) = 0 := by
  have hClosed : ∀ w : ℂ, ‖w‖ ≤ 1 → (X - C a : ℂ[X]).eval w ≠ 0 := by
    intro w hw hw0
    have heq : w = a := sub_eq_zero.mp (by simpa only [eval_sub, eval_X, eval_C] using hw0)
    rw [heq] at hw
    exact (not_le_of_gt ha) hw
  exact degree_normalizedCircleMap_eq_zero_of_forall_norm_le_one (X - C a) hClosed

/-- The normalized boundary map of `X - C a` has degree one when `a` lies
strictly inside the unit disk and degree zero otherwise. Boundary nonvanishing
excludes `‖a‖ = 1`; the interior case includes `a = 0`. This is the linear-factor
calculation for May, Chapter 1, §7, Problem (1). -/
theorem degree_normalizedCircleMap_X_sub_C (a : ℂ)
    (h : ∀ z : Circle, (X - C a : ℂ[X]).eval (z : ℂ) ≠ 0) :
    Circle.degree ((X - C a : ℂ[X]).normalizedCircleMap h) =
      (if ‖a‖ < 1 then 1 else 0 : ℤ) := by
  by_cases ha : ‖a‖ < 1
  · rw [ite_eq_left ha]
    exact degree_normalizedCircleMap_X_sub_C_of_norm_lt a h ha
  · rw [ite_eq_right ha]
    have hne : ‖a‖ ≠ 1 := by
      intro heq
      exact h ⟨a, mem_sphere_zero_iff_norm.mpr heq⟩ (by simp)
    exact degree_normalizedCircleMap_X_sub_C_of_one_lt_norm a h
      (lt_of_le_of_ne (le_of_not_gt ha) hne.symm)

/-- The degree of a normalized polynomial boundary map counts the roots strictly
inside the unit disk, with their multiset multiplicities. This is May,
Chapter 1, §7, Problem (1). -/
theorem degree_normalizedCircleMap (p : ℂ[X])
    (h : ∀ z : Circle, p.eval (z : ℂ) ≠ 0) :
    Circle.degree (p.normalizedCircleMap h) =
      ((p.roots.filter (fun z => ‖z‖ < 1)).card : ℤ) := by
  classical
  refine Submonoid.closure_induction
    (motive := fun (q : ℂ[X]) _ =>
      ∀ hq : ∀ z : Circle, q.eval (z : ℂ) ≠ 0,
        Circle.degree (q.normalizedCircleMap hq) =
          ((q.roots.filter (fun z => ‖z‖ < 1)).card : ℤ))
    ?_ ?_ ?_ (IsAlgClosed.splits p) h
  · intro q hq
    rcases hq with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · intro ha
      simpa only [roots_C, Multiset.filter_zero, Multiset.card_zero, Nat.cast_zero]
        using degree_normalizedCircleMap_C a ha
    · have heq : (X + C a : ℂ[X]) = X - C (-a) := by simp
      rw [heq]
      intro ha
      rw [degree_normalizedCircleMap_X_sub_C, roots_X_sub_C, Multiset.filter_singleton]
      by_cases ha' : ‖a‖ < 1 <;> simp [ha']
  · intro h1
    simpa using degree_normalizedCircleMap_C (1 : ℂ) h1
  · intro q r _ _ ihq ihr hqr
    have hq : ∀ z : Circle, q.eval (z : ℂ) ≠ 0 := by
      intro z
      exact left_ne_zero_of_mul (by simpa only [eval_mul] using hqr z)
    have hr : ∀ z : Circle, r.eval (z : ℂ) ≠ 0 := by
      intro z
      exact right_ne_zero_of_mul (by simpa only [eval_mul] using hqr z)
    have hqr0 : q * r ≠ 0 := by
      intro hzero
      exact hqr 1 (by simp only [hzero, eval_zero])
    rw [normalizedCircleMap_mul q r hq hr, Circle.degree_mul, ihq hq, ihr hr,
      roots_mul hqr0, Multiset.filter_add, Multiset.card_add, Nat.cast_add]

end Polynomial
