/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.TorusIntegral

/-!
# The Cauchy integral formula on a polydisc

The torus integral of the product Cauchy kernel recovers a complex-differentiable
map on a closed polydisc, with values in an arbitrary complete complex normed space.
The formula follows by induction from the one-variable Cauchy formula.
-/

@[expose] public section

open Complex Set MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℂ F]

private theorem torusIntegrable_cauchy {n : ℕ} {f : (Fin n → ℂ) → F}
    {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : ContinuousOn f {w | ∀ i, w i ∈ Metric.closedBall (c i) (R i)})
    (hz : ∀ i, z i ∈ Metric.ball (c i) (R i)) :
    TorusIntegrable (fun w => (∏ i, (w i - z i)⁻¹) • f w) c R := by
  have hR (i : Fin n) : 0 < R i :=
    lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp (hz i))
  have hsphere (θ : Fin n → ℝ) (i : Fin n) :
      torusMap c R θ i ∈ Metric.sphere (c i) (R i) :=
    circleMap_mem_sphere (c i) (hR i).le (θ i)
  have hne (θ : Fin n → ℝ) (i : Fin n) : torusMap c R θ i - z i ≠ 0 := by
    intro heq
    have heq' := sub_eq_zero.mp heq
    have hd := Metric.mem_sphere.mp (hsphere θ i)
    rw [heq'] at hd
    exact (ne_of_lt (Metric.mem_ball.mp (hz i))) hd
  have hmap : Continuous (torusMap c R) := by
    unfold torusMap
    fun_prop
  have hfc : Continuous (fun θ => f (torusMap c R θ)) :=
    hf.comp_continuous hmap (fun θ i => Metric.sphere_subset_closedBall (hsphere θ i))
  have hk (i : Fin n) : Continuous (fun θ : Fin n → ℝ =>
      (torusMap c R θ i - z i)⁻¹) :=
    ((continuous_apply i).comp hmap |>.sub continuous_const).inv₀ (fun θ => hne θ i)
  unfold TorusIntegrable
  apply Continuous.integrableOn_Icc
  exact (by fun_prop : Continuous (fun θ : Fin n → ℝ =>
    ∏ i, (torusMap c R θ i - z i)⁻¹)).smul hfc

private theorem differentiableOn_polydisc_head {n : ℕ}
    {f : (Fin (n + 1) → ℂ) → F} {c : Fin (n + 1) → ℂ} {R : Fin (n + 1) → ℝ}
    (hf : DifferentiableOn ℂ f {w | ∀ i, w i ∈ Metric.closedBall (c i) (R i)})
    {y : Fin n → ℂ} (hy : ∀ i, y i ∈ Metric.closedBall (c i.succ) (R i.succ)) :
    DifferentiableOn ℂ (fun x : ℂ => f (Fin.cons x y))
      (Metric.closedBall (c 0) (R 0)) := by
  apply hf.fun_comp
    (differentiable_id.finCons (differentiable_const y)).differentiableOn
  intro x hx i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa using hy j

private theorem differentiableOn_polydisc_tail {n : ℕ}
    {f : (Fin (n + 1) → ℂ) → F} {c : Fin (n + 1) → ℂ} {R : Fin (n + 1) → ℝ}
    (hf : DifferentiableOn ℂ f {w | ∀ i, w i ∈ Metric.closedBall (c i) (R i)})
    {x : ℂ} (hx : x ∈ Metric.closedBall (c 0) (R 0)) :
    DifferentiableOn ℂ (fun y : Fin n → ℂ => f (Fin.cons x y))
      {y | ∀ i, y i ∈ Metric.closedBall (c i.succ) (R i.succ)} := by
  apply hf.fun_comp ((differentiable_const x).finCons differentiable_id).differentiableOn
  intro y hy i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hx
  · simpa using hy j

/-- The product Cauchy kernel recovers a map from its integral over the boundary
torus of a closed polydisc. The target need not be finite-dimensional. -/
theorem DifferentiableOn.torusIntegral_cauchy [CompleteSpace F] {n : ℕ}
    {f : (Fin n → ℂ) → F} {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : DifferentiableOn ℂ f {w | ∀ i, w i ∈ Metric.closedBall (c i) (R i)})
    (hz : ∀ i, z i ∈ Metric.ball (c i) (R i)) :
    (∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w) =
      (2 * (Real.pi : ℂ) * I) ^ n • f z := by
  induction n with
  | zero =>
    rw [torusIntegral_dim0]
    simpa using congrArg f (Subsingleton.elim c z)
  | succ n ih =>
    let C : ℂ := 2 * (Real.pi : ℂ) * I
    have hR : 0 < R 0 := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp (hz 0))
    have hcons : Fin.cons (z 0) (z ∘ Fin.succ) = z := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hslice : DifferentiableOn ℂ (fun x : ℂ => f (Fin.cons x (z ∘ Fin.succ)))
        (Metric.closedBall (c 0) (R 0)) :=
      differentiableOn_polydisc_head hf (fun i => Metric.ball_subset_closedBall (hz i.succ))
    have hti : TorusIntegrable (fun w => (∏ i, (w i - z i)⁻¹) • f w) c R :=
      torusIntegrable_cauchy (c := c) (z := z) (R := R) hf.continuousOn hz
    rw [torusIntegral_succ (n := n) (E := F) (c := c) (R := R) hti]
    calc
      _ = ∮ x in C(c 0, R 0), C ^ n • ((x - z 0)⁻¹ • f (Fin.cons x (z ∘ Fin.succ))) := by
        apply circleIntegral.integral_congr hR.le
        intro x hx
        dsimp only
        have hfx : DifferentiableOn ℂ (fun y : Fin n → ℂ => f (Fin.cons x y))
            {y | ∀ i, y i ∈ Metric.closedBall (c i.succ) (R i.succ)} :=
          differentiableOn_polydisc_tail hf (Metric.sphere_subset_closedBall hx)
        have heq : (fun y : Fin n → ℂ =>
            (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y)) =
            (fun y => (x - z 0)⁻¹ •
              ((∏ i, (y i - z i.succ)⁻¹) • f (Fin.cons x y))) := by
          funext y
          simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_smul]
        rw [heq, torusIntegral_smul]
        simp only [Function.comp_def]
        rw [ih hfx (fun i => hz i.succ)]
        exact smul_comm _ _ _
      _ = C ^ n • (C • f (Fin.cons (z 0) (z ∘ Fin.succ))) := by
        rw [circleIntegral.integral_smul, hslice.circleIntegral_sub_inv_smul (hz 0)]
      _ = (2 * (Real.pi : ℂ) * I) ^ (n + 1) • f z := by
        rw [hcons, smul_smul, ← pow_succ]
