/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.MeasureTheory.Integral.ContinuousMap
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Continuous fields of operators and scalar integral kernels

An operator-norm-continuous field `φ : C(X, E →L[𝕜] F)` transposes to a continuous
linear map `E →L[𝕜] C(X, F)`. Here the space of continuous functions has the
compact-open topology, and `X` need not be compact or locally compact. A proper
normed target makes the transpose compact by the Arzelà–Ascoli theorem. Only the
operator-norm assertions require compact `X`.

For a finite Borel measure on compact `Y`, a continuous complex scalar kernel
on `X × Y` gives a compact operator `L²(Y, μ) →L[ℂ] C(X, ℂ)`. Conjugation of the
kernel section before the `L²` inner product makes its value the integral of
`κ (x, y) * u y`, without conjugating `κ` in that formula.

## Implementation notes

The kernel construction uses the stock finite-Borel continuous-function
embedding into `L²`. It imposes no measure or compactness on `X`, nor positivity,
full support, regularity, or countability on the measure space.

## References

The compactness argument uses Mathlib's compact-open Arzelà–Ascoli theorem.
The scalar-kernel application follows the compact-kernel argument in the
exposition *Pontryagin bidual reflexivity* by Formal Frontier Agents, §§1–2 and
9.1, in the context of Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
corrected second edition, electronic version 2.3, Definition (1.1.10) and
Theorem (1.1.11). No character-separation theorem is used here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology

universe u𝕜 uX uY uE uF

namespace ContinuousMap

section FieldTranspose

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {X : Type uX} [TopologicalSpace X]
variable {E : Type uE} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Transpose an operator-norm-continuous field by evaluation, with compact-open codomain. -/
def flipLinear (φ : C(X, E →L[𝕜] F)) : E →L[𝕜] C(X, F) where
  toFun v :=
    { toFun := fun x => φ x v
      continuous_toFun := (ContinuousLinearMap.apply 𝕜 F v).continuous.comp φ.continuous }
  map_add' v w := by
    ext x
    exact (φ x).map_add v w
  map_smul' a v := by
    ext x
    exact (φ x).map_smul a v
  cont := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (ContinuousLinearMap.apply 𝕜 F).continuous₂.comp₂ continuous_fst
      (φ.continuous.comp continuous_snd)

@[simp]
theorem flipLinear_apply (φ : C(X, E →L[𝕜] F)) (v : E) (x : X) :
    φ.flipLinear v x = φ x v := rfl

@[simp]
theorem evalCLM_comp_flipLinear (φ : C(X, E →L[𝕜] F)) (x : X) :
    (ContinuousMap.evalCLM (R := 𝕜) x).comp φ.flipLinear = φ x := by
  ext v
  rfl

@[simp]
theorem flipLinear_zero : (0 : C(X, E →L[𝕜] F)).flipLinear = 0 := by
  ext v x
  rfl

@[simp]
theorem flipLinear_add (φ ψ : C(X, E →L[𝕜] F)) :
    (φ + ψ).flipLinear = φ.flipLinear + ψ.flipLinear := by
  ext v x
  rfl

@[simp]
theorem flipLinear_smul (a : 𝕜) (φ : C(X, E →L[𝕜] F)) :
    (a • φ).flipLinear = a • φ.flipLinear := by
  ext v x
  rfl

variable [CompactSpace X]

/-- Transposition does not increase the sup operator norm on a compact parameter space. -/
theorem norm_flipLinear_le (φ : C(X, E →L[𝕜] F)) : ‖φ.flipLinear‖ ≤ ‖φ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound φ.flipLinear (M := ‖φ‖) (norm_nonneg φ)
  intro v
  apply ((φ.flipLinear v).norm_le (mul_nonneg (norm_nonneg φ) (norm_nonneg v))).2
  intro x
  exact ((φ x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg v))

/-- Transposition preserves the sup operator norm on a compact parameter space. -/
theorem norm_flipLinear (φ : C(X, E →L[𝕜] F)) : ‖φ.flipLinear‖ = ‖φ‖ := by
  refine le_antisymm (norm_flipLinear_le φ) ?_
  apply (φ.norm_le (norm_nonneg _)).2
  intro x
  apply (φ x).opNorm_le_bound (norm_nonneg _)
  intro v
  exact ((φ.flipLinear v).norm_coe_le_norm x).trans (φ.flipLinear.le_opNorm v)

end FieldTranspose

section CompactFieldTranspose

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {X : Type uX} [TopologicalSpace X]
variable {E : Type uE} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [ProperSpace F]

/-- A continuous field with proper normed target has compact transpose, for arbitrary `X`.

The proof applies the compact-open Arzelà–Ascoli theorem to the pointwise closure
of the image of the closed unit ball. -/
theorem isCompactOperator_flipLinear
    (φ : C(X, E →L[𝕜] F)) : IsCompactOperator φ.flipLinear := by
  let A : Set (X → F) :=
    (fun v : E => fun x : X => φ x v) '' Metric.closedBall (0 : E) 1
  have hAeq : A.Equicontinuous := by
    intro x
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    filter_upwards [(φ.continuous.tendsto x).eventually
      (Metric.ball_mem_nhds (φ x) hε)] with y hy
    rintro ⟨f, hf⟩
    rcases hf with ⟨v, hv, rfl⟩
    have hv1 : ‖v‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    calc
      dist (φ x v) (φ y v) = ‖(φ x - φ y) v‖ := by
        rw [dist_eq_norm]
        rfl
      _ ≤ ‖φ x - φ y‖ * 1 := (φ x - φ y).le_opNorm_of_le hv1
      _ = dist (φ x) (φ y) := by rw [mul_one, dist_eq_norm]
      _ < ε := by simpa only [Metric.mem_ball, dist_comm] using hy
  let P : Set (X → F) :=
    {f | ∀ x, f x ∈ Metric.closedBall (0 : F) ‖φ x‖}
  have hP : IsCompact P :=
    isCompact_pi_infinite (fun x => isCompact_closedBall (0 : F) ‖φ x‖)
  have hAP : A ⊆ P := by
    rintro f ⟨v, hv, rfl⟩
    intro x
    have hv1 : ‖v‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    simpa only [Metric.mem_closedBall, dist_zero_right, mul_one] using
      (φ x).le_opNorm_of_le hv1
  have hK : IsCompact (closure A) :=
    hP.of_isClosed_subset isClosed_closure (closure_minimal hAP hP.isClosed)
  have hKeq : (closure A).Equicontinuous := hAeq.closure
  let S : Set C(X, F) := {f | (f : X → F) ∈ closure A}
  have hSK : ContinuousMap.toFun '' S = closure A := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hKeq.continuous_of_mem hf⟩, hf, rfl⟩
  have hS : IsCompact S := by
    apply ArzelaAscoli.isCompact_of_equicontinuous S
    · rw [hSK]
      exact hK
    · exact hKeq.comp
        (fun g : S => (⟨(g.1 : X → F), g.2⟩ : closure A))
  refine ⟨S, hS, Filter.mem_of_superset
    (Metric.closedBall_mem_nhds (0 : E)
      (show (0 : ℝ) < 1 from zero_lt_one)) ?_⟩
  intro v hv
  change (φ.flipLinear v : X → F) ∈ closure A
  apply subset_closure
  refine ⟨v, hv, ?_⟩
  funext x
  simp only [ContinuousMap.flipLinear_apply]

end CompactFieldTranspose

section ScalarKernel

variable {X : Type uX} [TopologicalSpace X]
variable {Y : Type uY} [TopologicalSpace Y] [CompactSpace Y]
variable [MeasurableSpace Y] [BorelSpace Y]

local instance : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The field of functionals associated to the conjugated kernel sections. -/
private noncomputable def kernelFunctional (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) : C(X, Lp ℂ (2 : ℝ≥0∞) μ →L[ℂ] ℂ) where
  toFun x := innerSL ℂ
    (ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (star (κ.curry x)))
  continuous_toFun := (innerSL ℂ).continuous.comp
    ((ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ).continuous.comp
      κ.curry.continuous.star)

/-- Integrate a continuous complex scalar kernel against an `L²` input. -/
noncomputable def kernelOperator (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) : Lp ℂ (2 : ℝ≥0∞) μ →L[ℂ] C(X, ℂ) :=
  ({ toFun := fun x => innerSL ℂ
       (ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (star (κ.curry x)))
     continuous_toFun := (innerSL ℂ).continuous.comp
       ((ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ).continuous.comp
         κ.curry.continuous.star) } : C(X, Lp ℂ (2 : ℝ≥0∞) μ →L[ℂ] ℂ)).flipLinear

/-- Evaluation of a scalar-kernel operator as the `L²` inner product with its
conjugate kernel section. -/
theorem kernelOperator_apply_eq_inner (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) (u : Lp ℂ (2 : ℝ≥0∞) μ) (x : X) :
    kernelOperator μ κ u x =
      inner ℂ (ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (star (κ.curry x))) u := rfl

private theorem kernelOperator_eq_flipLinear (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) :
    kernelOperator μ κ = (kernelFunctional μ κ).flipLinear := rfl

private theorem kernel_inner_ae (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) (u : Lp ℂ (2 : ℝ≥0∞) μ) (x : X) :
    (fun y => inner ℂ
      (ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (star (κ.curry x)) y) (u y))
      =ᵐ[μ] (fun y => κ (x, y) * u y) := by
  filter_upwards
    [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ (star (κ.curry x))] with y hy
  simp only [ContinuousMap.coe_toLp] at hy ⊢
  rw [hy]
  simp [mul_comm]

private theorem integrable_kernel_mul (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) (u : Lp ℂ (2 : ℝ≥0∞) μ) (x : X) :
    Integrable (fun y => κ (x, y) * u y) μ :=
  (L2.integrable_inner (𝕜 := ℂ)
    (ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (star (κ.curry x))) u).congr
      (kernel_inner_ae μ κ u x)

/-- The kernel operator integrates the kernel itself, not its complex conjugate. -/
@[simp]
theorem kernelOperator_apply (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) (u : Lp ℂ (2 : ℝ≥0∞) μ) (x : X) :
    kernelOperator μ κ u x = ∫ y, κ (x, y) * u y ∂μ := by
  rw [kernelOperator_eq_flipLinear, flipLinear_apply]
  change innerSL ℂ
    (ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (star (κ.curry x))) u = _
  rw [innerSL_apply_apply, L2.inner_def]
  exact integral_congr_ae (kernel_inner_ae μ κ u x)

@[simp]
theorem kernelOperator_zero (μ : Measure Y) [IsFiniteMeasure μ] :
    kernelOperator μ (0 : C(X × Y, ℂ)) = 0 := by
  ext u x
  simp

@[simp]
theorem kernelOperator_add (μ : Measure Y) [IsFiniteMeasure μ]
    (κ η : C(X × Y, ℂ)) :
    kernelOperator μ (κ + η) = kernelOperator μ κ + kernelOperator μ η := by
  ext u x
  simp only [_root_.add_apply, ContinuousMap.add_apply, kernelOperator_apply,
    add_mul]
  exact integral_add (integrable_kernel_mul μ κ u x) (integrable_kernel_mul μ η u x)

@[simp]
theorem kernelOperator_smul (μ : Measure Y) [IsFiniteMeasure μ]
    (a : ℂ) (κ : C(X × Y, ℂ)) :
    kernelOperator μ (a • κ) = a • kernelOperator μ κ := by
  ext u x
  simp only [_root_.smul_apply, ContinuousMap.smul_apply, kernelOperator_apply,
    smul_eq_mul, mul_assoc, integral_const_mul]

/-- On continuous inputs the kernel operator agrees with continuous-map integration. -/
theorem kernelOperator_toLp_apply (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) (f : C(Y, ℂ)) (x : X) :
    kernelOperator μ κ (ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ f) x =
      integralCLM μ (κ.curry x * f) := by
  rw [kernelOperator_apply, integralCLM_apply]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ f] with y hy
  simp only [ContinuousMap.coe_toLp] at hy ⊢
  rw [hy]
  rfl

/-- A continuous scalar kernel gives a compact operator into the compact-open function space. -/
theorem isCompactOperator_kernelOperator (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) : IsCompactOperator (kernelOperator μ κ) := by
  rw [kernelOperator_eq_flipLinear]
  exact isCompactOperator_flipLinear (kernelFunctional μ κ)

variable [CompactSpace X]

/-- The scalar-kernel operator is bounded by the sup norm times the square root of the mass. -/
theorem norm_kernelOperator_le (μ : Measure Y) [IsFiniteMeasure μ]
    (κ : C(X × Y, ℂ)) :
    ‖kernelOperator μ κ‖ ≤ Real.sqrt (μ.real univ) * ‖κ‖ := by
  rw [kernelOperator_eq_flipLinear]
  have hLp : ‖(ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ)‖ ≤
      Real.sqrt (μ.real univ) := by
    have h := ContinuousMap.toLp_norm_le (E := ℂ) (p := (2 : ℝ≥0∞)) (𝕜 := ℂ) μ
    rw [ENNReal.toReal_ofNat] at h
    simpa only [Real.sqrt_eq_rpow, measureUnivNNReal, Measure.real, ENNReal.toReal,
      one_div] using h
  refine (norm_flipLinear_le (kernelFunctional μ κ)).trans ?_
  apply ((kernelFunctional μ κ).norm_le
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg κ))).2
  intro x
  change ‖innerSL ℂ
    (ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ (star (κ.curry x)))‖ ≤ _
  rw [innerSL_apply_norm]
  calc
    ‖ContinuousMap.toLp (2 : ℝ≥0∞) μ ℂ (star (κ.curry x))‖ ≤
        ‖(ContinuousMap.toLp (E := ℂ) (2 : ℝ≥0∞) μ ℂ)‖ * ‖star (κ.curry x)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.sqrt (μ.real univ) * ‖κ.curry x‖ := by
      rw [norm_star]
      exact mul_le_mul_of_nonneg_right hLp (norm_nonneg _)
    _ ≤ Real.sqrt (μ.real univ) * ‖κ‖ := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply ((κ.curry x).norm_le (norm_nonneg κ)).2
      intro y
      exact κ.norm_coe_le_norm (x, y)

end ScalarKernel

end ContinuousMap
