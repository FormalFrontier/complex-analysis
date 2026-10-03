/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.PiL2
import ComplexAnalysis.Analysis.Complex.PolydiscAnalytic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Analyticity of complex-differentiable maps in finite dimension

Complex Fréchet differentiability on an open subset of a finite-dimensional complex
normed space gives a convergent local multilinear power series for the original map
into any complete complex normed space. The forward implication follows from the
Cauchy formula on a polydisc; the reverse implication is available in Mathlib.

The existing one-variable theorem `DifferentiableOn.analyticOnNhd` has source `ℂ`.
The source here is any finite-dimensional complex normed space; the target is not
required to be finite-dimensional.
-/

set_option warningAsError true

@[expose] public section

universe u v

private theorem exists_closed_polydisc
    {n : ℕ} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : (Fin n → ℂ) →L[ℂ] E) {s : Set E} (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    ∃ R : ℝ, 0 < R ∧ ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ ≤ R) → x + T z ∈ s := by
  have hcont : Continuous (fun z : Fin n → ℂ => x + T z) :=
    continuous_const.add T.continuous
  have hopen : IsOpen {z : Fin n → ℂ | x + T z ∈ s} := hs.preimage hcont
  have hzero : (0 : Fin n → ℂ) ∈ {z : Fin n → ℂ | x + T z ∈ s} := by
    simpa using hx
  obtain ⟨r, hr, hball⟩ := (Metric.isOpen_iff.mp hopen) 0 hzero
  refine ⟨r / 2, by positivity, ?_⟩
  intro z hcoord
  apply hball
  have hz : ‖z‖ ≤ r / 2 := (pi_norm_le_iff_of_nonneg (by positivity)).2 hcoord
  simpa only [Metric.mem_ball, dist_zero_right] using lt_of_le_of_lt hz (half_lt_self hr)

/-- A complex Fréchet-differentiable map on an open set in a finite-dimensional
complex normed space is analytic near every point of the set. -/
theorem DifferentiableOn.analyticOnNhd_of_finiteDimensional
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {s : Set E} {f : E → F}
    (hf : DifferentiableOn ℂ f s) (hs : IsOpen s) : AnalyticOnNhd ℂ f s := by
  intro x hx
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    (ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ)).symm
  obtain ⟨R, hR, hbox⟩ := exists_closed_polydisc e.symm.toContinuousLinearMap hs hx
  have htrans : Differentiable ℂ (fun z : Fin (Module.finrank ℂ E) → ℂ =>
      x + e.symm z) := by
    simpa only [add_comm] using e.symm.differentiable.add_const x
  have hcoord : DifferentiableOn ℂ
      (fun z : Fin (Module.finrank ℂ E) → ℂ => f (x + e.symm z))
      {z | ∀ i, ‖z i‖ ≤ R} :=
    hf.fun_comp htrans.differentiableOn (fun z hz => hbox z hz)
  have hlocal : AnalyticAt ℂ
      (fun z : Fin (Module.finrank ℂ E) → ℂ => f (x + e.symm z)) 0 := by
    exact hcoord.analyticAt_zero_of_polydisc hR
  have hback : AnalyticAt ℂ (fun y : E => f (x + y)) 0 := by
    have hlocal₀ : AnalyticAt ℂ
        (fun z : Fin (Module.finrank ℂ E) → ℂ => f (x + e.symm z)) (e (0 : E)) := by
      simpa using hlocal
    simpa [Function.comp_def] using
      hlocal₀.compContinuousLinearMap (u := e.toContinuousLinearMap)
  have htranslate : AnalyticAt ℂ (fun y : E => y - x) x :=
    analyticAt_id.sub analyticAt_const
  have houter : AnalyticAt ℂ (fun y : E => f (x + y)) ((fun y : E => y - x) x) := by
    simpa using hback
  have heq : (fun y : E => f (x + (y - x))) = f := by
    funext y
    congr 1
    abel
  simpa only [Function.comp_def, heq] using
    houter.comp (f := fun y : E => y - x) htranslate

/-- On an open subset of a finite-dimensional complex normed space,
analyticity is equivalent to complex Fréchet differentiability. -/
theorem analyticOnNhd_iff_differentiableOn_of_finiteDimensional
    {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] {s : Set E} {f : E → F} (hs : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, fun hf => hf.analyticOnNhd_of_finiteDimensional hs⟩

/-- The scalar-valued specialization for an arbitrary finite Euclidean dimension,
including dimension zero. -/
theorem differentiableOn_analyticOnNhd_euclidean
    (n : ℕ) {s : Set (EuclideanSpace ℂ (Fin n))}
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hf : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : AnalyticOnNhd ℂ f s :=
  hf.analyticOnNhd_of_finiteDimensional hs
