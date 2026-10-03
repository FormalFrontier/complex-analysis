/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ComplexAnalysis.Analysis.Complex.FiniteDimensional
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Finite-dimensional complex analyticity: examples

These examples exercise an arbitrary Euclidean dimension, the empty and
zero-dimensional cases, a nonlinear map on a proper open domain, and a
non-scalar complete target. Differentiability is checked without using the
finite-dimensional analyticity implication.
-/

set_option warningAsError true

@[expose] public section

open Metric

/-- Scalar polynomials on Euclidean spaces of any finite dimension give
analytic functions on every open domain. -/
example (n : ℕ) (s : Set (EuclideanSpace ℂ (Fin n))) (hs : IsOpen s)
    (i : Fin n) : AnalyticOnNhd ℂ (fun z : EuclideanSpace ℂ (Fin n) => (z i) ^ 2) s := by
  have hcoord : Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin n) => z i) :=
    by simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable
  exact differentiableOn_analyticOnNhd_euclidean n (hcoord.pow 2).differentiableOn hs

/-- On the empty set the same theorem permits an entirely unrestricted global map. -/
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (f : E → F) : AnalyticOnNhd ℂ f ∅ := by
  have hf : DifferentiableOn ℂ f ∅ := by
    intro z hz
    exact False.elim hz
  exact hf.analyticOnNhd_of_finiteDimensional isOpen_empty

/-- Every function from a zero-dimensional complex Euclidean space is analytic. -/
example (f : EuclideanSpace ℂ (Fin 0) → ℂ) : AnalyticOnNhd ℂ f Set.univ := by
  have hf : DifferentiableOn ℂ f Set.univ := by
    have hconst : f = fun _ => f 0 := by
      funext z
      exact congrArg f (Subsingleton.elim z 0)
    rw [hconst]
    exact differentiableOn_const (E := EuclideanSpace ℂ (Fin 0)) (𝕜 := ℂ) (f 0)
  exact hf.analyticOnNhd_of_finiteDimensional isOpen_univ

/-- The square map is nonconstant and nonlinear on a proper open ball;
its differentiability does not depend on the multivariable theorem. -/
example : AnalyticOnNhd ℂ (fun z : ℂ => z ^ 2) (ball (0 : ℂ) 1) ∧
    (ball (0 : ℂ) 1 : Set ℂ) ≠ Set.univ ∧
    ∃ z ∈ ball (0 : ℂ) 1, ∃ w ∈ ball (0 : ℂ) 1,
      z + w ∈ ball (0 : ℂ) 1 ∧ (z + w) ^ 2 ≠ z ^ 2 + w ^ 2 := by
  have hf : DifferentiableOn ℂ (fun z : ℂ => z ^ 2) (ball (0 : ℂ) 1) :=
    differentiableOn_pow 2
  refine ⟨(analyticOnNhd_iff_differentiableOn_of_finiteDimensional isOpen_ball).2 hf,
    ?_, ?_⟩
  · intro h
    have hm : (2 : ℂ) ∈ ball (0 : ℂ) 1 := h.symm ▸ Set.mem_univ _
    norm_num [mem_ball] at hm
  · refine ⟨(1 / 4 : ℂ), ?_, (1 / 4 : ℂ), ?_, ?_, ?_⟩ <;> norm_num [mem_ball]

/-- Both coordinates of a genuinely vector-valued nonlinear map are complex
differentiable before the analyticity theorem is applied. -/
example : AnalyticOnNhd ℂ (fun z : EuclideanSpace ℂ (Fin 2) =>
    ((z 0) ^ 2, (z 1) ^ 3)) (ball (0 : EuclideanSpace ℂ (Fin 2)) 1) := by
  have h₀ : Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin 2) => z 0) :=
    by simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 2)).differentiable
  have h₁ : Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin 2) => z 1) :=
    by simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℂ) (1 : Fin 2)).differentiable
  exact ((h₀.pow 2).prodMk (h₁.pow 3)).differentiableOn.analyticOnNhd_of_finiteDimensional
    isOpen_ball

/-- The reverse direction recovers differentiability of an analytic map
without applying the multivariable implication. -/
example : DifferentiableOn ℂ
    (fun _ : EuclideanSpace ℂ (Fin 2) => ((3 : ℂ), (4 : ℂ)))
    (ball (0 : EuclideanSpace ℂ (Fin 2)) 1) :=
  (analyticOnNhd_iff_differentiableOn_of_finiteDimensional isOpen_ball).1
    analyticOnNhd_const

/-- For a one-variable map, Mathlib already proves the forward direction. -/
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℂ → F} {s : Set ℂ} (hs : IsOpen s) (hf : DifferentiableOn ℂ f s) :
    AnalyticOnNhd ℂ f s :=
  hf.analyticOnNhd hs

/-- On a complex line the generalized iff agrees with Mathlib's original iff. -/
example {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : ℂ → F} {s : Set ℂ} (hs : IsOpen s) :
    (analyticOnNhd_iff_differentiableOn_of_finiteDimensional (f := f) hs) =
      Complex.analyticOnNhd_iff_differentiableOn hs :=
  rfl
