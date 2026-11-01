/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import ComplexAnalysis.Analysis.InnerProductSpace.CompactOperator

/-!
# A moved vector in a finite eigenspace

The defect `U - id` selects an eigenspace containing a vector moved by `U`.
This checks the detector's intended use: an arbitrary nonzero eigenspace could
instead consist of fixed vectors. No commutation or isometry premise is needed
for this selection step.
-/

public section

universe u𝕜 uH

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- A nonzero defect on a compact operator selects a finite-dimensional eigenspace
containing a vector moved by `U`. -/
theorem ContinuousLinearMap.exists_eigenvector_comp_adjoint_moved (T U : H →L[𝕜] H)
    (hT : IsCompactOperator T)
    (hdefect : (U - ContinuousLinearMap.id 𝕜 H).comp T ≠ 0) :
    ∃ eigenvalue : 𝕜, eigenvalue ≠ 0 ∧
      FiniteDimensional 𝕜 (Module.End.eigenspace (T.comp T.adjoint).toLinearMap eigenvalue) ∧
      ∃ v : Module.End.eigenspace (T.comp T.adjoint).toLinearMap eigenvalue,
        U (v : H) ≠ (v : H) := by
  obtain ⟨eigenvalue, heigenvalue, hfinite, v, hv, hmove⟩ :=
    T.exists_eigenvector_comp_adjoint_detected
      (U - ContinuousLinearMap.id 𝕜 H) hT hdefect
  refine ⟨eigenvalue, heigenvalue, hfinite,
    ⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩, ?_⟩
  simpa only [sub_apply, ContinuousLinearMap.id_apply,
    sub_ne_zero] using hmove
