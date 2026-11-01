/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Detecting eigenspaces of compact positive squares

For a compact operator `T` on a complete real or complex Hilbert space, a
continuous linear map `B` which is nonzero on the range of `T` detects a vector
in a nonzero, finite-dimensional eigenspace of `T.comp T.adjoint`.

The proof uses Mathlib's compact self-adjoint spectral theorem: all eigenspaces,
including the kernel, have dense span. No separability, ambient finite dimension,
normality of `T`, or commutation hypothesis on `B` is needed. The zero-product
identity is valid without compactness.

## References

The compact self-adjoint spectral theorem and adjoint identities are provided by
Mathlib's `Analysis.InnerProductSpace.Spectrum` and
`Analysis.InnerProductSpace.Adjoint`.
-/

@[expose] public section

namespace ContinuousLinearMap

universe u𝕜 uH

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [CompleteSpace H]

/-- A continuous linear map annihilates `T T*` exactly when it annihilates `T`.
There is no commutation hypothesis on the two operators. -/
theorem comp_comp_adjoint_eq_zero_iff (B T : H →L[𝕜] H) :
    B.comp (T.comp T.adjoint) = 0 ↔ B.comp T = 0 := by
  constructor
  · intro h
    have hprod : (B.comp T).comp (B.comp T).adjoint = 0 := by
      rw [adjoint_comp]
      calc
        (B.comp T).comp (T.adjoint.comp B.adjoint) =
            (B.comp (T.comp T.adjoint)).comp B.adjoint := by
          ext v
          rfl
        _ = 0 := by rw [h]; rfl
    have hzero : (B.comp T).adjoint = 0 :=
      adjoint_comp_self_eq_zero_iff.mp (by
        simpa only [adjoint_adjoint] using hprod)
    apply adjoint.injective
    simpa using hzero
  · intro h
    calc
      B.comp (T.comp T.adjoint) = (B.comp T).comp T.adjoint := by
        ext v
        rfl
      _ = 0 := by rw [h]; rfl

/-- A nonzero defect on the range of a compact operator is detected on a
nonzero finite-dimensional eigenspace of its positive square. The eigenspace
has the submodule structure inherited from the original Hilbert space. -/
theorem exists_eigenvector_comp_adjoint_detected (T B : H →L[𝕜] H)
    (hT : IsCompactOperator T) (hBT : B.comp T ≠ 0) :
    ∃ eigenvalue : 𝕜, eigenvalue ≠ 0 ∧
      FiniteDimensional 𝕜 (Module.End.eigenspace (T.comp T.adjoint).toLinearMap eigenvalue) ∧
      ∃ v : H, (T.comp T.adjoint) v = eigenvalue • v ∧ B v ≠ 0 := by
  classical
  let S : H →L[𝕜] H := T.comp T.adjoint
  have hcompact : IsCompactOperator S := hT.comp_clm T.adjoint
  have hself : IsSelfAdjoint S := by
    apply isSelfAdjoint_iff'.mpr
    simp only [S, adjoint_comp, adjoint_adjoint]
  have hsymm : S.IsSymmetric := isSelfAdjoint_iff_isSymmetric.mp hself
  suffices hex : ∃ eigenvalue : 𝕜, eigenvalue ≠ 0 ∧
      ∃ v : H, S v = eigenvalue • v ∧ B v ≠ 0 by
    obtain ⟨eigenvalue, heigenvalue, v, hv, hBv⟩ := hex
    exact ⟨eigenvalue, heigenvalue,
      ContinuousLinearMap.finite_dimensional_eigenspace hcompact eigenvalue heigenvalue,
      v, hv, hBv⟩
  by_contra! h
  -- On the zero eigenspace `S` vanishes; on every other one `B` vanishes.
  have heigen (eigenvalue : 𝕜) (v : H)
      (hv : v ∈ Module.End.eigenspace S.toLinearMap eigenvalue) : (B.comp S) v = 0 := by
    have hv' : S v = eigenvalue • v := Module.End.mem_eigenspace_iff.mp hv
    by_cases heigenvalue : eigenvalue = 0
    · simp [ContinuousLinearMap.comp_apply, hv', heigenvalue]
    · simp [ContinuousLinearMap.comp_apply, hv', h eigenvalue heigenvalue v hv']
  let K : Submodule 𝕜 H :=
    ⨆ eigenvalue : 𝕜, Module.End.eigenspace S.toLinearMap eigenvalue
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    have horth : Kᗮ = ⊥ :=
      orthogonalComplement_iSup_eigenspaces_eq_bot hcompact hsymm
    rw [horth]
    simp
  have hspan : ∀ v ∈ K, (B.comp S) v = 0 := by
    intro v hv
    exact Submodule.iSup_induction
      (fun eigenvalue : 𝕜 => Module.End.eigenspace S.toLinearMap eigenvalue)
      (motive := fun z : H => (B.comp S) z = 0) hv heigen
      (map_zero (B.comp S))
      (fun x y hx hy => by
        calc
          (B.comp S) (x + y) = (B.comp S) x + (B.comp S) y :=
            map_add (B.comp S) x y
          _ = 0 := by rw [hx, hy, add_zero])
  -- Continuity extends vanishing from the spectral span to its closure.
  have hzero : B.comp S = 0 := by
    ext v
    have hv : v ∈ closure (K : Set H) := by
      rw [← Submodule.topologicalClosure_coe, hclosure]
      trivial
    exact closure_minimal hspan
      (isClosed_singleton.preimage (B.comp S).continuous) hv
  exact hBT ((comp_comp_adjoint_eq_zero_iff B T).mp hzero)

end ContinuousLinearMap
