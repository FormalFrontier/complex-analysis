# Complex analysis

Lean results on complex differentiability and analyticity in finite-dimensional
normed spaces. The target may be any complete complex normed space; supporting
modules provide vector-valued Cauchy integration and analytic polydisc kernels.

## Headline results

- **Finite-dimensional differentiability implies analyticity**
  ([`DifferentiableOn.analyticOnNhd_of_finiteDimensional`](ComplexAnalysis/Analysis/Complex/FiniteDimensional.lean)).
  A complex Fréchet-differentiable map on an open subset of a finite-dimensional
  complex normed space is analytic near every point of that set, when its target
  is a complete complex normed space; dimension zero is included.
- **Differentiability–analyticity equivalence**
  ([`analyticOnNhd_iff_differentiableOn_of_finiteDimensional`](ComplexAnalysis/Analysis/Complex/FiniteDimensional.lean)).
  On such an open set, analyticity near every point is equivalent to complex
  Fréchet differentiability, under the same source and target hypotheses.
- **Polydisc Cauchy formula**
  ([`DifferentiableOn.torusIntegral_cauchy`](ComplexAnalysis/Analysis/Complex/TorusCauchy.lean)).
  A complex-differentiable map on a positive-radius closed coordinate polydisc,
  valued in a complete complex normed space, agrees at interior points with
  its normalized torus boundary integral.

## Using the library

Add it to your `lakefile.toml`:

```toml
[[require]]
name = "complexAnalysis"
git = "https://github.com/FormalFrontier/complex-analysis.git"
rev = "main"
```

The dependency revision is recorded in `lake-manifest.json`; pin a specific
release commit if you need a fixed version. Import the full API, or import the
generic integration module independently:

```lean
import ComplexAnalysis

example (f : EuclideanSpace ℂ (Fin 2) → ℂ)
    (hf : DifferentiableOn ℂ f Set.univ) : AnalyticOnNhd ℂ f Set.univ :=
  hf.analyticOnNhd_of_finiteDimensional isOpen_univ
```

## Building

The Lean toolchain is pinned in `lean-toolchain`, and Mathlib and its transitive
dependencies are pinned in `lake-manifest.json`.

```sh
lake exe cache get && lake build
```

## Contents

| Module | Contents |
| --- | --- |
| `ComplexAnalysis.Analysis.Complex.FiniteDimensional` | Open-set analyticity theorem, equivalence, and Euclidean scalar client. |
| `ComplexAnalysis.Analysis.Complex.PolydiscAnalytic` | Analyticity at the origin from the polydisc Cauchy formula. |
| `ComplexAnalysis.Analysis.Complex.PolydiscKernel` | Banach-algebra-valued Cauchy kernels and vector-valued multiplication. |
| `ComplexAnalysis.Analysis.Complex.TorusCauchy` | Iterated torus Cauchy integral formula for polydiscs. |
| `ComplexAnalysis.Analysis.Complex.TorusKernel` | Torus kernel and its scalar boundary identities. |
| `ComplexAnalysis.MeasureTheory.Integral.ContinuousMap` | Bounded Bochner integration and normalized angular-cube averaging. |

Each library module has a corresponding `ComplexAnalysisTest` module. These
clients cover nonvacuity, zero dimension, nonlinear maps on proper open sets,
vector-valued targets, and kernel evaluation.

## Conventions and limitations

The source is a finite-dimensional complex normed space and the target is a
complete complex normed space; the main statement requires an open domain.
The proof uses finite-dimensional complex coordinates, an iterated Cauchy formula
on a closed polydisc, analytic inversion in the Banach algebra of continuous
boundary functions, and bounded integration of continuous vector-valued maps.
The integration module itself applies to continuous functions on compact
measured spaces with finite Borel measure, independently of complex
differentiability. No sheaf or geometric theorem is asserted.

## References

- The classical Cauchy integral formula and its iterated polydisc form.

## Credits and license

Authors: Formal Frontier Agents. The mathematical ideas use the classical
Cauchy formula, Banach-algebra inversion, and Mathlib's analytic and integration
APIs; AI agents assisted in the Lean development and documentation. Licensed
under Apache-2.0; see `LICENSE`.
