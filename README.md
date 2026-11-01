# Complex analysis

Lean results on complex differentiability and analyticity in finite-dimensional
normed spaces. The target may be any complete complex normed space; supporting
modules provide vector-valued Cauchy integration and analytic polydisc kernels.
The library also constructs normalized boundary maps of complex polynomials.

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
- **Polynomial boundary degree counts interior roots**
  ([`Polynomial.degree_normalizedCircleMap`](ComplexAnalysis/Analysis/Complex/PolynomialBoundary.lean)).
  A complex polynomial with no zeros on the unit circle gives an unbased continuous
  circle self-map by normalizing its values. Its degree equals the number of roots
  strictly inside the unit disk, counted with multiset multiplicity. Nonmonic
  polynomials, repeated roots and nonzero constants of arbitrary phase are included.

- **Exterior polynomial root-scaling homotopy**
  ([`Polynomial.normalizedCircleMapScaleRootsHomotopy`](ComplexAnalysis/Analysis/Complex/PolynomialExterior.lean)).
  If `p.eval w ≠ 0` whenever `1 ≤ ‖w‖`, root scaling over the real unit interval
  joins the normalized leading monomial to the canonical normalized boundary map.
  Its characteristic value is `normalize ((p.scaleRoots (t : ℂ)).eval z)`.
  The leading coefficient's arbitrary phase is retained; the corresponding degree
  statement is `Circle.degree (p.normalizedCircleMap _) = (p.natDegree : ℤ)`.

- **Compact scalar-kernel operators**
  ([`ContinuousMap.kernelOperator`](ComplexAnalysis/MeasureTheory/Integral/Kernel.lean)).
  A continuous scalar kernel on `X × Y`, with compact `Y` and a finite Borel
  measure, gives a compact complex-linear map from `L²(Y, μ)` to `C(X, ℂ)`.
  The parameter space `X` is arbitrary; compactness of `X` is needed only for
  the sup-norm bound. The construction uses a generic transpose of an
  operator-norm-continuous field, compact whenever its normed target is proper.

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

The Lean toolchain is pinned in `lean-toolchain`; Mathlib, Sphere Topology,
Polynomial Root Stability and all other dependencies are pinned in `lake-manifest.json`.

```sh
lake exe cache get && lake build
```

## Contents

| Module | Contents |
| --- | --- |
| `ComplexAnalysis.Analysis.Complex.FiniteDimensional` | Open-set analyticity theorem, equivalence, and Euclidean scalar client. |
| `ComplexAnalysis.Analysis.Complex.PolydiscAnalytic` | Analyticity at the origin from the polydisc Cauchy formula. |
| `ComplexAnalysis.Analysis.Complex.PolydiscKernel` | Banach-algebra-valued Cauchy kernels and vector-valued multiplication. |
| `ComplexAnalysis.Analysis.Complex.PolynomialBoundary` | Normalized polynomial boundary maps, constant and linear-factor degrees, and the interior-root multiplicity formula. |
| `ComplexAnalysis.Analysis.Complex.PolynomialExterior` | Exterior root-scaling homotopy and boundary degree, retaining the leading phase and including nonzero constants. |
| `ComplexAnalysis.Analysis.Complex.TorusCauchy` | Iterated torus Cauchy integral formula for polydiscs. |
| `ComplexAnalysis.Analysis.Complex.TorusKernel` | Torus kernel and its scalar boundary identities. |
| `ComplexAnalysis.MeasureTheory.Integral.ContinuousMap` | Bounded Bochner integration and normalized angular-cube averaging. |
| `ComplexAnalysis.MeasureTheory.Integral.Kernel` | Continuous fields of operators, compact transposes, and finite-measure scalar kernels. |

The `ComplexAnalysisTest` clients cover nonvacuity, zero dimension, nonlinear
maps on proper open sets, vector-valued targets, and kernel evaluation.

## Conventions and limitations

For the analyticity results, the source is a finite-dimensional complex normed
space and the target is a complete complex normed space; the domain is open.
The proof uses finite-dimensional complex coordinates, an iterated Cauchy formula
on a closed polydisc, analytic inversion in the Banach algebra of continuous
boundary functions, and bounded integration of continuous vector-valued maps.
The integration module itself applies to continuous functions on compact
measured spaces with finite Borel measure, independently of complex
differentiability. No sheaf or geometric theorem is asserted.

The interior-root multiplicity formula uses Mathlib's existing algebraic
closedness of `ℂ` (the fundamental theorem of algebra), its split-polynomial
induction and root multisets, and Sphere Topology's additivity of circle degree
under pointwise multiplication. Polynomials nonvanishing on the closed unit disk
also carry an explicit disk-scaling homotopy from their constant phase at zero
to their normalized boundary map; consequently this boundary map has degree zero.
The exterior root-scaling family is distinct: its degree route uses the leading
phase, products, powers and homotopy invariance, not the root-count formula.
No new fundamental theorem of algebra is asserted.

## References

- The classical Cauchy integral formula and its iterated polydisc form.
- J. Peter May, *A Concise Course in Algebraic Topology*, Chapter 1, §7,
  proof of the fundamental theorem of algebra, pp. 10–11, for root scaling;
  Problem (1), p. 11, for polynomial boundary degree and root multiplicity.

## Credits and license

Authors: Formal Frontier Agents. The mathematical ideas use the classical
Cauchy formula, Banach-algebra inversion, May's exterior root-scaling argument
and polynomial boundary-degree problem,
Mathlib's analytic, polynomial (including the fundamental theorem of algebra) and
integration APIs, Sphere Topology's normalization and circle-degree APIs, and
Polynomial Root Stability's continuity and nonvanishing API for root scaling;
AI agents assisted in the Lean development and documentation.
Licensed under Apache-2.0; see `LICENSE`.
