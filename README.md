<p align="center">
  <img src="logo.svg" alt="Problib" width="200" />
</p>

# Problib v26.9.3

`problib` is a Lean 4 library of the probability theory needed to give
probabilistic programming languages precise meaning, and to prove facts about
their programs.

It contains foundational theory of the real numbers, measures and integrals, probability kernels,
conditioning, and the conditions under which Monte Carlo inference is correct.

Every theorem in the library rests on Lean's three standard axioms (`propext`, `Quot.sound`,
and `Classical.choice`), and the library builds all requisite statements without
Mathlib (mostly, for speed of compilation: we sync and take content 
from Mathlib where required, with proper license attribution).

## Contents

problib is constructed in layers that build on each other:

- **Real numbers:** [Problib/Real.lean](Problib/Real.lean) constructs the reals
  as Dedekind cuts and proves them a complete ordered field. The nonnegative
  extended reals (`ENNReal`, with a point at infinity) support sums that commute
  with monotone suprema.
- **Measure and integration:** [Problib/Measure.lean](Problib/Measure.lean)
  builds Carathéodory outer measures from countable covers, and the Borel sets
  of the reals from half-open intervals. The nonnegative Lebesgue integral comes
  with monotone convergence, Fatou's lemma, and change of density. The layer
  also holds the Giry monad, whose `bind` feeds each outcome of a measure
  through a kernel.
- **Calculus:** [Problib/Analysis.lean](Problib/Analysis.lean) builds the
  logarithm, exponential, and square root on the reals, with derivatives, the
  rules of calculus, and differentiation under the integral sign. It evaluates
  Gaussian integrals and moments. Multivariate power series converge uniformly
  on smaller boxes and can be differentiated term by term. A map that splits its
  domain into countably many analytic pieces, with an analytic function on each,
  is _piecewise analytic under an analytic partition_ (PAP). Such maps are
  measurable, and composition, pairing, restriction, and countable gluing
  preserve them.
- **Kernels and conditioning:** a _kernel_ maps each parameter to a measure.
  Measurable s-finite kernels compose and allow the order of integration to be
  exchanged (Tonelli). Disintegration builds conditional probability kernels for
  compatible s-finite joint measures on standard Borel spaces, with the
  uniqueness premise above.
- **Markov chains:** iterating a kernel runs a Markov chain. When some iterate
  is bounded below by a fixed measure (a _minorization_), every starting law
  converges in total variation to a unique invariant law at a geometric rate. On
  a finite state space, a matrix power with one positive column certifies that
  bound. A Metropolis–Hastings chain there has it when every state reaches a
  holding target through moves to positive weight. The layer also defines
  irreducible, aperiodic, and Harris recurrent chains, and proves, for example,
  that a chain converging from every start is aperiodic. Chains without a
  minorization, such as random-walk proposals on unbounded spaces, have no
  convergence theorem yet.
- **Randomization:** Kallenberg's randomization lemma
  ([Kallenberg 2021](https://doi.org/10.1007/978-3-030-61871-1)) writes every
  standard Borel probability kernel as a measurable function of its parameter
  and a uniform random number. The lemma asserts that such a function exists and
  gives no algorithm for finding it. Its hypotheses matter here too: a zero
  kernel on an inhabited parameter space has no such decomposition.
- **Higher-order programs:** [Problib/QuasiBorel.lean](Problib/QuasiBorel.lean)
  formalizes quasi-Borel spaces
  ([Heunen et al. 2017](https://doi.org/10.1109/LICS.2017.8005137)), a setting
  for probability in which functions are values. It proves the category
  Cartesian closed and embeds the standard Borel spaces in it.
- **Inference:** [Problib/Inference.lean](Problib/Inference.lean) states when
  the building blocks of Monte Carlo inference are correct. A law of weighted
  draws is _calibrated_ for a measure when reweighting by the weights recovers
  the measure, which is what importance sampling needs. Calibration carries over
  to populations of draws, and resampling and the sequential steps of sequential
  Monte Carlo preserve it under stated conditions. A Metropolis–Hastings step is
  in detailed balance when its accepted part is symmetric, so it leaves its
  target invariant. Companion results show why weaker conditions fail: for
  example, the reciprocal of an unbiased density estimate is a biased weight.
- **Exact counting:**
  [Problib/Inference/KnowledgeCompilation.lean](Problib/Inference/KnowledgeCompilation.lean)
  checks compiled Boolean circuits. An untrusted compiler turns a circuit into
  an ordered decision diagram and supplies a certificate: a graph of local
  if-then-else identities, with no truth tables. When the checker accepts, the
  diagram agrees with the circuit on every input. A checked diagram's weighted
  count equals the integral of its output over independent Bernoulli inputs, so
  the probability that a circuit returns true is a count over its diagram.

## Use

`nix build` runs the package checks and installs the checked sources under
`result/share/problib/`. problib is a library, so it installs no executable.

```sh
nix build
```

The development shell supplies Lean and Lake. Inside it, `lake build` compiles
the library, and three targets run the axiom audits and the tests of the audit
itself:

```sh
nix develop --command lake build
nix develop --command lake build Problib.Axioms Trust.Axioms TrustTest
```

A Lake package depends on problib from its `lakefile.lean`:

```lean
require problib from git
  "https://github.com/a-tiny-project/problib.git" @ "v26.9.3"
```

or from its `lakefile.toml`:

```toml
[[require]]
name = "problib"
git = "https://github.com/a-tiny-project/problib.git"
rev = "v26.9.3"
```

`lake update problib` then fetches it, and `import Problib` brings in the
library. problib is checked under `leanprover/lean4:v4.31.0`, so the depending
package's `lean-toolchain` should name the same release.

## Audit

Problib makes usage of a `Trust` framework, which audits what each declaration's proof depends on. 
The package audit in [Problib/Axioms.lean](Problib/Axioms.lean) covers every
constant that `Problib` modules define: the declarations written in source, and
the equation lemmas, matchers, and other auxiliaries Lean generates from them.
Every declaration's axioms are among `propext`, `Quot.sound`, and
`Classical.choice`. The tests in `TrustTest` check that the audit rejects a
custom axiom, an unsafe declaration, and an unproved `sorry`.

The audit covers proofs, and a theorem's statement keeps its hypotheses: a user
of the theorem still has to establish them.

## Module map

- [Problib/Real.lean](Problib/Real.lean): Dedekind reals, order completeness,
  and nonnegative extended arithmetic.
- [Problib/Measure.lean](Problib/Measure.lean): outer measures, Borel sets,
  Lebesgue integration, kernels and their iteration, disintegration,
  randomization, and the Giry monad.
- [Problib/Probability.lean](Problib/Probability.lean): finite distributions
  with nonnegative rational weights, and finite sets.
- [Problib/QuasiBorel.lean](Problib/QuasiBorel.lean): quasi-Borel spaces,
  Cartesian closure, and Borel embeddings.
- [Problib/Inference.lean](Problib/Inference.lean): weighting, resampling,
  sequential Monte Carlo, Metropolis–Hastings, invariance of Markov kernels,
  checked decision diagrams, derivative estimators, and generative functions.
- [Problib/Analysis.lean](Problib/Analysis.lean): logarithm, exponential, square
  root, derivatives, Gaussian integrals, power series, PAP maps, and inverses of
  monotone functions.
- [Problib/Domain.lean](Problib/Domain.lean): complete partial orders,
  continuous maps, and fixed points reached by iteration.
- [Problib/Linear.lean](Problib/Linear.lean): rational matrices, sums, and
  duals.
- [Problib/Algebra.lean](Problib/Algebra.lean): laws of commutative monoids,
  groups, and semirings.
- [Problib/Countable.lean](Problib/Countable.lean): bijections, pairing
  enumerations, and decoding bounds for countable structures.
- [Problib/FiniteEnumeration.lean](Problib/FiniteEnumeration.lean): lists that
  enumerate every value of a finite type.
- [Problib/Power.lean](Problib/Power.lean): `Power α n`, the length-indexed
  vectors of `n` values of type `α`.
- [Problib/Axioms.lean](Problib/Axioms.lean): the audit manifest for the
  library's declarations.
- [Trust.lean](Trust.lean): the audit framework, which rejects custom axioms,
  unsafe declarations, and unproved goals.
- [TrustTest.lean](TrustTest.lean): the audit's own tests.

## License

AGPL-3.0-or-later. See [LICENSE](LICENSE).
