<p align="center">
  <img src="logo.svg" alt="Foundations" width="360" />
</p>

# Foundations v26.9.1

Probabilistic programming languages express models with uncertain variables,
observations, and inference. In discrete languages, program semantics denote
probability mass functions over program states. However, expressive models
require continuous distributions, density observations, and conditioning on
zero-probability events. Under continuous variables, standard discrete
operational semantics break down. Informal pen-and-paper arguments frequently
conceal soundness bugs when manipulating densities or exchanging integrals.

Rigorous semantics for continuous probabilistic programs requires measure theory
and Lebesgue integration. Yet formalizing these foundations exposes fragile
mathematical boundaries. For instance, conditioning on continuous observations
corresponds to measure disintegration. In the general disintegration theorem,
almost-everywhere conditional kernel uniqueness assumes a sigma-finite second
marginal. Outside this premise, multiple distinct valid probability kernels can
emerge under infinite atoms. Similarly, Olav Kallenberg's Randomization Lemma
([Kallenberg 2021](https://doi.org/10.1007/978-3-030-61871-1)) establishes that
standard Borel probability kernels decompose into uniform noise and
deterministic decoders. However, this classical result serves as an existence
theorem rather than an algorithm. In fact, a zero kernel on an inhabited
parameter domain admits no randomizer.

Foundations provides a dedicated, self-contained mathematical library in Lean 4
built from first principles. The project formalizes reusable compositional
probability mathematics across independent language and verification efforts. It
proves every theorem under Lean's standard three kernel axioms (`propext`,
`Quot.sound`, `Classical.choice`) without external dependencies.

Choosing a self-contained, Mathlib-free architecture controls dependency
boundaries and audit scope for downstream tools. The kernel axiom ceiling
remains the standard Lean boundary either way. However, this design choice
incurs substantial maintenance work, requiring the project to build real
analysis, measure theory, and integration from first principles.

Downstream languages like RePPL rely on Foundations to ground their denotational
semantics. However, Foundations does not contain RePPL's finite-calculus proof
package or prove the released RePPL executable compiler correct. Furthermore,
classical existence theorems for decoders and conditional kernels do not supply
general algorithms for continuous compilation. Developing continuous
higher-order probability monads and executable compiler refinement remain active
research frontiers.

## Mechanized mathematical layers

Foundations organizes over 5,000 checked production declarations from the
established baseline into connected layers:

- **Real analysis from Dedekind cuts:**
  [Foundations/Real.lean](Foundations/Real.lean) constructs real numbers as
  Dedekind cuts, proving completeness as an ordered field. Nonnegative extended
  reals (`ENNReal`) provide infinity-aware summation commuting with monotone
  suprema.
- **Continuous measure and Lebesgue integration:**
  [Foundations/Measure.lean](Foundations/Measure.lean) develops Carathéodory
  outer measures from countable covers. Half-open intervals generate standard
  Borel spaces. Nonnegative Lebesgue integration formalizes monotone
  convergence, Fatou's lemma, and density transforms.
- **S-finite kernels and Bayesian disintegration:** Measurable s-finite kernels
  compose and support Tonelli integral exchange. Disintegration theorems
  construct conditional probability kernels for compatible s-finite joint
  measures on standard Borel spaces. Conditional uniqueness holds almost
  everywhere under sigma-finite second marginals.
- **Randomization foundations:** Foundations formalizes Olav Kallenberg's
  Randomization Lemma
  ([Kallenberg 2021](https://doi.org/10.1007/978-3-030-61871-1)). Every standard
  Borel probability kernel decomposes into a uniform source and a measurable
  decoder.
- **Higher-order Quasi-Borel spaces:**
  [Foundations/QuasiBorel.lean](Foundations/QuasiBorel.lean) formalizes
  Quasi-Borel spaces
  ([Heunen et al. 2017](https://doi.org/10.1109/LICS.2017.8005137)),
  establishing Cartesian closure and standard Borel embeddings for higher-order
  probabilistic semantics.

## Classical existence and trust boundaries

The library maintains a strict distinction between mathematical existence and
computational realization:

- **Mathematical existence:** Theorems like Kallenberg's randomization lemma and
  measure disintegration establish that measurable decoders and conditional
  kernels exist under explicit hypotheses. They do not supply general algorithms
  to compute decoders for arbitrary continuous distributions.
- **Downstream integration:** Downstream languages like RePPL use Foundations to
  justify semantic correctness. Compiling continuous kernels into executable
  code remains an active research direction.
- **Mechanized status:** Real analysis, measure theory, s-finite kernels, and
  Giry monad properties are fully mechanized in Lean 4, passing independent
  axiom audits.

## Use

Build the library with Nix:

```sh
nix build
```

`nix build` runs package checks and installs checked library sources to
`result/share/foundations/`. Foundations is a library package. It does not
install a standalone command-line executable in `bin/`.

Enter the development shell and compile with Lake:

```sh
nix develop --command lake build
```

Run axiom audits and trust validation targets:

```sh
nix develop --command lake build Foundations.Axioms Trust.Axioms TrustTest
```

To consume Foundations as a Lake dependency in a downstream package:

```lean
require foundations from git
  "https://github.com/a-tiny-project/foundations.git" @ "v26.9.1"
```

Ensure your project uses the pinned Lean toolchain: `leanprover/lean4:v4.31.0`.

## Module map

- [Foundations/Real.lean](Foundations/Real.lean): Dedekind real numbers, order
  completeness, and nonnegative extended arithmetic.
- [Foundations/Measure.lean](Foundations/Measure.lean): Carathéodory outer
  measures, Borel algebras, and Lebesgue integration.
- [Foundations/Probability.lean](Foundations/Probability.lean): Probability
  spaces, finite distributions, and measure interpretations.
- [Foundations/QuasiBorel.lean](Foundations/QuasiBorel.lean): Quasi-Borel
  spaces, Cartesian closure, and Borel embeddings.
- [Foundations/Linear.lean](Foundations/Linear.lean): Vector spaces and rational
  linear algebra.
- [Foundations/Algebra.lean](Foundations/Algebra.lean): Core algebraic
  structures and ordering properties.
- [Foundations/Power.lean](Foundations/Power.lean): Integer and rational
  exponentiation.
- [Foundations/Axioms.lean](Foundations/Axioms.lean): Audit manifest verifying
  standard axiom bounds across production declarations.
- [Trust.lean](Trust.lean): Metaprogramming audit framework detecting unsafe
  declarations and unproved goals.
- [TrustTest.lean](TrustTest.lean): Verification tests confirming rejection of
  custom axioms and unproved obligations.

## Verification scope and trust boundaries

Foundations enforces strict verification discipline through the `Trust`
framework. Production audits verify that over 5,000 declarations rely solely on
Lean's standard three axioms: `propext`, `Quot.sound`, and `Classical.choice`.

Test suites in `TrustTest` verify that the audit framework detects and rejects
custom project axioms, unsafe declarations, and unproved `sorry` holes.

Axiom audits confirm the absence of unproved holes. They do not eliminate
explicit mathematical hypotheses from theorem statements.

## References

- Repository:
  [https://github.com/a-tiny-project/foundations](https://github.com/a-tiny-project/foundations)

## License

AGPL-3.0-or-later. See [LICENSE](LICENSE).
