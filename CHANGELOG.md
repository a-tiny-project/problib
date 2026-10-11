# Problib changelog

## v26.10.0

- Problib builds with Lean 4.34.1, where it built with Lean 4.31.0.
- The README is rewritten around installing the library, using it, and its
  limits.
- Declarations that nothing else in the library used are removed from the real,
  measure, probability and analysis layers, among them the module
  `Problib.Analysis.Real.PowerSeries.PolynomialAnalytic`.
  `seq_rn_of_density_ratio` is renamed `seq_rn_of_densityRatio`.
- Analysis proves the exponential analytic everywhere, the logarithm analytic on
  the positive reals, and the reciprocal analytic away from zero, each from its
  own series around every center. It adds the identity theorem for analytic
  functions of one coordinate, the fundamental theorem of calculus, limits and
  derivatives at one side of a point, and the theorem that a function with zero
  derivative on an open interval is constant there.
- The zeros of an analytic function that does not vanish on a whole interval
  have zero volume. From that, the intensional derivative of a piecewise
  analytic (PAP) map is its ordinary derivative almost everywhere under Lebesgue
  measure on the finite Euclidean spaces.
- Analysis adds Euler's Beta integral, the categorical family, the conjugacy of
  the Dirichlet and categorical families, and exponential families with their
  conjugate priors. `Problib.Analysis.Enclosure` encloses real numbers in closed
  intervals with rational endpoints, with modules for the exponential, the
  logarithm, the square root and π.
- A positive Harris chain on a countably generated space converges in total
  variation to its invariant law from every start exactly when it is aperiodic
  (`harris_converges_iff_aperiodic`). The proof adds small sets, their coupling,
  the periods of minorized step counts, and the composition of minorization
  bounds.
- Kernels gain finite products (`Kernel.pair`, `Kernel.finProduct`), pairs of
  kernels run side by side on the coordinates of a pair, site updates on
  dependent products, conditional kernels of joint densities, normalized
  families, and the accepted and rejected parts of an attempt.
- Measure theory adds measure-preserving equivalences, change of variables for a
  nonzero scaling, volumes invariant under translation and negation, the simplex
  reference measure, and finite configurations with their unordered quotient.
- The `measurability` tactic builds a measurability proof with the shape of the
  function it measures.
- Inference proves that Gibbs scans on factor graphs converge
  (`gibbs_scan_converges`), that an involutive accept and reject kernel leaves
  its target invariant (`involutive_invariant_of_reference`), with Hamiltonian
  Monte Carlo as an instance (`hmc_invariant`) and the leapfrog integrator as
  its reversible proposal, and that an invariant, irreducible step with
  dominated moves is Harris recurrent.
- Inference adds pseudo-marginal Metropolis–Hastings
  (`pseudoMarginalKernel_invariant`), particle marginal Metropolis–Hastings,
  populations of weighted draws with resampling and sequential extension, the
  selection of a lane by its weight, split and merge moves, and unbiased
  estimators of densities with their reciprocal weights.
- `Problib.Inference.Necessity` gains counterexamples for premises of the new
  theorems. For example, `gibbs_scan_converges` needs the joint density bounded
  below by a positive constant, and two bits constrained equal show why.
- The quasi-Borel layer adds expectation as a continuous functional on a
  predomain, the lifting and the randomizations of a predomain, countable
  products and couplings of probability laws, the normalization of s-finite law
  families, and counted proper weighting of population laws.
- `Problib.Real.Grind` offers opt-in `grind` algebra for the real carrier.
- `Problib.QuasiBorel.SFinite` adds `Concentrated`: a law is concentrated on a
  predicate when any two kernels that agree on the predicate bind it to one law.
  A Dirac law is concentrated on every predicate that holds at its point
  (`concentrated_pure`), a bind is concentrated when its kernel is at every
  point (`concentrated_bind`), and a law is concentrated on every predicate that
  holds almost everywhere under its measure (`concentrated_of_ae`).
- `Pi.IsProduct.reads_mixed` reads repeated keys from a finite product whose
  coordinate laws need agree only at the keys' first occurrences.
- Problib's mark is an inchworm.

Earlier releases are described at https://github.com/a-tiny-project/problib/releases.
