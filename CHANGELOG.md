# Problib changelog

## v26.10.1

- Analysis adds Fréchet derivatives of maps between finite vector spaces, the
  mean value inequality, the contraction principle, and the inverse function
  theorem in every dimension (`inverse_function`).
- `Problib.Measure.Kernel.Chart` builds a reference kernel that follows its
  parameter from countably many measurable charts, each with a Jacobian, an
  exact image test and an inverse. Each point is counted once, in the chart of
  least dimension and index whose image holds it. The reference is s-finite,
  every fiber is sigma-finite, and any s-finite law it covers has a jointly
  measurable density against it (`Family.derivative`). A split gives each
  measurable piece of the parameter space its own family. Two controls come with
  it: a draw placed on a moving line (`line_isDensity`) and a draw scaled by the
  parameter, whose density at zero is the source's total mass
  (`scale_isDensity_zero`).
- `Problib.Analysis.PAP.Trace` certifies a kernel between Euclidean components
  as a countable sum of trace pieces. Each piece has a partial PAP return map,
  jointly in the environment and the trace, and a weight that need only be
  measurable. Certificates close under return, draw, score, countable sums,
  substitution, bind, case splits on a c-analytic region, normalization and sums
  of strata. A kernel into a countable sum of components is certified one
  component at a time, and a bind from it splits over the components.
  `Certificate.Regular` states the finite, PAP weight a faithful consumer needs.
- `not_pap_of_dense_jumps` shows that a map of one coordinate with upward jumps
  at a set dense in a half-open interval has no PAP representation on a domain
  containing the interval.
- `pairVector`, `leftVector` and `rightVector` concatenate and split finite
  vectors measurably, and `volumePi_add` splits Lebesgue measure along them.
- `Problib.Analysis.Real.Matrix` adds real matrices on finite vectors: products,
  transposes, inner products and Gram matrices, the determinant by expansion
  along the first column, back substitution for upper triangular systems, and QR
  factorization by Gram–Schmidt (`orthonormalize_facts`). Under it a Gram matrix
  is `Rᵀ R` (`gram_eq_of_factor`).
- An upper triangular matrix with nonzero determinant multiplies volume by
  `|det R|` (`volumePi_image_upperTriangular`).
- Source-link build helpers take the source URL from explicit configuration or
  GitHub repository variables. Revision-only helpers resolve commits without a
  source URL.
- Build provenance preserves revision and version outputs when no source URL is
  configured. Consumers that read a source link receive the configuration
  diagnostic during compilation.
- `Kernel.Summarizes` states that a step kernel sends the law at a statistic to
  a weight times the law at the moved statistic. `foldList_bind_of_summarizes`
  then gives the ordered kernel of a list: the product of the weights times the
  law at the final statistic. `Urn.Latent.collapse` is now an instance of it.
- A one-node Gaussian network read once through a slope and an offset updates in
  closed form: `Network.single_update` gives the posterior mean `affineMean` and
  variance `affineVariance` of `y ~ N(offset + slope · μ, w)`.

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
