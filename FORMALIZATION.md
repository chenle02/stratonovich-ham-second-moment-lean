# Formalization scope

## The paper's argument and where Lean enters

The paper bounds and identifies the growth of `log E[u(t,x)²]` for the
Stratonovich hyperbolic Anderson model. The argument has three layers.

1. **Stochastic and analytic layer.** The chaos expansion, the two-chain
   pairing integrals, Wick pairings (beyond finite families of Gaussian
   values), Gaussian integration (beyond finitely many standard Gaussians),
   imported bounds,
   Laplace transforms and the variational asymptotics. **Not in Lean**,
   except a few slices: the Laplace transforms of the wave kernel and of
   the two-time kernel and the subordination formula (`ClockCopy` and its
   foundation modules), the Gaussian transform of the spectral measure
   (`MaskedSpectralGrowth`), the uniform scalar frequency row
   (`FrequencyRow`), the temporal completion `H_a` (`TimeCompletion`), the
   auxiliary mask norm (`MaskedAuxiliaryNorm`), the Gaussian heat envelope
   of the covariance (`VariationalMean`), a finite Hilbert-valued Bessel
   inequality (`PhaseBessel`), the wave Green measures `G_s` for
   `d = 1, 2, 3` (`WaveGreen`), the spectral identity and positive
   definiteness of `Gamma = delta_0(dx_1) dx_2` (`QuotientObstruction`), a
   finite Gaussian comparison under the positive semidefinite order
   (`GaussianComparison`), the two wave variance directions in spectral
   form (`WaveTwoVariances`), the variational floor and the Rayleigh-form
   rate (`VariationalFloor`, `VariationalRate`), the deterministic Fourier
   bound `L:spatial-fourier-bound` for the smooth spatial ratio and the
   static controls
   (`SpatialFourierBound`, `SpatialSmoothRatio`, `SpatialStaticControls`,
   `SpatialOccupationCompleted`), series types and the continuity of the
   growth types in the temporal exponent (`SeriesType`, `TypeContinuity`),
   the white-noise bound formulas and clock transforms
   (`WhiteRelativeWidth`, `WhiteClockLaplace`), the coefficient bound of
   the interval inventory product (`InventoryProduct`), an abstract `L^2`
   limit of a regularized series under a uniform scaled moment bound
   (`UniformSeriesTail`), the density of test functions in the
   weak-gradient `H^1` (`H1Density`), the physical four-linear extension
   and the spatial energy (`SpatialFourLinear`), the full physical
   occupation class (`OccupationPhysicalClass`; both completed in
   `SpatialOccupationL7Completed`), the scalar and Hilbert-space steps
   of the static interaction and interval coefficient bounds
   (`IntervalScalar`, `IntervalScalarCompleted`), the spectral-mass
   identity `R_Gamma(1) = R_alpha` (`SpectralMassIdentity`), Gaussian
   smoothing as a Fourier multiplier (`DampedMultiplier`), the positivity of
   the space-time occupation form, the deterministic occupation ceiling and
   the spatial bracket (`SpaceTimePositivity`, `OccupationCeilingFinite`,
   `SpatialBracket`, completed in `L8Completed`), the masked rates
   (`RemoveMask`), the finite Wick formula and the terminal-chain Wick
   formula with the chain measures given by their masses (`FiniteWick`,
   `TerminalWick`), an abstract compact Young baseline (`SymplecticFree`)
   and the Cauchy steps of the static phase orders (`StaticPhaseCauchy`),
   the Fourier transforms of the wave Green measures in `d = 1, 2, 3` and
   Archimedes' law for the sphere measure (`WaveGreenFourier`), the low-alpha
   convolution bound and the static contraction bounds
   (`LowAlphaConvolution`, `PhaseContractions`, completed in `L9Completed`),
   the exact occupation constant and ceiling (`RawOccupationEnergy`,
   `OccupationCeilingExact`), the normalized Hermite polynomials and the
   finite Gaussian Fock layer with values in a Hilbert factor
   (`GaussianHermite`, `HermiteFock`) and their consumers `L:fock-form`,
   `L:interval-contractions` and `E:occupied-multiplication` (`FockForm`),
   and the scalar and numerical-range steps of the complex phase bounds
   (`ComplexPhaseScalar`).
2. **Reductions to explicit inequalities.** At many points the analytic
   argument reduces to a finite statement: an exponent range, an exact
   rational or square-root inequality, a polynomial that must stay positive
   on a region, a determinant or matrix inverse, a count of coefficients in
   a finite word, or an integral comparison once integrability is known.
   **These are what Lean checks.**
3. **Assembly** of the main theorems from the layers above. **Not in Lean.**

So each module checks one reduction in layer 2. Its hypotheses state the
facts that layer 1 supplies (for example positivity of a parameter,
integrability of a function, or an inequality proved analytically in the
paper). Its conclusion is the fact that the paper then uses.

## Status of each kind of statement

| Kind | Count | Meaning |
|---|---|---|
| Whole result (ledger heading "whole result"), nothing supplied | 25 labelled results, `H:homog`, `E:kappa`, `E:driver-parameters`, `E:masked-time-schur` and `R:gaussian-one-variance-test`; 27 modules: 559 theorems, 135 definitions | Every conclusion of the result is a Lean conclusion under the manuscript's hypotheses (`H:homog` modelled in full; most results via exact-hypothesis wrappers); coverage class same-assumptions, conclusion full |
| Whole result, inputs supplied | none: the three results formerly here (`P:radius-mean-anchor`, `P:moment-growth-logconvex`, `C:static-moment-constant-continuity`) are proved for abstract objects whose construction is missing, so they are narrower results | — |
| Narrower result (ledger heading "narrower result: ...", naming what is missing) | 18 results with the manuscript's hypotheses and steps or parts of 30 further results; 31 modules and the audit file `HermiteWordFock`: 943 theorems, 199 definitions | Kernel-checked; some conclusion of the result is not a Lean conclusion. The 18 with the manuscript's hypotheses (coverage same-assumptions, weaker): `P:masked-quotient-obstruction` for the covariance functional (the noise `W` not constructed), `L:damped-homogeneous-norms` with its closing smoothing remark in a narrower reading (covariance smoothing only as membership of the Gaussian multiplier, without its spectral identification; the Green-smoothing identification is proved in `d = 1, 2, 3`), the Rayleigh lemma without its application, the dilation lemma for the integral-form cost, `P:masked-auxiliary-norm` without its clause for a real `H`, `L:variational-global-mean` without the mixed-derivative bounds, `P:variational-unmasked-rate` without its operator half, `L:spatial-static-controls`, `P:spatial-smooth-ratio` and `P:spatial-energy-map` for the Rayleigh-form rate and the integral-form cost, `P:spatial-four-linear` with the joint continuity of `C_4` in sequential form, `P:occupation-physical-class` over the class `O` modelled by joint representatives, `P:variational-positive-scores` without `Q_2 >= S_2^pos`, `T:intrinsic-occupation-ceiling` with the exact `C_occ` in both forms over the modelled class `O`, without `C_2 <= U_2`, `C:intrinsic-spatial-bracket` for `S_2^pos` in place of `C_2`, `L:positive-raw-embedding` in integral form (variance identity, row and Schur bounds), and `P:raw-occupation-energy` and `L:occupation-rayleigh-selection` over the class `O` modelled by joint representatives. The 30 further results (coverage inputs-supplied, weaker) have analytic inputs supplied or only some conclusions formalized: `P:radius-mean-anchor` for abstract random paths (the operator paths `M_R(Y_m)` not constructed), `P:moment-growth-logconvex` and `C:static-moment-constant-continuity` for an abstract moment function (the solution moments not constructed), `L:raw-block-indexed-cone` for an abstract ground family, `L:uniform-series-tail` for an abstract `L^2` family (chain measures fixed only by their masses), the finite comparison of `P:masked-noise-completion`, `P:wave-two-variances` with named inputs (spectral core with none), `P:interval-coefficients` with named inputs, `P:variational-remove-mask` (rates with none, the point display over a named input), `L:terminal-wick` (named measurability input, chain measures by their masses), `L:symplectic-free` (free group and Young convergence supplied), `L:fock-form` and `L:interval-contractions` (spatial column bound supplied), the scalar steps of `L:complex-phase` and `L:interval-complex`, `L:finite-word-cutoff` for one Gaussian mode per color, and the others listed in `coverage.yaml` |
| Foundation or proof steps (ledger heading "foundation: ..." or "proof steps of ...") | 18 modules: 466 theorems, 78 definitions | Kernel-checked facts used by labelled results, not a labelled result themselves: `WaveKernel`, `SpectralHomog`, `TimeFractional`, `DampedNorms`, `GaussianIBP`, `GaussianTest`, `WeakSobolev`, `VariationalFloor`, `SeriesType`, `H1Density`, `FiniteWick`, `GaussianHermite`, `HermiteFock`, `WaveGreen`, `WaveGreenFourier`, `SpaceTimePositivity`, and the proof steps `IntervalScalar` (the steps of `C:static-interaction`, with `E:static-block-series` in full) and `StaticPhaseCauchy` (the Cauchy steps of `P:static-phase-all-orders`), whose analytic inputs are supplied |
| Checked step fact (`StratonovichHAMAudit/`, except `HermiteWordFock`) | 82 theorems, 6 definitions | Kernel-checked; the ledger gives its paper label and outside inputs |
| of which helper lemmas (`internal`) | 847 theorems, 51 definitions | Kernel-checked; used inside one module |
| Other public definitions | 91 | Named quantities and measures used in the statements (87), and four instances on `TimeCompletion.Pre` (counting convention in the ledger Scope) |
| Negative controls | 68 | Wrong variants that Lean must reject |
| Refutations | 235 | Lean proofs refuting specified variants of declarations: manuscript scalar steps, Lean-route-only constructions, and controls of totalized arithmetic or of broader generalizations (the ledger states each one's domain) |

Heading categories (the same three are used for the statement ledger's
section headings; its Index by label points from each label to those sections
with their category, and states nothing per declaration). Labelling
convention of the ledger's section tables: every backticked manuscript label
in a label cell is an assignment and creates an Index pointer; a label
mentioned only as context goes in the "What it states" cell as "(Context:
...)"; a "no direct label" cell contains no manuscript label. The ledger Scope keeps the
model-choice register. M1, its only entry, is the `d = 3` wave Green measure
`(s/(4 pi)) map (omega -> s omega) volume.toSphere` (wave L6, decision 4);
its identification with the surface measure of the TeX is not proved. A
registered standard choice preserves whole status only when the result's
section names the model (as `LowAlphaConvolution`, `PhaseContractions` and
`L9Completed` do for M1); a missing construction (the noise `W`, an abstract
ground family, chain measures fixed by their masses, abstract random paths,
an abstract moment function) makes the result narrower.
(A) "whole result": every conclusion of the labelled result is a Lean
conclusion under the manuscript's hypotheses, possibly with named supplied
inputs that are disclosed (coverage class same-assumptions or
inputs-supplied, conclusion full; at present every whole result has the
manuscript's hypotheses alone); no other module carries it. (B) "narrower
result: ...": a labelled result some of whose conclusions are not Lean
conclusions, or are proved for a modelled object (such as the class `O` by
joint representatives, or the rate in Rayleigh form and the cost in integral
form) whose identification with the manuscript's object is not formalized;
the heading names what is missing. (C) "foundation: ..." or "proof steps of
...": facts used by labelled results, not a labelled result themselves; the
`StratonovichHAMAudit` step modules are of this kind except `HermiteWordFock`,
a narrower result.

Modules are counted by their ledger heading; a module that also proves
pieces of other results is counted once. Completion modules
(`ClockCopyHomog`, `MaskedContinuousWaveCompleted`, `L9Completed`,
`SpatialOccupationCompleted`, `SpatialOccupationL7Completed`,
`IntervalScalarCompleted`, `L8Completed`) discharge named inputs of other
modules; discharging an input does not make a narrower result whole, so
`L8Completed` (narrower results, including `L:uniform-series-tail` with the
chain measures fixed only by their masses) and the spatial and occupation
modules remain "narrower result". `ClockCopyHomog`,
`MaskedContinuousWaveCompleted` and `TimeSchur`, which have no section of
their own, count as whole-result modules; `DampedNorms`, `SpectralHomog`,
`TimeFractional`, `WaveKernel`, `GaussianIBP`, `GaussianTest` and
`WeakSobolev` as foundations.

These counts describe the package. They are not a percentage of the paper.
The 25 whole results and 18 narrower results with the manuscript's
hypotheses are deterministic lemmas,
propositions and corollaries used inside the analytic argument, and the
occupation ceiling `T:intrinsic-occupation-ceiling` (a narrower result: both
forms with the exact constant, for `S_c^pos`; `C_2 <= U_2` not formalized);
the other three main theorems are not formalized.

## Reading a statement

For each declaration, check three things against the paper:

1. the hypotheses match what the paper has available at that point;
2. the conclusion is what the paper uses next;
3. parameter ranges, strict versus non-strict inequalities and quantifier
   order agree.

The [statement ledger](docs/statement-ledger.md) records this for every row.
`Audit/<module>/` prints the full elaborated types, so the statements can be
read without opening an editor.

## Not yet included

Three development modules use a Gaussian-chaos library that is not yet
public: normalized Gaussian coordinates, vector Gaussian projection and
colored vector words. They are checked in the private development record
and will be added here when that library is released.

## Possible next steps

- the finite pair-partition counts behind the two-chain integrals;
- a reusable Laplace-to-time growth lemma, with its analytic inputs as
  hypotheses;
- the constant and exponent algebra of the main upper and lower bounds.
