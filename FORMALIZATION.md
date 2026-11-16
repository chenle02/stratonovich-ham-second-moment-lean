# Formalization scope

## The paper's argument and where Lean enters

The paper bounds and identifies the growth of `log E[u(t,x)²]` for the
Stratonovich hyperbolic Anderson model. The argument has three layers.

1. **Stochastic and analytic layer.** The chaos expansion, the two-chain
   pairing integrals (beyond the deterministic diagram model `DiagramModel`,
   register entry M4, and the diagram bounds built on it), Wick pairings (beyond finite families of Gaussian
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
   the scalar and numerical-range steps of the complex phase bounds
   (`ComplexPhaseScalar`), the Riesz spatial maxima in `d = 2, 3`
   (`HigherRieszTwo`, `HigherRieszThree`), the degree-one convolution bound
   (`AlphaOneConvolution`, completed in `L10Completed`), the white-noise
   model and the white moment bounds for `S_2^pos` (`WhiteModel`,
   `WhiteMomentBounds`), the fixed degree-split estimate on a finite Fock
   model (`FixedSplitCore`, `FixedSplit`), the multi-mode finite word cutoff
   and the identification of the interval coefficients `Q_(r,q)`
   (`FiniteWordCutoff`), the spatial column bound on a Fourier-side model
   (`FockColumnBound`), the static interaction bounds with fewer supplied
   inputs (`StaticInteractionCompleted`), and the constructed terminal-chain
   measures with their Green regularization (`TerminalWickInputs`,
   `TerminalWickRegularization`), the terminal Wick lemma in full for them
   (`TerminalWickComplete`), the spectral measure of the smoothed covariance
   (`DampedSmoothing`), the finite Gaussian linear-image comparison, the
   half-action identity and the Rayleigh transfer (`SourceTube`), and the
   operator form of the Fock sandwich bound on a finite Fock model of the
   cutoff Hilbert space (`FockSandwichModel`).
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
| Whole result (ledger heading "whole result"), nothing supplied | 44 labelled results, `H:homog`, `E:kappa`, `E:driver-parameters`, `E:masked-time-schur` and `R:gaussian-one-variance-test`; 40 modules (one of which, `SourceTube`, also holds the whole result with inputs supplied below): 1022 theorems, 254 definitions | Every conclusion of the result is a Lean conclusion under the manuscript's hypotheses (`H:homog` modelled in full; most results via exact-hypothesis wrappers); coverage class same-assumptions, conclusion full |
| Whole result, inputs supplied | 1 labelled result, `P:tube-rayleigh-transfer` (`SourceTube`, wave L12), with two named inputs from `L:tube-closed-geometry` (`TubeAttained`, `TubeTail`, true for the manuscript's tubes); the three results formerly here (`P:radius-mean-anchor`, `P:moment-growth-logconvex`, `C:static-moment-constant-continuity`) are proved for abstract objects whose construction is missing, so they are narrower results | Every conclusion of the result is a Lean conclusion under the manuscript's hypotheses and the named inputs; coverage class inputs-supplied, conclusion full |
| Narrower result (ledger heading "narrower result: ...", naming what is missing) | 16 results with the manuscript's hypotheses and steps, parts or narrower forms of 34 further results; 48 modules and the audit file `HermiteWordFock`: 1750 theorems, 421 definitions | Kernel-checked; some conclusion of the result is not a Lean conclusion. The 16 with the manuscript's hypotheses (coverage same-assumptions, weaker): `P:masked-quotient-obstruction` for the covariance functional (the noise `W` not constructed), the Rayleigh lemma without its application, the dilation lemma for the integral-form cost, `P:variational-unmasked-rate` without its operator half, `L:spatial-static-controls`, `P:spatial-smooth-ratio` and `P:spatial-energy-map` for the Rayleigh-form rate and the integral-form cost, `P:variational-positive-scores` without `Q_2 >= S_2^pos`, `T:intrinsic-occupation-ceiling` with the exact `C_occ` in both forms over the class `O` itself (wave L14), without `C_2 <= U_2`, `C:intrinsic-spatial-bracket` for `S_2^pos` in place of `C_2`, `L:positive-raw-embedding` without the mean identity and the canonical versions (wave L14: the Bochner inclusion over the `L^2` completions of M5), `L:occupation-raw-square` over fields modelled by joint representatives (wave L14), `L:positive-physical-gram` without the label row and the entrywise order (wave L14), `L:occupation-rayleigh-selection` for the Rayleigh-form rate and the integral-form cost (over `O` itself since wave L14), and `L:fock-form` (also in operator form, `FockSandwichModel`) and `L:interval-contractions` on a Fourier-side model not identified with the physical-space operators. (`L:damped-homogeneous-norms` and `L:terminal-wick`, narrower until wave L11, are whole results since wave L12 (over M1; `L:damped-homogeneous-norms` over M1 and M3); `P:masked-auxiliary-norm`, `L:variational-global-mean`, `P:spatial-four-linear`, `P:occupation-physical-class` and `P:raw-occupation-energy` since waves L13 and L14.) The 34 further results (coverage inputs-supplied, weaker) have analytic inputs supplied or only some conclusions formalized: `P:radius-mean-anchor` for abstract random paths (the operator paths `M_R(Y_m)` not constructed), `P:moment-growth-logconvex` and `C:static-moment-constant-continuity` for an abstract moment function (the solution moments not constructed), `L:raw-block-indexed-cone` for an abstract ground family, the finite comparison of `P:masked-noise-completion`, `P:wave-two-variances` with named inputs (spectral core with none), `P:interval-coefficients` with named inputs, `P:variational-remove-mask` (rates with none, the point display over a named input), `L:symplectic-free` (free group and Young convergence supplied), the scalar steps of `L:complex-phase` and `L:interval-complex`, `L:fixed-split` on a finite Fock model (segment bound, Dyson cube identity, invariance of the cross subspaces, entire coefficients and the column bound supplied; the cutoff evolution and its coefficients not constructed), through which `P:interval-coefficients` takes, in place of the input `L:fixed-split`, the inputs of that lemma (and, in place of the added hypothesis `hQ` on `Q_(r,q)` that wave L10 needed, the Duhamel word expansion `DuhamelWords` of the coefficients), `C:static-interaction` with the order bounds and the identification of the interaction map proved (and, on the Fourier-side model of `FockSandwichModel`, the operator form of `E:fock-sandwich`), `T:white-moment-bounds` for `S_2^pos` in place of `C_2` (the energy value of `P:white-spatial-energy` supplied; the time exponent and `c = 0` not formalized), from wave L13 `P:d1-upper`, `P:low-alpha-upper`, `C:d1-first-calibration`, `L:white-test` and `P:riesz-small` (diagram values and coefficient bounds on the model M4 with nothing supplied; statements about the solution from the named input `MixedMoment` (the statement of `P:mixed`), and for `C:d1-first-calibration` also `FirstMomentSeries` (main TeX lines 796, 5856-5857)), `P:signed-closed-form` (the form bounds and the bounded resolvent of the form for an abstract Hermitian pairing, `E:signed-multiplier-form` supplied as `SignedMultiplierForm`; `H_V`, its domains, `E:signed-quarter-phase`, the dual completion and `L:signed-limiting-multiplier` not formalized), from wave L14 `C:three-product-riesz` and `C:three-finite-images` (moment bounds from `ThreeTransfer`, the statement of `P:three-transfer`, for an abstract model; the asymptotic clause only for a supplied spectral measure of the low endpoint), and the others listed in `coverage.yaml` |
| Foundation or proof steps (ledger heading "foundation: ..." or "proof steps of ...") | 27 modules: 800 theorems, 169 definitions | Kernel-checked facts used by labelled results, not a labelled result themselves: `WaveKernel`, `SpectralHomog`, `TimeFractional`, `DampedNorms`, `GaussianIBP`, `GaussianTest`, `WeakSobolev`, `VariationalFloor`, `SeriesType`, `H1Density`, `FiniteWick`, `GaussianHermite`, `HermiteFock`, `WaveGreen`, `WaveGreenFourier`, `SpaceTimePositivity`, and the proof steps `IntervalScalar` (the steps of `C:static-interaction`, with `E:static-block-series` in full) `StaticPhaseCauchy` (the Cauchy steps of `P:static-phase-all-orders`) and `FixedSplitCore` (the model-free steps of `L:fixed-split`, with the analytic bounds as premises), whose analytic inputs are supplied, the foundation `WhiteModel` (the white-noise model, `H:homog` with `alpha = d = 1` proved, and steps of `T:white-moment-bounds`), and the proof steps `TerminalWickRegularization` (nothing supplied: the mass and convergence facts of the Green-regularization paragraph of the proof of `L:terminal-wick` are proved for a common-noise construction whose factors are identified with `p_eta * G_h` one at a time; the identification of the whole regularized chain measure with the TeX's product, and the paragraph's last clause, are not formalized; in `d = 3` over the registered model choice M1); from waves L13 and L14 the foundations `DiagramModel` (the diagram model M4, `P:mixed` the named input `MixedMoment`), `DiagramBridge` (its `d = 1` positions form), and `H1Mathlib` (the weak-gradient `H^1` identified with Mathlib's Sobolev space), the control `PhaseShiftControl`, and the proof steps `TwoSimplexTime` and `WhiteCollapse` |
| Checked step fact (`StratonovichHAMAudit/`, except `HermiteWordFock`) | 82 theorems, 6 definitions | Kernel-checked; the ledger gives its paper label and outside inputs |
| of which helper lemmas (`internal`) | 2161 theorems, 141 definitions | Kernel-checked; used inside one module, or (491 theorems since v0.10.0) compared in the helper configuration `comparator-helpers.json`, a smoke check credited to no manuscript result |
| Other public definitions | 113 | Named quantities and measures used in the statements (107: 100 `def`, 7 `abbrev`), one structure (`FockColumnBound.L2Map`, a Lean-route data structure), four instances on `TimeCompletion.Pre`, and the syntax constant `WhiteFour.tacticTw_close` of a local tactic macro (no claim since v0.10.0); counted from the elaborated environment, source-written declarations only (no Lean-generated projection, constructor or derived instance) |
| Negative controls | 68 | Wrong variants that Lean must reject |
| Refutations | 372 | Lean proofs refuting specified variants of declarations: manuscript scalar steps, Lean-route-only constructions, and controls of totalized arithmetic or of broader generalizations (the ledger states each one's domain) |

Heading categories (the same three are used for the statement ledger's
section headings; its Index by label points from each label to those sections
with their category, and states nothing per declaration). Labelling
convention of the ledger's section tables: every backticked manuscript label
in a label cell is an assignment and creates an Index pointer; a label
mentioned only as context goes in the "What it states" cell as "(Context:
...)"; a "no direct label" cell contains no manuscript label. The ledger Scope keeps the
model-choice register. M1 is the `d = 3` wave Green measure
`(s/(4 pi)) map (omega -> s omega) volume.toSphere` (wave L6, decision 4);
its identification with the surface measure of the TeX is not proved. M2
(wave L11) is the Gaussian space `L^2(Omega; X)` over finitely many
coordinates as normalized Hermite coefficient vectors, with finite sums and
integrals of words taken coordinatewise (used by `FiniteWordCutoff`, and by
`FockSandwichModel` for its cutoff Hilbert space); the identification of a
Bochner integral with the coordinatewise integral is not proved. M3 (wave L12,
accepted by the author on 2026-11-13) is the smoothed covariance `p_eps * Gamma` of `L:damped-homogeneous-norms` as
the measure with Lebesgue density `gamma_eps(x) = int p_eps(x - y) Gamma(dy)`
(used by `DampedSmoothing`); its identification with Mathlib's `Measure.conv`
of `N(0, eps I)` and `Gamma` is not proved. M4 (wave L13; accepted by the
author on 2026-11-13) is the deterministic two-chain diagram model
`DiagramModel` (diagram integrals with the Green factors as measures of the
increments, and for a covariance measure the limit of common-width
smoothings); its identification with the positions form is proved in
`d = 1` only, and its identification with the TeX's joint limit at
arbitrary vertexwise widths is not proved; the common-width convergence of
the diagrams is the named input `DiagramLimits` and, with the finiteness of
the limits, a clause of the named input `MixedMoment` (the statement of
`P:mixed`); the diagram limits are proved for white noise in `d = 1` and the
order-two Riesz limit in `RieszFourDiagrams`. M5 (wave L14; accepted by the
author on 2026-11-13) realizes `H_t (x) G`, `H_t`, `H_I` and `H_Gamma` as
`L^2` completions under the kernel and covariance forms
(`OccupationCompletion`, `SourceHeatGram`, and the codomain `H_sp` of `Q` in
`ClassOH1`); no tensor identification and no isometry between `H_sp` and
`H_Gamma` is proved. M6 (wave L14; accepted by the author on 2026-11-13) is
`H^1` as the graph of the weak gradient in `L^2 x L^2` (`ClassOH1.H1R`), with
its topology proved equal to that of Mathlib's `H^1`; not proved: that every
real element of Mathlib's `H^1` comes from it. Named inputs of waves L13 and
L14: `MixedMoment` (`P:mixed`), `DiagramLimits` (the common-width diagram
limits of `L:joint-fixed-order`), `FirstMomentSeries` (main TeX lines 796,
5856-5857, for `C:d1-first-calibration`), `SignedMultiplierForm`
(`E:signed-multiplier-form`, with the Hermitian pairing, for
`P:signed-closed-form`) and `ThreeTransfer` (`P:three-transfer`); see the
ledger Scope. A registered standard choice preserves whole status only when the result's
section names the model (as `LowAlphaConvolution`, `PhaseContractions`,
`L9Completed`, `HigherRieszThree`, `AlphaOneConvolution` and `L10Completed`
do for M1, as `TerminalWickInputs` does for M1 in `L:uniform-series-tail`,
`TerminalWickComplete` for M1 in `L:terminal-wick`, `FiniteWordCutoff` for
M2, `DampedSmoothing` for M1 and M3, `D1Spatial` and `WhiteFour` for M4,
`SourceHeatGram` for M5, and `ClassOH1` and `ClassOBridge` for M6; the narrower
section `HigherRieszTwo` and the proof steps `TerminalWickRegularization` also
name M1, which they use in the steps in `d = 3`); a missing construction (the
noise `W`, an abstract ground family, chain measures fixed by their masses,
abstract random paths, an abstract moment function, the cutoff evolution of
`L:fixed-split`, the identification of the Fourier-side model of
`FockColumnBound` and `FockSandwichModel` with the physical-space operators,
the solution and its chaos terms behind `P:mixed`, the abstract moment model
of the three-dimensional corollaries) makes the result narrower.
(A) "whole result": every conclusion of the labelled result is a Lean
conclusion under the manuscript's hypotheses, possibly with named supplied
inputs that are disclosed (coverage class same-assumptions or
inputs-supplied, conclusion full; at present every whole result has the
manuscript's hypotheses alone except `P:tube-rayleigh-transfer`, which has two
named inputs); no other module carries it. (B) "narrower
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
`IntervalScalarCompleted`, `L8Completed`, `L10Completed`) discharge named inputs of other
modules; discharging an input does not make a narrower result whole, so
`L8Completed` (narrower results, including `L:uniform-series-tail` with the
chain measures fixed only by their masses) and the spatial and occupation
modules remain "narrower result" (so do `UniformSeriesTail` and
`L8Completed` for `L:uniform-series-tail`, which is whole in
`TerminalWickInputs`, a narrower-result module because of
`L:terminal-wick`, which is whole in `TerminalWickComplete`); `AlphaOneConvolution`, whose two named
inputs `L10Completed` discharges, proves every conclusion of
`L:alpha-one-convolution` and is a whole result. `HigherRieszTwo` (the
`d = 2` clause and the steps shared with `d = 3`) is a narrower-result
module; `HigherRieszThree` holds the whole lemma. `ClockCopyHomog`,
`MaskedContinuousWaveCompleted` and `TimeSchur`, which have no section of
their own, count as whole-result modules; `DampedNorms`, `SpectralHomog`,
`TimeFractional`, `WaveKernel`, `GaussianIBP`, `GaussianTest` and
`WeakSobolev` as foundations.

These counts describe the package. They are not a percentage of the paper.
The 44 whole results and 16 narrower results with the manuscript's
hypotheses are deterministic lemmas,
propositions and corollaries used inside the analytic argument, and the
occupation ceiling `T:intrinsic-occupation-ceiling` (a narrower result: both
forms with the exact constant over the class `O` itself, for `S_c^pos`;
`C_2 <= U_2` not formalized);
of the other three main theorems, `T:white-moment-bounds` is a narrower
result (for `S_2^pos` in place of `C_2`, with the energy value of
`P:white-spatial-energy` supplied), and `T:full-upper` and
`T:intrinsic-second-moment` are not formalized.

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

- the proof of `P:mixed` (the named input `MixedMoment`: the Wick formula
  at positive widths, the joint diagram limits of `L:joint-fixed-order` and
  the `L^2` convergence of the chaos series), which would turn the
  diagram-model results of waves L13 and L14 into statements about the
  solution;
- a reusable Laplace-to-time growth lemma, with its analytic inputs as
  hypotheses;
- the constant and exponent algebra of the main upper and lower bounds.
