# Formalization scope

## The paper's argument and where Lean enters

The paper bounds and identifies the growth of `log E[u(t,x)²]` for the
Stratonovich hyperbolic Anderson model. The argument has three layers.

1. **Stochastic and analytic layer.** The chaos expansion of the solution
   (beyond the source-field model M9 of `SourceInterface`, wave L19: a
   centered Gaussian field with the source's positive-width covariance, the
   fixed-order Stratonovich integrals `X_n` as `L^2` limits and the `L^2`
   series `u = sum_n X_n`, which since wave L20 satisfies the mild equation
   `E:mild-construction` (`P:mild-construction`; no uniqueness, and no
   identification with an independently specified solution of the SPDE)), the two-chain
   pairing integrals (beyond the deterministic diagram model `DiagramModel`,
   register entry M4, the label-set model M7 of `PairingInterface`, the
   gap-coordinate Wick-measure model M8 of `WickInterface`, the positive-width
   pairing integrals of M9, and the diagram
   bounds and deterministic diagram limits built on them), Wick pairings (beyond finite families of Gaussian
   values), Gaussian integration (beyond finitely many standard Gaussians and
   the isonormal field of `SourceIsonormal`),
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

So each module checks one reduction in layer 2, except that the wave-L19
modules also construct, in Lean, the source-field series of model M9 (a
slice of layer 1), and wave L20 proves that this series is a mild solution
in the source's sense (`P:mild-construction`, read as `E:mild-construction`;
no uniqueness is asserted, so its identification with a solution of the
SPDE given otherwise stays open). A module's hypotheses state the
facts that layer 1 supplies (for example positivity of a parameter,
integrability of a function, or an inequality proved analytically in the
paper). Its conclusion is the fact that the paper then uses.

## Status of each kind of statement

| Kind | Count | Meaning |
|---|---|---|
| Whole result (ledger heading "whole result"), nothing supplied | 59 labelled results (among them, from wave L20, `P:mild-construction` for every source field of M9 (non-vacuous at `m9`), `P:d1-upper`, `C:d1-first-calibration` (with the conditional rate clause for the constructed solution), `P:low-alpha-upper` and `P:envelope` (with `rho > kappa`), the Riesz instance of `H:homog` in `d = 1` now proved; from wave L19, `P:mixed`, `L:vertex-crude`, `L:joint-fixed-order`, `L:crude-corrected` and `L:white-test`, stated for every source field of the source-field model M9 and non-vacuous at the constructed instance `m9`; from wave L18, `L:spatial-wick-measures` on the gap-coordinate Wick-measure model M8; from wave L17, `L:translated-covariance-CS` and `L:pairing-product-envelope`, the latter on the label-set model M7; from wave L16, `L:positive-raw-embedding`, whose conclusion is full by the author's decision of 2026-11-20: the mean identity for `T_R` and `U` constructed in Lean to meet the frozen specifications, not identified in Lean with the section's maps, `H_I` the kernel completion M5; its theorems sit in narrower-result modules, so it is not among the modules counted here), `H:homog`, `E:kappa`, `E:driver-parameters`, `E:masked-time-schur` and `R:gaussian-one-variance-test`; 49 modules (one of which, `SourceTube`, also holds a whole result with inputs supplied below): 1308 theorems, 282 definitions (public inventory; claims: 1307 theorems and 281 definitions, since `MaskedAuxiliaryReal.Cx.ext_iff`, generated by `@[ext]`, and the syntax constant `WhiteFour.tacticTw_close` have no claim) | Every conclusion of the result is a Lean conclusion under the manuscript's hypotheses (`H:homog` modelled in full; most results via exact-hypothesis wrappers); coverage class same-assumptions, conclusion full |
| Whole result, inputs supplied | 1 labelled result, `P:tube-rayleigh-transfer` (`SourceTube`, wave L12), since wave L21 with one named input from `L:tube-closed-geometry` (`TubeTail`, true for the manuscript's tubes; `TubeAttained`, the second input of wave L12, is proved at the manuscript's tubes by `SourceTubeAttained`, wave L21, and the wrapper `tube_rayleigh_transfer_paper_l21` takes only `TubeTail`); `C:d1-first-calibration`, counted here at the wave-L19 integration, was a narrower result at the L19 gate (the author's decision of 2026-11-22: its conditional rate clause was not stated for the constructed solution) and is a whole result with the manuscript's hypotheses since wave L20; the three results formerly here (`P:radius-mean-anchor`, `P:moment-growth-logconvex`, `C:static-moment-constant-continuity`) are proved for abstract objects whose construction is missing, so they are narrower results | Every conclusion of the result is a Lean conclusion under the manuscript's hypotheses and the named inputs; coverage class inputs-supplied, conclusion full |
| Narrower result (ledger heading "narrower result: ...", naming what is missing) | 22 results with the manuscript's hypotheses and steps, parts or narrower forms of 30 further results; 69 modules and the audit file `HermiteWordFock`: 2106 theorems, 454 definitions | Kernel-checked; some conclusion of the result is not a Lean conclusion. The 22 with the manuscript's hypotheses (coverage same-assumptions, weaker): from wave L21 `L:tube-closed-geometry` (every tube closed, `{d_delta <= r} = T_r` and the lower semicontinuity of `d_delta`, nothing supplied; the Gaussian tail and the almost sure finiteness not formalized), from wave L20 `P:riesz-small` (`E:riesz-two` for the chaos terms of every source field and `E:riesz-four` on M4 with nothing supplied; the multiplicities of `E:total-four` not formalized; `P:envelope` and `P:low-alpha-upper`, narrower at the L19 gate, are whole since wave L20), `P:masked-quotient-obstruction` for the covariance functional (the noise `W` not constructed), the Rayleigh lemma without its application, the dilation lemma for the integral-form cost, `P:variational-unmasked-rate` without its operator half, `L:spatial-static-controls`, `P:spatial-smooth-ratio` and `P:spatial-energy-map` for the Rayleigh-form rate and the integral-form cost, `P:variational-positive-scores` without `Q_2 >= S_2^pos`, `T:intrinsic-occupation-ceiling` with the exact `C_occ` in both forms over the class `O` itself (wave L14), without `C_2 <= U_2`, `C:intrinsic-spatial-bracket` for `S_2^pos` in place of `C_2`, `L:uniform-E-lift` without the lift `L_F` and the complex extension (wave L15), from wave L16 `L:uniform-mean-cutoff` (uniqueness of the multiplier not stated), `P:cameron-temporal-map` (not trace class as the cell sums of decision 7), `L:uniform-mean-tensor` on finite tensors and the map `U` of `P:cameron-full-mean`, `L:occupation-raw-square` over fields modelled by joint representatives (wave L14), `L:positive-physical-gram` without the label row and the entrywise order (wave L14), `L:occupation-rayleigh-selection` for the Rayleigh-form rate and the integral-form cost (over `O` itself since wave L14), and `L:fock-form` (also in operator form, `FockSandwichModel`) and `L:interval-contractions` on a Fourier-side model not identified with the physical-space operators. (`L:damped-homogeneous-norms` and `L:terminal-wick`, narrower until wave L11, are whole results since wave L12 (over M1; `L:damped-homogeneous-norms` over M1 and M3); `P:masked-auxiliary-norm`, `L:variational-global-mean`, `P:spatial-four-linear`, `P:occupation-physical-class` and `P:raw-occupation-energy` since waves L13 and L14.) The 30 further results (coverage inputs-supplied, weaker) have analytic inputs supplied or only some conclusions formalized (`C:d1-first-calibration`, `P:d1-upper`, `P:riesz-small` and `P:mild-construction`, here at the L19 gate, left this class in wave L20): from wave L16 `P:cameron-spatial-map` (`E` part; compactness from the named input `CutoffCompact`) and `P:uniform-mean-regulator` (the regulator constructed with `CutoffCompact`, with the first bound of `E:uniform-completed-mean`; that its mean takes a.e. compact values in the `L(E)`-valued `L^r` model is a separate result; the projection and tail half not formalized), `P:radius-mean-anchor` for abstract random paths (the operator paths `M_R(Y_m)` not constructed), `P:moment-growth-logconvex` and `C:static-moment-constant-continuity` for an abstract moment function (the solution moments not constructed), `L:raw-block-indexed-cone` for an abstract ground family, the finite comparison of `P:masked-noise-completion`, `P:wave-two-variances` with named inputs (spectral core with none), `P:interval-coefficients` with named inputs, `P:variational-remove-mask` (rates with none, the point display over a named input), `L:symplectic-free` (free group and Young convergence supplied), the scalar steps of `L:complex-phase` and `L:interval-complex`, `L:fixed-split` on a finite Fock model (segment bound, Dyson cube identity, invariance of the cross subspaces, entire coefficients and the column bound supplied; the cutoff evolution and its coefficients not constructed), through which `P:interval-coefficients` takes, in place of the input `L:fixed-split`, the inputs of that lemma (and, in place of the added hypothesis `hQ` on `Q_(r,q)` that wave L10 needed, the Duhamel word expansion `DuhamelWords` of the coefficients), `C:static-interaction` with the order bounds and the identification of the interaction map proved (and, on the Fourier-side model of `FockSandwichModel`, the operator form of `E:fock-sandwich`), `T:white-moment-bounds` for `S_2^pos` in place of `C_2` (the energy value of `P:white-spatial-energy` supplied; the time exponent and `c = 0` not formalized), `P:signed-closed-form` (the form bounds and the bounded resolvent of the form for an abstract Hermitian pairing, `E:signed-multiplier-form` supplied as `SignedMultiplierForm`; `H_V`, its domains, `E:signed-quarter-phase`, the dual completion and `L:signed-limiting-multiplier` not formalized), from wave L14 `C:three-product-riesz` and `C:three-finite-images` (moment bounds from `ThreeTransfer`, the statement of `P:three-transfer`, for an abstract model; the asymptotic clause only for a supplied spectral measure of the low endpoint), and the others listed in `coverage.yaml` |
| Foundation or proof steps (ledger heading "foundation: ..." or "proof steps of ...") | 67 modules: 1834 theorems, 571 definitions (public inventory; claims: 1831 theorems and 565 definitions, since the nine anonymous instances of `UniformMeanInterface`, whose names Lean generates (three `CompleteSpace` instances counted as theorems, six definitions), have no claim since wave L15) | Kernel-checked facts used by labelled results, not a labelled result themselves: `WaveKernel`, `SpectralHomog`, `TimeFractional`, `DampedNorms`, `GaussianIBP`, `GaussianTest`, `WeakSobolev`, `VariationalFloor`, `SeriesType`, `H1Density`, `FiniteWick`, `GaussianHermite`, `HermiteFock`, `WaveGreen`, `WaveGreenFourier`, `SpaceTimePositivity`, and the proof steps `IntervalScalar` (the steps of `C:static-interaction`, with `E:static-block-series` in full) `StaticPhaseCauchy` (the Cauchy steps of `P:static-phase-all-orders`) and `FixedSplitCore` (the model-free steps of `L:fixed-split`, with the analytic bounds as premises), whose analytic inputs are supplied, the foundation `WhiteModel` (the white-noise model, `H:homog` with `alpha = d = 1` proved, and steps of `T:white-moment-bounds`), and the proof steps `TerminalWickRegularization` (nothing supplied: the mass and convergence facts of the Green-regularization paragraph of the proof of `L:terminal-wick` are proved for a common-noise construction whose factors are identified with `p_eta * G_h` one at a time; the identification of the whole regularized chain measure with the TeX's product, and the paragraph's last clause, are not formalized; in `d = 3` over the registered model choice M1); from waves L13 and L14 the foundations `DiagramModel` (the diagram model M4, `P:mixed` the named input `MixedMoment`), `DiagramBridge` (its `d = 1` positions form), and `H1Mathlib` (the weak-gradient `H^1` identified with Mathlib's Sobolev space), the control `PhaseShiftControl`, and the proof steps `TwoSimplexTime` and `WhiteCollapse`; from wave L15 the foundations `UniformMeanInterface` (the phase space `H^(1/2) x H^(-1/2)` on the manuscript's Fourier norm, `B_E`, multipliers, and the named inputs `CameronSpatialMap` and `UniformMeanRegulator`) and `UniformMeanFoundation` (density of real tests, duality on tests, multipliers); from wave L16 the foundations `CameronInterface` (the Sobolev scale `H^s`, specifications and statement shapes, the named input `CutoffCompact` and the proved fallback `TemporalCompact`), `CompactOperatorFoundation` (compactness of finite-rank limits, adjoints and `L^2`-kernel operators) and `CameronTemporalSqrt` (compact spectral theorem, positive square roots), and the proof steps `CameronTemporalKernel`, `CameronTemporalYoung` and `CameronTemporalMap` of `P:cameron-temporal-map`; from wave L17 the foundations `PairingInterface` (the label-set two-chain model M7, the statement shapes of the pairing-envelope chain, the fallback named inputs `ConvolutionNorms` and `RegionalHalfBound`, used nowhere) and `GreenSmoothed3` (the density of the Green-smoothed `d = 3` wave kernel), and the proof steps `PairingConvolution`, `PairingRegional` and `PairingCapRemoval` of `L:pairing-product-envelope` and `PairingBridge`, `PairingDampedNorms` and `PairingSmoothedNorms` of `L:crude-corrected` and `P:envelope`; from wave L18 the foundation `WickInterface` (the gap-coordinate Wick-measure model M8, the statement shapes of the wave and the fallback named inputs `SpatialPositiveLaplace`, `WickMassBound`, `SpatialWickWeakLimit` and `JointTemporalTail`, used nowhere), and the proof steps `WickSpectral`, `WickBridge`, `WickMass`, `WickScaling` and `WickStep4` of `L:spatial-wick-measures` and `JointTail` of `L:joint-fixed-order`; from wave L19 the foundations `SourceInterface` (the source-field model M9, the statement shapes of the wave and the fallback named inputs `SourceNoise` and `TerminalReversal`, used nowhere), `SourceIsonormal` (the isonormal Gaussian field, Mathlib only) and `SourceFeatures` (the feature map of the source covariance), and the proof steps `SourceWick`, `SourceReversal` and `SourceMixed` of `P:mixed` and `SourceFixedOrder` and `SourceGreenFirst` of `L:joint-fixed-order`; from wave L20 the foundations `MildInterface` (the mild integral on M9: total fields, the mild measures, `I_(n,a)`, `I_a`, the closed Gaussian polynomial spaces `PolyLE`/`LinG`, the statement shapes of the wave and the fallback named inputs `JointMeasurability` and `TerminalFubini`, used nowhere) and `RieszInstanceOne` (the Riesz instance of `H:homog` in `d = 1`), and the proof steps `MildOccupied`, `MildPolyMem`, `MildFields`, `MildTerminalFubini`, `MildPartialVertex`, `MildGreenWidth` and `MildConstruction` (Steps 5-6 and the assembly, with the item targets as hypotheses; discharged in `MildFinal`) of `P:mild-construction` |
| Checked step fact (`StratonovichHAMAudit/`, except `HermiteWordFock`) | 82 theorems, 6 definitions | Kernel-checked; the ledger gives its paper label and outside inputs |
| of which helper lemmas (`internal`) | 3331 theorems, 317 definitions | Kernel-checked; used inside one module (the nine anonymous instances of `UniformMeanInterface`, whose names Lean generates, are kernel-checked but not claimed since wave L15), or (491 theorems since v0.10.0) compared in the helper configuration `comparator-helpers.json`, a smoke check credited to no manuscript result |
| Other public definitions (in no module subtotal above) | 112 | Named quantities and measures used in the statements (107: 100 `def`, 7 `abbrev`), one structure (`FockColumnBound.L2Map`, a Lean-route data structure), and four instances on `TimeCompletion.Pre`; counted from the elaborated environment, source-written declarations only (no Lean-generated projection, constructor or derived instance). The other seven public definitions without a row or claim, `WhiteFour.tacticTw_close` and the six anonymous instances of `UniformMeanInterface`, are counted in their modules' subtotals above (119 public definitions without a row in all) |
| Negative controls | 68 | Wrong variants that Lean must reject |
| Refutations | 372 | Lean proofs refuting specified variants of declarations: manuscript scalar steps, Lean-route-only constructions, and controls of totalized arithmetic or of broader generalizations (the ledger states each one's domain) |

The theorem and definition counts of the table are public-inventory counts:
theorems 1308 + 2106 + 1834 + 82 = 5330 and definitions 282 + 454 + 571 + 6 +
112 = 1425 (Lean-generated declarations such as the `noConfusion` of
`SourceInterface.SourceModel` not counted). The claims of `claims.yaml` are 5326 theorems (5330 less
`MaskedAuxiliaryReal.Cx.ext_iff` and the three anonymous `CompleteSpace`
instances of `UniformMeanInterface`) and 1306 definitions (1425 less the 112
other public definitions, `WhiteFour.tacticTw_close` and the six other
anonymous instances of `UniformMeanInterface`), 6632 claims in all. The
helper-lemma line counts claims.

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
`d = 1` (`DiagramBridge`) and, for a measurable covariance and Green measures
with a finite jointly measurable density, in every dimension (`PairingBridge.spatial_eq_of_density`, wave L17;
not for the `d = 3` sphere measure); the TeX's joint limit at arbitrary
vertexwise widths is formalized on M8 (wave L18), and M4's common-width limit
follows from its full-kernel limit (temporal width `0`,
`JointFixedOrder.joint_limit_aux`) at common vertex width `eps/2` through the
identity `JointFixedOrder.m8_m4_identity`; the
common-width convergence of the diagrams was the named input `DiagramLimits`
and, with the finiteness of the limits, is a clause of the named input
`MixedMoment` (the statement of `P:mixed`); the diagram limits were proved for
white noise in `d = 1` and the order-two Riesz limit in `RieszFourDiagrams`,
and in wave L18 for every `H:homog` covariance in `d = 1, 2, 3`
(`WickFinal.diagramLimits_homog_l18`; in `d = 1` also by domination,
`RieszDiagramLimits`, `RieszDiagramLimitsHomog`), which discharges
`DiagramLimits`. M5 (wave L14; accepted by the
author on 2026-11-13) realizes `H_t (x) G`, `H_t`, `H_I` and `H_Gamma` as
`L^2` completions under the kernel and covariance forms
(`OccupationCompletion`, `SourceHeatGram`, and the codomain `H_sp` of `Q` in
`ClassOH1`); no tensor identification and no isometry between `H_sp` and
`H_Gamma` is proved. M6 (wave L14; accepted by the author on 2026-11-13) is
`H^1` as the graph of the weak gradient in `L^2 x L^2` (`ClassOH1.H1R`), with
its topology proved equal to that of Mathlib's `H^1`; not proved: that every
real element of Mathlib's `H^1` comes from it. M7 (wave L17, decision 3;
accepted by the author on 2026-11-20) is the label-set two-chain model of
`PairingInterface`: the pairing integrals `I_D(G)` of
`E:pairing-diagram-general` over a label type, chains as lists, the matching
as a finite set of pairs, per-edge data and the norms of the TeX, with a
bridge inequality from M4 (`PairingBridge.m4_bridge`; finite Green
densities, interface amendment 1), not an identification. M8 (wave L18,
decision 6; accepted by the author on 2026-11-21) is the gap-coordinate
Wick-measure model of `WickInterface`: M4's labels and pairings, one gap per
label, the Green measures as in M4, vertexwise spatial widths and vertexwise
temporal widths (Laplace domains `(0, (delta_j v delta_h)^(-1)]` of the Gamma
mixture), the measures `rho_(eps,D)`, `nu_(eps,D)` and the regularized
diagrams `F_(eps,delta,D)`; it is the TeX's own definition in gap
coordinates (a modelling statement, not a Lean theorem), with an identity to
M4 (`JointFixedOrder.m8_m4_identity`: under `H:homog`, for `D in Pi2 m n` and
`t > 0`, M4's diagram at pair width `eps > 0` is M8's at vertex width `eps/2`
and temporal width `0`) and an inequality to M7 (`WickBridge.m8_m7_bridge`:
under `H:homog`, for `D in Pi2 m n`, positive vertexwise widths, a Green
family `G_s = g(s, .) dy` with `g` finite and jointly measurable, measurable
Laplace domains in `(0, infinity)` and damping `theta >= 0`, with the per-edge
data `wickEdge`; `<=` only). M9 (wave L19, decision 2; approved by the
author on 2026-11-21 and fidelity-reviewed before the items that use it) is
the source-field model of `SourceInterface`: the positive-width source fields
of `E:pairing-source-covariance` (main TeX lines 1352-1370) as one real field
`W` on space-time points with a positive width pair, on any probability
space, that is a centered Gaussian field with covariance `srcCov` (the
temporal kernel of M7 and M8 at the cap `delta v delta'`, the spatial
covariance `p_(eps+eps') * Gamma`); results are stated for every such field
(the manuscript's statement, decision 4) and are non-vacuous at the
constructed instance `m9` (an isonormal field on a real Hilbert feature
space, `SourceFinal.source_field_l19`); `Y_n^a` is the `L^2`-valued Bochner
integral over the terminal chain measure, `S_n(g_n)` its limit at common
noise widths (decision 5), `X_n = S_n(g_n)`, `X_0 = 1` and `u = sum_n X_n` in
`L^2` (decision 6). No M4 diagram is realized at positive widths; the
terminal pairing integrals at positive widths are M8 diagrams after the chain
reversal (each pairing integral with the reversed pairing,
`SourceReversal.terminal_reversal`; summed over pairings,
`terminal_mixed_moment`), and M4 enters through the limits and the
regularized diagram bounds. Named inputs of waves L13
to L16 other than `DiagramLimits` and the two wave-L15 data structures (five
listed, three open; with the two of wave L12 below, the named inputs still
supplied after wave L20 were `SignedMultiplierForm`, `ThreeTransfer`,
`CutoffCompact`, `TubeAttained` and `TubeTail`; wave L21 proves `TubeAttained`
(`SourceTubeAttained`), so at the end point the author set on 2026-11-23 four are
left: `SignedMultiplierForm`, `ThreeTransfer`, `TubeTail` and `CutoffCompact`): of waves L13 and L14, `MixedMoment` (`P:mixed`) and
`FirstMomentSeries` (main TeX lines 796, 5856-5857, for
`C:d1-first-calibration`), both discharged in wave L19 for the chaos terms and
solution of every source field (`SourceFinal.mixed_terms_l19`,
`first_moment_series_l19`; the seven consumer wrappers of `SourceFinal` take
neither; the earlier wrappers for abstract random variables, still credited
by the consumer rows, keep them as inputs; the white case of `P:d1-upper`,
which had no source-field form at wave L19, has one since wave L20,
`CleanupWrappers.d1_upper_paper_white_l20`), `SignedMultiplierForm`
(`E:signed-multiplier-form`, with the Hermitian pairing, for
`P:signed-closed-form`) and `ThreeTransfer` (`P:three-transfer`); of wave
L15 (data structures standing for objects the manuscript constructs):
`CameronSpatialMap` (the `E` part of `P:cameron-spatial-map`) and
`UniformMeanRegulator` (`T_R`, `C_t` and `C_t (x) I` of
`P:uniform-mean-regulator`), both constructed in wave L16 from its named
input `CutoffCompact` (the compactness sentence of
`P:cutoff-singular-values`), which stays open; see the ledger Scope. The wave-L13 named input
`DiagramLimits` (the common-width diagram limits of `L:joint-fixed-order`) is
discharged in wave L18 (`WickFinal.diagramLimits_l18`;
`RieszDiagramLimits.coeffALim_riesz_le'` replaces its only standalone use in
the Riesz case); the four fallback named inputs of wave L18
(`SpatialPositiveLaplace`, `WickMassBound`, `SpatialWickWeakLimit`,
`JointTemporalTail`) are used nowhere, their contents proved, and so are
the two fallback named inputs of wave L19 (`SourceNoise`, `TerminalReversal`)
and the two of wave L20 (`JointMeasurability`, `TerminalFubini`).
At the L19 gate the three Riesz consumer rows (`P:d1-upper`, `P:riesz-small`
and the Riesz form of `C:d1-first-calibration`) kept the hypothesis
`hH : HomogCovariance 1 alpha alpha0 (volume.withDensity (riesz c alpha)) mu`
explicit (the author's decision of 2026-11-22). Wave L20 proves that Riesz
instance of `H:homog` in `d = 1` (`RieszInstanceOne.riesz_homogCovariance_one`,
the spectral measure a Gaussian mixture) and states the three rows without it
(`CleanupWrappers.*_closed_l20`); `hH` is no longer a remaining condition. A registered standard choice preserves whole status only when the result's
section names the model (as `LowAlphaConvolution`, `PhaseContractions`,
`L9Completed`, `HigherRieszThree`, `AlphaOneConvolution` and `L10Completed`
do for M1, as `TerminalWickInputs` does for M1 in `L:uniform-series-tail`,
`TerminalWickComplete` for M1 in `L:terminal-wick`, `FiniteWordCutoff` for
M2, `DampedSmoothing` for M1 and M3, `D1Spatial` and `WhiteFour` for M4, `PairingEnvelope` for M7, `WickMeasures` for M8, `SourceVertexCrude`, `SourceExpansion` and `SourceFinal` for M9, `MildFinal` and `CleanupWrappers` for M9 (and M1 in `d = 3`),
`SourceHeatGram` for M5, and `ClassOH1` and `ClassOBridge` for M6; the narrower
section `HigherRieszTwo` and the proof steps `TerminalWickRegularization` also
name M1, which they use in the steps in `d = 3`); a missing construction (the
noise `W`, an abstract ground family, chain measures fixed by their masses,
abstract random paths, an abstract moment function, the cutoff evolution of
`L:fixed-split`, the identification of the Fourier-side model of
`FockColumnBound` and `FockSandwichModel` with the physical-space operators,
the solution and its chaos terms behind `P:mixed` before wave L19, the abstract moment model
of the three-dimensional corollaries) makes the result narrower.
(A) "whole result": every conclusion of the labelled result is a Lean
conclusion under the manuscript's hypotheses, possibly with named supplied
inputs that are disclosed (coverage class same-assumptions or
inputs-supplied, conclusion full; at present every whole result has the
manuscript's hypotheses alone except `P:tube-rayleigh-transfer`, which has two
named inputs, one (`TubeTail`) since wave L21); no other module
carries it. (B) "narrower
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
The 59 whole results and 22 narrower results with the manuscript's
hypotheses are lemmas, propositions and corollaries used inside the analytic
argument (mostly deterministic; among the exceptions `L:terminal-wick` and the
wave-L19 results stated for every source field of the model M9), and the
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

- none planned for the Lean companion: it closes after wave L21 (`TubeAttained`
  proved), the end point the author set on 2026-11-23; `SignedMultiplierForm`,
  `ThreeTransfer`, `TubeTail` and `CutoffCompact` stay supplied. Beyond that
  point:
- a reusable Laplace-to-time growth lemma, with its analytic inputs as
  hypotheses;
- the constant and exponent algebra of the main upper and lower bounds.
