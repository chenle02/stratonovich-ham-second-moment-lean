<div align="center">

# Stratonovich HAM Second Moment: Lean Companion

Lean 4 checks of finite, algebraic and scalar steps in the paper

> Le Chen, *The second moment of the hyperbolic Anderson model* (in
> preparation).

[![Lean](https://img.shields.io/badge/Lean-v4.35.0-153e63)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-56a0058-153e63)](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
[![Release](https://img.shields.io/badge/release-v0.9.0-153e63)](https://github.com/chenle02/stratonovich-ham-second-moment-lean/releases/tag/v0.9.0)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24199105.svg)](https://doi.org/10.5281/zenodo.24199105)
[![License](https://img.shields.io/badge/license-Apache--2.0-153e63)](LICENSE)
[![sorry](https://img.shields.io/badge/library%20sorry-0-153e63)](#verification-record)
[![Axioms](https://img.shields.io/badge/library%20axioms-standard%20only-153e63)](#verification-record)

[What is checked](#what-is-checked) ·
[What is not checked](#what-is-not-checked) ·
[Build](#build) ·
[Architecture](#architecture) ·
[Paper map](#theorem-to-paper-map) ·
[Milestones](#milestones) ·
[Trust](#trust) ·
[Verification record](#verification-record) ·
[Cite](#citation)

</div>

The paper studies the Stratonovich hyperbolic Anderson model with temporal
covariance `|s-t|^(-α₀)` and homogeneous spatial covariance of order `α`.
It shows that `log E[u(t,x)²]` grows on the scale `t^κ`, with
`κ = (4-α-α₀)/(3-α)`, and identifies the limit by a variational formula.

> [!IMPORTANT]
> **This is a partial formalization.** Lean checks the steps listed below. It
> does not check the paper end to end. The SPDE, its solution, the
> Stratonovich integrals, the Gaussian noise and the analytic estimates are
> outside Lean. Where a checked step needs such a fact, the Lean statement takes
> it as an explicit hypothesis, and the paper's proof supplies it.
>
> The correspondence between the Lean statements and the paper was checked by
> **AI correspondence review** (models from a different family than the
> ledger's author), **not by human verification**; see [Trust](#trust).

## At a glance

| | |
|---|---|
| Lean modules | 100 proof modules: 24 step modules in `StratonovichHAMAudit/` and 76 in `StratonovichHAMSecondMoment/` (besides these, the consumer `HermiteWordConsumer`, the axiom report `Axioms` and the umbrella) |
| Labelled results of the manuscript (220) | 25 whole results; 18 narrower results; steps or parts of 30 further results; 3 main theorems outside Lean; 144 not formalized ([COMPLETION.md](COMPLETION.md)) |
| Public declarations | 2050 theorems and 509 definitions; 2468 checked facts in [`claims.yaml`](claims.yaml) |
| Axioms | proof library: only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` (`Challenge.lean`, the comparator's statement file, states each compared theorem with `sorry` by design) |
| Negative controls, refutations, audit files | 68, 235, 101 |
| Pinned toolchain | Lean `4.35.0`, Mathlib `56a0058` |
| Verified state | the wave-L9 gate (development commit `6eb79c7`, manuscript revision `a284420`); the receipts that bind this repository's root commit are added by the commit after it, which the tag `v0.9.0` marks |
| Correspondence to the paper | AI review from a different model family, accepted by the author; not a human verification |

## This release

`v0.9.0` is the first public release. Its tree is the tree of the wave-L9 gate
of the private development repository (development commit `34b65d7`, a
docs-only successor of the verified commit `6eb79c7`), with release
documentation added and the cluster evidence in `verification/` redacted; no
Lean file and no other build input changed. [provenance/DEVELOPMENT.md](provenance/DEVELOPMENT.md) names the
development repository and the commit, and lists every change. Waves L10 to
L14 are in development and not part of this release (see
[COMPLETION.md](COMPLETION.md), "In progress"); `v1.0.0` is planned after they
are gated.

Commit hashes in this README, in [COMPLETION.md](COMPLETION.md), in the
[statement ledger](docs/statement-ledger.md) and in `verification/` are
commits of the development repository.

## What is checked

24 modules in `StratonovichHAMAudit/`, each one step of the paper's proofs
(one of them, `HermiteWordFock`, applies a step to the Fock model and gives
the one-mode special case of a labelled result), and 76 modules in
`StratonovichHAMSecondMoment/`. Counted by labelled result (Theorem,
Proposition, Lemma, Corollary), they give 25 whole results, in which every
conclusion is a Lean conclusion under the manuscript's hypotheses alone; 18
narrower results with the manuscript's hypotheses, each with its missing
part stated; and steps or parts of 30 further results. Counted by module,
the ledger marks 27 modules "whole result", 31 "narrower result" and 18 "foundation" or "proof steps" (the
foundations: a wave-kernel and time-fractional covariance slice with spectral
homogeneity and the damped-norm finiteness, finite Gaussian integration by
parts, a Gaussian Schwartz test, weak gradients and a variational floor,
elementary series bounds, the density of test functions in the
weak-gradient `H^1`, the finite Wick (Isserlis) formula, the normalized
Hermite polynomials and the finite Gaussian Fock layer, the wave Green
measures and their Fourier transforms, the integral-form space-time
occupation identities, and the proof steps of the static interaction,
interval coefficient and static phase bounds).

<details>
<summary><b>With the paper's own hypotheses, nothing supplied</b> (list)</summary>

- **With the paper's own hypotheses, nothing supplied** (most via
  exact-hypothesis `_paper` wrapper theorems; whole results, and narrower
  results whose missing part is stated in parentheses):
  - `L:gaussian-scalar-powers` (weighted AM-GM, finite Hölder,
    `E Z^r <= (E Z)^r`);
  - `L:gram-scalar-algebra`;
  - `L:tube-rayleigh-tail` (a Gaussian tail integral bound; its "In
    particular" application excepted);
  - `L:equilibrium-gamma-beta` (Gamma and Beta identities);
  - `L:temporal-equilibrium` (the equilibrium density of the temporal
    kernel, its potential identity on `[0,1]` and its mass);
  - `L:gaussian-trace-bounds`, `P:finite-gaussian-matrix` and
    `R:gaussian-one-variance-test` (moments of finite Gaussian matrix
    series; the finite part of the compact Gaussian section);
  - `E:kappa` (`1 < κ < 2`) and `E:driver-parameters`, under Hypothesis
    `H:homog` modelled in full in Lean (covariance and spectral measures,
    positive-definiteness, scaling).
  - `L:variational-control-dilation` (the dilation of controls and the
    scaling of mean, cost and rate), for the cost in its integral form and
    the rate defined by its Rayleigh characterization; their identification
    with the expectation and the spectral bottom is not formalized.
  - `L:variational-heat-envelope` (the Gaussian envelope of the covariance)
    and `L:variational-global-mean` (bounds and time-Lipschitz bound of the
    original mean; the bounds on every mixed derivative are not
    formalized).
  - `P:masked-spectral-growth` (the translated spectral mass and the ball
    bound); the homogeneity of the spectral measure is derived from
    `H:homog`.
  - `P:masked-auxiliary-norm` (the auxiliary measure `nu_R` is even,
    tempered and Radon with ball bounds uniform in `R`, and the
    Hilbert-valued Fourier bound `E:masked-hilbert-fourier`, proved for any
    complex Banach space; the clause for a real `H` after complexification
    is not formalized).
  - `P:clock-copy-obstruction` (analytic clocks cannot copy the cross-pair
    time transform: `0 < J <= J_1 < K`, and `J_1 = (2 - 2^a) K` when
    `alpha = 1`).
  - `L:masked-time-completion` (the temporal completion `H_a`, built as the
    completion of `L^2(0,T)`: positive semidefinite, separable, the Schur
    bound `E:masked-time-schur`, the continuous extension, the complexified
    norm, interval amplitudes, and density of the real compact smooth
    tests), and `L:masked-temporal-modulation` (the modulation bound);
  - `L:masked-trig-products` and `L:masked-continuous-wave` (the
    trigonometric products and the continuous sine factors `c_r, b_r`,
    `||1_I F_r G_rho||_a^2 <= C_1(a)(1+T)^4 h^(2-a) Q_h(r,rho)` with the
    paper's `C_1`, in that `H_a`).
  - `P:frequency-row` and `C:frequency-time` (the uniform scalar row
    `sup_xi J_h(xi) <= K C B_alpha(h)` with `K` chosen before
    `d, nu, C, h`, and its time exponent above one half).
  - `L:occupation-kernel-row` (the damped occupation kernel and its exact
    row maximum `R_star`) and `L:spatial-physical-pair` (the physical pair
    measure is sigma-finite and the pairing does not depend on the
    representatives).
  - `L:phase-bessel` (the Hilbert-valued finite Bessel inequality and its
    conjugated version; proved for any measure space and any complete
    complex inner product space, without a basis).
  - `L:damped-homogeneous-norms` (the damped norms: finiteness, scaling
    `N_0 = theta^(-2)`, `N_1`, `N_2^2`, temporal tails, and the
    multiplier comparison `E:damped-multiplier-comparison` (both bounds, for
    a general measurable multiplier in `[0,1]` and Laplace domains, and the
    remarks on Gaussian smoothing in a narrower form: the Gaussian
    multipliers belong to the class, without the spectral identification of
    the smoothed covariance; the `N_0` mass identity; Green smoothing as a
    Fourier multiplier, identified with the damped norm in `d = 1, 2, 3`
    by `damped_homogeneous_norms_fourier_one` and
    `WaveGreenFourier.damped_homogeneous_norms_fourier_wave`);
    the wave Green measures `G_s`, `d = 1, 2, 3`, are built
    with mass `s`, support in the closed `s`-ball and scaling
    `G_s(sA) = sG_1(A)`; in `d = 3` Mathlib's sphere measure is taken as
    the surface measure, registered model choice M1: its identification
    with the surface measure of the TeX is not proved). Their Fourier transforms
    `G_s hat(xi) = sin(s|xi|)/|xi|` in `d = 1, 2, 3` and Archimedes' law for
    the sphere measure are proved as reusable facts.
  - (Model-choice register, kept in the ledger Scope: a registered standard
    definitional choice, recorded with the identification that is not
    formalized, keeps a result whole only when its section names the model;
    a missing construction makes a result narrower. The only entry is M1,
    the `d = 3` wave Green measure via Mathlib's `volume.toSphere`, whose
    identification with surface measure is not proved; the two whole
    results below use it.)
  - `L:low-alpha-convolution` (the radial mass `mu(B_r) = r^alpha V` and the
    convolution bound for the wave Green measures smoothed by `N(0, eta I)`,
    `d = 1, 2, 3`, `alpha < 1`, with integrability).
  - `L:phase-contractions` (`E:phase-resolvent`, `E:phase-trace` and the
    Fourier form of the trace, under the standing assumptions of the
    static-phase section, and under `H:homog` in `d = 3`).
  - `P:masked-quotient-obstruction` (a physical mask need not preserve
    noise-null tests: for `Gamma = delta_0(dx_1) dx_2`, which Lean proves
    satisfies `H:homog` with `alpha = 1`, a smooth compact mask `zeta` and
    a test `F` with `E W(F)^2 = 0 < E W(zeta F)^2`; `E W(F)^2` is read as
    the covariance functional of `E:cov`; narrower: the noise is not
    constructed, so the identification with noise variances is not
    formalized).
  - `P:variational-unmasked-rate` (its Rayleigh-form part: a uniform
    positive floor, the Lipschitz bounds and `0 < I_Psi < infinity`; the
    operator statements, including `lambda = sqrt(-E_s)`, are not
    formalized).
  - `L:spatial-static-controls` (the smooth temporal controls:
    `lambda_z(c)^2` finite and positive, `lambda_z` Lipschitz on positive
    intervals, the static score bound) and
    `P:spatial-smooth-ratio` (`R_0` positive and finite, by the
    deterministic Fourier bound `L:spatial-fourier-bound`, as in the
    manuscript, without `T:full-upper`, and the smooth score bound); both
    score bounds in an existential form and as bounds on the supremum
    `S_1^pos`, whose finiteness is proved (`P:variational-positive-scores`
    below).
  - `L:spatial-fourier-bound` (`b > 0` and
    `0 <= A_sp(g) <= 2^(1+alpha) R b^(alpha/2)` for every covariance of
    `H:homog`, including zero and singular ones; with the manuscript's
    constant `R_alpha`, proved equal to the resolvent
    `int mu(dxi)/(1+|xi|^2)`).
  - `L:positive-series-type` (the type of a positive coefficient series:
    `tau = nu K^(1/nu)` in both directions).
  - `C:white-relative-width` (the relative width of the white-noise bound
    formulas `K_0(a)` and `M_a`; the bounds on `C_2` themselves,
    `T:white-moment-bounds`, stay outside Lean) and `L:white-clock-laplace`
    (the cross-pair and self-pair Laplace transforms of the white-space
    falsification case, with the side condition `eta_1, eta_2 > 0` made
    explicit).
  - `L:inventory-product` (the coefficient bound `C^k/(k!)^nu` for the
    interval inventory product, with an explicit constant `C` depending
    only on `alpha, alpha0`).
  - `P:spatial-four-linear` (the physical four-linear extension on `H^1`:
    `A_sp(f) <= R_0 N(f)^4`, the square Cauchy-Schwarz inequality, absolute
    convergence and `E:spatial-four-linear`, multilinearity and joint
    continuity of `C_4` in sequential form, `R_sp = R_0` and `A_sp > 0`)
    and `P:spatial-energy-map` (`E_sp = (2-alpha)/2 alpha^(alpha/(2-alpha))
    R_sp^(2/(2-alpha))` in `(0, infinity)`; the static energy score bound
    in an existential form and as a bound on `S_1^pos`);
    the density of test functions in `H^1` that both proofs use is proved
    (`H1Density`).
  - `P:occupation-physical-class` (the full physical occupation class: the
    pairings `B_Gamma(g_s^2, g_t^2)` are a.e.-measurable and do not depend
    on the representatives, `J(g) <= R_star R_sp T(g)^(alpha/2) < infinity`,
    and `0 < E_star^O <= R_star^(2/(2-alpha)) E_sp`; the class `O` is
    modelled by jointly measurable representatives of `g` and `grad g`
        instead of strongly `H^1`-measurable fields).
  - `P:variational-positive-scores` (everything except `Q_2 >= S_2^pos`:
    the value sets are nonempty and bounded above, `S_c^pos` is finite,
    positive and equal to `c^((4-alpha)/(3-alpha)) S_1^pos`; the boundedness
    is proved deterministically from the occupation ceiling, not by the
    manuscript's stochastic argument).
  - `P:raw-occupation-energy` (`A(g)`, `C_occ` and `E_zeta^O` defined,
    `0 < C_occ <= K_0 R_sp`, the dilation identities and both displays) and
    `L:occupation-rayleigh-selection` (near-optimal occupation fields, by a
    finite-cell field of real unit tests), over the class `O` modelled by
    joint representatives.
  - `T:intrinsic-occupation-ceiling` (`c I_Psi - v_Psi/2 <= U_c` and
    `S_c^pos <= U_c` for every `c > 0`, both forms with the exact `C_occ`;
    `O` modelled by joint representatives; `C_2 <= U_2` not formalized; the
    form with the larger constant `K_0 R_sp` also remains) and
    `C:intrinsic-spatial-bracket` (the bracket and the strict comparison for
    the variational value `S_2^pos` in place of `C_2`, with the exact
    `E_(1/2)^O` in the comparison).
  - `L:positive-raw-embedding` (the variance identity in integral form, the
    row bound `int_I |s-t|^(-a) dt <= K_0` and the scalar Schur bound; the
    Hilbert spaces `H_t`, `H_I` are not built). The integral identities used
    by `L:occupation-raw-square` are proved for continuous compactly
    supported fields, a class different from the lemma's, and its final
    display also for finite-cell fields; neither is counted.

</details>

<details>
<summary><b>Parts of further results</b> (selected results; every labelled result and its status is in <a href="COMPLETION.md">COMPLETION.md</a> and <a href="coverage.yaml">coverage.yaml</a>)</summary>

- **Parts of further results**:
  - `P:radius-mean-anchor` (for abstract random paths, with the moment
    bound of the operator paths supplied; the operator paths `M_R(Y_m)` and
    the residual noises are not constructed);
  - `P:moment-growth-logconvex` (log-convexity and continuity of the upper
    growth rate in the temporal exponent) and
    `C:static-moment-constant-continuity` (recovery of the static moment
    constant as `a -> 0+` and the ratio limit `2^(kappa_st)`), both for an
    abstract moment function, with the full-moment coefficient series and
    its interpolation, the static law, the static minorant, the full upper
    bound and Cauchy-Schwarz supplied; the solution moments are not
    constructed;
  - `L:raw-block-indexed-cone` (the cone induction behind the block
    lower bound, every conclusion for an abstract ground family supplied as
    one hypothesis structure; its identification with the physical wave
    family of the compact mean family is not formalized);
  - `L:uniform-series-tail` (uniform term and tail bounds and the `L^2`
    regularization limit from a uniform scaled second moment, for an
    abstract `L^2` family; the absolute convergence and the nonnegative
    mixed moments it takes from `L:terminal-wick` are proved in Lean for
    nonnegative covariance with the chain measures fixed only by their
    masses, so the identification with the terminal-chain terms is not
    formalized);
  
  - `P:wave-two-variances` (both variance directions in spectral form,
    uniform in `R`, `I` and the family, and its `h^(2 beta)` form, with no
    input; the statement for `E|l_R|^2` takes
    `E:variance-normalized-covariance` and the isometry `J` as named
    inputs);
  - the finite Gaussian comparison of `P:masked-noise-completion`
    (`E N(X)^p <= E N(Y)^p` for `X ~ N(0,A)`, `Y ~ N(0,B)`, `A <= B` in
    positive semidefinite order, any seminorm, `p >= 1`; the noise
    statements of that proposition are not formalized);
  - the facts about the wave Green measures quoted in the proof of
    `L:higher-riesz`, and the Cauchy, scalar and series steps of
    `P:static-phase-all-orders` (both displays for abstract Banach-space
    quantities; the circle bound, entireness in the coupling, the
    coefficient identification, the norm comparisons, the cutoff removals
    and the free bound supplied);
  - the scalar and Hilbert-space steps of `C:static-interaction`
    (`E:static-block-series` in full; the order, parity and first-variance
    bounds and the per-block bound supplied) and of
    `P:interval-coefficients` (the assembly of the coefficient bound from
    the energy-split identity and `L:fixed-split` as supplied inputs, with
    `L:inventory-product` proved in Lean, and the summation to the phase
    bound);
  - `P:variational-remove-mask` (the masks and every rate statement with
    nothing supplied; the point lower bound from the supplied original
    point bound of `P:raw-block-original-lower`);
  - `L:terminal-wick` (the Bochner integrals, the majorant
    `E:terminal-term-majorant`, the Wick formula with nonnegative pairing
    integrals, the comparison per mixed moment and absolute convergence,
    for real `r`; the `L^2` strong measurability of the field products is
    supplied, the chain measures enter by their total masses
    `T^(2n)/(2n)!`, and the Wick formula adds a hypothesis the lemma does
    not make, joint measurability of the covariance);
  - `L:symplectic-free` (both compact-baseline displays on an abstract
    Hilbert space, with the free group, reversal and translations and the
    convergence of the left Young sums supplied; the per-frequency
    symplectic identity and the force skewness);
  - `L:fock-form` and `L:interval-contractions` (the Gaussian cutoff bound
    `d_N rho^(alpha/2-2)` and its symmetry on the Hermite-degree cutoff, the
    band compression, the vacuum phase insertion and `E:interval-fock`, from
    the spatial column bound and `E:interval-column` as supplied inputs, for
    the multiplied Gaussian coordinates), and the finite-coordinate
    multiplication bound `E:occupied-multiplication` of the proof of
    `P:mild-construction`;
  - `L:complex-phase` and `L:interval-complex` (the numerical-range, scalar
    and Banach-algebra steps with nothing supplied; the operator bounds from
    Crouzeix-Palencia and the inverse-root integral representation as
    supplied inputs; the phase propagator itself is not formalized);
  - `L:finite-word-cutoff` (exact cutoffs for finite Gaussian words, with
    nothing supplied, but only for one Gaussian coordinate per color, in
    normalized Hermite coefficients; the lemma's several modes per color and
    the sentence on finite sums and Bochner integrals of words are not
    formalized).

</details>

Counts:

- **2050 public theorems** and **509 public definitions**. All 2050
  theorems (1203 reusable, 847 helper lemmas) and 418 of the definitions are
  the checked facts listed in `claims.yaml`.
- Every public declaration of the proof library depends only on Lean's
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no
  `sorry` in it; `Challenge.lean`, the comparator's statement file, restates
  each compared theorem with `sorry` by design (see Verification record).
- **68 negative controls** in `controls/`. Each one states a wrong variant
  (a wrong constant, sign or range, or a dropped hypothesis), and Lean must
  reject it for a mathematical reason. They show the checked statements are
  sharp enough to exclude the plausible mistakes.
- **235 refutations** in `refutations/`, which go further: each one is a Lean
  proof that a specified variant of a declaration is false: a manuscript
  scalar step, a Lean-route-only construction, or a control of totalized
  arithmetic or of a broader generalization (the ledger states each one's
  domain).
- **101 audit files** in `Audit/`, which print the full types and axioms of
  the public declarations and run consumer examples.

Typical content: parameter ranges for `κ` and related exponents, exact
rational and square-root inequalities, polynomial positivity certificates,
small matrix identities, finite counting of Hermite-word coefficients, and
integral comparisons whose integrability inputs are hypotheses.

The [statement ledger](docs/statement-ledger.md) maps each declaration to the
manuscript label it supports, says what it states, and names the inputs that
stay outside Lean. [FORMALIZATION.md](FORMALIZATION.md) gives the overall
scope.

## What is not checked

- the existence, uniqueness and chaos expansion of the solution;
- Stratonovich integrals, Wick pairings beyond finite families of Gaussian
  values, and the Gaussian noise measure (only finitely many independent
  standard Gaussians, the finite-dimensional centered Gaussian laws of
  `GaussianComparison`, the finite Wick formula of `FiniteWick` and the
  finite Hermite and Fock layer of `GaussianHermite` and `HermiteFock` are in
  Lean);
- the imported bounds from the earlier literature;
- the Laplace-transform-to-time growth conversion and the variational
  asymptotics;
- three of the 35 development modules: normalized Gaussian coordinates,
  vector Gaussian projection and colored vector words. They depend on a
  Gaussian-chaos Lean library that is not yet public. Their 9 facts were
  checked in the private development record but **cannot be reproduced from
  this repository**, and nothing here relies on them. They will be added
  when that library is released.

## Build

Requires [elan](https://github.com/leanprover/elan). Pinned: Lean `4.35.0`,
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Transitive pins are in
`lake-manifest.json`; do not run `lake update` for a routine build.

```sh
lake exe cache get        # Mathlib build cache
lake build                # all 100 modules (umbrella: StratonovichHAMSecondMoment)
lake build StratonovichHAMSecondMoment.Axioms   # axioms of every public declaration
scripts/check-controls.sh # all negative controls must be rejected
```

To use one step, import its module, for example
`import StratonovichHAMAudit.MiddleCross`.

To use the companion as a Lake dependency:

```toml
[[require]]
name = "stratonovich-ham-second-moment-lean"
git = "https://github.com/chenle02/stratonovich-ham-second-moment-lean"
rev = "v0.9.0"
```

## Architecture

| Path | Contents |
|---|---|
| `StratonovichHAMAudit/` | the 24 step modules |
| `StratonovichHAMSecondMoment/` | the 76 library modules (whole results, narrower results, foundations and proof steps) |
| `StratonovichHAMSecondMoment.lean` | umbrella module importing all of them |
| `StratonovichHAMSecondMoment/Axioms.lean` | `#print axioms` for every public declaration |
| `controls/` | negative controls, one directory per module |
| `refutations/` | Lean proofs refuting specified variants of declarations: manuscript scalar steps, Lean-route-only constructions, and controls of totalized arithmetic or of broader generalizations (the ledger states each one's domain) |
| `Audit/` | full-type and axiom printouts and a consumer example for each proof module |
| `claims.yaml` | the checked facts, with summaries |
| `docs/statement-ledger.md` | manuscript label to Lean declaration map |
| `provenance/manuscript-anchor.json` | SHA-256 of the manuscript revision the labels refer to, and of each Lean source |
| `verify.sh` | the build-and-axiom check used for verification records |
| `coverage.yaml` | one row per covered manuscript result, with its coverage class and the exact scope of the conclusion |
| `docs/coverage-scope-tex.yaml` | LaTeX versions of the coverage scope sentences |
| `comparator.json`, `Challenge.lean`, `Solution.lean`, `ChallengeDefs/` | the comparator tier: every theorem claim restated in `Challenge.lean` and proved from the project in `Solution.lean` |
| `scripts/` | the negative-control runner and the comparator scaffolding |
| `COMPLETION.md` | milestones and the status of every labelled result |
| `.lean-receipts/` | lean-pkg receipts (lower tier and comparator) |
| `verification/` | external-kernel replays and the Slurm receipt pilot on the Easley cluster |
| `provenance/DEVELOPMENT.md` | the development repository, the release commit and what changed |

## Theorem-to-paper map

- [docs/statement-ledger.md](docs/statement-ledger.md): every Lean
  declaration, the manuscript label it supports, what it states, and the
  inputs that stay outside Lean.
- [COMPLETION.md](COMPLETION.md): the status of each of the manuscript's 220
  labelled results, with its TeX file and line.
- [coverage.yaml](coverage.yaml): the coverage class and conclusion scope of
  every covered result.
- [FORMALIZATION.md](FORMALIZATION.md): the overall scope.

Manuscript labels and TeX line numbers refer to the revision recorded in
[provenance/manuscript-anchor.json](provenance/manuscript-anchor.json).

## Milestones

Each milestone is the commit where the author closed a gate. The milestone
tags (`L0-companion-created`, `ledger-gate`, `L1-gate` ... `L9-gate`,
`reanchor-975feb3`) live in the private development repository and are listed
with their commits in [COMPLETION.md](COMPLETION.md); this repository carries
only the release tag `v0.9.0`.

| Tag | Commit | Date | Manuscript | Claims | Theorems | Coverage rows (same / inputs / outside) | Milestone |
|---|---|---|---|---|---|---|---|
| `L0-companion-created` | `38d1616` | 2026-11-09 | `cf979d6` | 88 | 82 | 25: 21 inputs-supplied, 4 outside | companion created and registered; 23 Mathlib-only seams; lean-pkg verified-private |
| `ledger-gate` | `48ce162` | 2026-11-10 | `ba01d98` | 88 | 82 | 28: 24 / 4 | statement-ledger correspondence gate closed by the author |
| `L1-gate` | `b876362` | 2026-11-10 | `ba01d98` | 117 | 104 | 28: 5 same / 19 inputs / 4 | wave L1: five labelled results in full; H:homog modelled |
| `L2-gate` | `79afdde` | 2026-11-10 | `ba01d98` | 223 | 188 | 29: 7 / 18 / 4 | wave L2: S:temporal-equilibrium, P:radius-mean-anchor, L:masked-trig-products |
| `L3-gate` | `dfc2fe8` | 2026-11-10 | `3920258` | 557 | 470 | 33: 11 / 18 / 4 | wave L3: control dilation, indexed cone, clock-copy obstruction, finite Gaussian slice |
| `L4-gate` | `ac6f767` | 2026-11-11 | `3920258` | 724 | 611 | 40: 20 / 16 / 4 | wave L4: masked spectral growth, time-Schur, frequency row, occupation kernel row |
| `reanchor-975feb3` | `d40f394` | 2026-11-11 | `975feb3` | 724 | 611 | 40: 20 / 16 / 4 | re-anchor to manuscript 975feb3 (zero-covariance remark), narrow re-check accepted |
| `L5-gate` | `712c307` | 2026-11-11 | `975feb3` | 972 | 810 | 46: 26 / 16 / 4 | wave L5: H_a completion, masked continuous wave, auxiliary norm, damped norms, heat envelope, phase Bessel |
| `L6-gate` | `bfa2fd0` | 2026-11-11 | `975feb3` | 1463 | 1210 | 59: 34 / 21 / 4 | wave L6: wave Green measures, quotient obstruction, two variances, variational floor and rate, spatial ratio, static controls, series type, white width |
| `L7-gate` | `f3be834` | 2026-11-12 | `a284420` | 1731 | 1430 | 67: 39 / 24 / 4 | wave L7 (inventory product, series tail, H^1 density, four-linear, occupation class, interval/static steps) and re-anchor to a284420 |
| `L8-gate` | `aff7409` | 2026-11-12 | `a284420` | 2108 | 1747 | 71: 43 / 25 / 3 | wave L8 (spectral mass identity, damped-norm lower bounds, space-time positivity, finite occupation ceiling, spatial bracket, mask removal, finite and terminal Wick, symplectic free group, static phase Cauchy-Schwarz; S1Bdd proved) |
| `L9-gate` | `6eb79c7` | 2026-11-12 | `a284420` | 2468 | 2050 | 80: 47 / 30 / 3 | wave L9 (low-alpha convolution in d = 1, 2, 3 and phase contractions in d = 3 with nothing supplied, wave Green Fourier identities, complex phase scalar steps, exact occupation ceiling C_occ, Gaussian Hermite polynomials, Fock layer and Fock form, one-mode finite word cutoff) |

## Trust

A successful build checks that the proofs are correct for the statements as
written in Lean. Whether a Lean statement says what the paper needs is a
separate question. The statement ledger answers it row by row and is meant
to be read next to the paper. Lean does not check that correspondence.

**Correspondence review, in short.** Each wave's ledger rows were reviewed
against the manuscript by AI models from a different family than the ledger's
author, and the author accepted every wave, the last at the wave-L9 gate. The
full record follows.

<details>
<summary><b>Correspondence review record, wave by wave</b></summary>

**Correspondence review.** The statement ledger at commit `48ce162`, read
against manuscript revision `ba01d98`, has passed independent
correspondence review: every one of its 88 rows was checked with complete
reading of the cited manuscript sources, every finding was resolved, and
the author accepted the result on 2026-11-10. The 29 rows added since then
for the `StratonovichHAMSecondMoment` modules (including the Lean model of Hypothesis
`H:homog`) passed a separate sequence of three independent reviews at
commit `b876362`, against the same revision; the author accepted it on
2026-11-10. The 106 rows added for the wave-L2 modules
(`TemporalEquilibrium`, `RadiusMeanAnchor`, `MaskedTrigProducts`) passed
three independent reviews and a confirmation review at commit `79afdde`,
against the same revision; every finding was resolved, and the author
accepted the result on 2026-11-10. The 334 rows of wave L3
(`VariationalDilation` with `WeakSobolev`, `IndexedCone`, `ClockCopy` with
its foundation, `FiniteGaussianMatrix` with `GaussianIBP`) passed four
independent reviews, whose findings were all repaired, and a confirmation
review, at commit `dfc2fe8` against manuscript revision `3920258`; the
author accepted the result on 2026-11-10. After wave L3, 347 declarations
mapped to a manuscript label and 210 checked computations with no direct
label. The 167 rows of wave L4 (`GaussianTest`, `MaskedSpectralGrowth`,
`ClockCopyHomog`, `TimeSchur`, `MaskedModulation`, `FrequencyRow`,
`OccupationKernelRow`; totals now 419 labelled and 305 unlabelled), and the
changes wave L4 made to existing ledger sections and coverage rows
(`P:clock-copy-obstruction`, `L:damped-homogeneous-norms`,
`L:masked-trig-products`), passed four independent reviews, whose findings
were all repaired, and a confirmation review at commit `ac6f767`, against
manuscript revision `3920258`; the author accepted the result on
2026-11-11. The ledger was then re-anchored to manuscript revision
`975feb3`, which adds a remark that `H:homog` allows zero covariance and
qualifies a strict comparison in `T:first` (not cited here), and moves TeX
line numbers; a narrow independent review of the rows that depend on
`H:homog` and of the re-anchor passed at commit `d40f394` with no findings;
the author accepted it on 2026-11-11. The 248 rows of wave L5
(`TimeCompletion`, `MaskedContinuousWaveCompleted`, `MaskedContinuousWave`,
`MaskedAuxiliaryNorm`, `DampedNormsHomog`, `VariationalMean`,
`PhaseBessel`; totals now 535 labelled and 437 unlabelled), and the changes
wave L5 made to existing ledger sections and coverage rows, passed six
independent reviews, whose findings (all in the documentation) were
repaired, and a confirmation review at commit `712c307`, against manuscript
revision `975feb3`; the author accepted the result on 2026-11-11. The 491
rows of wave L6 (`WaveGreen`, `QuotientObstruction`, `GaussianComparison`,
`WaveTwoVariances`, `VariationalFloor`, `VariationalRate`,
`SpatialFourierBound`, `SpatialSmoothRatio`, `SpatialStaticControls`,
`SpatialOccupationCompleted`, `SeriesType`, `TypeContinuity`,
`WhiteRelativeWidth`, `WhiteClockLaplace`; totals now 737 labelled and 726
unlabelled), and the changes wave L6 made to existing ledger sections and
coverage rows, passed eight independent reviews, whose findings (all in
the documentation) were repaired, and a confirmation review, whose one
finding (a stale doc comment) was repaired; a narrow re-confirmation of
that repair passed at commit `bfa2fd0`, against manuscript revision
`975feb3`, with no findings; the author accepted the result on 2026-11-11.
The 268 rows of wave L7 (`InventoryProduct`, `UniformSeriesTail`,
`H1Density`, `SpatialFourLinear`, `OccupationPhysicalClass`,
`IntervalScalar`, `IntervalScalarCompleted`,
`SpatialOccupationL7Completed`), and the changes wave L7 made to existing
ledger sections and coverage rows, passed six independent reviews at commit
`a8fb495` against manuscript revision `975feb3`, whose findings (one fatal,
a wrong plain-English description of the rate lambda as the Rayleigh
supremum instead of its square root; one major; seven minor; all in the
documentation) were repaired, and a confirmation review, whose two remaining
documentation findings were repaired with the re-anchor below. The ledger was then re-anchored
to manuscript revision `a284420`, which adds Lemma `L:spatial-fourier-bound`
(the deterministic bound of `SpatialFourierBound`, now used by the
manuscript for `R_0 < infinity` in `P:spatial-smooth-ratio`) and replaces
the smoothing sentence of `L:damped-homogeneous-norms` by the multiplier
comparison `E:damped-multiplier-comparison`; TeX line numbers moved, the
rows for both edited results were rewritten and a coverage row was added for
`L:spatial-fourier-bound` (totals now 891 labelled and 840 unlabelled). A
narrow independent review of the re-anchor and of the rows of the two edited
results found four documentation findings, among them wrong TeX line
locators caused by file misattribution; all 1781 affected citations were
then checked against the TeX and 46 corrected, and a confirmation review
passed at commit `f3be834`, against manuscript revision `a284420`, with no
findings; the author accepted wave L7 and the re-anchor on 2026-11-12
(gate closed at `f3be834` over manuscript revision `a284420`). The 377
rows of wave L8 (`SpectralMassIdentity`, `DampedMultiplier`,
`SpaceTimePositivity`, `OccupationCeilingFinite`, `SpatialBracket`,
`RemoveMask`, `FiniteWick`, `TerminalWick`, `SymplecticFree`,
`StaticPhaseCauchy`, `L8Completed`; totals now 1122 labelled and 986
unlabelled) and the changes wave L8 made to existing ledger sections and
coverage rows passed six reviews at commit `3518233` (documentation
findings only, no Lean error, all repaired in two rounds: among them the
global measurability of the covariance in `L:terminal-wick` is now recorded
as an added restriction, and the smoothing scope of
`L:damped-homogeneous-norms` states both gaps), a confirmation review and a
re-confirmation, which passed with high confidence at commit `168b3c0`; the
author accepted wave L8 on 2026-11-12 (gate closed at `aff7409` over
manuscript revision `a284420`, with the chain measures of `L:terminal-wick`
supplied through their mass and that added restriction recorded). The 360 rows of wave L9
(`WaveGreenFourier`, `LowAlphaConvolution`, `PhaseContractions`,
`RawOccupationEnergy`, `OccupationCeilingExact`, `ComplexPhaseScalar`,
`GaussianHermite`, `HermiteFock`, `FockForm`, `HermiteWordFock`,
`L9Completed`; totals now 1300 labelled and 1168 unlabelled after the review repairs) and the changes
wave L9 made to existing ledger sections and coverage rows were reviewed in
eight correspondence reviews and the documentation was repaired over several
rounds (the strict "whole result" convention, the split modelled-object rule
with a model-choice register, and the Index as a pointer table, all decided
by the author), with a final confirmation at commit `ff40fde` (among
other changes, `L:damped-homogeneous-norms` keeps a narrower conclusion and
`L:finite-word-cutoff` counts as formalized in part, for one Gaussian mode
per color); the author accepted wave L9 on 2026-11-12 (gate closed at
`6eb79c7` over manuscript revision `a284420`). These
reviews were done by AI
models from a different family than the ledger's author; they are not a
human verification, and they do not check the analytic inputs that stay
outside Lean. A later change to the ledger or to a cited label needs a new
review.

</details>

## Verification record

**This repository.** A receipt names the commit it binds, so the receipts
for this repository's root commit cannot be part of that commit: a lower-tier
receipt and a comparator receipt are cut at the root commit and added, with
nothing else, by the commit after it, which the release tag `v0.9.0` marks.
They are the files in `.lean-receipts/` whose 12-hex prefix is the root commit
(`git rev-list --max-parents=0 HEAD`). The other receipts in `.lean-receipts/`
bind commits of the development repository and are kept as development
evidence.

**Development record.**

Commit `6eb79c7` (the wave-L9 gate) has both lean-pkg receipts in
`.lean-receipts/` (earlier commits have their own): a lower-tier receipt (a
fresh build of all modules and the axiom report, 0 `sorry`, only the standard
axioms, and the axioms of all 2468 claims read from the built environment)
and a comparator receipt (Palomar's toolchain mechanism): every one of the
2050 theorem claims is
judged against its own restatement in `Challenge.lean`, whose types are
checked to be equal to the claimed declarations' by
`scripts/comparator/CheckFidelity.lean`. With both, `lean-pkg claims ledger`
reports no open claim. Later commits that change only documentation stay
bound to it. A receipt records the build and the statements'
self-consistency; it does not by itself establish that the statements
match the paper (see Trust).

Independent external-kernel replays on the Easley cluster ran
`leanchecker --fresh` (which also re-checks every imported Mathlib
declaration) on each module separately, in three gates: commit `837778a`
(35 targets), `687e631` (12 wave-L3 targets) and `2f5ee14` (17 targets).
All 64 runs pass. Together they cover every one of the 51 library modules
and the umbrella at a commit where that module and all its imports are
identical to `2f5ee14` (`verification/leanchecker-easley-2026-11-10/`,
`verification/leanchecker-easley-wave-l3/`,
`verification/leanchecker-easley-wave-l4/`). The three comparator-tier
libraries (`ChallengeDefs`, `Challenge`, `Solution`), which the umbrella
does not import, were not replayed. The Lean sources of the modules
covered there are unchanged at `712c307` except for doc comments (TeX
line numbers moved to manuscript revision `975feb3`), so these replays
were not repeated. A fourth gate replayed commit `712c307`, where wave L5
closed: the seven modules added in wave L5 (`TimeCompletion`,
`MaskedContinuousWave`, `MaskedContinuousWaveCompleted`,
`MaskedAuxiliaryNorm`, `DampedNormsHomog`, `VariationalMean`,
`PhaseBessel`), the umbrella and `Axioms` (9 targets, all pass;
`verification/leanchecker-easley-wave-l5/`). Since `712c307`,
`DampedNorms` and `DampedNormsHomog` have changed only in comments. A fifth
gate replayed commit `bfa2fd0`, where wave L6 closed: the fourteen modules
added in wave L6, the umbrella and `Axioms` (16 targets, all pass; default
mode 73/73; `verification/leanchecker-easley-wave-l6/`); every other module
has, with comments stripped, the same source and imports as at an earlier
`--fresh` replay. A sixth gate replayed commit `f3be834`, where wave L7
closed: the eight modules added in wave L7, the umbrella and `Axioms` (10
targets, all pass; default mode 81/81;
`verification/leanchecker-easley-wave-l7/`); every other module has, with
comments stripped, the same source and imports as at an earlier `--fresh`
replay. So every library module through wave L7 has passed a `--fresh`
replay. A seventh gate replayed commit `aff7409`, where wave L8 closed, as
a cluster array with one target per task: all 92 targets `--fresh` (92/92
pass) and a default-mode replay of all of them (92/92 pass;
`verification/leanchecker-easley-wave-l8/`). So every library module
through wave L8 has passed a `--fresh` replay, all of them at `aff7409`.
An eighth gate replayed commit `6eb79c7`, where wave L9 closed, as a
cluster array: all 103 targets `--fresh` (103/103 pass) and a default-mode
replay of all of them (pass; `verification/leanchecker-easley-wave-l9/`). So
every library module through wave L9 has passed a `--fresh` replay, all of
them at `6eb79c7`. At the same commit a lower-tier receipt was also produced
on the cluster with `lean-pkg receipt slurm`; it agrees with the local
receipt claim by claim (`verification/slurm-receipt-pilot-wave-l9/`).

## Citation

Cite the paper, and this repository by its release tag or exact commit. See
[CITATION.cff](CITATION.cff). Release v0.9.0 is archived on Zenodo as
[doi:10.5281/zenodo.24199105](https://doi.org/10.5281/zenodo.24199105); the concept DOI
[doi:10.5281/zenodo.24199104](https://doi.org/10.5281/zenodo.24199104) always resolves to the latest release.

```bibtex
@software{chen:26:stratonovich,
  author  = {Chen, Le},
  title   = {stratonovich-ham-second-moment-lean: Lean companion to the second moment of the Stratonovich hyperbolic Anderson model},
  year    = {2026},
  version = {0.9.0},
  doi     = {10.5281/zenodo.24199105},
  url     = {https://github.com/chenle02/stratonovich-ham-second-moment-lean}
}
```

## License

Apache-2.0; see [LICENSE](LICENSE) and [NOTICE.md](NOTICE.md).

## Attribution and acknowledgments

AI coding assistants helped write the Lean code and documentation. Lean's
kernel checked the proofs. The mathematical correspondence is the author's
responsibility.

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg)
([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).
