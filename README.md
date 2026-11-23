<div align="center">

# Stratonovich HAM Second Moment: Lean Companion

Lean 4 checks of finite, algebraic and scalar steps in the paper

> Le Chen, *Stratonovich Waves Driven by Space-Time Gaussian Noise: Second Moment and Exact Asymptotics*
> (arXiv:2611.23014).

The book has its own site: <https://chenle02.github.io/stratonovich-ham-second-moment/>.
Its releases are archived on Zenodo: [doi:10.5281/zenodo.24342309](https://doi.org/10.5281/zenodo.24342309) (all versions).

[![Lean](https://img.shields.io/badge/Lean-v4.35.0-153e63)](lean-toolchain)
[![Mathlib](https://img.shields.io/badge/Mathlib-56a0058-153e63)](https://github.com/leanprover-community/mathlib4/tree/56a005855ea17e0b0958f73ec801ae140b0a1679)
[![Release](https://img.shields.io/badge/release-v0.10.0-153e63)](https://github.com/chenle02/stratonovich-ham-second-moment-lean/releases/tag/v0.10.0)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24199104.svg)](https://doi.org/10.5281/zenodo.24199104)
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
> does not check the paper end to end. The SPDE, the identification of its
> mild solution with the chaos series, the Gaussian noise of the source and
> most analytic estimates are outside Lean. Since wave L19 a centered Gaussian
> field with the source's positive-width covariance, the fixed-order
> Stratonovich integrals as `L^2` limits and the `L^2` series `u = sum_n X_n`
> are constructed in Lean (model M9), and since wave L20 this `u` satisfies the
> mild equation `E:mild-construction` (`P:mild-construction`, for every source
> field; no uniqueness). Where a checked step needs such a fact, the Lean statement takes
> it as an explicit hypothesis, and the paper's proof supplies it.
>
> The correspondence between the Lean statements and the paper was checked by
> **AI correspondence review** (models from a different family than the
> ledger's author), **not by human verification**; see [Trust](#trust).

## At a glance

| | |
|---|---|
| Lean modules | 139 proof modules: 24 step modules in `StratonovichHAMAudit/` and 115 in `StratonovichHAMSecondMoment/` (besides these, the consumer `HermiteWordConsumer`, the axiom report `Axioms` and the umbrella) |
| Labelled results of the manuscript (220) | 44 whole results; 1 whole result with two named inputs supplied; 16 narrower results; steps or parts of 34 further results; 2 main theorems outside Lean; 123 not formalized ([COMPLETION.md](COMPLETION.md)) |
| Public declarations | 3654 theorems and 962 definitions; 4502 checked facts in [`claims.yaml`](claims.yaml) (3653 theorems, 849 definitions) |
| Comparator | all 3653 theorem claims compared with their restatements: 1553 credited to a manuscript result in [`coverage.yaml`](coverage.yaml) (`comparator.json`: 1134 named by the rows at the wave-L13/L14 gate, 419 added in this release by the direct-label rule), 2100 helper theorems compared as a declared smoke check and credited to no result (`comparator-helpers.json`, [`lean-pkg-signoff.json`](lean-pkg-signoff.json)) |
| Axioms | proof library: only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` (`Challenge.lean`, the comparator's statement file, states each compared theorem with `sorry` by design) |
| Negative controls, refutations, audit files | 68, 372, 137 |
| Pinned toolchain | Lean `4.35.0`, Mathlib `56a0058` |
| Verified state | the wave-L13 and wave-L14 gates (development commit `8f51004`, manuscript revision `a284420`), with every manuscript line citation re-anchored to manuscript revision `39f2597a`; the receipts that bind this release's tree commit are added by the commit after it |
| Correspondence to the paper | AI review from a different model family, accepted by the author; not a human verification |

## This release

`v0.10.0` is the wave-L13 and wave-L14 gates (waves L10 to L14 since
`v0.9.0`). Its tree is the tree of development commit `09cfc11` of the
private development repository: the gate commit `8f51004` with its
receipts, its Easley evidence and its gate record, two claims that named
Lean-generated declarations dropped, the comparator split in two
configurations (below), release documentation, and the re-anchor of every
manuscript line citation to manuscript revision `39f2597a`, with the cluster
evidence in `verification/` redacted; no Lean proof file changed after the
gate except in comments (the re-anchored line citations). It
is one commit on top of `v0.9.0`'s history, followed by a receipts commit.
[provenance/DEVELOPMENT.md](provenance/DEVELOPMENT.md) names the development
repository and the commit, and lists every change.

What is new besides waves L10 to L14: every compared theorem is accounted
for. 1553 theorems are credited to rows of `coverage.yaml`: the 1134 that
the rows named at the gate, and 419 whose statement-ledger label cell names
a direct manuscript label with a coverage row (credited to that row in this
release). The other 2100 helper theorems are compared in a separate
configuration that `lean-pkg-signoff.json` declares a smoke check, and the
491 of them that were marked `reusable` are now marked `internal` in
`claims.yaml`. With that, lean-pkg renders the generated verification and
coverage pages, which the
[documentation site](https://chenle02.github.io/stratonovich-ham-second-moment-lean/)
now carries.

**The book's release.** The book is released as tag `v1.0.0` of the
[book repository](https://github.com/chenle02/stratonovich-ham-second-moment),
original-history revision `86cf977b` (public commit `51a02011ba40`; the
tag's commit `643d1dcc8911` adds `history/commit-map.tsv` on top). The
public history of that repository is rewritten, and its
`history/commit-map.tsv` translates original-history revisions, including the
manuscript revisions named in this README, to public commits. One of them,
`39f2597a`, has no public commit: it is a merge that added only a private
record to its first parent `74d2ec31`, so the public history keeps that parent
(public commit `a6fc8b9baaca`) and drops the merge. Every TeX file of the
manuscript is byte-identical in `39f2597a` and in `a6fc8b9baaca`, so the line
citations anchored to `39f2597a` read the same in the public history. The
book's front matter differs from `39f2597a`: a line under the title
on the title page, and a new Preface paragraph on responsibility and
authorship, with one figure moved. No line of the title page or the Preface
is cited here. Every other change between the two revisions to a TeX file
that this companion cites replaces lines one for one and touches no cited
line. So every manuscript line citation here, anchored to `39f2597a`, cites
the same line numbers and the same text in `86cf977b`. No Lean file, receipt
or claim changed; `provenance/manuscript-anchor.json` keeps the file hashes
of `39f2597a`.

Commit hashes in this README, in [COMPLETION.md](COMPLETION.md), in the
[statement ledger](docs/statement-ledger.md) and in `verification/` are
commits of the development repository.

## What is checked

24 step modules in `StratonovichHAMAudit/` (the 25th file there,
`HermiteWordConsumer`, has no public declaration: private definitions and
`example`s that exercise `HermiteWord`, so it is not counted as a step),
each one step of the paper's proofs
(one of them, `HermiteWordFock`, applies a step to the Fock model and gives
the one-mode special case of a labelled result), and 185 modules in
`StratonovichHAMSecondMoment/`. Counted by labelled result (Theorem,
Proposition, Lemma, Corollary), they give 59 whole results, in which every
conclusion is a Lean conclusion under the manuscript's hypotheses alone; one
whole result with inputs supplied (`P:tube-rayleigh-transfer`, one named
input since wave L21); 22 narrower results with the manuscript's hypotheses, each with its
missing part stated; and steps, parts or narrower forms of 30 further results
with inputs supplied. Counted by module, the
ledger marks 49 modules "whole result", 69 "narrower result" and 67
"foundation" or "proof steps" (the
foundations: a wave-kernel and time-fractional covariance slice with spectral
homogeneity and the damped-norm finiteness, finite Gaussian integration by
parts, a Gaussian Schwartz test, weak gradients and a variational floor,
elementary series bounds, the density of test functions in the
weak-gradient `H^1`, the finite Wick (Isserlis) formula, the normalized
Hermite polynomials and the finite Gaussian Fock layer, the wave Green
measures and their Fourier transforms, the integral-form space-time
occupation identities, the spatial white-noise model, and the proof steps
of the static interaction, interval coefficient, static phase and fixed
split bounds and of the Green regularization of the terminal Wick lemma;
from waves L13 and L14 the deterministic two-chain diagram model and its
`d = 1` positions form, the time integrals of the diagram bounds, the
white-noise limit of the `d = 1` diagrams, an in-domain control of a
phase-contraction step, and the weak-gradient `H^1` identified with
Mathlib's Sobolev space; from wave L15 the phase space `H^(1/2) x
H^(-1/2)` on the manuscript's Fourier norm, with the density of real tests,
the duality on tests and the multipliers of bounded smooth functions; from
wave L16 the Sobolev scale `H^s` on Fourier coordinates with the statement
shapes of the Cameron-map chain, compactness of finite-rank limits, adjoints
and `L^2`-kernel operators, the compact spectral theorem with positive
square roots, and the proof steps of the temporal mean; from wave L17 the
label-set two-chain model M7 of the pairing envelope with the statement
shapes of the pairing-envelope chain, the density of the Green-smoothed
`d = 3` wave kernel, and the proof steps of the envelope (convolution norms,
regional half-bound, cap removal) and of its application (the bridge from
the diagram model M4 and the edge norms of damped and smoothed Green
kernels); from wave L18 the gap-coordinate Wick-measure model M8 with the
statement shapes of the Wick-measure chain, and the proof steps of the
spatial Wick measures (the spectral form and positive Laplace formula, the
per-edge bridge to M7, the uniform mass bound by the envelope route, the
scaling, the finite-measure Laplace argument) and of the joint temporal
tail); from wave L19 the source-field model M9 with the statement shapes of
the source-field chain, the isonormal Gaussian field on a real Hilbert space
and the feature map of the source covariance (the constructed instance), and
the proof steps of `P:mixed` (the positive-width Wick formula for two width
families, the chain reversal, the fixed-order mixed moments at common
widths) and of `L:joint-fixed-order` (the `L^2` construction and the Green
width removed first)).

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
    original mean, and, in wave L13, every derivative of the mean bounded
    globally in space, uniformly on compact time sets; a whole result).
  - `P:masked-spectral-growth` (the translated spectral mass and the ball
    bound); the homogeneity of the spectral measure is derived from
    `H:homog`.
  - `P:masked-auxiliary-norm` (the auxiliary measure `nu_R` is even,
    tempered and Radon with ball bounds uniform in `R`, and the
    Hilbert-valued Fourier bound `E:masked-hilbert-fourier`, proved for any
    complex Banach space, and, in wave L13, the clause for a real `H` after
    complexification, in a complexification built in the companion; a
    whole result).
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
    remarks on Gaussian smoothing: spatial smoothing gives the multiplier
    `e^(-eps|xi|^2/2)`, whose product with the spectral measure is the unique
    tempered spectral measure of the smoothed covariance, wave L12,
    `DampedSmoothing`; the `N_0` mass identity; Green smoothing as a
    Fourier multiplier, identified with the damped norm in `d = 1, 2, 3`
    by `damped_homogeneous_norms_fourier_one` and
    `WaveGreenFourier.damped_homogeneous_norms_fourier_wave`; a whole result
    since wave L12, over M1 and M3);
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
    a missing construction makes a result narrower. M1 is the `d = 3` wave
    Green measure via Mathlib's `volume.toSphere`, whose identification with
    surface measure is not proved; the four whole results below,
    `L:uniform-series-tail` (wave L11, in `d = 3`), and `L:terminal-wick` and
    `L:damped-homogeneous-norms` (wave L12) use it, and so do the proof steps
    `TerminalWickRegularization` (wave L11, in `d = 3`). M2
    (wave L11) is the Gaussian space `L^2(Omega; X)` over finitely many
    coordinates as normalized Hermite coefficient vectors, with integrals of
    words taken coordinatewise (the identification of a Bochner integral in
    `L^2(Omega; X)` with the coordinatewise integral is not proved);
    `L:finite-word-cutoff` uses it, and `FockSandwichModel` uses it for its
    cutoff Hilbert space. M3 (wave
    L12, accepted by the author on 2026-11-13) is the smoothed covariance `p_eps * Gamma` as the measure with
    Lebesgue density `gamma_eps`, whose identification with Mathlib's
    convolution of measures is not proved; `L:damped-homogeneous-norms`
    uses it. M4 (wave L13; accepted by the author on 2026-11-13) is the
    deterministic two-chain diagram model `DiagramModel`: the diagram
    integrals `J_(m,n,D)(t)` with the Green factors as measures of the
    increments and, for a covariance measure, the limit of common-width
    smoothings; its identification with the positions form is proved in
    `d = 1` (`DiagramBridge`) and, for a measurable covariance and Green
    measures with a finite jointly measurable density, in every dimension (`PairingBridge`, wave L17; not
    for the `d = 3` sphere measure); the TeX's joint limit at arbitrary
    vertexwise widths is formalized on M8 (wave L18), and M4's common-width
    limit follows from its full-kernel limit (temporal width `0`,
    `JointFixedOrder.joint_limit_aux`) at common vertex width `eps/2` through
    the identity `JointFixedOrder.m8_m4_identity`; the
    common-width convergence of the diagrams was the named input
    `DiagramLimits` and, with the finiteness of the limits, is a clause of
    `MixedMoment`; the diagram limits are proved for white noise in `d = 1`,
    the order-two Riesz limit in `RieszFourDiagrams`, and, in wave L18, for
    every `H:homog` covariance in `d = 1, 2, 3` (`DiagramLimits`
    discharged), and `MixedMoment` is discharged in wave L19 for the chaos
    terms of every source field (model M9);
    `L:d1-spatial` and `P:white-four` use it. M5 (wave L14; accepted by the
    author on 2026-11-13) realizes the completion spaces `H_t (x) G`, `H_t`,
    `H_I` and `H_Gamma` as `L^2` completions under the kernel and covariance
    forms, with no tensor identification and no isometry between `H_sp` and
    `H_Gamma` proved; `L:source-spatial-heat` uses it, and so do the
    narrower `OccupationCompletion` and the `Q` rows of `ClassOH1`. M6 (wave
    L14; accepted by the author on 2026-11-13) is `H^1` as the graph of the
    weak gradient in `L^2 x L^2`, with its topology proved equal to that of
    Mathlib's `H^1` (not proved: that every real element of Mathlib's `H^1`
    comes from it); `P:spatial-four-linear`, `P:occupation-physical-class`
    and `P:raw-occupation-energy` use it.)
  - `L:low-alpha-convolution` (the radial mass `mu(B_r) = r^alpha V` and the
    convolution bound for the wave Green measures smoothed by `N(0, eta I)`,
    `d = 1, 2, 3`, `alpha < 1`, with integrability).
  - `L:phase-contractions` (`E:phase-resolvent`, `E:phase-trace` and the
    Fourier form of the trace, under the standing assumptions of the
    static-phase section, and under `H:homog` in `d = 3`).
  - `L:higher-riesz` (Riesz spatial maxima: Hypothesis `H:spatial-maximum`
    with `delta = alpha - 1` and `M = M_d` for `gamma = c|x|^(-alpha)` in
    `d = 2, 3`, and the optimality of `M_3`; the hypothesis is modelled for a
    covariance with a density, which is no narrowing for this lemma).
  - `L:alpha-one-convolution` (the degree-one convolution bound
    `0 <= pairing <= pi V/2` and its polar form, under `H:homog` with
    `alpha = 1`, `d = 1, 2, 3`, with integrability of the pairing).
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
    formulas `K_0(a)` and `M_a`; `T:white-moment-bounds` is proved for the
    variational value `S_2^pos`, with the white-noise energy `E_sp = c^2/6`
    of `P:white-spatial-energy` supplied, see below; the bounds on `C_2`
    stay outside Lean) and `L:white-clock-laplace`
    (the cross-pair and self-pair Laplace transforms of the white-space
    falsification case, with the side condition `eta_1, eta_2 > 0` made
    explicit).
  - `L:inventory-product` (the coefficient bound `C^k/(k!)^nu` for the
    interval inventory product, with an explicit constant `C` depending
    only on `alpha, alpha0`).
  - `P:spatial-four-linear` (the physical four-linear extension on `H^1`:
    `A_sp(f) <= R_0 N(f)^4`, the square Cauchy-Schwarz inequality, absolute
    convergence and `E:spatial-four-linear`, multilinearity and joint continuity of `C_4` (in sequential form, and in
    wave L14 on `(H^1)^4` in the product topology, with `H^1` the
    weak-gradient graph space M6; a whole result), `R_sp = R_0` and
    `A_sp > 0`)
    and `P:spatial-energy-map` (`E_sp = (2-alpha)/2 alpha^(alpha/(2-alpha))
    R_sp^(2/(2-alpha))` in `(0, infinity)`; the static energy score bound
    in an existential form and as a bound on `S_1^pos`);
    the density of test functions in `H^1` that both proofs use is proved
    (`H1Density`).
  - `P:occupation-physical-class` (the full physical occupation class: the
    pairings `B_Gamma(g_s^2, g_t^2)` are a.e.-measurable and do not depend
    on the representatives, `J(g) <= R_star R_sp T(g)^(alpha/2) < infinity`,
    and `0 < E_star^O <= R_star^(2/(2-alpha)) E_sp`; in wave L14 over the
    class `O` of strongly `H^1`-measurable fields itself, whose joint
    representatives are constructed; a whole result).
  - `P:variational-positive-scores` (everything except `Q_2 >= S_2^pos`:
    the value sets are nonempty and bounded above, `S_c^pos` is finite,
    positive and equal to `c^((4-alpha)/(3-alpha)) S_1^pos`; the boundedness
    is proved deterministically from the occupation ceiling, not by the
    manuscript's stochastic argument).
  - `P:raw-occupation-energy` (`A(g)`, `C_occ` and `E_zeta^O` defined,
    `0 < C_occ <= K_0 R_sp`, the dilation identities and both displays) and
    `L:occupation-rayleigh-selection` (near-optimal occupation fields, by a
    finite-cell field of real unit tests), over the class `O` itself in wave
    L14 (the first a whole result; the second with the rate in Rayleigh form
    and the cost in integral form).
  - `T:intrinsic-occupation-ceiling` (`c I_Psi - v_Psi/2 <= U_c` and
    `S_c^pos <= U_c` for every `c > 0`, both forms with the exact `C_occ`
    over the class `O` itself (wave L14); `C_2 <= U_2` not formalized; the
    form with the larger constant `K_0 R_sp` also remains) and
    `C:intrinsic-spatial-bracket` (the bracket and the strict comparison for
    the variational value `S_2^pos` in place of `C_2`, with the exact
    `E_(1/2)^O` in the comparison).
    - `L:positive-raw-embedding` (the variance identity in integral form, the
    row bound `int_I |s-t|^(-a) dt <= K_0` and the scalar Schur bound; in
    wave L14 `E:positive-bochner-inclusion` for every real Hilbert space,
    with `H_t (x) G` the kernel completion of model choice M5, and
    `||Psi||^2_(H_I) = v_Psi`; the a.e. mean identity for the uniform `E` mean and
    a canonical version agreeing a.e., proved in wave L15 for a supplied
    regulator and in wave L16 with nothing supplied for maps `T_R` and `U`
    constructed in Lean to meet the frozen specifications `IsSpatialMeanMap`
    and `UTensorSpec`; conclusion full by the author's decision of
    2026-11-20, with this scope: no Lean theorem identifies these maps with
    the section's `T_R` and `C_t (x) I` or with a regulator's maps, and
    `H_I` is the kernel completion M5) and
    `L:occupation-raw-square`
    (wave L14: the square map `Q` into `H_sp`, continuous on `H^1`, and
    `rho_g` in `H_I` with both identities, for fields of `O` modelled by
    joint representatives; narrower: not restated on `O` itself).
  - `L:uniform-E-lift` (wave L15, every covariance and cutoff profile: each
    `L` in `V_(E,R)` is `B_E(M)` with `||L|| = ||M||`, the unique potential
    `V` with `M u = V u` on tests, and `E:uniform-E-pairing` with the symmetry
    of the pairing for real states; narrower: the lift `L_F` into the signed-static class and
    the Hermitian extension to complex states are not formalized).
  - The Cameron-map chain (wave L16, TeX lines at book 1.1.3):
    `L:cameron-fractional-products` (a whole result, with smooth
    Littlewood-Paley bands, so the constant `C_s` differs from the proof's
    sharp-band constant and depends on `(alpha, s)` only);
    `L:uniform-mean-cutoff` (the cutoff multiplier for every real `sigma`
    with norm at most `M_sigma`, its uniqueness not stated, and
    `E:uniform-spatial-mean`); `P:cameron-temporal-map` (every clause, with
    "not trace class" and "not Hilbert-Schmidt" as the divergent cell sums of
    decision 7); `L:uniform-mean-tensor` on finite tensors; and the map `U`
    of `P:cameron-full-mean` with `||U|| <= ||C_t||` (kernel-positivity
    route; the compactness of the full mean and its tail not formalized).
  - The pairing-envelope chain (wave L17, TeX lines at book 1.1.3):
    `L:translated-covariance-CS` (every dimension, zero norms and measures
    included; a whole result) and `L:pairing-product-envelope` (on the
    label-set two-chain model M7, every dimension and label type; a whole
    result).
  - The Wick-measure chain (wave L18, TeX lines at book 1.1.3):
    `L:spatial-wick-measures` (on the gap-coordinate model M8, `d = 1, 2,
    3`, nothing supplied; Steps 2-3 by the envelope route (b) instead of
    Brownian occupation moments; a whole result) and the deterministic half
    of `L:joint-fixed-order` (finite joint diagram limits at arbitrary
    vertexwise spatial and temporal rates in `d = 1, 2, 3` with
    `E:joint-temporal-tail`).
  - The source-field chain (wave L19, TeX lines at book 1.1.3), for every
    source field of the model M9 (the positive-width fields of
    `E:pairing-source-covariance` on any probability space; non-vacuous at
    the constructed instance `m9`), `d = 1, 2, 3`: `L:joint-fixed-order` (now
    a whole result: the `L^2` limit `X_n` of `Y_n^a` at arbitrary vertexwise
    rates, equal to the common-width limit `S_n(g_n)`, and Green smoothing
    removed first), `P:mixed` (a whole result, `t > 0`: `E:mixed-moment`
    and `E:full-second`), `L:vertex-crude` (a whole result), and with
    `MixedMoment` and `FirstMomentSeries` thereby discharged for these chaos
    terms and this solution (the earlier wrappers for abstract random
    variables, still credited, keep them as inputs)
    `L:crude-corrected` and `L:white-test` (whole results, `d = 3` included
    for `L:crude-corrected`), `P:envelope` and `P:low-alpha-upper` (narrower
    at the L19 gate, whole since wave L20).
  - The mild construction (wave L20, TeX lines at book 1.1.3), for every
    source field of M9 under `H:homog`, `d = 1, 2, 3`:
    `P:mild-construction` (a whole result: `E:mild-construction`, the
    integral of `u W_(eps,delta)` against `G(t-s, x-dy) ds` tends to
    `u(t,x) - 1` in `L^2` as `eps, delta -> 0` at arbitrary rates, for
    `t > 0` and every `x`; in `d = 3` the Green-width limit first, by the
    common-noise route; non-vacuous at `m9`; no uniqueness), with
    `E:occupied-multiplication` on the closed polynomial spaces of any
    centered Gaussian field, `X_n(s,y)` in `P_(<=n)`, joint measurability,
    spatial `L^2` continuity, the terminal-kernel Fubini and the partial and
    external vertex limits; the Riesz instance of `H:homog` in `d = 1`
    (`E:d1-covariances`, the spectral measure a Gaussian mixture); and the
    deferred wrappers, so that `P:d1-upper` (white and Riesz cases),
    `C:d1-first-calibration` (with the conditional rate clause for the
    constructed solution), `P:low-alpha-upper` (both inequalities) and
    `P:envelope` (with `rho > kappa`) are whole results with the
    manuscript's hypotheses, and `P:riesz-small` has the manuscript's
    hypotheses with a narrower conclusion (the multiplicity sentence).
  - `L:d1-spatial` (wave L13: the `d = 1` spatial estimate on the diagram
    model M4, both covariances, every split and pairing, a width per pair;
    a whole result) and `P:white-four` (wave L13: the nine order-four white
    diagrams, the exchanged chains, `E:total-four` and the scaling; a whole
    result over M4).
  - `L:source-spatial-heat` (wave L14: `H_Gamma`, separable and containing
    the Schwartz tests, and the heat operators: positive, self-adjoint,
    contractions converging strongly to the identity; a whole result over
    M5) and `L:positive-physical-gram` (wave L14: the covariance vectors in
    `H_I` and both Grams positive semidefinite; narrower: the label row and
    the entrywise order are not formalized).
  - `L:product-endpoints`, `L:plane-endpoints` and `L:endpoint-closure`
    (wave L14: the strict product and plane-supported endpoints of the
    three-dimensional covariances, with `V_low = c/pi` for the plane
    endpoint's exhibited spectral measure, and their closure
    under linear images and finite positive sums; the positive definiteness
    of the Riesz measures they need is proved; whole results).
  - `L:finite-word-cutoff` (exact cutoffs for finite Gaussian words, wave
    L11: several Gaussian modes per color, the cutoff on the total Hermite
    degree of each color, any finite word with `r_i <= N_i`, and finite sums
    and integrals of words; a whole result over the model choice M2; the
    one-mode case of wave L9 remains).
  - `L:uniform-series-tail` (uniform term and tail bounds, the `L^2`
    regularization limit and the bound `B_1`, wave L11: for chain integrals
    over the constructed terminal-chain measures `g_n^{T,x}`, with the
    lemma's hypotheses only; a whole result).
  - `L:terminal-wick` (wave L11: the chain measures `g_n^{T,x}` constructed
    with mass `T^(2n)/(2n)!`, the Bochner integrals, the majorant, the Wick
    formula, nonnegativity of the pairing integrals when the covariance is
    entrywise nonnegative, the comparison and absolute convergence, with the
    lemma's hypotheses only; wave L12: the comparison sentence for the second
    moments of the partial sums of every finite order, for real `r` (the
    full-series comparison is a Lean-side corollary), and absolute
    convergence for complex `r`; a whole result over M1; the mass
    and convergence facts of the Green-regularization paragraph of its proof
    are proved in `d = 1, 2, 3` for a common-noise construction whose factors
    are identified with `p_eta * G_h` one at a time; the identification of
    the whole regularized chain measure with the TeX's product, and the
    paragraph's last clause, are not formalized).
  - `L:source-finite-comparison` (wave L12: the moment comparison for a
    centered Gaussian vector with covariance at most `C I` against
    independent standard Gaussians, with both moments finite).
  - `L:tube-half-action` (wave L12: the supremum identity with the Gaussian
    quadratic cost, in the extended reals).
  - `L:tube-closed-geometry` (wave L21: every tube `T_r` is closed,
    `{d_delta <= r} = T_r` (the first identity of `E:tube-attained-radius`) and
    `d_delta` is lower semicontinuous; narrower: the Gaussian tail and the
    almost sure finiteness, which rest on the imported Borell isoperimetric
    theorem, are not formalized).
  - `L:fock-form` and `L:interval-contractions` (wave L11: the Gaussian
    cutoff bound, `E:interval-column`, the band compression, the vacuum
    phase insertion and `E:interval-fock`, with nothing supplied, for
    finitely many real modes on a Fourier-side model; narrower: the
    identification of that model with the physical-space operators and of
    the modes with the Gaussian coordinates of `W_eps` is not formalized;
    wave L12 adds the operator form of the Gaussian cutoff bound on that
    model, with `A_0 = -Delta` on the band and the cutoff field bounded and
    self-adjoint).

</details>

- **Whole results with inputs supplied**:
  - `P:tube-rayleigh-transfer` (wave L12: the comparison with the Rayleigh
    integral, with jumps of `G` and infinite expectations allowed; in the
    nonzero-law case the Gaussian tail of `L:tube-closed-geometry`, which
    rests on the imported Borell isoperimetric theorem, is supplied (the
    closed tubes with least-radius attainment were supplied too until wave
    L21, which proves them); the zero-law case needs no input).
- **Narrower results with inputs supplied** (waves L13, L14, L16, L17, L18;
  statements about an abstract model rest on the statement of
  `P:three-transfer`, `ThreeTransfer`; in wave L16 the compactness sentence
  of `P:cutoff-singular-values` is the named input `CutoffCompact`):
  - `P:cameron-spatial-map` (wave L16, `E` part: the bounded map, its
    smooth-test formula and its row at all states with nothing supplied; the
    compactness of the map and of its values from `CutoffCompact`; the `F`
    columns not formalized) and `P:uniform-mean-regulator` (wave L16: the
    regulator of wave L15, `UniformMeanRegulator`, constructed with
    `CutoffCompact` as its only input, with the first bound of
    `E:uniform-completed-mean` and compact values; the projection and tail
    half not formalized).
  - `C:three-product-riesz` and `C:three-finite-images` (the endpoint
    hypotheses discharged; the moment and asymptotic bounds from
    `ThreeTransfer` for an abstract moment model, the asymptotic clause only
    for a supplied spectral measure of the low endpoint).
  - `P:signed-closed-form` (the form bounds `E:signed-form-bounds` and the
    bounded resolvent of the form, for an abstract Hermitian pairing with
    `E:signed-multiplier-form` supplied as the named input
    `SignedMultiplierForm`; the self-adjoint operator `H_V`, `D(A^(1/2)) =
    H^1`, `E:signed-quarter-phase`, the dual completion `H^(-1/2)`, the
    commutation with real conjugation and `L:signed-limiting-multiplier` are
    not formalized).

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
  - `P:wave-two-variances` (both variance directions in spectral form,
    uniform in `R`, `I` and the family, and its `h^(2 beta)` form, with no
    input; the statement for `E|l_R|^2` takes
    `E:variance-normalized-covariance` and the isometry `J` as named
    inputs);
  - the finite Gaussian comparison of `P:masked-noise-completion`
    (`E N(X)^p <= E N(Y)^p` for `X ~ N(0,A)`, `Y ~ N(0,B)`, `A <= B` in
    positive semidefinite order, any seminorm, `p >= 1`; the noise
    statements of that proposition are not formalized);
  - the Cauchy, scalar and series steps of
    `P:static-phase-all-orders` (both displays for abstract Banach-space
    quantities; the circle bound, entireness in the coupling, the
    coefficient identification, the norm comparisons, the cutoff removals
    and the free bound supplied; in wave L11 the circle bound is derived
    from `L:complex-phase` with the operator form of `E:fock-sandwich`, the
    Crouzeix-Palencia and inverse-root inputs and the propagator
    identification supplied; in wave L12 the operator form of
    `E:fock-sandwich` is proved on the Fourier-side model);
  - the scalar and Hilbert-space steps of `C:static-interaction`
    (`E:static-block-series` in full; in wave L11 the identification
    `I = sum sigma^n Y_n`, the order bounds and the per-block step are
    proved, with the inputs of `P:static-phase-all-orders`, the parity and
    first-variance bounds and the per-block bound on adapted phases
    supplied; in wave L12 re-issued with the operator form of
    `E:fock-sandwich` proved on the Fourier-side model) and of `P:interval-coefficients` (the assembly of the
    coefficient bound from the energy-split identity as a supplied input,
    with `L:inventory-product` proved in Lean and `L:fixed-split` discharged
    by its Fock-model assembly below; the added hypothesis bounding each
    `Q_(r,q)` by the cutoff inner product, accepted for now by the author,
    is removed in wave L11, where `Q_(r,q)` is identified with that inner
    product (its real part enters the scalar assembly) from the Duhamel word
    expansion of the coefficients as a named input; and the summation to the
    phase bound);
  - `P:variational-remove-mask` (the masks and every rate statement with
    nothing supplied; the point lower bound from the supplied original
    point bound of `P:raw-block-original-lower`);
  - `L:symplectic-free` (both compact-baseline displays on an abstract
    Hilbert space, with the free group, reversal and translations and the
    convergence of the left Young sums supplied; the per-frequency
    symplectic identity and the force skewness);
  - the finite-coordinate multiplication bound `E:occupied-multiplication`
    of the proof of `P:mild-construction` (the abstract forms of
    `L:fock-form` and `L:interval-contractions`, with the spatial column
    bound supplied, remain in `FockForm`; their completed forms are listed
    above);
  - `L:complex-phase` and `L:interval-complex` (the numerical-range, scalar
    and Banach-algebra steps with nothing supplied; the operator bounds from
    Crouzeix-Palencia and the inverse-root integral representation as
    supplied inputs; the phase propagator itself is not formalized);
  - `L:fixed-split` (`E:fixed-split-bound` with
    `C_split = 100^8 e^8 max{1, 12 delta^(-2)}` for any `delta > 0`, on a
    finite Fock model of the cutoff Gaussian space; the segment bound of
    `L:interval-complex`, `E:interval-cross-cube`, `E:interval-column`, the
    invariance of the cross subspaces and the entire coefficients are
    supplied, and the cutoff evolution is not constructed);
  - `T:white-moment-bounds` (the two bounds of `E:white-moment-bounds` for
    the variational value `S_2^pos` in place of `C_2`, for `c > 0`, with the
    value `E_sp = c^2/6` of `P:white-spatial-energy` supplied (reserved
    package B9); the white-noise model is proved to satisfy `H:homog` with
    `alpha = d = 1`; `C_2 = S_2^pos`, the time exponent and `c = 0` are not
    formalized).

</details>

Counts:

- **5330 public theorems** and **1425 public definitions** (counted from the
  elaborated environment: every non-private `def`, `abbrev`, `instance`,
  `structure` and `inductive` written in the source, not the declarations
  Lean generates, such as projections or a derived `DecidableEq` instance).
  5326 of the 5330 theorems (all but `MaskedAuxiliaryReal.Cx.ext_iff`,
  which `@[ext]` generates, and the three anonymous `CompleteSpace`
  instances of `UniformMeanInterface`, whose names Lean generates; 1995
  reusable, 3331 helper lemmas marked `internal`) and 1306 of the definitions
  are the checked facts listed in `claims.yaml` (the six other anonymous
  instances of `UniformMeanInterface` are not claimed for the same reason;
  all nine are compiled and kernel-checked with their module).
- The comparator checks all 5326 theorem claims against their restatements
  in `Challenge.lean`, in two configurations. `comparator.json` holds the
  2056 theorems credited to a manuscript result, each the declaration of a
  claim that a row of `coverage.yaml` names: the 1134 that the rows named at
  the wave-L13/L14 gate (reviewed with their waves; 243 of them have a "no
  direct label" ledger cell or only labels without a coverage row, and are
  named by the row whose result they serve), and 419 more credited in
  v0.10.0 by a rule: the row of a direct manuscript label in the label cell
  of their ledger row, 24 of wave L15, 100 of wave L16, 121 of wave L17,
  104 of wave L18, 76 of wave L19, 71 of wave L20 and 7 of wave L21 by the
  same rule. `comparator-helpers.json` holds the other 3270, which
  neither applies to; `lean-pkg-signoff.json` declares it a smoke check, so
  these theorems are compared but credited to no result (see the ledger's
  comparator accounting).
- Every public declaration of the proof library depends only on Lean's
  standard axioms (`propext`, `Classical.choice`, `Quot.sound`). There is no
  `sorry` in it; `Challenge.lean`, the comparator's statement file, restates
  each compared theorem with `sorry` by design (see Verification record).
- **68 negative controls** in `controls/`. Each one states a wrong variant
  (a wrong constant, sign or range, or a dropped hypothesis), and Lean must
  reject it for a mathematical reason. They show the checked statements are
  sharp enough to exclude the plausible mistakes.
- **372 refutations** in `refutations/`, which go further: each one is a Lean
  proof that a specified variant of a declaration is false: a manuscript
  scalar step, a Lean-route-only construction, or a control of totalized
  arithmetic or of a broader generalization (the ledger states each one's
  domain).
- **137 audit files** in `Audit/`, which print the full types and axioms of
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

- the uniqueness of the solution of the SPDE, and the identification of the
  `L^2` series `u = sum_n X_n` of wave L19 (a mild solution in the sense of
  `E:mild-construction` since wave L20, `P:mild-construction`) with an
  independently specified solution;
- the Gaussian noise measure of the source and Wick pairings beyond finite
  families of Gaussian values (in Lean: finitely many independent standard
  Gaussians, the finite-dimensional centered Gaussian laws of
  `GaussianComparison` and `SourceTube`, the finite Wick formula of
  `FiniteWick`, the finite Hermite and Fock layer of `GaussianHermite` and
  `HermiteFock`, and, since wave L19, an isonormal Gaussian field on a real
  Hilbert space (covariance the inner product) and its pullback along the
  feature map of the source covariance (covariance `srcCov`), the
  fixed-order Stratonovich integrals `X_n` as `L^2` limits and the `L^2`
  series `u`, model M9);
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
lake build                # the umbrella StratonovichHAMSecondMoment (it imports 210 modules: 185 library, 25 StratonovichHAMAudit) and the Axioms module
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
rev = "v0.10.0"
```

## Architecture

| Path | Contents |
|---|---|
| `StratonovichHAMAudit/` | the 24 step modules and `HermiteWordConsumer` (private checks of `HermiteWord`, not a step) |
| `StratonovichHAMSecondMoment/` | the 185 library modules (whole results, narrower results, foundations and proof steps) |
| `StratonovichHAMSecondMoment.lean` | umbrella module importing all of them |
| `StratonovichHAMSecondMoment/Axioms.lean` | `#print axioms` for every public declaration |
| `controls/` | negative controls, one directory per module |
| `refutations/` | Lean proofs refuting specified variants of declarations: manuscript scalar steps, Lean-route-only constructions, and controls of totalized arithmetic or of broader generalizations (the ledger states each one's domain) |
| `Audit/` | full-type and axiom printouts and a consumer example for each proof module |
| `claims.yaml` | the checked facts, with summaries |
| `docs/statement-ledger.md` | manuscript label to Lean declaration map |
| `provenance/manuscript-anchor.json` | SHA-256 of the manuscript revision the labels refer to, and of each Lean source |
| `verify.sh` | the build-and-axiom check used for verification records |
| `coverage.yaml` | one row per covered manuscript result, with its coverage class, the exact scope of the conclusion and the claims credited to it |
| `docs/coverage-scope-tex.yaml` | LaTeX versions of the coverage scope sentences |
| `comparator.json`, `comparator-helpers.json`, `lean-pkg-signoff.json`, `Challenge.lean`, `Solution.lean`, `ChallengeDefs/` | the comparator tier: every theorem claim restated in `Challenge.lean` and proved from the project in `Solution.lean`; `comparator.json` holds the theorems credited to a coverage row, `comparator-helpers.json` the helper theorems, a smoke check declared in `lean-pkg-signoff.json` |
| `scripts/` | the negative-control runner and the comparator scaffolding (`CheckFidelity.lean` checks every restatement of both configurations) |
| `COMPLETION.md` | milestones and the status of every labelled result |
| `.lean-receipts/` | lean-pkg receipts (lower tier and comparator) |
| `verification/` | external-kernel replays and the Slurm receipt pilots on the Easley cluster |
| `site/` | sources of the documentation site (gh-pages) |
| `provenance/DEVELOPMENT.md` | the development repository, the release commit and what changed |

## Theorem-to-paper map

- [docs/statement-ledger.md](docs/statement-ledger.md): every Lean
  declaration, the manuscript label it supports, what it states, and the
  inputs that stay outside Lean.
- [COMPLETION.md](COMPLETION.md): the status of each of the manuscript's 220
  labelled results, with its TeX file and line.
- [coverage.yaml](coverage.yaml): the coverage class, conclusion scope and
  credited claims of every covered result; the generated
  [coverage page](https://chenle02.github.io/stratonovich-ham-second-moment-lean/coverage.html)
  shows it row by row.
- [FORMALIZATION.md](FORMALIZATION.md): the overall scope.

Manuscript labels and TeX line numbers refer to the revision recorded in
[provenance/manuscript-anchor.json](provenance/manuscript-anchor.json).

## Milestones

Each milestone is the commit where the author closed a gate. The milestone
tags (`L0-companion-created`, `ledger-gate`, `L1-gate` ... `L14-gate`,
`reanchor-975feb3`) live in the private development repository and are listed
with their commits in [COMPLETION.md](COMPLETION.md); this repository carries
only the release tags `v0.9.0` and `v0.10.0`.

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
| `L10-gate` | `b2bf7a9` | 2026-11-13 | `a284420` | 2757 | 2268 | 82: 49 / 31 / 2 | wave L10 (higher Riesz bound in full for d = 2 and 3 with the optimal constant in d = 3, the white-noise model and the white moment bounds for S_2^pos with the spatial energy supplied, the fixed split with the added hypothesis hQ accepted for now, alpha-one convolution from the homogeneity hypothesis alone) |
| `L11-gate` | `b780f10` | 2026-11-13 | `a284420` | 2955 | 2423 | 82: 54 / 26 / 2 | wave L11 (the finite word cutoff for several modes per color, which removes the fixed split's added hypothesis hQ in a new wrapper; the spatial column bound of the Fock form for a concrete Fourier-side model; the chain measures of the terminal Wick lemma constructed, with the uniform series tail whole; the static interaction bounds with fewer supplied inputs) |
| `L12-gate` | `56fc59e` | 2026-11-13 | `a284420` | 3107 | 2541 | 85: 56 / 27 / 2 | wave L12 (the terminal Wick lemma in full for the constructed chain measures; the damped homogeneous norms in full with the smoothed covariance modelled by its density, model choice M3; source finite comparison and tube half action in full; the tube Rayleigh transfer from two supplied inputs; the Fock sandwich proved on the Fourier-side model) |
| `L13-gate` | `8f51004` | 2026-11-13 | `a284420` | 4504 | 3654 | 101: 64 / 35 / 2 | waves L13 and L14, closed together (the two-chain diagram model, model choice M4, with the mixed-moment proposition supplied; the spatial and order-four white diagram bounds in full on the model; the Chapter 3 upper bounds with their moment statements resting on the supplied input; H^1 identified with Mathlib's Sobolev space and the resolvent form layer) |
| `L14-gate` | `8f51004` | 2026-11-13 | `a284420` | 4504 | 3654 | 101: 64 / 35 / 2 | waves L13 and L14, closed together (the occupation completion spaces, model choice M5, and H^1 as the weak-gradient graph, model choice M6, with the four-linear form, the occupation class and the raw occupation energy in full; the source spatial heat lemma in full; the d = 3 endpoint lemmas in full with the positive definiteness of the Riesz densities proved) |

## Trust

A successful build checks that the proofs are correct for the statements as
written in Lean. Whether a Lean statement says what the paper needs is a
separate question. The statement ledger answers it row by row and is meant
to be read next to the paper. Lean does not check that correspondence.

**Correspondence review, in short.** Each wave's ledger rows were reviewed
against the manuscript by AI models from a different family than the ledger's
author, and the author accepted every wave, the last two at the wave-L13 and wave-L14 gates. The
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
`6eb79c7` over manuscript revision `a284420`). The 289 rows of wave L10
(`HigherRieszTwo`, `HigherRieszThree`, `AlphaOneConvolution`,
`L10Completed`, `WhiteModel`, `WhiteMomentBounds`, `FixedSplitCore`,
`FixedSplit`; totals now 1481 labelled and 1276 unlabelled), their section
headings under the strict convention and the changes wave L10 made to
existing ledger sections and coverage rows were reviewed in eight
correspondence reviews (documentation findings only, no Lean error, all
repaired), a confirmation review and a re-confirmation, which passed with
high confidence at commit `0904978`; the author accepted wave L10 on
2026-11-13 (gate closed at `b2bf7a9` over manuscript revision `a284420`,
with the added hypothesis `hQ` of the fixed-split assembly recorded as
accepted for now). The 198 rows of
wave L11 (`FiniteWordCutoff`, `FockColumnBound`,
`StaticInteractionCompleted`, `TerminalWickInputs`,
`TerminalWickRegularization`; totals now 1583 labelled and 1372
unlabelled), the model-choice register entry M2, the coverage rows it
changed (`L:finite-word-cutoff` and `L:uniform-series-tail` whole;
`L:terminal-wick`, `L:fock-form` and `L:interval-contractions` with the
manuscript's hypotheses and a narrower conclusion; `C:static-interaction`,
`P:static-phase-all-orders` and `P:interval-coefficients` with fewer or
different supplied inputs) and the changes wave L11 made to existing ledger
sections were checked in a first round of correspondence reviews
(documentation findings only, no Lean error, all repaired) and a
confirmation review, which passed with high confidence at commit
`c2acf53`; the author accepted wave L11 on 2026-11-13 (gate closed at
`b780f10` over manuscript revision `a284420`). The 152 rows of wave L12
(`TerminalWickComplete`, `DampedSmoothing`, `SourceTube`,
`FockSandwichModel`; totals now 1653 labelled and 1454 unlabelled), the
model-choice register entry M3 (accepted by the author on 2026-11-13), the
coverage rows it changed (`L:terminal-wick` whole over M1 and
`L:damped-homogeneous-norms` whole over M1 and M3;
`L:source-finite-comparison` and `L:tube-half-action` new and whole;
`P:tube-rayleigh-transfer` new, whole with two named inputs; `L:fock-form`
in operator form, still narrower; `C:static-interaction` and
`P:static-phase-all-orders` with `FockSandwich` proved on the Fourier-side
model) and the changes wave L12 made to existing ledger sections were
checked in a first round of correspondence reviews (documentation findings
only, no Lean error, all repaired) and a confirmation review, which passed
with high confidence at commit `0e1e687`; the author accepted wave L12 on
2026-11-13 (gate closed at `56fc59e` over manuscript revision `a284420`,
with the model-choice register entry M3 recorded). The 1397 rows of waves
L13 and L14 (22 modules, from
`DiagramModel` to `ClassOBridge`; totals now 2263 labelled and 2241
unlabelled), the model-choice register entries M4, M5 and M6 (accepted by
the author on 2026-11-13), the named inputs `MixedMoment`, `DiagramLimits`,
`FirstMomentSeries`, `SignedMultiplierForm` and `ThreeTransfer`, the 16 new
coverage rows (with `P:signed-closed-form`, added when the review moved
`ResolventForm` from foundation to narrower result), the nine changed ones
(`L:variational-global-mean`, `P:masked-auxiliary-norm`,
`P:spatial-four-linear`, `P:occupation-physical-class` and
`P:raw-occupation-energy` now whole; `L:occupation-rayleigh-selection`,
`T:intrinsic-occupation-ceiling`, `C:intrinsic-spatial-bracket` and
`L:positive-raw-embedding` rescoped) and the changes waves L13 and L14 made
to existing ledger sections were checked in a first round of correspondence
reviews (documentation findings only, no Lean error, all repaired) and a
confirmation review, which passed with high confidence at commit
`f7cf727`; the author accepted waves L13 and L14 on 2026-11-13 (gates
closed together at `8f51004` over manuscript revision `a284420`). These
reviews were done by AI
models from a different family than the ledger's author; they are not a
human verification, and they do not check the analytic inputs that stay
outside Lean. A later change to the ledger or to a cited label needs a new
review.

Wave L15 (item L15-UM, scope (a), approved by the author on 2026-11-19, which
reopened the Lean work for this item) was gated on 2026-11-20 (tag
`L15-gate`): four modules (`UniformMeanInterface`, `UniformMeanFoundation`,
`UniformELift`, `PositiveRawMean`), the coverage row `L:uniform-E-lift`, the
changed row `L:positive-raw-embedding` and the named inputs
`CameronSpatialMap` and `UniformMeanRegulator`. Its TeX citations, first at
revision `c3c2431d` (book v1.0.2), were moved to `0788ddee` (book 1.1.0) by
item R1 of wave L16; among the files cited by wave L15, only
`integrated_uniform_mean.tex` and `integrated_uniform_products.tex` changed
between the two (seven other TeX files of the book changed).

Wave L16 (approved by the author on 2026-11-20, the Cameron-map chain) was
gated on 2026-11-20 (tag `L16-gate`, commit `ebac849`): fifteen modules
(`CameronInterface`, `CompactOperatorFoundation`, `UniformMeanCutoff`,
`CameronProducts`, `CameronSpatial`, `CameronTemporalKernel`,
`CameronTemporalYoung`, `CameronTemporalSqrt`, `CameronTemporalMap`,
`CameronTemporalTarget`, `CameronUMap`, `UniformMeanTensor`,
`UniformMeanAssembly`, `UniformMeanDischarge`, `CameronFinal`), 429 ledger
rows citing TeX lines at revision `0788ddee` (book 1.1.0), seven new
coverage rows, the changed row `L:positive-raw-embedding` (now with nothing
supplied) and the named input `CutoffCompact` (the compactness sentence of
`P:cutoff-singular-values`, kept a named input by the author's decision of
2026-11-20). L15's named inputs `CameronSpatialMap` and
`UniformMeanRegulator` are constructed, with `CutoffCompact` as the only
input; the fallback `TemporalCompact` is proved. Its statements and
documentation were reviewed, its receipts cut and its modules replayed on
Easley before the gate (see `COMPLETION.md`). No refutation or audit files
were written for wave L16.

Wave L17 (approved by the author on 2026-11-20, the pairing-envelope chain)
was closed by the author on 2026-11-21 (tag `L17-gate`): fifteen
modules (`PairingInterface`, `PairingTranslatedCS`, `PairingConvolution`,
`PairingRegional`, `PairingCapRemoval`, `PairingEnvelope`, `PairingBridge`,
`PairingDampedNorms`, `HomogeneousEnvelope`, `CrudeCorrected`,
`EnvelopeFinal`, `GreenSmoothed3`, `PairingSmoothedNorms`, `EnvelopeD3`,
`EnvelopeD3Final`), 508 ledger rows (their TeX citations at revision
`0788ddee`, book 1.1.0), four new coverage rows (`L:translated-covariance-CS` and
`L:pairing-product-envelope` in full; `L:crude-corrected` and `P:envelope`
narrower with the named input `MixedMoment`) and the model choice M7 (the
label-set two-chain model, with a bridge from M4). No new named input; the
fallbacks `ConvolutionNorms` and `RegionalHalfBound` are used nowhere. Its
statements and documentation were reviewed, its receipts cut and its modules
replayed on Easley before the gate (see `COMPLETION.md`). No refutation or
audit files were written for wave L17.

Wave L18 (approved by the author on 2026-11-21, the Wick-measure chain and the
discharge of `DiagramLimits`) was integrated on branch `wave-l18/int`; the
author closed its gate on 2026-11-21 (tag `L18-gate`): thirteen modules (`WickInterface`, `RieszDiagramLimits`,
`RieszDiagramLimitsHomog`, `WickSpectral`, `WickBridge`, `WickMass`,
`WickScaling`, `WickStep4`, `WickMeasures`, `JointFixedOrder`,
`EnvelopeD3Wave`, `JointTail`, `WickFinal`), 380 ledger rows (TeX citations
at `0788ddee`), two new coverage rows (`L:spatial-wick-measures` in full;
`L:joint-fixed-order` narrower, its deterministic half), four extended rows
(`P:d1-upper`, `P:riesz-small`, `L:crude-corrected`, `P:envelope`; classes
unchanged) and the model choice M8 (the gap-coordinate Wick-measure model;
under `H:homog`, for `D in Pi2 m n` and `t > 0`, M4's diagram at pair width
`eps > 0` equals M8's at vertex width `eps/2` and temporal width `0`; under
`H:homog`, for `D in Pi2 m n`, positive vertexwise widths, a Green family
`G_s = g(s, .) dy` with `g` finite and jointly measurable, measurable Laplace
domains in `(0, infinity)` and damping `theta >= 0`, M8's damped integral is
at most M7's pairing integral with the per-edge data `wickEdge`, `<=` only). The named input `DiagramLimits` is discharged; besides
it, the ledger Scope lists seven named inputs of waves L13 to L16
(`MixedMoment`, `FirstMomentSeries`, `SignedMultiplierForm`, `ThreeTransfer`,
`CameronSpatialMap`, `UniformMeanRegulator`, `CutoffCompact`), five of them
open (the two map inputs are constructed in wave L16); the four fallback
named inputs of the wave are used nowhere. Its statements and documentation
were reviewed, its receipts cut and its modules replayed on Easley before the
gate (see `COMPLETION.md`). No refutation or audit files were written for
wave L18.

Wave L19 (approved by the author on 2026-11-21, the source-field chain: the
`L^2` construction of `L:joint-fixed-order`, `P:mixed`, `L:vertex-crude`, and
the discharge of `MixedMoment` and `FirstMomentSeries`) was integrated on
branch `wave-l19/int`; the author closed its gate on 2026-11-22 (tag
`L19-gate`): eleven modules
(`SourceInterface`, `SourceIsonormal`, `SourceFeatures`, `SourceWick`,
`SourceReversal`, `SourceFixedOrder`, `SourceGreenFirst`,
`SourceVertexCrude`, `SourceMixed`, `SourceExpansion`, `SourceFinal`), 292
ledger rows (TeX citations at `0788ddee`), two new coverage rows (`P:mixed`
and `L:vertex-crude`, both in full), `L:joint-fixed-order` now in full, the
seven consumer rows updated (`L:crude-corrected` and `L:white-test` full
with the manuscript's hypotheses; `P:envelope` and `P:low-alpha-upper` with
the manuscript's hypotheses and a narrower conclusion;
`C:d1-first-calibration`, `P:d1-upper` and `P:riesz-small` with inputs
supplied and a narrower conclusion), and the model choice M9 (the
source fields of `E:pairing-source-covariance` on any probability space,
with the constructed instance `m9`; no M4 diagram is realized at positive
widths, each positive-width pairing integral is an M8 diagram after the
chain reversal, with the reversed pairing, and M4 enters through the limits
and through the regularized diagram bounds). The three Riesz consumer
rows keep the Riesz instance of `H:homog` as the explicit hypothesis `hH`
(the author's decision of 2026-11-22): it is true, but not formalized in the
library. The ledger Scope lists five named inputs of waves L13 to L16 besides
`DiagramLimits` and the two wave-L15 data structures (`MixedMoment` and
`FirstMomentSeries`, discharged in wave L19; `SignedMultiplierForm`,
`ThreeTransfer` and `CutoffCompact`, open); the two fallback named inputs of
the wave (`SourceNoise`, `TerminalReversal`) are used nowhere. The documentation
review's accepted findings were repaired in docs-only commits (the
author's decisions of 2026-11-22). No refutation or
audit files were written for wave L19.

Wave L20 (approved by the author on 2026-11-22 with the default answers to
its thirteen decisions: `P:mild-construction` for every source field, the
Riesz instance of `H:homog` in `d = 1`, the deferred wrappers and a
comment-only docstring pass) was integrated on branch `wave-l20/int`
and gated (below): eleven modules (`MildInterface`, `MildOccupied`,
`MildPolyMem`, `MildFields`, `MildTerminalFubini`, `MildPartialVertex`,
`MildGreenWidth`, `MildConstruction`, `MildFinal`, `RieszInstanceOne`,
`CleanupWrappers`), 306 ledger rows (TeX citations at `0788ddee`), six
coverage rows updated (`P:mild-construction`, `P:d1-upper`,
`C:d1-first-calibration`, `P:low-alpha-upper` and `P:envelope` in full with
the manuscript's hypotheses; `P:riesz-small` with the manuscript's
hypotheses and a narrower conclusion), no new model choice (M9 extended by
the mild integral), and the comment-only docstring pass over 39 earlier
library modules and 16 of their `ChallengeDefs/` mirrors (55 files). The Riesz `hH` and the
white-case `MixedMoment` of `P:d1-upper` are gone from the headline theorems
of every row (retained L19 wrappers that the rows credit keep `hH`, and
retained forms for abstract random variables keep `MixedMoment`). The named
inputs still supplied at wave L20 were `SignedMultiplierForm`, `ThreeTransfer`,
`CutoffCompact`, `TubeAttained` (discharged in wave L21, the end point
the author set on 2026-11-23, below) and `TubeTail`; the two fallback named inputs
of the wave (`JointMeasurability`, `TerminalFubini`) are used nowhere. The
author closed the wave-L20 gate on 2026-11-23 (tag `L20-gate` on `5cdd493`): Lean statements
reviewed by DeepSeek V4 Pro (eight scopes, no MAJOR or CRITICAL finding), documentation by
GPT-6.2-Sol (repaired docs-only), receipts `4842df8`, external kernel replay
`verification/leanchecker-easley-wave-l20/` (below). No refutation or audit files were written for wave L20.

Wave L21 (the author's end point of 2026-11-23: "Close the Lean companion after L20 plus
TubeAttained as an item in L21") closed its gate on 2026-11-23 (tag `L21-gate` on `38a3e00`): one module, `SourceTubeAttained`, discharges the named input `TubeAttained` at the
manuscript's tubes (closed images of Hilbert balls under a bounded map by Banach-Alaoglu, without
separability; least-radius attainment by rescaling a near-optimal control), 12 ledger rows (TeX
citations of `integrated_gaussian_tubes.tex` at `0788ddee`), one new coverage row
(`L:tube-closed-geometry` with the manuscript's hypotheses and a narrower conclusion: the
Gaussian tail and the almost sure finiteness are not formalized) and one updated
(`P:tube-rayleigh-transfer`, still a whole result with inputs supplied, now `TubeTail` only), and
the comment-only Lean docstring corrections deferred from the wave-L20 reviews. The named inputs
still supplied, at the end point, are `SignedMultiplierForm`, `ThreeTransfer`, `TubeTail` and
`CutoffCompact`. The statement review of the module (DeepSeek V4 Pro: PASS_WITH_NOTES, high, no
MAJOR or CRITICAL finding, citation notes repaired comment-only) and the documentation review
(GPT-6.2-Sol, repaired docs-only) are done; receipts `39c4365`; external kernel replay
`verification/leanchecker-easley-wave-l21/` (below). With wave L21 the Lean work reaches the
author's end point: no further proof waves are planned. No refutation or audit files were written for wave L21.

The ledger was then re-anchored to manuscript revision `39f2597a`, which adds
front matter and appendices. It renames the appendix-local direct-bound constant
`C_2` to `C_dir`. It clarifies the attribution of the quoted source result
`T:first`. It adds a front-guide paragraph of entry points. It adds explanatory
sentences to most proofs (a readability pass) without changing any statement. It
corrects six places of the original text in results not formalized here. It
removes an unused setup step from one proof. Earlier waves were anchored to
`975feb3` and then `a284420`.
Every TeX line locator was moved by the git diff of its file or, inside a proof
rewritten by the readability pass, by the pass's line map, and checked to cite
the same text (except 1 range whose words are kept but re-wrapped around
inserted explanatory sentences); locators resolved by hand were read and cite
the same object, whose wording may have changed. The file of every locator was
checked against the cited labels.

For release v0.11.0 the companion was re-anchored again, to manuscript revision
`edf7085f` (book 1.1.3). Until then the citations of waves up to L14 were at
`39f2597a` and those of waves L15 to L21 at `0788ddee` (book 1.1.0). Previously
correct locators keep their numbers: the lines cited at `39f2597a` have the same
numbers at `edf7085f`, and between `0788ddee` and `edf7085f` the book changed only
version numbers, dates and links in place, on no cited line. Five stale scaffold
docstrings and their five `Challenge.lean` copies, which carried line numbers of
book v1.0.2 (`c3c2431d`), now match `claims.yaml`. Current locators read
`edf7085f` (book 1.1.3); explicitly historical statements (gate and wave records,
checks and readings at a revision, the frozen interface records under `docs/`)
keep their revisions.

</details>

## Verification record

**This repository.** A receipt names the commit it binds, so the receipts
for a release's tree commit cannot be part of that commit: a lower-tier
receipt and a comparator receipt are cut at the tree commit and added, with
nothing else, by the commit after it, which the release tag marks (`v0.9.0`,
`v0.10.0`). For `v0.10.0` they are the files in `.lean-receipts/` whose 12-hex
prefix is the parent of the commit that `v0.10.0` marks. The comparator
receipt covers both configurations, `comparator.json` (1553 theorems credited
to coverage rows) and `comparator-helpers.json` (2100 helper theorems, a
smoke check). The other receipts in `.lean-receipts/` bind the `v0.9.0` root
commit or commits of the development repository and are kept as evidence.

**Development record.**

Commit `8f51004` (the wave-L13 and wave-L14 gates) has both lean-pkg receipts in
`.lean-receipts/` (earlier commits have their own): a lower-tier receipt (a
fresh build of all modules and the axiom report, 0 `sorry`, only the standard
axioms, and the axioms of all 4504 claims read from the built environment)
and a comparator receipt (Palomar's toolchain mechanism): every one of the
3654 theorem claims is
judged against its own restatement in `Challenge.lean`, whose types are
checked to be equal to the claimed declarations' by
`scripts/comparator/CheckFidelity.lean`. With both, `lean-pkg claims ledger`
reports no open claim. Later commits that change only documentation stay
bound to it. A receipt records the build and the statements'
self-consistency; it does not by itself establish that the statements
match the paper (see Trust).

Since release v0.10.0 the theorem claims are compared in two
configurations (the counts here are those of v0.10.0; the current ones are
under Counts): `comparator.json` (the 1553 theorems credited to rows of
`coverage.yaml`: 1134 named at the wave-L13/L14 gate, 419 added by the
direct-label rule) and `comparator-helpers.json` (the 2100 helper theorems,
declared a smoke check in `lean-pkg-signoff.json`); `CheckFidelity.lean`
checks the restatements of both, and 491 helper claims formerly `reusable`
are `internal`. The receipts of `8f51004` judged the 3654 theorem claims of
that commit in one configuration; the release commit of the public
repository carries its own receipts for the two.

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
receipt claim by claim (`verification/slurm-receipt-pilot-wave-l9/`). A
ninth gate replayed commit `b2bf7a9`, where wave L10 closed: all 111
targets `--fresh` (111/111 pass) and a default-mode replay of all of them
(pass; `verification/leanchecker-easley-wave-l10/`). So every library module
through wave L10 has passed a `--fresh` replay, all of them at `b2bf7a9`. A
second cluster lower-tier receipt at that commit again agrees with the local
receipt claim by claim (`verification/slurm-receipt-pilot-wave-l10/`). A
tenth gate replayed commit `b780f10`, where wave L11 closed: all 116
targets `--fresh` (116/116 pass) and a default-mode replay of all of them
(pass; `verification/leanchecker-easley-wave-l11/`). So every library module
through wave L11 has passed a `--fresh` replay, all of them at `b780f10`.
An eleventh gate replayed commit `56fc59e`, where wave L12 closed: all 120
targets `--fresh` (120/120 pass) and a default-mode replay of all of them
(pass; `verification/leanchecker-easley-wave-l12/`), at most two tasks per
cluster node. So every library module through wave L12 has passed a
`--fresh` replay, all of them at `56fc59e`.
A twelfth gate replayed commit `8f51004`, where waves L13 and L14 closed:
all 142 targets `--fresh` (142/142 pass) and a default-mode replay of all of
them (pass; `verification/leanchecker-easley-wave-l13-l14/`), at most two
tasks per cluster node. So every library module through wave L14 has passed
a `--fresh` replay, all of them at `8f51004`. At this commit `lean-pkg receipt
check` also reports three bookkeeping findings that do not affect the
receipts: two claims in `claims.yaml` name declarations generated by Lean
(`WhiteFour.tacticTw_close`, the syntax of a tactic macro, and
`MaskedAuxiliaryReal.Cx.ext_iff`, generated by `@[ext]`); structure-field
claims of `EndpointLemmas` marked `reusable` are compared but not matched to
their claims by the checker; and compared helper theorems are not yet
credited to coverage rows. Release v0.10.0 resolves them: the two claims are
dropped; lean-pkg 0.29.0 does not index structure fields or `@[ext]`
lemmas (`lean_scan.declarations`), so the 27 claims of such projections
cannot be matched by it: they are compared in the helper configuration, and
the 18 of them that were `reusable` (the fields of `EndpointLemmas.IsCov`,
`EndpointPair` and `ProductParams`, and of `ClassOBridge.IsClassO`) are
`internal`; the helper accounting above credits
or declares every compared theorem.
A thirteenth gate replayed commit `315a332`, where wave L15 was integrated:
the four new modules `UniformMeanInterface`, `UniformMeanFoundation`,
`UniformELift` and `PositiveRawMean` `--fresh` (4/4 pass), and a
default-mode replay of all 146 targets (pass;
`verification/leanchecker-easley-wave-l15/`). The other 142 modules have
not been replayed `--fresh` at `315a332`; 111 of them differ from `8f51004`
only in comments with unchanged line counts, the umbrella changed (it imports
the four new modules) and `Axioms` imports it.
A fourteenth gate replayed commit `ebac849`, the wave-L16 gate commit: the
fifteen new modules `CameronInterface`, `CompactOperatorFoundation`,
`UniformMeanCutoff`, `CameronProducts`, `CameronSpatial`,
`CameronTemporalYoung`, `CameronTemporalKernel`, `CameronTemporalSqrt`,
`CameronTemporalMap`, `CameronTemporalTarget`, `CameronUMap`,
`UniformMeanTensor`, `UniformMeanAssembly`, `UniformMeanDischarge` and
`CameronFinal`, and the umbrella, `--fresh` (16/16 pass), and a default-mode
replay of all 161 targets (pass;
`verification/leanchecker-easley-wave-l16/`). The umbrella's `--fresh` run
re-checks every library module except `Axioms` as an import; `Axioms`, which
imports the umbrella, is replayed in default mode only. The other 145 modules
are byte-identical to `315a332`.
A fifteenth gate replayed commit `68d0c5e`, the wave-L17 gate commit: the
fifteen new modules `PairingInterface`, `PairingTranslatedCS`,
`PairingConvolution`, `PairingCapRemoval`, `PairingRegional`,
`PairingEnvelope`, `PairingBridge`, `PairingDampedNorms`,
`HomogeneousEnvelope`, `CrudeCorrected`, `EnvelopeFinal`, `GreenSmoothed3`,
`PairingSmoothedNorms`, `EnvelopeD3` and `EnvelopeD3Final`, and the umbrella,
`--fresh` (16/16 pass), and a default-mode replay of all 176 targets (pass;
`verification/leanchecker-easley-wave-l17/`). The umbrella's `--fresh` run
re-checks every library module except `Axioms` as an import; `Axioms`, which
imports the umbrella, is replayed in default mode only. The other 160 modules
are byte-identical to `ebac849`.
A sixteenth gate replayed commit `6e4644d`, the wave-L18 gate commit: the
thirteen new modules `WickInterface`, `RieszDiagramLimits`,
`RieszDiagramLimitsHomog`, `WickSpectral`, `WickBridge`, `WickMass`,
`WickScaling`, `WickStep4`, `WickMeasures`, `JointFixedOrder`,
`EnvelopeD3Wave`, `JointTail` and `WickFinal`, and the umbrella, `--fresh`
(14/14 pass), and a default-mode replay of all 189 targets (pass;
`verification/leanchecker-easley-wave-l18/`). The umbrella's `--fresh` run
re-checks every library module except `Axioms` as an import; `Axioms`, which
imports the umbrella, is replayed in default mode only. The other 175 modules
are byte-identical to `68d0c5e`.
A seventeenth gate replayed commit `fe9f1de`, the wave-L19 gate commit: the
eleven new modules `SourceInterface`, `SourceIsonormal`, `SourceFeatures`,
`SourceWick`, `SourceReversal`, `SourceFixedOrder`, `SourceGreenFirst`,
`SourceVertexCrude`, `SourceMixed`, `SourceExpansion` and `SourceFinal`, and
the umbrella, `--fresh` (12/12 pass), and a default-mode replay of all 200
targets (pass; `verification/leanchecker-easley-wave-l19/`). The umbrella's
`--fresh` run re-checks every library module except `Axioms` as an import;
`Axioms`, which imports the umbrella, is replayed in default mode only. The
other 188 modules are byte-identical to `6e4644d`.
An eighteenth gate replayed commit `5cdd493`, the wave-L20 gate commit: the
eleven new modules `MildInterface`, `MildOccupied`, `MildPolyMem`,
`MildFields`, `MildTerminalFubini`, `MildPartialVertex`, `MildGreenWidth`,
`MildConstruction`, `MildFinal`, `RieszInstanceOne` and `CleanupWrappers`,
and the umbrella, `--fresh` (12/12 pass), and a default-mode replay of all
211 targets (pass; `verification/leanchecker-easley-wave-l20/`). The
umbrella's `--fresh` run re-checks every library module except `Axioms` as an
import; `Axioms`, which imports the umbrella, is replayed in default mode
only. Of the other 198 modules, 159 are byte-identical to `fe9f1de` and 39
differ from it only in comments.
A nineteenth gate replayed commit `38a3e00`, the wave-L21 gate commit: the
new module `SourceTubeAttained` and the umbrella, `--fresh` (2/2 pass), and a
default-mode replay of all 212 targets (pass;
`verification/leanchecker-easley-wave-l21/`). The umbrella's `--fresh` run
re-checks every library module except `Axioms` as an import; `Axioms`, which
imports the umbrella, is replayed in default mode only. Of the other 209
modules, 189 are byte-identical to `5cdd493` and 20 differ from it only in
comments.

## Citation

Cite the paper, and this repository by its release tag or exact commit. See
[CITATION.cff](CITATION.cff). The releases are archived on Zenodo; the concept DOI
[doi:10.5281/zenodo.24199104](https://doi.org/10.5281/zenodo.24199104) always resolves to the latest release
(release v0.10.0: [doi:10.5281/zenodo.24295453](https://doi.org/10.5281/zenodo.24295453);
release v0.9.0: [doi:10.5281/zenodo.24199105](https://doi.org/10.5281/zenodo.24199105)).

```bibtex
@software{chen:26:stratonovich,
  author  = {Chen, Le},
  title   = {stratonovich-ham-second-moment-lean: Lean companion to the second moment of the Stratonovich hyperbolic Anderson model},
  year    = {2026},
  version = {0.10.0},
  doi     = {10.5281/zenodo.24199104},
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
