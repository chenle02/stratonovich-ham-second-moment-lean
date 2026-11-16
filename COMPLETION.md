# Completion record

What the Lean companion verifies of the manuscript, kept current at every milestone. Every milestone is an annotated git tag on the commit where the author closed the gate. The tags and the commits in this file belong to the private development repository named in `provenance/DEVELOPMENT.md`; the public repository carries only the release tags `v0.9.0` (the wave-L9 gate) and `v0.10.0` (the wave-L13 and wave-L14 gates), whose Lean proof files are those of the gate (release documentation added, cluster evidence redacted; `v0.10.0` also drops two claims of Lean-generated declarations, splits the comparator configuration and marks the helper claims `internal`, see `provenance/DEVELOPMENT.md`). Claims count Lean declarations in `claims.yaml`; coverage rows count manuscript labelled results (see `coverage.yaml` for the exact scope of each). "Same" = formalized with the manuscript's hypotheses; "inputs" = analytic inputs supplied as named hypotheses. Correspondence was checked by AI reviews from a different model family, not by a human; supplied inputs are not verified.

## Milestones

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

Every tagged commit carries lean-pkg receipts or is a docs-only descendant of one (see `.lean-receipts/` and the README verification record). External kernel replays (`leanchecker --fresh` on Easley) cover every library module through wave L14, all of them at `8f51004` (the wave-L13 and wave-L14 gates); see `verification/`.

## Lean freeze (2026-11-13)

Wave L14 is the last Lean wave: the author froze the Lean work after it. No wave is in progress. The table by labelled result below is at the wave-L14 gate; the remaining results are left for future work or for the community.

## Completion by labelled result (manuscript 39f2597a, companion 8f51004, gates L13-gate and L14-gate)

| Status | Count | Share |
|---|---|---|
| formalized, manuscript hypotheses | 44 | 20% |
| formalized, manuscript hypotheses, narrower conclusion | 16 | 7% |
| inputs supplied, every conclusion proved | 1 | 0% |
| inputs supplied, steps/narrower | 34 | 15% |
| outside Lean (main theorem) | 2 | 1% |
| not formalized | 123 | 56% |
| total labelled results (Theorem, Proposition, Lemma, Corollary) | 220 | 100% |

No theorem of the manuscript is verified end to end. Of the four main theorems, two (`T:full-upper` and `T:intrinsic-second-moment`) are recorded as outside Lean; `T:intrinsic-occupation-ceiling` is formalized in both forms with the exact constant `C_occ`, over the class `O` itself (wave L14), for `S_c^pos`, and its moment sentence `C_2 <= U_2` is not formalized; `T:white-moment-bounds` is proved for the variational value `S_2^pos` in place of `C_2`, with the white-noise energy `E_sp = c^2/6` of `P:white-spatial-energy` supplied (reserved package B9), and its time exponent and the case `c = 0` are not formalized. The remaining work is dominated by foundations Mathlib lacks (Gaussian chaos, Cameron-Martin, the chaos expansion of the solution, Young integration of operator paths and self-adjoint operators).

## Covered displays and remarks (not counted above)

Four coverage rows are for a displayed equation or a remark rather than a numbered result:

| Label | Coverage class | Conclusion |
|---|---|---|
| `E:driver-parameters` | same-assumptions | full |
| `E:kappa` | same-assumptions | full |
| `E:masked-time-schur` | same-assumptions | full |
| `R:gaussian-one-variance-test` | same-assumptions | full |

## Every labelled result

| Label | Kind | File:line (39f2597a) | Status |
|---|---|---|---|
| `T:first` | Theorem | notes_stratonovich_ham_second_moment.tex:604 | not formalized |
| `T:crude` | Theorem | notes_stratonovich_ham_second_moment.tex:640 | not formalized |
| `P:Jensen` | Proposition | notes_stratonovich_ham_second_moment.tex:659 | not formalized |
| `T:intro-upper` | Theorem | notes_stratonovich_ham_second_moment.tex:699 | not formalized |
| `T:intro-second-moment` | Theorem | notes_stratonovich_ham_second_moment.tex:753 | not formalized |
| `P:mixed` | Proposition | notes_stratonovich_ham_second_moment.tex:834 | not formalized |
| `L:white-test` | Lemma | notes_stratonovich_ham_second_moment.tex:940 | inputs supplied, steps/narrower |
| `L:damped-homogeneous-norms` | Lemma | notes_stratonovich_ham_second_moment.tex:1011 | formalized, manuscript hypotheses |
| `L:translated-covariance-CS` | Lemma | notes_stratonovich_ham_second_moment.tex:1187 | not formalized |
| `L:pairing-product-envelope` | Lemma | notes_stratonovich_ham_second_moment.tex:1489 | not formalized |
| `L:spatial-wick-measures` | Lemma | notes_stratonovich_ham_second_moment.tex:1679 | not formalized |
| `L:joint-fixed-order` | Lemma | notes_stratonovich_ham_second_moment.tex:1854 | not formalized |
| `L:crude-corrected` | Lemma | notes_stratonovich_ham_second_moment.tex:1978 | not formalized |
| `L:vertex-crude` | Lemma | notes_stratonovich_ham_second_moment.tex:2062 | not formalized |
| `P:mild-construction` | Proposition | notes_stratonovich_ham_second_moment.tex:2152 | inputs supplied, steps/narrower |
| `P:envelope` | Proposition | notes_stratonovich_ham_second_moment.tex:2352 | not formalized |
| `L:phase-contractions` | Lemma | notes_stratonovich_ham_second_moment.tex:2509 | formalized, manuscript hypotheses |
| `P:static-phase-variance` | Proposition | notes_stratonovich_ham_second_moment.tex:2613 | not formalized |
| `L:complex-phase` | Lemma | notes_stratonovich_ham_second_moment.tex:2751 | inputs supplied, steps/narrower |
| `L:fock-form` | Lemma | notes_stratonovich_ham_second_moment.tex:2960 | formalized, manuscript hypotheses, narrower conclusion |
| `L:finite-word-cutoff` | Lemma | notes_stratonovich_ham_second_moment.tex:3036 | formalized, manuscript hypotheses |
| `P:static-phase-all-orders` | Proposition | notes_stratonovich_ham_second_moment.tex:3088 | inputs supplied, steps/narrower |
| `C:static-interaction` | Corollary | notes_stratonovich_ham_second_moment.tex:3217 | inputs supplied, steps/narrower |
| `L:interval-contractions` | Lemma | notes_stratonovich_ham_second_moment.tex:3385 | formalized, manuscript hypotheses, narrower conclusion |
| `L:interval-complex` | Lemma | notes_stratonovich_ham_second_moment.tex:3474 | inputs supplied, steps/narrower |
| `L:inventory-product` | Lemma | notes_stratonovich_ham_second_moment.tex:3581 | formalized, manuscript hypotheses |
| `L:fixed-split` | Lemma | notes_stratonovich_ham_second_moment.tex:3675 | inputs supplied, steps/narrower |
| `P:interval-coefficients` | Proposition | notes_stratonovich_ham_second_moment.tex:4054 | inputs supplied, steps/narrower |
| `L:terminal-wick` | Lemma | notes_stratonovich_ham_second_moment.tex:4291 | formalized, manuscript hypotheses |
| `L:uniform-series-tail` | Lemma | notes_stratonovich_ham_second_moment.tex:4419 | formalized, manuscript hypotheses |
| `T:full-upper` | Theorem | notes_stratonovich_ham_second_moment.tex:4474 | outside Lean (main theorem) |
| `P:white-four` | Proposition | notes_stratonovich_ham_second_moment.tex:4946 | formalized, manuscript hypotheses |
| `L:static-four` | Lemma | notes_stratonovich_ham_second_moment.tex:5019 | not formalized |
| `P:riesz-small` | Proposition | notes_stratonovich_ham_second_moment.tex:5125 | inputs supplied, steps/narrower |
| `L:d1-spatial` | Lemma | notes_stratonovich_ham_second_moment.tex:5359 | formalized, manuscript hypotheses |
| `P:d1-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:5454 | inputs supplied, steps/narrower |
| `L:low-alpha-convolution` | Lemma | notes_stratonovich_ham_second_moment.tex:5566 | formalized, manuscript hypotheses |
| `L:alpha-one-convolution` | Lemma | notes_stratonovich_ham_second_moment.tex:5635 | formalized, manuscript hypotheses |
| `P:low-alpha-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:5711 | inputs supplied, steps/narrower |
| `C:d1-first-calibration` | Corollary | notes_stratonovich_ham_second_moment.tex:5830 | inputs supplied, steps/narrower |
| `P:higher-transfer` | Proposition | notes_stratonovich_ham_second_moment.tex:5936 | not formalized |
| `L:higher-riesz` | Lemma | notes_stratonovich_ham_second_moment.tex:6103 | formalized, manuscript hypotheses |
| `C:higher-riesz` | Corollary | notes_stratonovich_ham_second_moment.tex:6192 | not formalized |
| `P:higher-obstructions` | Proposition | notes_stratonovich_ham_second_moment.tex:6231 | not formalized |
| `L:static-holder-input` | Lemma | notes_stratonovich_ham_second_moment.tex:6366 | not formalized |
| `P:static-holder-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:6425 | not formalized |
| `L:planar-endpoints` | Lemma | notes_stratonovich_ham_second_moment.tex:6675 | not formalized |
| `L:planar-static-input` | Lemma | notes_stratonovich_ham_second_moment.tex:6854 | not formalized |
| `P:planar-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:6934 | not formalized |
| `C:planar-range` | Corollary | notes_stratonovich_ham_second_moment.tex:7128 | not formalized |
| `L:product-endpoints` | Lemma | notes_stratonovich_ham_second_moment.tex:7170 | formalized, manuscript hypotheses |
| `L:plane-endpoints` | Lemma | notes_stratonovich_ham_second_moment.tex:7316 | formalized, manuscript hypotheses |
| `L:endpoint-closure` | Lemma | notes_stratonovich_ham_second_moment.tex:7418 | formalized, manuscript hypotheses |
| `P:three-transfer` | Proposition | notes_stratonovich_ham_second_moment.tex:7537 | not formalized |
| `C:three-product-riesz` | Corollary | notes_stratonovich_ham_second_moment.tex:7945 | inputs supplied, steps/narrower |
| `C:three-finite-images` | Corollary | notes_stratonovich_ham_second_moment.tex:7991 | inputs supplied, steps/narrower |
| `L:physical-spectral-energy` | Lemma | notes_stratonovich_ham_second_moment.tex:8087 | not formalized |
| `L:mean-coefficient-holder` | Lemma | notes_stratonovich_ham_second_moment.tex:8293 | not formalized |
| `L:positive-series-type` | Lemma | notes_stratonovich_ham_second_moment.tex:8419 | formalized, manuscript hypotheses |
| `P:static-minorant-lower` | Proposition | notes_stratonovich_ham_second_moment.tex:8472 | not formalized |
| `P:near-static-mean-gap` | Proposition | notes_stratonovich_ham_second_moment.tex:8560 | not formalized |
| `L:full-moment-coefficient-holder` | Lemma | notes_stratonovich_ham_second_moment.tex:8668 | not formalized |
| `P:moment-growth-logconvex` | Proposition | notes_stratonovich_ham_second_moment.tex:8770 | inputs supplied, steps/narrower |
| `C:static-moment-constant-continuity` | Corollary | notes_stratonovich_ham_second_moment.tex:8843 | inputs supplied, steps/narrower |
| `L:white-clock-laplace` | Lemma | notes_stratonovich_ham_second_moment.tex:8915 | formalized, manuscript hypotheses |
| `P:clock-copy-obstruction` | Proposition | notes_stratonovich_ham_second_moment.tex:9033 | formalized, manuscript hypotheses |
| `P:actual-operator-driver` | Proposition | integrated_actual_operator_driver.tex:27 | not formalized |
| `L:driver-noise-basis` | Lemma | integrated_actual_operator_driver.tex:59 | not formalized |
| `L:driver-covariance-coefficients` | Lemma | integrated_actual_operator_driver.tex:152 | not formalized |
| `L:driver-gain-localization` | Lemma | integrated_actual_operator_driver.tex:211 | not formalized |
| `L:driver-actual-variances` | Lemma | integrated_actual_operator_driver.tex:303 | not formalized |
| `L:driver-dominated-tails` | Lemma | integrated_actual_operator_driver.tex:466 | not formalized |
| `L:driver-gaussian-tail-average` | Lemma | integrated_actual_operator_driver.tex:496 | not formalized |
| `L:driver-interval-limit` | Lemma | integrated_actual_operator_driver.tex:542 | inputs supplied, steps/narrower |
| `L:driver-holder-limit` | Lemma | integrated_actual_operator_driver.tex:671 | inputs supplied, steps/narrower |
| `L:cameron-fractional-products` | Lemma | integrated_cameron_mean.tex:30 | not formalized |
| `P:cameron-spatial-map` | Proposition | integrated_cameron_mean.tex:104 | not formalized |
| `L:cameron-supported-tensor` | Lemma | integrated_cameron_mean.tex:194 | not formalized |
| `P:cameron-temporal-map` | Proposition | integrated_cameron_mean.tex:226 | not formalized |
| `P:cameron-full-mean` | Proposition | integrated_cameron_mean.tex:322 | not formalized |
| `L:cameron-actual-residual` | Lemma | integrated_cameron_mean.tex:434 | not formalized |
| `P:cameron-actual-embedding` | Proposition | integrated_cameron_mean.tex:499 | not formalized |
| `L:gaussian-scalar-powers` | Lemma | integrated_compact_gaussian.tex:14 | formalized, manuscript hypotheses |
| `L:gaussian-trace-bounds` | Lemma | integrated_compact_gaussian.tex:68 | formalized, manuscript hypotheses |
| `P:finite-gaussian-matrix` | Proposition | integrated_compact_gaussian.tex:138 | formalized, manuscript hypotheses |
| `L:cutoff-factorization` | Lemma | integrated_compact_gaussian.tex:283 | not formalized |
| `P:cutoff-singular-values` | Proposition | integrated_compact_gaussian.tex:469 | not formalized |
| `P:compact-two-envelopes` | Proposition | integrated_compact_gaussian.tex:583 | not formalized |
| `L:compact-positive-order` | Lemma | integrated_compact_gaussian.tex:663 | not formalized |
| `P:localized-finite-variance` | Proposition | integrated_compact_gaussian.tex:721 | not formalized |
| `C:finite-gaussian-operators` | Corollary | integrated_compact_gaussian.tex:785 | not formalized |
| `P:cutoff-boundary-tests` | Proposition | integrated_compact_gaussian.tex:882 | not formalized |
| `P:compact-ground-family` | Proposition | integrated_compact_mean_family.tex:34 | not formalized |
| `L:compact-fractional-phase` | Lemma | integrated_compact_mean_family.tex:141 | not formalized |
| `P:compact-E-wave` | Proposition | integrated_compact_mean_family.tex:207 | not formalized |
| `P:compact-F-projection` | Proposition | integrated_compact_mean_family.tex:329 | not formalized |
| `P:compact-F-complement` | Proposition | integrated_compact_mean_family.tex:437 | not formalized |
| `L:compact-raw-profile` | Lemma | integrated_compact_mean_family.tex:529 | not formalized |
| `P:compact-original-common-trial` | Proposition | integrated_compact_mean_family.tex:611 | not formalized |
| `L:constant-phase-free` | Lemma | integrated_constant_phase_young.tex:21 | not formalized |
| `P:constant-phase-driver` | Proposition | integrated_constant_phase_young.tex:113 | not formalized |
| `L:constant-source-response` | Lemma | integrated_constant_phase_young.tex:170 | not formalized |
| `P:constant-young-linear` | Proposition | integrated_constant_phase_young.tex:234 | not formalized |
| `P:constant-gaussian-flow` | Proposition | integrated_constant_phase_young.tex:335 | not formalized |
| `L:constant-source-solution` | Lemma | integrated_constant_phase_young.tex:490 | not formalized |
| `P:constant-raw-average` | Proposition | integrated_constant_phase_young.tex:566 | not formalized |
| `P:constant-compact-base` | Proposition | integrated_constant_phase_young.tex:666 | not formalized |
| `P:masked-spectral-growth` | Proposition | integrated_covariance_foundation.tex:37 | formalized, manuscript hypotheses |
| `P:masked-auxiliary-norm` | Proposition | integrated_covariance_foundation.tex:106 | formalized, manuscript hypotheses |
| `L:masked-time-completion` | Lemma | integrated_covariance_foundation.tex:188 | formalized, manuscript hypotheses |
| `P:masked-noise-completion` | Proposition | integrated_covariance_foundation.tex:249 | inputs supplied, steps/narrower |
| `P:masked-quotient-obstruction` | Proposition | integrated_covariance_foundation.tex:340 | formalized, manuscript hypotheses, narrower conclusion |
| `L:masked-temporal-modulation` | Lemma | integrated_covariance_foundation.tex:396 | formalized, manuscript hypotheses |
| `L:masked-trig-products` | Lemma | integrated_covariance_foundation.tex:459 | formalized, manuscript hypotheses |
| `L:masked-continuous-wave` | Lemma | integrated_covariance_foundation.tex:494 | formalized, manuscript hypotheses |
| `L:exact-canonical-scaling` | Lemma | integrated_exact_scaling.tex:10 | inputs supplied, steps/narrower |
| `P:tube-wiener-realization` | Proposition | integrated_gaussian_tubes.tex:26 | not formalized |
| `L:tube-closed-geometry` | Lemma | integrated_gaussian_tubes.tex:151 | not formalized |
| `P:tube-rayleigh-transfer` | Proposition | integrated_gaussian_tubes.tex:226 | inputs supplied, every conclusion proved |
| `P:tube-actual-law` | Proposition | integrated_gaussian_tubes.tex:298 | not formalized |
| `L:tube-actual-endpoint` | Lemma | integrated_gaussian_tubes.tex:381 | not formalized |
| `P:tube-coarse-envelope` | Proposition | integrated_gaussian_tubes.tex:461 | not formalized |
| `L:tube-rayleigh-tail` | Lemma | integrated_gaussian_tubes.tex:553 | formalized, manuscript hypotheses, narrower conclusion |
| `L:tube-half-action` | Lemma | integrated_gaussian_tubes.tex:581 | formalized, manuscript hypotheses |
| `L:positive-raw-embedding` | Lemma | integrated_intrinsic_constant.tex:24 | formalized, manuscript hypotheses, narrower conclusion |
| `L:positive-physical-gram` | Lemma | integrated_intrinsic_constant.tex:144 | formalized, manuscript hypotheses, narrower conclusion |
| `L:positive-uniform-optimizer` | Lemma | integrated_intrinsic_constant.tex:205 | not formalized |
| `P:positive-signed-comparison` | Proposition | integrated_intrinsic_constant.tex:289 | not formalized |
| `P:positive-score-cutoff` | Proposition | integrated_intrinsic_constant.tex:392 | not formalized |
| `T:intrinsic-second-moment` | Theorem | integrated_intrinsic_constant.tex:437 | outside Lean (main theorem) |
| `L:masked-chain-comparison` | Lemma | integrated_masked_moments.tex:24 | not formalized |
| `P:masked-source-moments` | Proposition | integrated_masked_moments.tex:130 | not formalized |
| `P:masked-canonical-transfer` | Proposition | integrated_masked_moments.tex:213 | not formalized |
| `L:occupation-raw-square` | Lemma | integrated_occupation_ceiling.tex:25 | formalized, manuscript hypotheses, narrower conclusion |
| `P:raw-occupation-energy` | Proposition | integrated_occupation_ceiling.tex:112 | formalized, manuscript hypotheses |
| `L:occupation-rayleigh-selection` | Lemma | integrated_occupation_ceiling.tex:181 | formalized, manuscript hypotheses, narrower conclusion |
| `T:intrinsic-occupation-ceiling` | Theorem | integrated_occupation_ceiling.tex:249 | formalized, manuscript hypotheses, narrower conclusion |
| `C:intrinsic-spatial-bracket` | Corollary | integrated_occupation_ceiling.tex:320 | formalized, manuscript hypotheses, narrower conclusion |
| `L:point-actual-finiteness` | Lemma | integrated_point_transfer.tex:20 | not formalized |
| `L:point-fast-sources` | Lemma | integrated_point_transfer.tex:76 | not formalized |
| `L:point-compact-source` | Lemma | integrated_point_transfer.tex:161 | not formalized |
| `P:point-source-cone` | Proposition | integrated_point_transfer.tex:245 | not formalized |
| `P:original-point-transfer` | Proposition | integrated_point_transfer.tex:330 | not formalized |
| `L:gram-scalar-algebra` | Lemma | integrated_positive_gram.tex:27 | formalized, manuscript hypotheses |
| `L:gram-dual-minimum` | Lemma | integrated_positive_gram.tex:53 | not formalized |
| `P:gram-positive-optimizer` | Proposition | integrated_positive_gram.tex:115 | inputs supplied, steps/narrower |
| `L:gram-realization` | Lemma | integrated_positive_gram.tex:182 | not formalized |
| `P:gram-entrywise-comparison` | Proposition | integrated_positive_gram.tex:214 | inputs supplied, steps/narrower |
| `L:radius-outer-maps` | Lemma | integrated_radius_anchor.tex:39 | not formalized |
| `P:radius-compact-envelopes` | Proposition | integrated_radius_anchor.tex:103 | not formalized |
| `P:radius-actual-moments` | Proposition | integrated_radius_anchor.tex:192 | not formalized |
| `C:radius-covariance-residuals` | Corollary | integrated_radius_anchor.tex:305 | not formalized |
| `P:radius-mean-anchor` | Proposition | integrated_radius_anchor.tex:344 | inputs supplied, steps/narrower |
| `L:raw-block-inputs` | Lemma | integrated_raw_block_lower.tex:52 | inputs supplied, steps/narrower |
| `P:raw-block-gaussian-law` | Proposition | integrated_raw_block_lower.tex:150 | not formalized |
| `L:raw-block-uniform-error` | Lemma | integrated_raw_block_lower.tex:220 | not formalized |
| `L:raw-block-indexed-cone` | Lemma | integrated_raw_block_lower.tex:317 | inputs supplied, steps/narrower |
| `L:raw-block-restart` | Lemma | integrated_raw_block_lower.tex:467 | inputs supplied, steps/narrower |
| `P:raw-block-point-comparison` | Proposition | integrated_raw_block_lower.tex:585 | not formalized |
| `P:raw-block-original-lower` | Proposition | integrated_raw_block_lower.tex:740 | inputs supplied, steps/narrower |
| `L:signed-score-envelope` | Lemma | integrated_signed_moment_upper.tex:20 | not formalized |
| `P:signed-moment-bulk-tail` | Proposition | integrated_signed_moment_upper.tex:107 | not formalized |
| `P:signed-operator-upper` | Proposition | integrated_signed_moment_upper.tex:182 | not formalized |
| `P:original-signed-point-upper` | Proposition | integrated_signed_moment_upper.tex:246 | not formalized |
| `L:signed-limiting-multiplier` | Lemma | integrated_signed_static.tex:11 | not formalized |
| `P:signed-closed-form` | Proposition | integrated_signed_static.tex:50 | inputs supplied, steps/narrower |
| `L:signed-spectral-wave` | Lemma | integrated_signed_static.tex:137 | not formalized |
| `P:signed-physical-wave` | Proposition | integrated_signed_static.tex:233 | not formalized |
| `L:source-finite-comparison` | Lemma | integrated_source_convergence.tex:21 | formalized, manuscript hypotheses |
| `P:source-gaussian-transfer` | Proposition | integrated_source_convergence.tex:53 | not formalized |
| `L:source-spatial-heat` | Lemma | integrated_source_convergence.tex:169 | formalized, manuscript hypotheses |
| `L:source-retaining-isometry` | Lemma | integrated_source_convergence.tex:212 | not formalized |
| `P:source-canonical-convergence` | Proposition | integrated_source_convergence.tex:319 | not formalized |
| `L:source-pointfield-regularity` | Lemma | integrated_source_convergence.tex:450 | not formalized |
| `P:source-ordinary-response` | Proposition | integrated_source_convergence.tex:528 | not formalized |
| `L:spatial-physical-pair` | Lemma | integrated_spatial_occupation.tex:13 | formalized, manuscript hypotheses |
| `L:spatial-static-controls` | Lemma | integrated_spatial_occupation.tex:42 | formalized, manuscript hypotheses, narrower conclusion |
| `L:spatial-fourier-bound` | Lemma | integrated_spatial_occupation.tex:122 | formalized, manuscript hypotheses |
| `P:spatial-smooth-ratio` | Proposition | integrated_spatial_occupation.tex:224 | formalized, manuscript hypotheses, narrower conclusion |
| `P:spatial-four-linear` | Proposition | integrated_spatial_occupation.tex:298 | formalized, manuscript hypotheses |
| `P:spatial-energy-map` | Proposition | integrated_spatial_occupation.tex:406 | formalized, manuscript hypotheses, narrower conclusion |
| `L:occupation-kernel-row` | Lemma | integrated_spatial_occupation.tex:477 | formalized, manuscript hypotheses |
| `P:occupation-physical-class` | Proposition | integrated_spatial_occupation.tex:504 | formalized, manuscript hypotheses |
| `L:symplectic-free` | Lemma | integrated_symplectic_phase.tex:32 | inputs supplied, steps/narrower |
| `L:symplectic-source-mean` | Lemma | integrated_symplectic_phase.tex:163 | not formalized |
| `P:symplectic-source` | Proposition | integrated_symplectic_phase.tex:237 | not formalized |
| `P:symplectic-raw` | Proposition | integrated_symplectic_phase.tex:279 | not formalized |
| `P:symplectic-block-mean` | Proposition | integrated_symplectic_phase.tex:360 | not formalized |
| `L:equilibrium-gamma-beta` | Lemma | integrated_temporal_equilibrium.tex:14 | formalized, manuscript hypotheses |
| `L:temporal-equilibrium` | Lemma | integrated_temporal_equilibrium.tex:39 | formalized, manuscript hypotheses |
| `L:uniform-mean-cutoff` | Lemma | integrated_uniform_mean.tex:29 | not formalized |
| `L:uniform-mean-spatial-tails` | Lemma | integrated_uniform_mean.tex:71 | not formalized |
| `L:uniform-mean-tensor` | Lemma | integrated_uniform_mean.tex:188 | not formalized |
| `P:uniform-mean-regulator` | Proposition | integrated_uniform_mean.tex:262 | not formalized |
| `P:uniform-actual-cameron` | Proposition | integrated_uniform_mean.tex:353 | not formalized |
| `L:uniform-E-lift` | Lemma | integrated_uniform_products.tex:33 | not formalized |
| `P:uniform-E-spectral` | Proposition | integrated_uniform_products.tex:69 | not formalized |
| `P:uniform-rate-averaging` | Proposition | integrated_uniform_products.tex:246 | not formalized |
| `L:uniform-product-budgets` | Lemma | integrated_uniform_products.tex:336 | not formalized |
| `P:uniform-mean-product` | Proposition | integrated_uniform_products.tex:405 | not formalized |
| `C:uniform-polynomial-balls` | Corollary | integrated_uniform_products.tex:504 | not formalized |
| `P:uniform-arbitrary-residual` | Proposition | integrated_uniform_products.tex:547 | not formalized |
| `L:variational-heat-envelope` | Lemma | integrated_unmasked_variational.tex:29 | formalized, manuscript hypotheses |
| `L:variational-global-mean` | Lemma | integrated_unmasked_variational.tex:86 | formalized, manuscript hypotheses |
| `P:variational-unmasked-rate` | Proposition | integrated_unmasked_variational.tex:127 | formalized, manuscript hypotheses, narrower conclusion |
| `P:variational-remove-mask` | Proposition | integrated_unmasked_variational.tex:228 | inputs supplied, steps/narrower |
| `L:variational-control-dilation` | Lemma | integrated_unmasked_variational.tex:314 | formalized, manuscript hypotheses, narrower conclusion |
| `P:variational-positive-scores` | Proposition | integrated_unmasked_variational.tex:371 | formalized, manuscript hypotheses, narrower conclusion |
| `P:frequency-row` | Proposition | integrated_wave_variance.tex:48 | formalized, manuscript hypotheses |
| `C:frequency-time` | Corollary | integrated_wave_variance.tex:172 | formalized, manuscript hypotheses |
| `P:actual-wave-form` | Proposition | integrated_wave_variance.tex:247 | inputs supplied, steps/narrower |
| `L:phase-bessel` | Lemma | integrated_wave_variance.tex:426 | formalized, manuscript hypotheses |
| `P:wave-two-variances` | Proposition | integrated_wave_variance.tex:452 | inputs supplied, steps/narrower |
| `P:wave-square-columns` | Proposition | integrated_wave_variance.tex:568 | not formalized |
| `L:white-cdf-square` | Lemma | integrated_white_evaluation.tex:17 | not formalized |
| `P:white-spatial-energy` | Proposition | integrated_white_evaluation.tex:79 | inputs supplied, steps/narrower |
| `T:white-moment-bounds` | Theorem | integrated_white_evaluation.tex:140 | inputs supplied, steps/narrower |
| `C:white-relative-width` | Corollary | integrated_white_evaluation.tex:174 | formalized, manuscript hypotheses |
| `L:young-upper-growth` | Lemma | integrated_young_upper_foundation.tex:15 | not formalized |
| `P:young-upper-multiplicative` | Proposition | integrated_young_upper_foundation.tex:78 | not formalized |
