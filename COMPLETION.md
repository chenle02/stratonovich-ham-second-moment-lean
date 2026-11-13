# Completion record

What the Lean companion verifies of the manuscript, kept current at every milestone. Every milestone is an annotated git tag on the commit where the author closed the gate. The tags and the commits in this file belong to the private development repository named in `provenance/DEVELOPMENT.md`; the public repository carries only the release tag `v0.9.0`, whose Lean files and other build inputs are those of the wave-L9 gate (release documentation added, cluster evidence redacted). Claims count Lean declarations in `claims.yaml`; coverage rows count manuscript labelled results (see `coverage.yaml` for the exact scope of each). "Same" = formalized with the manuscript's hypotheses; "inputs" = analytic inputs supplied as named hypotheses. Correspondence was checked by AI reviews from a different model family, not by a human; supplied inputs are not verified.

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

Every tagged commit carries lean-pkg receipts or is a docs-only descendant of one (see `.lean-receipts/` and the README verification record). External kernel replays (`leanchecker --fresh` on Easley) cover every library module through wave L9, all of them at `6eb79c7` (the wave-L9 gate); see `verification/`.

## In progress (not yet gated; updated 2026-11-12)

The milestone table above lists closed gates only. The table by labelled result below is at the wave-L9 gate; waves L10 to L14 are not counted anywhere yet.

| Wave | State | Content |
|---|---|---|
| L10 | all eight items integrated; comparator over 2268 theorem claims; external kernel replay of its 21 new modules passed; documentation being brought to the wave-L9 conventions before its reviews | higher Riesz bound in full for d = 2 and 3 with the optimal constant, the white-noise model and the white moment bounds for S_2^pos (spatial energy supplied), the fixed split (model-free core, and the assembly on the Fock model with its analytic inputs supplied), alpha-one convolution from the homogeneity hypothesis alone |
| L11 | five items done (four integrated); documentation drafted; documentation merge after wave L10 | the spatial column bound of the Fock form proved for a concrete Fourier-side model; the chain measures of the terminal Wick lemma constructed, the lemma and the second-moment sentence of the uniform series tail stated for them with the manuscript's hypotheses only, and their Green regularization limit; the static interaction bounds with fewer supplied inputs; the finite word cutoff for several modes per color, which removes the fixed split's added hypothesis on the cutoff coefficients (the Duhamel word expansion of the coefficients supplied instead) |
| L12 | four items done and checked independently; the re-anchor to the current manuscript and the remaining items wait for the L11 documentation merge | terminal Wick comparison for the constructed chain measures; spectral identification of the smoothed covariance (damped homogeneous norms with nothing supplied); source finite comparison and the tube half action; the Fock sandwich proved on the concrete Fourier-side model |
| L13 | three items done and checked independently; the two-chain diagram model built, its fidelity review passed the definitions and asked for two refutation repairs (running); the diagram bounds wait for the repair | the variational global mean with every mixed derivative bounded; the real-H clause of the masked auxiliary norm; an in-domain refutation for the static-phase shift bound; the diagram model with the mixed-moment proposition as a supplied input |
| L14 | three items done and checked independently; a follow-up running | the completion spaces of the occupation layer (raw square and embedding, still narrower); source spatial heat lemma in full and the physical Gram vectors; the d = 3 endpoint lemmas (positive definiteness of product Riesz densities supplied) and their two corollaries |

## Completion by labelled result (manuscript a284420, companion 6eb79c7, gate L9-gate)

| Status | Count | Share |
|---|---|---|
| formalized, manuscript hypotheses | 25 | 11% |
| formalized, manuscript hypotheses, narrower conclusion | 18 | 8% |
| inputs supplied, every conclusion proved | 0 | 0% |
| inputs supplied, steps/narrower | 30 | 14% |
| outside Lean (main theorem) | 3 | 1% |
| not formalized | 144 | 65% |
| total labelled results (Theorem, Proposition, Lemma, Corollary) | 220 | 100% |

No theorem of the manuscript is verified end to end. Of the four main theorems, three are recorded as outside Lean; `T:intrinsic-occupation-ceiling` is formalized in both forms with the exact constant `C_occ`, over the class `O` modelled by joint representatives, for `S_c^pos`; its moment sentence `C_2 <= U_2` is not formalized. The remaining work is dominated by foundations Mathlib lacks (Gaussian chaos, Cameron-Martin, the chaos expansion of the solution, Young integration of operator paths, Sobolev spaces and self-adjoint operators).

## Covered displays and remarks (not counted above)

Four coverage rows are for a displayed equation or a remark rather than a numbered result:

| Label | Coverage class | Conclusion |
|---|---|---|
| `E:driver-parameters` | same-assumptions | full |
| `E:kappa` | same-assumptions | full |
| `E:masked-time-schur` | same-assumptions | full |
| `R:gaussian-one-variance-test` | same-assumptions | full |

## Every labelled result

| Label | Kind | File:line (a284420) | Status |
|---|---|---|---|
| `T:first` | Theorem | notes_stratonovich_ham_second_moment.tex:445 | not formalized |
| `T:crude` | Theorem | notes_stratonovich_ham_second_moment.tex:475 | not formalized |
| `P:Jensen` | Proposition | notes_stratonovich_ham_second_moment.tex:494 | not formalized |
| `T:intro-upper` | Theorem | notes_stratonovich_ham_second_moment.tex:534 | not formalized |
| `T:intro-second-moment` | Theorem | notes_stratonovich_ham_second_moment.tex:583 | not formalized |
| `P:mixed` | Proposition | notes_stratonovich_ham_second_moment.tex:658 | not formalized |
| `L:white-test` | Lemma | notes_stratonovich_ham_second_moment.tex:734 | not formalized |
| `L:damped-homogeneous-norms` | Lemma | notes_stratonovich_ham_second_moment.tex:804 | formalized, manuscript hypotheses, narrower conclusion |
| `L:translated-covariance-CS` | Lemma | notes_stratonovich_ham_second_moment.tex:952 | not formalized |
| `L:pairing-product-envelope` | Lemma | notes_stratonovich_ham_second_moment.tex:1233 | not formalized |
| `L:spatial-wick-measures` | Lemma | notes_stratonovich_ham_second_moment.tex:1395 | not formalized |
| `L:joint-fixed-order` | Lemma | notes_stratonovich_ham_second_moment.tex:1543 | not formalized |
| `L:crude-corrected` | Lemma | notes_stratonovich_ham_second_moment.tex:1643 | not formalized |
| `L:vertex-crude` | Lemma | notes_stratonovich_ham_second_moment.tex:1705 | not formalized |
| `P:mild-construction` | Proposition | notes_stratonovich_ham_second_moment.tex:1774 | inputs supplied, steps/narrower |
| `P:envelope` | Proposition | notes_stratonovich_ham_second_moment.tex:1937 | not formalized |
| `L:phase-contractions` | Lemma | notes_stratonovich_ham_second_moment.tex:2072 | formalized, manuscript hypotheses |
| `P:static-phase-variance` | Proposition | notes_stratonovich_ham_second_moment.tex:2165 | not formalized |
| `L:complex-phase` | Lemma | notes_stratonovich_ham_second_moment.tex:2288 | inputs supplied, steps/narrower |
| `L:fock-form` | Lemma | notes_stratonovich_ham_second_moment.tex:2472 | inputs supplied, steps/narrower |
| `L:finite-word-cutoff` | Lemma | notes_stratonovich_ham_second_moment.tex:2531 | inputs supplied, steps/narrower |
| `P:static-phase-all-orders` | Proposition | notes_stratonovich_ham_second_moment.tex:2578 | inputs supplied, steps/narrower |
| `C:static-interaction` | Corollary | notes_stratonovich_ham_second_moment.tex:2686 | inputs supplied, steps/narrower |
| `L:interval-contractions` | Lemma | notes_stratonovich_ham_second_moment.tex:2829 | inputs supplied, steps/narrower |
| `L:interval-complex` | Lemma | notes_stratonovich_ham_second_moment.tex:2900 | inputs supplied, steps/narrower |
| `L:inventory-product` | Lemma | notes_stratonovich_ham_second_moment.tex:2986 | formalized, manuscript hypotheses |
| `L:fixed-split` | Lemma | notes_stratonovich_ham_second_moment.tex:3053 | not formalized |
| `P:interval-coefficients` | Proposition | notes_stratonovich_ham_second_moment.tex:3402 | inputs supplied, steps/narrower |
| `L:terminal-wick` | Lemma | notes_stratonovich_ham_second_moment.tex:3600 | inputs supplied, steps/narrower |
| `L:uniform-series-tail` | Lemma | notes_stratonovich_ham_second_moment.tex:3703 | inputs supplied, steps/narrower |
| `T:full-upper` | Theorem | notes_stratonovich_ham_second_moment.tex:3758 | outside Lean (main theorem) |
| `P:white-four` | Proposition | notes_stratonovich_ham_second_moment.tex:4160 | not formalized |
| `L:static-four` | Lemma | notes_stratonovich_ham_second_moment.tex:4222 | not formalized |
| `P:riesz-small` | Proposition | notes_stratonovich_ham_second_moment.tex:4313 | not formalized |
| `L:d1-spatial` | Lemma | notes_stratonovich_ham_second_moment.tex:4525 | not formalized |
| `P:d1-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:4605 | not formalized |
| `L:low-alpha-convolution` | Lemma | notes_stratonovich_ham_second_moment.tex:4702 | formalized, manuscript hypotheses |
| `L:alpha-one-convolution` | Lemma | notes_stratonovich_ham_second_moment.tex:4760 | not formalized |
| `P:low-alpha-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:4820 | not formalized |
| `C:d1-first-calibration` | Corollary | notes_stratonovich_ham_second_moment.tex:4923 | not formalized |
| `P:higher-transfer` | Proposition | notes_stratonovich_ham_second_moment.tex:5020 | not formalized |
| `L:higher-riesz` | Lemma | notes_stratonovich_ham_second_moment.tex:5167 | inputs supplied, steps/narrower |
| `C:higher-riesz` | Corollary | notes_stratonovich_ham_second_moment.tex:5239 | not formalized |
| `P:higher-obstructions` | Proposition | notes_stratonovich_ham_second_moment.tex:5272 | not formalized |
| `L:static-holder-input` | Lemma | notes_stratonovich_ham_second_moment.tex:5395 | not formalized |
| `P:static-holder-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:5442 | not formalized |
| `L:planar-endpoints` | Lemma | notes_stratonovich_ham_second_moment.tex:5671 | not formalized |
| `L:planar-static-input` | Lemma | notes_stratonovich_ham_second_moment.tex:5827 | not formalized |
| `P:planar-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:5893 | not formalized |
| `C:planar-range` | Corollary | notes_stratonovich_ham_second_moment.tex:6065 | not formalized |
| `L:product-endpoints` | Lemma | notes_stratonovich_ham_second_moment.tex:6106 | not formalized |
| `L:plane-endpoints` | Lemma | notes_stratonovich_ham_second_moment.tex:6235 | not formalized |
| `L:endpoint-closure` | Lemma | notes_stratonovich_ham_second_moment.tex:6317 | not formalized |
| `P:three-transfer` | Proposition | notes_stratonovich_ham_second_moment.tex:6422 | not formalized |
| `C:three-product-riesz` | Corollary | notes_stratonovich_ham_second_moment.tex:6796 | not formalized |
| `C:three-finite-images` | Corollary | notes_stratonovich_ham_second_moment.tex:6841 | not formalized |
| `L:physical-spectral-energy` | Lemma | notes_stratonovich_ham_second_moment.tex:6929 | not formalized |
| `L:mean-coefficient-holder` | Lemma | notes_stratonovich_ham_second_moment.tex:7116 | not formalized |
| `L:positive-series-type` | Lemma | notes_stratonovich_ham_second_moment.tex:7222 | formalized, manuscript hypotheses |
| `P:static-minorant-lower` | Proposition | notes_stratonovich_ham_second_moment.tex:7265 | not formalized |
| `P:near-static-mean-gap` | Proposition | notes_stratonovich_ham_second_moment.tex:7337 | not formalized |
| `L:full-moment-coefficient-holder` | Lemma | notes_stratonovich_ham_second_moment.tex:7434 | not formalized |
| `P:moment-growth-logconvex` | Proposition | notes_stratonovich_ham_second_moment.tex:7517 | inputs supplied, steps/narrower |
| `C:static-moment-constant-continuity` | Corollary | notes_stratonovich_ham_second_moment.tex:7575 | inputs supplied, steps/narrower |
| `L:white-clock-laplace` | Lemma | notes_stratonovich_ham_second_moment.tex:7646 | formalized, manuscript hypotheses |
| `P:clock-copy-obstruction` | Proposition | notes_stratonovich_ham_second_moment.tex:7754 | formalized, manuscript hypotheses |
| `P:actual-operator-driver` | Proposition | integrated_actual_operator_driver.tex:26 | not formalized |
| `L:driver-noise-basis` | Lemma | integrated_actual_operator_driver.tex:58 | not formalized |
| `L:driver-covariance-coefficients` | Lemma | integrated_actual_operator_driver.tex:121 | not formalized |
| `L:driver-gain-localization` | Lemma | integrated_actual_operator_driver.tex:165 | not formalized |
| `L:driver-actual-variances` | Lemma | integrated_actual_operator_driver.tex:245 | not formalized |
| `L:driver-dominated-tails` | Lemma | integrated_actual_operator_driver.tex:372 | not formalized |
| `L:driver-gaussian-tail-average` | Lemma | integrated_actual_operator_driver.tex:397 | not formalized |
| `L:driver-interval-limit` | Lemma | integrated_actual_operator_driver.tex:427 | inputs supplied, steps/narrower |
| `L:driver-holder-limit` | Lemma | integrated_actual_operator_driver.tex:528 | inputs supplied, steps/narrower |
| `L:cameron-fractional-products` | Lemma | integrated_cameron_mean.tex:26 | not formalized |
| `P:cameron-spatial-map` | Proposition | integrated_cameron_mean.tex:77 | not formalized |
| `L:cameron-supported-tensor` | Lemma | integrated_cameron_mean.tex:139 | not formalized |
| `P:cameron-temporal-map` | Proposition | integrated_cameron_mean.tex:168 | not formalized |
| `P:cameron-full-mean` | Proposition | integrated_cameron_mean.tex:230 | not formalized |
| `L:cameron-actual-residual` | Lemma | integrated_cameron_mean.tex:316 | not formalized |
| `P:cameron-actual-embedding` | Proposition | integrated_cameron_mean.tex:359 | not formalized |
| `L:gaussian-scalar-powers` | Lemma | integrated_compact_gaussian.tex:13 | formalized, manuscript hypotheses |
| `L:gaussian-trace-bounds` | Lemma | integrated_compact_gaussian.tex:47 | formalized, manuscript hypotheses |
| `P:finite-gaussian-matrix` | Proposition | integrated_compact_gaussian.tex:98 | formalized, manuscript hypotheses |
| `L:cutoff-factorization` | Lemma | integrated_compact_gaussian.tex:205 | not formalized |
| `P:cutoff-singular-values` | Proposition | integrated_compact_gaussian.tex:304 | not formalized |
| `P:compact-two-envelopes` | Proposition | integrated_compact_gaussian.tex:385 | not formalized |
| `L:compact-positive-order` | Lemma | integrated_compact_gaussian.tex:436 | not formalized |
| `P:localized-finite-variance` | Proposition | integrated_compact_gaussian.tex:465 | not formalized |
| `C:finite-gaussian-operators` | Corollary | integrated_compact_gaussian.tex:508 | not formalized |
| `P:cutoff-boundary-tests` | Proposition | integrated_compact_gaussian.tex:567 | not formalized |
| `P:compact-ground-family` | Proposition | integrated_compact_mean_family.tex:34 | not formalized |
| `L:compact-fractional-phase` | Lemma | integrated_compact_mean_family.tex:114 | not formalized |
| `P:compact-E-wave` | Proposition | integrated_compact_mean_family.tex:162 | not formalized |
| `P:compact-F-projection` | Proposition | integrated_compact_mean_family.tex:256 | not formalized |
| `P:compact-F-complement` | Proposition | integrated_compact_mean_family.tex:338 | not formalized |
| `L:compact-raw-profile` | Lemma | integrated_compact_mean_family.tex:398 | not formalized |
| `P:compact-original-common-trial` | Proposition | integrated_compact_mean_family.tex:461 | not formalized |
| `L:constant-phase-free` | Lemma | integrated_constant_phase_young.tex:21 | not formalized |
| `P:constant-phase-driver` | Proposition | integrated_constant_phase_young.tex:97 | not formalized |
| `L:constant-source-response` | Lemma | integrated_constant_phase_young.tex:137 | not formalized |
| `P:constant-young-linear` | Proposition | integrated_constant_phase_young.tex:190 | not formalized |
| `P:constant-gaussian-flow` | Proposition | integrated_constant_phase_young.tex:259 | not formalized |
| `L:constant-source-solution` | Lemma | integrated_constant_phase_young.tex:381 | not formalized |
| `P:constant-raw-average` | Proposition | integrated_constant_phase_young.tex:439 | not formalized |
| `P:constant-compact-base` | Proposition | integrated_constant_phase_young.tex:522 | not formalized |
| `P:masked-spectral-growth` | Proposition | integrated_covariance_foundation.tex:34 | formalized, manuscript hypotheses |
| `P:masked-auxiliary-norm` | Proposition | integrated_covariance_foundation.tex:88 | formalized, manuscript hypotheses, narrower conclusion |
| `L:masked-time-completion` | Lemma | integrated_covariance_foundation.tex:141 | formalized, manuscript hypotheses |
| `P:masked-noise-completion` | Proposition | integrated_covariance_foundation.tex:188 | inputs supplied, steps/narrower |
| `P:masked-quotient-obstruction` | Proposition | integrated_covariance_foundation.tex:258 | formalized, manuscript hypotheses, narrower conclusion |
| `L:masked-temporal-modulation` | Lemma | integrated_covariance_foundation.tex:300 | formalized, manuscript hypotheses |
| `L:masked-trig-products` | Lemma | integrated_covariance_foundation.tex:347 | formalized, manuscript hypotheses |
| `L:masked-continuous-wave` | Lemma | integrated_covariance_foundation.tex:378 | formalized, manuscript hypotheses |
| `L:exact-canonical-scaling` | Lemma | integrated_exact_scaling.tex:4 | inputs supplied, steps/narrower |
| `P:tube-wiener-realization` | Proposition | integrated_gaussian_tubes.tex:21 | not formalized |
| `L:tube-closed-geometry` | Lemma | integrated_gaussian_tubes.tex:127 | not formalized |
| `P:tube-rayleigh-transfer` | Proposition | integrated_gaussian_tubes.tex:184 | not formalized |
| `P:tube-actual-law` | Proposition | integrated_gaussian_tubes.tex:251 | not formalized |
| `L:tube-actual-endpoint` | Lemma | integrated_gaussian_tubes.tex:318 | not formalized |
| `P:tube-coarse-envelope` | Proposition | integrated_gaussian_tubes.tex:379 | not formalized |
| `L:tube-rayleigh-tail` | Lemma | integrated_gaussian_tubes.tex:458 | formalized, manuscript hypotheses, narrower conclusion |
| `L:tube-half-action` | Lemma | integrated_gaussian_tubes.tex:485 | not formalized |
| `L:positive-raw-embedding` | Lemma | integrated_intrinsic_constant.tex:23 | formalized, manuscript hypotheses, narrower conclusion |
| `L:positive-physical-gram` | Lemma | integrated_intrinsic_constant.tex:113 | not formalized |
| `L:positive-uniform-optimizer` | Lemma | integrated_intrinsic_constant.tex:158 | not formalized |
| `P:positive-signed-comparison` | Proposition | integrated_intrinsic_constant.tex:220 | not formalized |
| `P:positive-score-cutoff` | Proposition | integrated_intrinsic_constant.tex:298 | not formalized |
| `T:intrinsic-second-moment` | Theorem | integrated_intrinsic_constant.tex:332 | outside Lean (main theorem) |
| `L:masked-chain-comparison` | Lemma | integrated_masked_moments.tex:24 | not formalized |
| `P:masked-source-moments` | Proposition | integrated_masked_moments.tex:101 | not formalized |
| `P:masked-canonical-transfer` | Proposition | integrated_masked_moments.tex:162 | not formalized |
| `L:occupation-raw-square` | Lemma | integrated_occupation_ceiling.tex:24 | not formalized |
| `P:raw-occupation-energy` | Proposition | integrated_occupation_ceiling.tex:93 | formalized, manuscript hypotheses, narrower conclusion |
| `L:occupation-rayleigh-selection` | Lemma | integrated_occupation_ceiling.tex:150 | formalized, manuscript hypotheses, narrower conclusion |
| `T:intrinsic-occupation-ceiling` | Theorem | integrated_occupation_ceiling.tex:205 | formalized, manuscript hypotheses, narrower conclusion |
| `C:intrinsic-spatial-bracket` | Corollary | integrated_occupation_ceiling.tex:253 | formalized, manuscript hypotheses, narrower conclusion |
| `L:point-actual-finiteness` | Lemma | integrated_point_transfer.tex:20 | not formalized |
| `L:point-fast-sources` | Lemma | integrated_point_transfer.tex:62 | not formalized |
| `L:point-compact-source` | Lemma | integrated_point_transfer.tex:127 | not formalized |
| `P:point-source-cone` | Proposition | integrated_point_transfer.tex:192 | not formalized |
| `P:original-point-transfer` | Proposition | integrated_point_transfer.tex:245 | not formalized |
| `L:gram-scalar-algebra` | Lemma | integrated_positive_gram.tex:26 | formalized, manuscript hypotheses |
| `L:gram-dual-minimum` | Lemma | integrated_positive_gram.tex:52 | not formalized |
| `P:gram-positive-optimizer` | Proposition | integrated_positive_gram.tex:101 | inputs supplied, steps/narrower |
| `L:gram-realization` | Lemma | integrated_positive_gram.tex:149 | not formalized |
| `P:gram-entrywise-comparison` | Proposition | integrated_positive_gram.tex:175 | inputs supplied, steps/narrower |
| `L:radius-outer-maps` | Lemma | integrated_radius_anchor.tex:39 | not formalized |
| `P:radius-compact-envelopes` | Proposition | integrated_radius_anchor.tex:89 | not formalized |
| `P:radius-actual-moments` | Proposition | integrated_radius_anchor.tex:159 | not formalized |
| `C:radius-covariance-residuals` | Corollary | integrated_radius_anchor.tex:248 | not formalized |
| `P:radius-mean-anchor` | Proposition | integrated_radius_anchor.tex:281 | inputs supplied, steps/narrower |
| `L:raw-block-inputs` | Lemma | integrated_raw_block_lower.tex:51 | inputs supplied, steps/narrower |
| `P:raw-block-gaussian-law` | Proposition | integrated_raw_block_lower.tex:120 | not formalized |
| `L:raw-block-uniform-error` | Lemma | integrated_raw_block_lower.tex:166 | not formalized |
| `L:raw-block-indexed-cone` | Lemma | integrated_raw_block_lower.tex:233 | inputs supplied, steps/narrower |
| `L:raw-block-restart` | Lemma | integrated_raw_block_lower.tex:339 | inputs supplied, steps/narrower |
| `P:raw-block-point-comparison` | Proposition | integrated_raw_block_lower.tex:423 | not formalized |
| `P:raw-block-original-lower` | Proposition | integrated_raw_block_lower.tex:542 | inputs supplied, steps/narrower |
| `L:signed-score-envelope` | Lemma | integrated_signed_moment_upper.tex:20 | not formalized |
| `P:signed-moment-bulk-tail` | Proposition | integrated_signed_moment_upper.tex:88 | not formalized |
| `P:signed-operator-upper` | Proposition | integrated_signed_moment_upper.tex:150 | not formalized |
| `P:original-signed-point-upper` | Proposition | integrated_signed_moment_upper.tex:198 | not formalized |
| `L:signed-limiting-multiplier` | Lemma | integrated_signed_static.tex:11 | not formalized |
| `P:signed-closed-form` | Proposition | integrated_signed_static.tex:40 | not formalized |
| `L:signed-spectral-wave` | Lemma | integrated_signed_static.tex:111 | not formalized |
| `P:signed-physical-wave` | Proposition | integrated_signed_static.tex:176 | not formalized |
| `L:source-finite-comparison` | Lemma | integrated_source_convergence.tex:20 | not formalized |
| `P:source-gaussian-transfer` | Proposition | integrated_source_convergence.tex:43 | not formalized |
| `L:source-spatial-heat` | Lemma | integrated_source_convergence.tex:129 | not formalized |
| `L:source-retaining-isometry` | Lemma | integrated_source_convergence.tex:168 | not formalized |
| `P:source-canonical-convergence` | Proposition | integrated_source_convergence.tex:245 | not formalized |
| `L:source-pointfield-regularity` | Lemma | integrated_source_convergence.tex:347 | not formalized |
| `P:source-ordinary-response` | Proposition | integrated_source_convergence.tex:404 | not formalized |
| `L:spatial-physical-pair` | Lemma | integrated_spatial_occupation.tex:12 | formalized, manuscript hypotheses |
| `L:spatial-static-controls` | Lemma | integrated_spatial_occupation.tex:40 | formalized, manuscript hypotheses, narrower conclusion |
| `L:spatial-fourier-bound` | Lemma | integrated_spatial_occupation.tex:102 | formalized, manuscript hypotheses |
| `P:spatial-smooth-ratio` | Proposition | integrated_spatial_occupation.tex:167 | formalized, manuscript hypotheses, narrower conclusion |
| `P:spatial-four-linear` | Proposition | integrated_spatial_occupation.tex:220 | formalized, manuscript hypotheses, narrower conclusion |
| `P:spatial-energy-map` | Proposition | integrated_spatial_occupation.tex:301 | formalized, manuscript hypotheses, narrower conclusion |
| `L:occupation-kernel-row` | Lemma | integrated_spatial_occupation.tex:361 | formalized, manuscript hypotheses |
| `P:occupation-physical-class` | Proposition | integrated_spatial_occupation.tex:387 | formalized, manuscript hypotheses, narrower conclusion |
| `L:symplectic-free` | Lemma | integrated_symplectic_phase.tex:31 | inputs supplied, steps/narrower |
| `L:symplectic-source-mean` | Lemma | integrated_symplectic_phase.tex:136 | not formalized |
| `P:symplectic-source` | Proposition | integrated_symplectic_phase.tex:187 | not formalized |
| `P:symplectic-raw` | Proposition | integrated_symplectic_phase.tex:221 | not formalized |
| `P:symplectic-block-mean` | Proposition | integrated_symplectic_phase.tex:282 | not formalized |
| `L:equilibrium-gamma-beta` | Lemma | integrated_temporal_equilibrium.tex:13 | formalized, manuscript hypotheses |
| `L:temporal-equilibrium` | Lemma | integrated_temporal_equilibrium.tex:37 | formalized, manuscript hypotheses |
| `L:uniform-mean-cutoff` | Lemma | integrated_uniform_mean.tex:25 | not formalized |
| `L:uniform-mean-spatial-tails` | Lemma | integrated_uniform_mean.tex:61 | not formalized |
| `L:uniform-mean-tensor` | Lemma | integrated_uniform_mean.tex:145 | not formalized |
| `P:uniform-mean-regulator` | Proposition | integrated_uniform_mean.tex:202 | not formalized |
| `P:uniform-actual-cameron` | Proposition | integrated_uniform_mean.tex:278 | not formalized |
| `L:uniform-E-lift` | Lemma | integrated_uniform_products.tex:33 | not formalized |
| `P:uniform-E-spectral` | Proposition | integrated_uniform_products.tex:69 | not formalized |
| `P:uniform-rate-averaging` | Proposition | integrated_uniform_products.tex:206 | not formalized |
| `L:uniform-product-budgets` | Lemma | integrated_uniform_products.tex:279 | not formalized |
| `P:uniform-mean-product` | Proposition | integrated_uniform_products.tex:333 | not formalized |
| `C:uniform-polynomial-balls` | Corollary | integrated_uniform_products.tex:413 | not formalized |
| `P:uniform-arbitrary-residual` | Proposition | integrated_uniform_products.tex:451 | not formalized |
| `L:variational-heat-envelope` | Lemma | integrated_unmasked_variational.tex:24 | formalized, manuscript hypotheses |
| `L:variational-global-mean` | Lemma | integrated_unmasked_variational.tex:65 | formalized, manuscript hypotheses, narrower conclusion |
| `P:variational-unmasked-rate` | Proposition | integrated_unmasked_variational.tex:99 | formalized, manuscript hypotheses, narrower conclusion |
| `P:variational-remove-mask` | Proposition | integrated_unmasked_variational.tex:169 | inputs supplied, steps/narrower |
| `L:variational-control-dilation` | Lemma | integrated_unmasked_variational.tex:225 | formalized, manuscript hypotheses, narrower conclusion |
| `P:variational-positive-scores` | Proposition | integrated_unmasked_variational.tex:271 | formalized, manuscript hypotheses, narrower conclusion |
| `P:frequency-row` | Proposition | integrated_wave_variance.tex:47 | formalized, manuscript hypotheses |
| `C:frequency-time` | Corollary | integrated_wave_variance.tex:141 | formalized, manuscript hypotheses |
| `P:actual-wave-form` | Proposition | integrated_wave_variance.tex:212 | inputs supplied, steps/narrower |
| `L:phase-bessel` | Lemma | integrated_wave_variance.tex:346 | formalized, manuscript hypotheses |
| `P:wave-two-variances` | Proposition | integrated_wave_variance.tex:368 | inputs supplied, steps/narrower |
| `P:wave-square-columns` | Proposition | integrated_wave_variance.tex:465 | not formalized |
| `L:white-cdf-square` | Lemma | integrated_white_evaluation.tex:17 | not formalized |
| `P:white-spatial-energy` | Proposition | integrated_white_evaluation.tex:58 | inputs supplied, steps/narrower |
| `T:white-moment-bounds` | Theorem | integrated_white_evaluation.tex:101 | outside Lean (main theorem) |
| `C:white-relative-width` | Corollary | integrated_white_evaluation.tex:131 | formalized, manuscript hypotheses |
| `L:young-upper-growth` | Lemma | integrated_young_upper_foundation.tex:15 | not formalized |
| `P:young-upper-multiplicative` | Proposition | integrated_young_upper_foundation.tex:57 | not formalized |
