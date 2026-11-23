# Completion record

What the Lean companion verifies of the manuscript, kept current at every milestone. Every milestone is an annotated git tag on the commit where the author closed the gate. The tags and the commits in this file belong to the private development repository named in `provenance/DEVELOPMENT.md`; the public repository carries only the release tags `v0.9.0` (the wave-L9 gate), `v0.10.0` (the wave-L13 and wave-L14 gates) and `v0.11.0` (the wave-L15 to wave-L21 gates), whose Lean proof files are those of the gate up to comments (release documentation added, cluster evidence redacted; `v0.10.0` also drops two claims of Lean-generated declarations, splits the comparator configuration and marks the helper claims `internal`; `v0.11.0` re-anchors the line citations to `edf7085f`; see `provenance/DEVELOPMENT.md`). Claims count Lean declarations in `claims.yaml`; coverage rows count manuscript labelled results (see `coverage.yaml` for the exact scope of each). "Same" = formalized with the manuscript's hypotheses; "inputs" = analytic inputs supplied as named hypotheses. Correspondence was checked by AI reviews from a different model family, not by a human; supplied inputs are not verified.

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
| `L15-gate` | `18c5c1d` | 2026-11-20 | `c3c2431d` (L15 citations; earlier rows stay on `39f2597a`, the same text) | 4705 | 3803 | 102: 64 / 36 / 2 | wave L15, item L15-UM in scope (a): the phase space `H^(1/2) x H^(-1/2)` with density of real tests, duality and multipliers; `L:uniform-E-lift` with nothing supplied (narrower: the lift `L_F` and the complex extension not formalized); the a.e. mean identity of `E:positive-raw-mean` and a canonical version agreeing a.e., for a supplied `UniformMeanRegulator`, so `L:positive-raw-embedding` is narrower with inputs supplied; closed by the author 2026-11-20 |
| `L16-gate` | `ebac849` | 2026-11-20 | `0788ddee` (book 1.1.0; the wave-L15 citations moved to it, earlier rows stay on `39f2597a`, the same text) | 5134 | 4137 | 109: 70 / 37 / 2 | wave L16, the Cameron-map chain: `L:cameron-fractional-products` in full; L15's named inputs `CameronSpatialMap` and `UniformMeanRegulator` constructed, with the named input `CutoffCompact` (the compactness sentence of `P:cutoff-singular-values`, kept by the author's decision); `L:positive-raw-embedding` with nothing supplied, conclusion full by the author's decision; `P:cameron-temporal-map` narrower; closed by the author 2026-11-20 |
| `L17-gate` | `68d0c5e` | 2026-11-21 | `0788ddee` (book 1.1.0) | 5642 | 4555 | 113: 72 / 39 / 2 | wave L17, the pairing-envelope chain: `L:translated-covariance-CS` and `L:pairing-product-envelope` in full with nothing supplied (label-set model M7, bridge from M4; interface amendment 1); `L:crude-corrected` and `P:envelope` narrower with `MixedMoment` supplied (diagram bounds in `d = 1, 2`, and `d = 3` for Green-smoothed kernels uniformly in `eta`; `E:envelope-growth` without the comparison `rho > kappa`); closed by the author 2026-11-21 |
| `L18-gate` | `6e4644d` | 2026-11-21 | `0788ddee` (book 1.1.0) | 6022 | 4862 | 115: 74 / 39 / 2 | wave L18, spatial Wick measures and the deterministic half of `L:joint-fixed-order`: `L:spatial-wick-measures` in full with nothing supplied (model M8); `L:joint-fixed-order` narrower with nothing supplied (deterministic half; the L^2 construction not formalized); the named input `DiagramLimits` discharged for every `H:homog` covariance in `d = 1, 2, 3`; closed by the author 2026-11-21 |
| `L19-gate` | `fe9f1de` | 2026-11-22 | `0788ddee` (book 1.1.0) | 6314 | 5077 | 117: 80 / 35 / 2 | wave L19, the `L^2` construction on source fields (model M9): `P:mixed`, `L:vertex-crude` and `L:joint-fixed-order` with the manuscript's hypotheses; the named inputs `MixedMoment` and `FirstMomentSeries` discharged for the chaos terms and solution of every source field; closed by the author 2026-11-22 |
| `L20-gate` | `5cdd493` | 2026-11-23 | `0788ddee` (book 1.1.0) | 6620 | 5314 | 117: 84 / 31 / 2 | wave L20, the mild construction on source fields: `P:mild-construction` with the manuscript's hypotheses; the `d = 1` Riesz instance of `H:homog`, so the Riesz `hH` leaves three rows; `P:d1-upper`, `C:d1-first-calibration`, `P:low-alpha-upper` and `P:envelope` in full; comment-only docstring pass over 55 earlier files; closed by the author 2026-11-23 |
| `L21-gate` | `38a3e00` | 2026-11-23 | `0788ddee` (book 1.1.0) | 6632 | 5326 | 118: 85 / 31 / 2 | wave L21, the last proof wave of the author's end point: the named input `TubeAttained` discharged at the manuscript's tubes; `L:tube-closed-geometry` with the manuscript's hypotheses (narrower conclusion); `P:tube-rayleigh-transfer` with `TubeTail` the one input left; the deferred wave-L20 Lean-comment corrections; closed by the author 2026-11-23 |

Every tagged commit carries lean-pkg receipts or is a docs-only descendant of one (see `.lean-receipts/` and the README verification record). External kernel replays (`leanchecker --fresh` on Easley) cover every library module through wave L14 at `8f51004` (the wave-L13 and wave-L14 gates), the wave-L15 modules at `315a332` and the wave-L16 modules at `ebac849`, with default mode over all modules at each; see `verification/`.

## Lean freeze (2026-11-13) and wave L15

Wave L14 was to be the last Lean wave: the author froze the Lean work after it. On 2026-11-19 the author approved one further item, L15-UM in scope (a) (the uniform `E` lift and the mean identity of `E:positive-raw-mean`, with the spatial and temporal mean maps supplied as named inputs). On 2026-11-20 the author approved wave L16 (the Cameron-map chain: the core items L16-0 to L16-D and the re-anchor R1, with the default answers to its twelve decisions), which constructs those two named inputs; the compactness sentence of `P:cutoff-singular-values` stays the named input `CutoffCompact` (the author's decision of 2026-11-20). The author closed the L16 gate on 2026-11-20 (tag `L16-gate`) and approved wave L17 (the pairing-envelope chain, default answers to its twelve decisions), launched after the L16 gate. The author closed the L17 gate on 2026-11-21 (tag `L17-gate`) and approved wave L18 the same day (the Wick-measure chain and the discharge of the named input `DiagramLimits`, with the default answers to its thirteen decisions); the author closed the L18 gate on 2026-11-21 (tag `L18-gate`) and approved wave L19 the same day (the `L^2` construction of `L:joint-fixed-order`, `P:mixed`, `L:vertex-crude` and the discharge of the named inputs `MixedMoment` and `FirstMomentSeries`, with the default answers to its thirteen decisions). The author closed the L19 gate on 2026-11-22 (tag `L19-gate`) and approved wave L20 the same day (`P:mild-construction` for every source field, the `d = 1` Riesz instance of `H:homog`, the deferred wrappers and a comment-only docstring pass, with the default answers to its thirteen decisions). On 2026-11-23 the author set the end point of the Lean work: the companion closes after wave L20 and wave L21 (the named input `TubeAttained` of `L:tube-closed-geometry`); `SignedMultiplierForm`, `ThreeTransfer`, `TubeTail` and `CutoffCompact` stay supplied. The author closed the L20 gate on 2026-11-23 (tag `L20-gate`). The author closed the L21 gate on 2026-11-23 (tag `L21-gate`). With it the Lean work reaches the author's end point: no further proof waves are planned; the named inputs `SignedMultiplierForm`, `ThreeTransfer`, `TubeTail` and `CutoffCompact` stay supplied.

## Waves L15 to L21 (all gates closed; updated 2026-11-23)

The milestone table above lists closed gates only. The table by labelled result below is at the L21 gate.

| Wave | State | Content |
|---|---|---|
| L15 | gate closed by the author 2026-11-20 at `18c5c1d` (tag `L15-gate`): item L15-UM (UM-0, UM-1, UM-2) merged on branch `wave-l15/int` (`04f106c`, <MACHINE> build clean, standard axioms only); Lean statements reviewed by a second model family (DeepSeek V4 Pro scopes 1-3: PASS and PASS_WITH_NOTES, notes documentation only); documentation reviewed by GPT-6.2-Sol (scope 4: first round FAIL on documentation only, all 18 findings repaired; confirmation 4a PASS_WITH_NOTES, 4b FAIL on one wording overstatement, repaired at `04f6b6a` without a further review round); documentation with TeX citations at `c3c2431d` (book v1.0.2); comparator extended to all 3803 theorem claims (1577 credited, 2226 helper smoke check; the nine claims naming Lean-generated instances of `UniformMeanInterface` dropped, 4705 claims); receipts at `18c5c1d` (lower tier: 0 sorry, standard axioms, 4705 claims; comparator: 1577 + 2226 pass); Easley `leanchecker --fresh` 4/4 new modules and default mode 146/146 at `315a332` (no library file changed after it) | the phase space `H^(1/2) x H^(-1/2)` on the manuscript's Fourier norm, density of real tests, duality and multipliers (foundations); `L:uniform-E-lift` with nothing supplied (narrower: the lift `L_F` and the complex extension not formalized); the a.e. mean identity of `E:positive-raw-mean` and a canonical version agreeing a.e., for a supplied `UniformMeanRegulator` (named inputs `UniformMeanRegulator` and `CameronSpatialMap`), so `L:positive-raw-embedding` becomes a narrower result with inputs supplied |
| L16 | gate closed by the author 2026-11-20 at `ebac849` (tag `L16-gate`): items L16-0 (interface), A1, A2, B1, B2, C and D merged on branch `wave-l16/int` (`1d9883a`: <MACHINE> build 9208 jobs, 0 warnings; the 29 headline theorems on the standard axioms only; lean-fence and lean-regress CLEAN against `09d3406`); item R1 (the wave-L15 TeX citations moved from `c3c2431d` to `0788ddee`, book 1.1.0) and the documentation at `0788ddee`; 429 new claims (334 theorems, 95 definitions; 5134 in all), comparator extended to all 4137 theorem claims (1677 credited, 2460 helper smoke check); Lean statements reviewed by DeepSeek V4 Pro (scopes S1-S4: PASS_WITH_NOTES, notes documentation only); documentation reviewed by GPT-6.2-Sol (first round FAIL on documentation only, all 19 findings repaired at `ca75d10`; one confirmation per packet on `108fa80`: no CRITICAL or MAJOR finding left after adjudication, six wording fixes applied at `5f0d8c8` without a further review round; four Lean docstring line numbers deferred to a later docs-only Lean pass); receipts at `ebac849` (lower tier: 0 sorry, standard axioms, 5134 claims; comparator: 1677 + 2460 pass); Easley `leanchecker --fresh` 16/16 (the 15 new modules and the umbrella) and default mode 161/161 at `ebac849` | `L:cameron-fractional-products` in full; `L:uniform-mean-cutoff`, `P:cameron-temporal-map` (not trace class as the cell sums of decision 7), `L:uniform-mean-tensor` on finite tensors and the map `U` of `P:cameron-full-mean` narrower with nothing supplied; `P:cameron-spatial-map` (`E` part) and `P:uniform-mean-regulator` (the regulator with the first bound; a.e. compact values of its mean in the `L(E)`-valued `L^r` model, a separate result) with the named input `CutoffCompact` (the compactness sentence of `P:cutoff-singular-values`, not formalized); L15's named inputs `CameronSpatialMap` and `UniformMeanRegulator` constructed; `L:positive-raw-embedding` with nothing supplied, conclusion full by the author's decision of 2026-11-20 ("Upgrade L:positive-raw-embedding to full; keep P:cameron-temporal-map weaker."; the mean identity is proved for maps constructed to meet the frozen specifications, not identified in Lean with the section's maps) |
| L17 | gate closed by the author 2026-11-21 at `68d0c5e` (tag `L17-gate`): items L17-0 (interface `PairingInterface`, with interface amendment 1 of 2026-11-20: `M4BridgeTarget` requires finite Green densities), A, B, C, D, E and the time-boxed item E3 (`d = 3`) merged on branch `wave-l17/int` (`f04817d`; <MACHINE> build of the umbrella and `Axioms`, 9223 jobs, 0 warnings; `#print axioms` on all 508 new declarations: standard axioms only; no anonymous instance; lean-fence and lean-regress CLEAN against `38ac748`); TeX citations at `0788ddee` (book 1.1.0); 508 new claims (418 theorems, 90 definitions; 5642 in all), comparator extended to all 4555 theorem claims (1798 credited, 2757 helper smoke check); gate commit `68d0c5e` (<MACHINE>: `Challenge` and `Solution` build clean, 9364 jobs; CheckFidelity 4555 of 4555 Challenge types equal, 0 problems; lean-fence and lean-regress CLEAN against `38ac748`, the `sorry` of `Challenge` and of its manual statement files exempt by design); Lean statements reviewed by DeepSeek V4 Pro (seven scopes: PASS_WITH_NOTES, high, no MAJOR or CRITICAL finding); documentation reviewed by GPT-6.2-Sol (first round FAIL on documentation only, all findings repaired at `a34a5eb`; one confirmation per packet: docs-b FAIL with three PARTIAL and three new MINOR items, docs-a FAIL with four PARTIAL and two new MINOR items, its report extracted from the reviewer's final message and not accepted by the runner, accepted by the author; the remainders applied at `be81d6e` without a further review round); receipts at `68d0c5e` (`d1a3a12`; lower tier: 0 sorry, standard axioms, 5642 claims; comparator: 1798 + 2757 pass); Easley `leanchecker --fresh` 16/16 (the 15 new modules and the umbrella) and default mode 176/176 at `68d0c5e` (`0bf7a39`); Lean docstring line numbers and wording deferred to a later docs-only Lean pass | `L:translated-covariance-CS` and `L:pairing-product-envelope` in full with nothing supplied (the latter on the label-set two-chain model, model choice M7, with a bridge from M4); `L:crude-corrected` and `P:envelope` on the diagram model M4: the diagram bounds at every noise width in `d = 1, 2`, and in `d = 3` for the Green-smoothed kernels uniformly in `eta > 0` (the limit `eta -> 0` not formalized), the moment sentences in `d = 1, 2` for random variables with the supplied input `MixedMoment` (narrower, inputs supplied); `E:envelope-growth` as the two-sided log-growth bound of the numerical majorant `B_K` with the exponent `rho = beta/(beta-1)` (the comparison `rho > kappa` of its display not stated in Lean, the author's decision of 2026-11-20) |
| L18 | gate closed by the author 2026-11-21 at `6e4644d` (tag `L18-gate`): items L18-0 (interface `WickInterface`, model M8), A (`RieszDiagramLimits`, with the decision-5 add-on `RieszDiagramLimitsHomog`), B (`WickSpectral`), C (`WickBridge`, `WickMass`, `WickScaling`), D (`WickStep4`, `WickMeasures`) and E (`JointFixedOrder`, `EnvelopeD3Wave`, `JointTail`) merged on branch `wave-l18/int` with the hypothesis-free wrappers `WickFinal` (`ae463de`; <MACHINE> build of the umbrella and `Axioms`, 9236 jobs, 0 warnings; `#print axioms` on all 380 new declarations: standard axioms only; no anonymous instance; no fallback named input used); TeX citations at `0788ddee` (book 1.1.0), docstring line numbers corrected comment-only before the gate; 380 new claims (307 theorems, 73 definitions; 6022 in all), comparator extended to all 4862 theorem claims (1902 credited, 2960 helper smoke check); gate commit `6e4644d` (<MACHINE>: `Challenge` and `Solution` build clean, 9386 jobs; CheckFidelity 4862 of 4862 Challenge types equal, 0 problems; lean-fence and lean-regress CLEAN against `02f922f`, the `sorry` of `Challenge` and of its manual statement files exempt by design); Lean statements reviewed by DeepSeek V4 Pro (eight scopes: PASS and PASS_WITH_NOTES, high, no MAJOR or CRITICAL finding; the route differences of items A, C, D and E judged valid proofs); documentation reviewed by GPT-6.2-Sol (first round FAIL on documentation only, two CRITICAL findings downgraded to MINOR by the author, all findings repaired at `a83c778`; one confirmation per packet with the broadened citation audit: FAIL with MINOR remainders, applied at `aad8b91` without a further review round); receipts at `6e4644d` (`afd018d`; lower tier: 0 sorry, standard axioms, 6022 claims; comparator: 1902 + 2960 pass); Easley `leanchecker --fresh` 14/14 (the 13 new modules and the umbrella) and default mode 189/189 at `6e4644d` (`eb19140`); Lean docstring line numbers and wording deferred to a later docs-only Lean pass | `L:spatial-wick-measures` in full with nothing supplied, `d = 1, 2, 3`, on the gap-coordinate model M8 (Steps 2-3 by the envelope route (b) instead of Brownian occupation moments); `L:joint-fixed-order` narrower: the deterministic half (finite joint diagram limits at arbitrary vertexwise spatial and temporal rates, with `E:joint-temporal-tail`), the `L^2` construction of `X_n` not formalized; the named input `DiagramLimits` discharged for every `H:homog` covariance in `d = 1, 2, 3` (in `d = 1` also by domination), so the limit-coefficient displays of `P:d1-upper` need no supplied input and the order-four identification of `P:riesz-small` is proved; the `d = 3` diagram halves of `L:crude-corrected` and `P:envelope` for the wave Green measure; `MixedMoment` stays supplied |
| L19 | gate closed by the author 2026-11-22 at `fe9f1de` (tag `L19-gate`): items L19-0 (interface `SourceInterface`, model M9; M9 fidelity review by DeepSeek V4 Pro, three scopes PASS / PASS_WITH_NOTES, no interface defect, three documentation items done at the gate), A (`SourceIsonormal`), B (`SourceFeatures`), C (`SourceWick`, `SourceReversal`), D (`SourceFixedOrder`, `SourceGreenFirst`), E (`SourceMixed`, `SourceExpansion`) and G (`SourceVertexCrude`) merged on branch `wave-l19/int` with the hypothesis-free wrappers `SourceFinal` (`8e61d09`; <MACHINE> build of the umbrella and `Axioms`, 9247 jobs; `#print axioms` on all 294 new declarations: standard axioms only; four named instances, no anonymous instance; neither fallback named input (`SourceNoise`, `TerminalReversal`) used). Gate commit `fe9f1de` (the last commit changing Lean, claims or comparator files): claims 6314 (L19: 215 theorems, 77 definitions; all names resolve, 0 problems); comparator extended to all 5077 theorems (1978 credited, 3099 helpers; 46 statements restated from source; <MACHINE> `lake build Challenge Solution` clean, 9405 jobs; CheckFidelity 5077 of 5077 equal, 0 problems); lean-fence CLEAN against `470ee26` with `--check-inputs`, the 20 input records declared and the 21 interface names of the approved wave as approvals (`SourceField`, the 15 targets, `SourceModel`, `SourceNoise`, `TerminalReversal`, and the discharged `MixedMoment`, `FirstMomentSeries` as conclusions and in the generic moment-step lemmas); lean-regress CLEAN (build log and `#print axioms` of all 294 new declarations). Lean statements reviewed by DeepSeek V4 Pro (eight scopes: PASS and PASS_WITH_NOTES, no CRITICAL finding; the undisclosed `MixedMoment` hypotheses rated MAJOR by the author and disclosed); documentation reviewed by GPT-6.2-Sol (first round FAIL on documentation only, the accepted findings repaired at `e6e1cb1`; one confirmation per packet with the broadened citation audit, its wording fixes applied at `487872f` and `b994fc0` without a further review round, the author's decisions of 2026-11-22); receipts at `fe9f1de` (`5e2b86f`; lower tier: 0 sorry, standard axioms, 6314 claims; comparator: 1978 + 3099 pass, both configurations); Easley `leanchecker --fresh` 12/12 (the 11 new modules and the umbrella) and default mode 200/200 at `fe9f1de` (`a330722`); Lean docstring line numbers and wording deferred to the docs-only pass of wave L20. | `P:mixed`, `L:vertex-crude` and `L:joint-fixed-order` formalized with the manuscript's hypotheses (for every source field, model M9, non-vacuous at the constructed `m9`); `MixedMoment` and `FirstMomentSeries` discharged for the chaos terms and solution of every source field, so `L:crude-corrected` and `L:white-test` move to full with the manuscript's hypotheses, `P:envelope` and `P:low-alpha-upper` to the manuscript's hypotheses with a narrower conclusion, and `C:d1-first-calibration` to inputs supplied with a narrower conclusion (the conditional rate clause for the constructed `u` is not stated in Lean; the composed wrapper is deferred to the next Lean pass, the author's decision of 2026-11-22); the three Riesz consumer rows keep the Riesz instance of `H:homog` explicit (the author's decision of 2026-11-22). |
| L20 | gate closed by the author 2026-11-23 at `5cdd493` (tag `L20-gate`; integration `1b3cb25`): items L20-0 (interface `MildInterface`; fidelity review by DeepSeek V4 Pro, PASS_WITH_NOTES, two NOTEs accepted without change), A (`MildOccupied`), B (`MildPolyMem`), C (`MildFields`), D (`MildTerminalFubini`, `MildPartialVertex`), E (`MildGreenWidth`), F (`MildConstruction`), the hypothesis-free wrappers `MildFinal`, R (`RieszInstanceOne`), W (`CleanupWrappers`) and DOC (comment-only docstring pass over 39 earlier library modules and 16 of their `ChallengeDefs/` mirrors, 55 files); <MACHINE> build of the umbrella and `Axioms` clean (9258 jobs); `#print axioms` on all 321 new declarations: standard axioms only; five named instances, no anonymous instance; neither fallback named input (`JointMeasurability`, `TerminalFubini`) used; docstring TeX citations at `0788ddee` corrected comment-only at the gate (`3d651aa`); gate commit `5cdd493` (the last commit changing Lean, claims or comparator files): claims 6620 (L20: 237 theorems, 69 definitions; all names resolve, 0 problems); comparator extended to all 5314 theorems (2049 credited, 3265 helpers; 83 statements restated from source; <MACHINE> `lake build Challenge Solution` clean, 9423 jobs; CheckFidelity 5314 of 5314 equal, 0 problems; every existing `ChallengeDefs` copy, DOC's comment-edited mirrors included, regenerated byte-identical); lean-fence CLEAN against `d813957` with `--check-inputs`, 22 input records declared and as approvals the 22 L20 targets it flags plus the Lean-route predicates `MildOccupied.RepOn` and `LinOn` (confirmed by the author 2026-11-23; the fallbacks `JointMeasurability`, `TerminalFubini` and the carried-over `SourceField`, `SourceModel` approved but not flagged); lean-regress CLEAN (build log and `#print axioms` of all 321 new declarations; no statement change in an earlier module; DOC's comment-stripped diff empty for all 55 earlier files it touched). Lean statements reviewed by DeepSeek V4 Pro (eight scopes: four PASS, four PASS_WITH_NOTES, high, no MAJOR or CRITICAL finding); documentation reviewed by GPT-6.2-Sol (first round FAIL on documentation only; docs-only repairs `d3b2f8e`, `9706469`, `4fe5c33`, `fdbb0ae` after one confirmation per packet and one narrow confirmation; the review decisions confirmed by the author 2026-11-23); receipts at `5cdd493` (`4842df8`; lower tier: 0 sorry, standard axioms, 6620 claims; comparator: 2049 + 3265 pass, both configurations); Easley `leanchecker --fresh` 12/12 (the 11 new modules and the umbrella) and default mode 211/211 at `5cdd493` (`1b94926`); 21 Lean-comment items from the reviews applied comment-only in the L21 gate commit | `P:mild-construction` formalized with the manuscript's hypotheses for every source field (`E:mild-construction` along arbitrary rates, decision 2; the `d = 3` Green-width sentence by the common-noise route, decision 3; non-vacuous at `m9`); the Riesz instance of `H:homog` in `d = 1` (`E:d1-covariances`) formalized, so the Riesz `hH` leaves `P:d1-upper`, `P:riesz-small` and `C:d1-first-calibration`; `P:d1-upper` (white wrapper), `C:d1-first-calibration` (conditional rate clause for the constructed `u`), `P:low-alpha-upper` (second inequality) and `P:envelope` (`rho > kappa`) in full with the manuscript's hypotheses; `P:riesz-small` with the manuscript's hypotheses and a narrower conclusion (the multiplicities of `E:total-four`). |
| L21 | gate closed by the author 2026-11-23 at `38a3e00` (tag `L21-gate`): the one item of the author's end point of 2026-11-23, `SourceTubeAttained` (`fcb3f58`, merged with the umbrella import last), and the comment-only Lean docstring corrections deferred from the wave-L20 reviews (C1-C19 of the GPT-6.2-Sol documentation review except C11, whose cited line 5534 is right at `0788ddee`, and the DeepSeek gate items g1.1 and g3.2: 20 library modules and 8 of their `ChallengeDefs/` mirrors, 28 files; every regenerated `ChallengeDefs` copy byte-identical); <MACHINE> build of the umbrella and `Axioms` clean (9259 jobs, 0 warnings); `#print axioms` on all 12 new declarations: standard axioms only; no instance declared; the statement review of the module (DeepSeek V4 Pro, one scope: PASS_WITH_NOTES, high, no MINOR, MAJOR or CRITICAL finding; seven citation notes repaired comment-only at `fcb3f58`); gate commit `38a3e00` (the last commit changing Lean, claims or comparator files): claims 6632 (L21: 12 theorems; all names resolve, 0 problems); comparator extended to all 5326 theorems (2056 credited, 3270 helpers; one statement restated from source, four under `open scoped Pointwise`; <MACHINE> `lake build Challenge Solution` clean, 9424 jobs; CheckFidelity 5326 of 5326 equal, 0 problems); lean-fence CLEAN against `5cdd493` with `--check-inputs`, the 22 input records of wave L20 and its two fallbacks declared, `TubeAttained` (the conclusion discharged) and `TubeTail` (the one input left) as approvals (confirmed by the author 2026-11-23); lean-regress CLEAN (build log and `#print axioms` of the 12 new declarations; no statement change in an earlier module; comment-stripped diff empty for all 28 earlier files changed); documentation reviewed by GPT-6.2-Sol (two packets: the L21 records PASS_WITH_NOTES, high; the comment-only commit FAIL on two wording findings rated MINOR under the author's delegation; docs-only repairs `adeac06`; four Lean-comment rewordings and two claim summaries deferred to the v0.11.0 release preparation; the review decisions confirmed by the author 2026-11-23); receipts at `38a3e00` (`39c4365`; lower tier: 0 sorry, standard axioms, 6632 claims; comparator: 2056 + 3270 pass, both configurations); Easley `leanchecker --fresh` 2/2 (`SourceTubeAttained` and the umbrella) and default mode 212/212 at `38a3e00` (`ade3f31`) | `TubeAttained` proved at the manuscript's tubes for a compact `M_delta` (closed images by Banach-Alaoglu without separability, attainment by rescaling); `L:tube-closed-geometry` with the manuscript's hypotheses and a narrower conclusion (every tube closed, `{d_delta <= r} = T_r`, `d_delta` lower semicontinuous; the Gaussian tail and the almost sure finiteness not formalized); `P:tube-rayleigh-transfer` whole with one named input, `TubeTail`. At the end point the named inputs still supplied are `SignedMultiplierForm`, `ThreeTransfer`, `TubeTail` and `CutoffCompact`. |

## Completion by labelled result (manuscript edf7085f, book 1.1.3; companion: the L13/L14 gate commit 8f51004 plus wave L15 (gate `18c5c1d`), wave L16 (gate `ebac849`) and wave L17 (gate `68d0c5e`), wave L18 (gate `6e4644d`), wave L19 (gate `fe9f1de`) and wave L20 (gate `5cdd493`) and wave L21 (gate `38a3e00`), gates L13-gate to L21-gate; the coordinates in this table were re-anchored from 39f2597a (rows of waves through L14) and 0788ddee (rows of waves L15 to L21) to edf7085f without changing their TeX line numbers)

| Status | Count | Share |
|---|---|---|
| formalized, manuscript hypotheses | 59 | 27% |
| formalized, manuscript hypotheses, narrower conclusion | 22 | 10% |
| inputs supplied, every conclusion proved | 1 | 0% |
| inputs supplied, steps/narrower | 30 | 14% |
| outside Lean (main theorem) | 2 | 1% |
| not formalized | 106 | 48% |
| total labelled results (Theorem, Proposition, Lemma, Corollary) | 220 | 100% |

No theorem of the manuscript is verified end to end. Of the four main theorems, two (`T:full-upper` and `T:intrinsic-second-moment`) are recorded as outside Lean; `T:intrinsic-occupation-ceiling` is formalized in both forms with the exact constant `C_occ`, over the class `O` itself (wave L14), for `S_c^pos`, and its moment sentence `C_2 <= U_2` is not formalized; `T:white-moment-bounds` is proved for the variational value `S_2^pos` in place of `C_2`, with the white-noise energy `E_sp = c^2/6` of `P:white-spatial-energy` supplied (reserved package B9), and its time exponent and the case `c = 0` are not formalized. The remaining work is dominated by foundations Mathlib lacks (Gaussian chaos, Cameron-Martin, the identification of the source-field `L^2` series constructed in wave L19 (a mild solution in the source's sense since wave L20, with no uniqueness assertion) with the solution of the SPDE, Young integration of operator paths and self-adjoint operators).

## Covered displays and remarks (not counted above)

Four coverage rows are for a displayed equation or a remark rather than a numbered result:

| Label | Coverage class | Conclusion |
|---|---|---|
| `E:driver-parameters` | same-assumptions | full |
| `E:kappa` | same-assumptions | full |
| `E:masked-time-schur` | same-assumptions | full |
| `R:gaussian-one-variance-test` | same-assumptions | full |

## Every labelled result

| Label | Kind | File:line (edf7085f) | Status |
|---|---|---|---|
| `T:first` | Theorem | notes_stratonovich_ham_second_moment.tex:604 | not formalized |
| `T:crude` | Theorem | notes_stratonovich_ham_second_moment.tex:640 | not formalized |
| `P:Jensen` | Proposition | notes_stratonovich_ham_second_moment.tex:659 | not formalized |
| `T:intro-upper` | Theorem | notes_stratonovich_ham_second_moment.tex:699 | not formalized |
| `T:intro-second-moment` | Theorem | notes_stratonovich_ham_second_moment.tex:753 | not formalized |
| `P:mixed` | Proposition | notes_stratonovich_ham_second_moment.tex:834 | formalized, manuscript hypotheses |
| `L:white-test` | Lemma | notes_stratonovich_ham_second_moment.tex:940 | formalized, manuscript hypotheses |
| `L:damped-homogeneous-norms` | Lemma | notes_stratonovich_ham_second_moment.tex:1011 | formalized, manuscript hypotheses |
| `L:translated-covariance-CS` | Lemma | notes_stratonovich_ham_second_moment.tex:1187 | formalized, manuscript hypotheses |
| `L:pairing-product-envelope` | Lemma | notes_stratonovich_ham_second_moment.tex:1489 | formalized, manuscript hypotheses |
| `L:spatial-wick-measures` | Lemma | notes_stratonovich_ham_second_moment.tex:1679 | formalized, manuscript hypotheses |
| `L:joint-fixed-order` | Lemma | notes_stratonovich_ham_second_moment.tex:1854 | formalized, manuscript hypotheses |
| `L:crude-corrected` | Lemma | notes_stratonovich_ham_second_moment.tex:1978 | formalized, manuscript hypotheses |
| `L:vertex-crude` | Lemma | notes_stratonovich_ham_second_moment.tex:2062 | formalized, manuscript hypotheses |
| `P:mild-construction` | Proposition | notes_stratonovich_ham_second_moment.tex:2152 | formalized, manuscript hypotheses |
| `P:envelope` | Proposition | notes_stratonovich_ham_second_moment.tex:2352 | formalized, manuscript hypotheses |
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
| `P:riesz-small` | Proposition | notes_stratonovich_ham_second_moment.tex:5125 | formalized, manuscript hypotheses, narrower conclusion |
| `L:d1-spatial` | Lemma | notes_stratonovich_ham_second_moment.tex:5359 | formalized, manuscript hypotheses |
| `P:d1-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:5454 | formalized, manuscript hypotheses |
| `L:low-alpha-convolution` | Lemma | notes_stratonovich_ham_second_moment.tex:5566 | formalized, manuscript hypotheses |
| `L:alpha-one-convolution` | Lemma | notes_stratonovich_ham_second_moment.tex:5635 | formalized, manuscript hypotheses |
| `P:low-alpha-upper` | Proposition | notes_stratonovich_ham_second_moment.tex:5711 | formalized, manuscript hypotheses |
| `C:d1-first-calibration` | Corollary | notes_stratonovich_ham_second_moment.tex:5830 | formalized, manuscript hypotheses |
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
| `L:cameron-fractional-products` | Lemma | integrated_cameron_mean.tex:30 | formalized, manuscript hypotheses |
| `P:cameron-spatial-map` | Proposition | integrated_cameron_mean.tex:104 | inputs supplied, steps/narrower |
| `L:cameron-supported-tensor` | Lemma | integrated_cameron_mean.tex:194 | not formalized |
| `P:cameron-temporal-map` | Proposition | integrated_cameron_mean.tex:226 | formalized, manuscript hypotheses, narrower conclusion |
| `P:cameron-full-mean` | Proposition | integrated_cameron_mean.tex:322 | formalized, manuscript hypotheses, narrower conclusion |
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
| `L:tube-closed-geometry` | Lemma | integrated_gaussian_tubes.tex:151 | formalized, manuscript hypotheses, narrower conclusion |
| `P:tube-rayleigh-transfer` | Proposition | integrated_gaussian_tubes.tex:226 | inputs supplied, every conclusion proved |
| `P:tube-actual-law` | Proposition | integrated_gaussian_tubes.tex:298 | not formalized |
| `L:tube-actual-endpoint` | Lemma | integrated_gaussian_tubes.tex:381 | not formalized |
| `P:tube-coarse-envelope` | Proposition | integrated_gaussian_tubes.tex:461 | not formalized |
| `L:tube-rayleigh-tail` | Lemma | integrated_gaussian_tubes.tex:553 | formalized, manuscript hypotheses, narrower conclusion |
| `L:tube-half-action` | Lemma | integrated_gaussian_tubes.tex:581 | formalized, manuscript hypotheses |
| `L:positive-raw-embedding` | Lemma | integrated_intrinsic_constant.tex:24 | formalized, manuscript hypotheses |
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
| `L:uniform-mean-cutoff` | Lemma | integrated_uniform_mean.tex:40 | formalized, manuscript hypotheses, narrower conclusion |
| `L:uniform-mean-spatial-tails` | Lemma | integrated_uniform_mean.tex:82 | not formalized |
| `L:uniform-mean-tensor` | Lemma | integrated_uniform_mean.tex:199 | formalized, manuscript hypotheses, narrower conclusion |
| `P:uniform-mean-regulator` | Proposition | integrated_uniform_mean.tex:273 | inputs supplied, steps/narrower |
| `P:uniform-actual-cameron` | Proposition | integrated_uniform_mean.tex:364 | not formalized |
| `L:uniform-E-lift` | Lemma | integrated_uniform_products.tex:33 | formalized, manuscript hypotheses, narrower conclusion |
| `P:uniform-E-spectral` | Proposition | integrated_uniform_products.tex:71 | not formalized |
| `P:uniform-rate-averaging` | Proposition | integrated_uniform_products.tex:248 | not formalized |
| `L:uniform-product-budgets` | Lemma | integrated_uniform_products.tex:338 | not formalized |
| `P:uniform-mean-product` | Proposition | integrated_uniform_products.tex:407 | not formalized |
| `C:uniform-polynomial-balls` | Corollary | integrated_uniform_products.tex:506 | not formalized |
| `P:uniform-arbitrary-residual` | Proposition | integrated_uniform_products.tex:549 | not formalized |
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
