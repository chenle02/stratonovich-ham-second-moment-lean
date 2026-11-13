<div class="boundary" markdown="1">
**The generated coverage and verification pages come with v0.10.0.**
lean-pkg renders a package's verification and coverage pages only when every
theorem judged by the recorded comparator receipt is credited to a row of
`coverage.yaml`. In v0.9.0 the comparator judged all 2050 theorem claims, and
1408 of them are helper theorems that no coverage row names yet, so lean-pkg
0.29.0 refuses to render those pages. The helpers will be mapped in v0.10.0;
they are not attributed to results here. Until then the status of each
labelled result is in the [completion record](completion.html) and the
[statement ledger](statement-ledger.html), and
[`coverage.yaml`](https://github.com/chenle02/stratonovich-ham-second-moment-lean/blob/main/coverage.yaml)
is the machine-readable map of the covered results.
</div>
