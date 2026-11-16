<div class="boundary" markdown="1">
**How to read the comparison status on this page.** This page is generated
by lean-pkg 0.29.0 and is reproduced without change. For a result whose
coverage row also names definition claims (47 of the 99 results in Lean),
it says "its statement was not compared by a second checker", and its
summary line counts only the other 52, because the comparator compares
theorem statements and not definitions. Every theorem claim that a row
names is compared: all 1553 theorems of `comparator.json`, in the
comparator receipt of this release. The definitions are checked by Lean's
kernel in the build; the comparator's restated theorems mention verbatim
copies of them (`ChallengeDefs/`), which
`scripts/comparator/CheckFidelity.lean` checks to be equal to the project's.
</div>
