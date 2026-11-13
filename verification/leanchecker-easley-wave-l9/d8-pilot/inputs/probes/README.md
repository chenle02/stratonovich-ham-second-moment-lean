# D8 pilot probe inputs

The fifteen probe files of the D8 pilot task, stored as `.lean.txt` so that
they are not Lean build inputs of this package (the job copied them into its
own scratch project, outside every library of `lakefile.toml`). Rename a file
to `.lean` to run it again. Their sha256 values before the rename are listed
in the job's own records in this directory.
