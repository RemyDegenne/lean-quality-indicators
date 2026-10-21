# Repeated proof machinery

Find a substantial mathematical argument repeated at two or more source locations,
including the target file. Identify the common steps, search for an existing lemma, and
give a precise shared statement with the actual hypotheses and dependencies. Check that
it covers every cited case. Explain how each proof uses it and why the helper, its proof
and all call sites are clearer overall.

Routine inductions, common tactics, short case splits, duplicate statements and a few
repeated calculation steps are insufficient. Do not flag an extraction that merely
relocates repetition or complicates the original arguments.
