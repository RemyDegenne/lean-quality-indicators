# Poor simplification interfaces

Find concrete problems with the file's simp interface: a missing canonical simp lemma or
attribute, a rewrite in an unsuitable direction, competing rules, unwanted expansion or a
credible rewrite cycle. Give a specific expression, its desired normal form and the
relevant existing rules. Read the definitions and actual uses, then propose the exact
lemma, attribute or orientation change and explain why it improves those uses.

Do not recommend simp annotations solely because an identity looks simple. Consider
termination, canonical forms, assumptions, existing simp coverage and downstream effects.
Without running Lean, do not claim a loop or simplifier failure was experimentally observed.
