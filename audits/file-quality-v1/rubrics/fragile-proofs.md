# Fragile proofs

Find proofs that depend on incidental generated names, implementation details rather than
an available public interface, or an unnecessarily sensitive chain of rewrites. Identify
the precise dependency and a plausible routine change that would break it. Propose a
replacement using a more stable interface or explicit argument, citing the actual lemmas.

Proof length, automation, a particular tactic, or unfolding a definition is not alone a
finding. The proposed replacement must improve maintainability without hiding the
mathematical reasoning. Do not invent hypothetical API changes merely to criticise a proof.
