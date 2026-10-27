@[expose] public section

namespace BGS.Markoff

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

/-- Four raw projective corners, with one label for each factor of the corresponding weighted
initial form.  A normalization proof should inject its boundary points into this finite type. -/
abbrev splitTraceNormalizationBoundaryLabels (d e : ℕ) :=
  Fin 4 × Fin (Nat.gcd d e)

end
end BGS.Markoff
end
