@[expose] public section

noncomputable section

section

open Complex Filter Set

open scoped Topology

namespace NumberField.Odlyzko

/-- A completed zeta pole factor used in the Odlyzko-bound argument. -/
noncomputable def completedZetaPoleFactor (s : ℂ) : ℂ :=
  s * (s - 1)

end NumberField.Odlyzko
end
end
end
