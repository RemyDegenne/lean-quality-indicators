@[expose] public section

noncomputable section

namespace NavierStokes.BaseContextAssembly

open Set Function Filter WeightedClasses

open scoped ContDiff Topology BigOperators EuclideanSpace

/-- Plane: an abbreviation for `PressureStream.Plane`. -/
abbrev Plane := PressureStream.Plane

end NavierStokes.BaseContextAssembly
end
end
