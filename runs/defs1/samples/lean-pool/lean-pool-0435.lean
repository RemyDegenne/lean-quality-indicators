@[expose] public section

namespace Homogenization

/-- Predicate-level vector `L²` membership on `U`. -/
noncomputable abbrev MemVectorL2 {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  MeasureTheory.MemLp f 2 (volumeMeasureOn U)

end Homogenization
end
