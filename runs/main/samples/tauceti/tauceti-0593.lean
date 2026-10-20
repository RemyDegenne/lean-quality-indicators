public noncomputable section

open scoped AbstractMeasure

variable {G H R : Type*} [TopologicalSpace G] [TopologicalSpace H]
  [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

namespace AbstractMeasure

variable [Monoid G] [ContinuousMul G]

variable [LocallyCompactSpace G]

@[simp]
theorem algebraMap_apply (r : R) (f : C(G, R)) : algebraMap R D(G, R) r f = r * f 1 := by
  simp [Algebra.algebraMap_eq_smul_one]

end AbstractMeasure
end
