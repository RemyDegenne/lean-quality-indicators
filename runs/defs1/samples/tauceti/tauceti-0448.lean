public section

noncomputable section

open Metric Real

open scoped unitInterval

namespace TauCeti

/-- The north pole `(1, 0, 0)` of `S²`. -/
def Sphere2.north : Sphere2 :=
  ⟨!₂[1, 0, 0], by simp [EuclideanSpace.norm_eq, Fin.sum_univ_three]⟩

end TauCeti
end
end
