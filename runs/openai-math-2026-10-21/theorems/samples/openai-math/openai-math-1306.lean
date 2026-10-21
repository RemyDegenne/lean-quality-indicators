namespace OAI

noncomputable section

open scoped BigOperators

open scoped BigOperators Matrix

open scoped Matrix

namespace CoboundaryExpanders.RankTwoGeometry

section

open MatrixOpposition TypedCosetFaces Elementary

open scoped Matrix

variable {K : Type} [Field K]

@[simp] lemma ca_mul (g h : upperGroup K 3) : ca (g*h) = ca g+ca h := by
  rw [←upper3_coords g,←upper3_coords h,upper3_mul]; rfl

end
end CoboundaryExpanders.RankTwoGeometry
end
end OAI
