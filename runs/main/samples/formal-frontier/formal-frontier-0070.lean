public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace TopCat

namespace TopCat.Sheaf

variable {X : TopCat.{0}}

local instance (x : X) (U : Opens X) : Decidable (x ∈ U) := Classical.dec _

@[simp]
theorem toFlasqueResolution_f_zero (F : Sheaf AddCommGrpCat X) :
    (toFlasqueResolution F).f 0 = (toFlasqueEnvelope (X := X)).app F := by
  apply CochainComplex.fromSingle₀Equiv_symm_apply_f_zero

end TopCat.Sheaf
end
end
