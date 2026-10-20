public section

noncomputable section

namespace TauCeti

open CategoryTheory MulOpposite

open scoped TensorProduct

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)

local notation "Γ" => zigzagAlgebraInternalGrading k G

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

@[simp]
theorem zigzagGradedBimoduleUnitIso_inv_apply (x : zigzagGradedBimodule k G) :
    (zigzagGradedBimoduleUnitIso k G).inv.hom x = ULift.up x := (rfl)

end TauCeti
end
end
