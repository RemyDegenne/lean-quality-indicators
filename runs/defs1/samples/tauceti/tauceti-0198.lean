public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

section Lift

variable {B : Type*} [Ring B] [Algebra k B]

/-- The universal property of the zigzag quotient: an algebra map out of the path algebra which
kills every uniform relator factors through the quotient. -/
noncomputable def zigzagLift (f : pathAlgebra k (DoubledQuiver G) →ₐ[k] B)
    (hf : ∀ x, IsZigzagRelator k G x → f x = 0) : nonisolatedZigzagQuotient k G →ₐ[k] B :=
  Ideal.Quotient.liftₐ _ f fun _ ha =>
    (TwoSidedIdeal.mem_ker f).mp <| zigzagIdeal_le_ker k G f hf (TwoSidedIdeal.mem_asIdeal.mp ha)

end Lift
end TauCeti
end
