@[expose] public section

local notation x " ⊗ₘ " y => TensorProduct.map x y

open scoped TensorProduct

variable {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B]

open scoped TensorProduct

variable {A B : Type*} [ha : starAlgebra A] [hb : starAlgebra B]
    [hA : QuantumSet A] [hB : QuantumSet B]

open scoped InnerProductSpace

attribute [local instance] starAlgebra.mulOpposite

attribute [local instance] InnerProductAlgebra.mulOpposite

attribute [local instance] QuantumSet.mulOpposite

/-- Opposite-algebra version of a module dual functional. -/
def Module.Dual.op {R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  (f : Module.Dual R A) :
  Module.Dual R Aᵐᵒᵖ :=
(unop R).toLinearMap ∘ₗ LinearMap.op f

end
