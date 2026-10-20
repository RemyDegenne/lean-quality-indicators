@[expose] public section

universe u

variable {R : Type*}

namespace QuadraticAlgebra

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

section CommSemiring

variable [CommSemiring R]

@[simp]
theorem C_eq_algebraMap : QuadraticAlgebra.C = (algebraMap R (QuadraticAlgebra R a b)) := rfl

end CommSemiring
end QuadraticAlgebra
end
