@[expose] public section

namespace QuadraticAlgebra

variable {K R : Type*} {a b : R}

section omega

section

variable [Zero R] [One R]

/-- The representative of the root in the quadratic algebra -/
def omega : QuadraticAlgebra R a b :=
  ⟨0, 1⟩

end
end omega
end QuadraticAlgebra
end
