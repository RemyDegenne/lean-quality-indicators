@[expose] public section

noncomputable section

namespace EuclideanJordan

open EuclideanJordanAlgebra (smul_mul jordan inner_assoc mul_one')

variable {J : Type*} [NormedAddCommGroup J] [InnerProductSpace ℝ J] [EuclideanJordanAlgebra J]

@[simp] theorem mem_peirceOneSub {c : J} (hc : c * c = c) {x : J} :
    x ∈ peirceOneSub hc ↔ c * x = x := Iff.rfl

end EuclideanJordan
end
end
