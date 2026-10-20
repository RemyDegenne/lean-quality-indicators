public section

namespace TauCeti

open LinearMap (BilinForm)

section Semiring

variable (k : Type*) [CommSemiring k] (X : Type*)

variable {k X}

theorem permutationForm_apply (v w : MonoidAlgebra k X) :
    permutationForm k X v w = v.coeff.sum fun x a => a * w.coeff x := by
  simp [permutationForm, Finsupp.sum, LinearMap.toSpanSingleton_apply]

end Semiring
end TauCeti
end
