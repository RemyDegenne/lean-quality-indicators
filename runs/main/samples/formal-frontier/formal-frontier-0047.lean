@[expose] public section

universe u v w

open CategoryTheory

open scoped TensorProduct

namespace KTheory.ProjectiveClass

variable (R : Type u) [CommRing R]

theorem tensorMul_comm (a b : ProjectiveClass R) :
    tensorMul R a b = tensorMul R b a := by
  refine induction_on R a ?_
  intro M
  refine induction_on R b ?_
  intro N
  simpa only [tensorMul_of_module] using
    (of_eq_of_equiv R (M ⊗[Rᵐᵒᵖ] N) (TensorProduct.comm Rᵐᵒᵖ M N))

end KTheory.ProjectiveClass
end
