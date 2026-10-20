@[expose] public section

universe v w x u

open CategoryTheory MonoidalCategory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

namespace MonoidalCategory

attribute [local ext] TensorProduct.ext

@[simp]
theorem tensorμ_apply
    {A B C D : SemimoduleCat R} (x : A) (y : B) (z : C) (w : D) :
    tensorμ A B C D ((x ⊗ₜ y) ⊗ₜ (z ⊗ₜ w)) = (x ⊗ₜ z) ⊗ₜ (y ⊗ₜ w) := rfl

end MonoidalCategory
end SemimoduleCat
end
