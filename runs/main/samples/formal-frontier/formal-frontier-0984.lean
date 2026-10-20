@[expose] public section

universe uR uC uG

open scoped TensorProduct

namespace MonoidAlgebra

variable {R : Type uR} {C : Type uC} {G : Type uG}

section Coalgebra

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

theorem liftGroupLikeCoalgHom_toLinearMap (f : G → GroupLike R C) :
    (liftGroupLikeCoalgHom f).toLinearMap =
      (Finsupp.linearCombination R (fun g => (f g).val)).comp
        (coeffLinearEquiv R).toLinearMap := rfl

end Coalgebra
end MonoidAlgebra
end
