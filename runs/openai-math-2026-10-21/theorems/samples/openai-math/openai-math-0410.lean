namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace PolynomialOrdering

open AssociativeElimination

open scoped TensorProduct

variable {R α β U : Type*} [CommRing R] [Ring U] [Algebra R U]

variable (f : A R α →ₐ[R] U) (g : A R β →ₐ[R] U)

theorem evaluate_merge (z : V (R:=R) (α:=α) (β:=β)) :
    evaluate f g (merge z)=interpret f g z := by
  have h : (evaluate f g).toLinearMap.comp merge=interpret f g := by
    apply TensorProduct.ext'
    intro p q
    simp
  exact LinearMap.congr_fun h z

end PolynomialOrdering
end DeligneDrinfeld
end
end OAI
