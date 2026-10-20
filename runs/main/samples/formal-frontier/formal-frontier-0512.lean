@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

@[simp] theorem substitute_generator {B : Type v} [Ring B] (n : ℕ)
    (f : R →+* B) (values : Fin n → Submonoid.center B) (j : Fin n) :
    substitute n f values (generator n j) = values j := by
  simp [substitute, generator, AddMonoidAlgebra.liftNCRingHom_single,
    multiplesHom_apply]

end
end CentralPolynomialSimplex
end
