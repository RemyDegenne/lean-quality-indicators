@[expose] public section

open CategoryTheory

universe u v

namespace CentralPolynomialSimplex

noncomputable section

variable {R : Type u} [Ring R]

theorem generator_mem_center (n : ℕ) (j : Fin n) :
    generator (R := R) n j ∈ Set.center (PolyRing R n) :=
  Semigroup.mem_center_iff.mpr fun p =>
    (AddMonoidAlgebra.of'_commute (R := R) (M := Fin n →₀ ℕ)
      (fun _ => add_comm _ _) p).eq.symm

end
end CentralPolynomialSimplex
end
