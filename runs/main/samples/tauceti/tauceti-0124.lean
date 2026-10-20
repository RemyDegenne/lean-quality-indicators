public section

open CategoryTheory Matrix WithConv

namespace TauCeti.ConstantMultiplication

universe u v w

variable (R : Type u) [CommRing R] (n : ℕ) (C : Fin n → Matrix (Fin n) (Fin n) R)

section Matrices

variable {S : Type v} [CommRing S] [Algebra R S]

theorem mul_imageStructureMatrix (M N : Matrix (Fin n) (Fin n) S) (k : Fin n) :
    M * imageStructureMatrix R n C N k = ∑ a, N a k • (M * (C a).map (algebraMap R S)) := by
  rw [imageStructureMatrix_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Matrix.mul_smul _ _ _

end Matrices
end TauCeti.ConstantMultiplication
end
