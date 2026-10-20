@[expose] public section

namespace HermitianMat

open ComplexOrder

open scoped Matrix

variable {𝕜 : Type*} [RCLike 𝕜]

variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι]

variable {A B C : HermitianMat n 𝕜}

variable {M : Matrix m n 𝕜} {N : Matrix n n 𝕜}

omit [Fintype n] in
theorem lt_iff_posdef : A < B ↔ (B - A).mat.PosSemidef ∧ A ≠ B :=
  lt_iff_le_and_ne

end HermitianMat
end
