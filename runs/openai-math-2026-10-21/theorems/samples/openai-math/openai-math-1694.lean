namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

section Structure

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem adaptedMonomialBasis_bracket_height {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) :
    ∀ i j k, RationalHeightLE ((F.adaptedMonomialBasis b ω hlayers w).repr
      ⁅F.adaptedMonomialBasis b ω hlayers w i, F.adaptedMonomialBasis b ω hlayers w j⁆ k) H := by
  classical
  intro i j k
  rw [F.adaptedMonomialBasis_bracket]
  split_ifs
  · exact hb _ _ _
  · exact rationalHeightLE_zero hH

end Structure
end Erdos3.NilpotentLieFiltration
end
end OAI
