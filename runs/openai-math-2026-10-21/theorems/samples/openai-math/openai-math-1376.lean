namespace OAI

noncomputable section

open scoped BigOperators

namespace MinUncut.Outer

open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof

attribute [local instance] Classical.propDecidable coordsDecEq

variable {Name I : Type*} [Fintype I] {m n : ℕ}

lemma localWeight_sum {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (g : GridData) (a b : ℚ) (j : Test) (F : LocalSample A m n g → ℝ) :
    (∑ p, (localWeight g a b j p:ℝ)*F p)=
      (𝔼 B, 𝔼 C, 𝔼 z, ∑ q : TestCoordinates m n → Fin g.L,
        (gridWeight g q:ℝ)*(noiseWeight a B C j:ℝ)*F (B,C,z,q))/(b:ℝ) := by
  simp only [localWeight,Rat.cast_div,Rat.cast_mul,Rat.cast_inv,Rat.cast_natCast,
    Fintype.sum_prod_type,Fintype.expect_eq_sum_div_card]
  simp only [div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro q _
  ring

end MinUncut.Outer
end
end OAI
