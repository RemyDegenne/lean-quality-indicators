namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceAllocationEnergy

open CanonicalQuadraticSieve CenteredMomentGaussEnergy

open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass

open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum

local notation "O" => ActualEisensteinCubic.O

 theorem gaussPolynomial_allocation {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ) (z : O) :
    gaussPolynomial S a ha (fun i => ∑ B,b B*d B i) z=
      ∑ B,b B*gaussPolynomial S a ha (d B) z := by
  simp only [gaussPolynomial,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem finite_allocation_energy {α γ : Type*} [Fintype γ]
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (b : γ → ℂ) (d : γ → α → ℂ) (rows : Finset O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (hmajor : ∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (∑ z∈rows,‖gaussPolynomial S a ha (fun i => ∑ B,b B*d B i) z‖^2)≤
      (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*(gaussEnergy S a ha (d B) W K).re := by
  calc
    _ ≤ ∑ z∈rows,(Fintype.card γ:ℝ)*∑ B,‖b B‖^2*‖gaussPolynomial S a ha (d B) z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      rw [gaussPolynomial_allocation]
      simpa only [Finset.card_univ,norm_mul,mul_pow] using
        CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B => b B*gaussPolynomial S a ha (d B) z)
    _ = (Fintype.card γ:ℝ)*∑ B,‖b B‖^2*∑ z∈rows,‖gaussPolynomial S a ha (d B) z‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      exact mul_le_mul_of_nonneg_left
        (finite_energy_le_gaussEnergy S a ha (d B) W K hK rows hW hmajor) (sq_nonneg _)

end SevenEighths.CenteredMomentSourceAllocationEnergy
end
end OAI
