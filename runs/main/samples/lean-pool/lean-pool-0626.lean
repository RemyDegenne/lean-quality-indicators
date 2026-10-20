@[expose] public section

namespace RamanujanNagell

open QuadraticAlgebra

lemma ufd_associated_dichotomy (α β : R) (m : ℕ)
    (h_prod : α * β = θ ^ m * θ' ^ m)
    (h_coprime : IsCoprime α β)
    (hα : ¬IsUnit α) (hβ : ¬IsUnit β) :
    Associated α (θ ^ m) ∨ Associated α (θ' ^ m) := by
  rcases theta_pow_dvd_of_coprime_prod α β m h_prod h_coprime with h | h
  · exact Or.inl (associated_of_theta_pow_dvd α β m h_prod h_coprime hα hβ h)
  · exact Or.inr (associated_of_theta_pow_dvd_right α β m h_prod h_coprime hα hβ h)

end RamanujanNagell
end
