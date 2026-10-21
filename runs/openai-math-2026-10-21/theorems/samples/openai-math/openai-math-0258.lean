namespace OAI

section

noncomputable section

open scoped BigOperators

namespace ElasticityBoundaryMVTower

open ElasticityBoundaryMVNormal

theorem finite_physical_amplitudes (l m : ℂ) (hm : m≠0) (he : l+2*m≠0) (hp : l+3*m≠0)
    (A : ℕ → W →ₗ[ℂ] W) (hA : A 0=normal l m)
    (p₀ : W) (h₀ : normal l m p₀=0) (N K : ℕ) (hKN : N≤K) :
    ∃ (p : ℕ → W) (R : Polynomial W), p 0=p₀ ∧
      (∀ n, 0<n → boundary (p n)=0) ∧
      residualPolynomial A p K N=Polynomial.X^(N+1)*R := by
  obtain ⟨p,hp0,hb,hc⟩ := triangular_amplitudes l m hm he hp A hA p₀ h₀
  obtain ⟨R,hR⟩ := residual_high_order_factor A p hKN hc
  exact ⟨p,R,hp0,hb,hR⟩

end ElasticityBoundaryMVTower
end
end
end OAI
