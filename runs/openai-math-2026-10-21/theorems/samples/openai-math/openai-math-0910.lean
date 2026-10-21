namespace OAI

section

noncomputable section

namespace BoltzmannNonuniqueness.PeriodicApproximation

open CollisionCompactness

variable {X : Type*}

theorem regularizedPostRate_difference {N D : ℝ} (hN : 0 < N)
    {f g : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (hg : ∀ p, 0 ≤ g p)
    (hfg : ∀ p, |f p-g p| ≤ D) (z : (X × (Velocity × Velocity)) × Sphere) :
    |regularizedPostRate N f z-regularizedPostRate N g z| ≤ 24*N^2*D :=
  regularizedPreRate_difference hN hf hg hfg (scatterTriple z)

end BoltzmannNonuniqueness.PeriodicApproximation
end
end
end OAI
