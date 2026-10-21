namespace OAI

noncomputable section

namespace Problem340.Construction

theorem rawOrbit_hasScheduledPassageAt (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift D x t₀)))
    (k : ℤ) (hstart : t₀ < 100 * (k : ℝ)) :
    HasScheduledPassageAt (rawClockLift D x t₀) k :=
  clock_passage_scheduling_at D
    (fun z => (hgate z).1) (fun z => (hgate z).2)
    (rawClockLift_succ D x t₀ h₀) hunbounded k (by simpa using hstart)

end Problem340.Construction
end
end OAI
