public section

set_option autoImplicit false

open CategoryTheory Topology

namespace CompHausAddCommGrp.FiniteBar

noncomputable section

universe u

variable {R H K : Type u} [CommRing R]

variable [Group H] [Fintype H] [Group K] [Fintype K]

variable (B : Rep.{u} R H) (C : Rep.{u} R K)

variable [TopologicalSpace B] [CompactSpace B] [T2Space B]

variable [IsTopologicalAddGroup B]

variable [TopologicalSpace C] [CompactSpace C] [T2Space C]

variable [IsTopologicalAddGroup C]

variable (hB : ∀ h, Continuous (B.ρ h))

variable (hC : ∀ k, Continuous (C.ρ k))

variable (f : H →* K) (φ : B ⟶ Rep.res f C)

variable (hφ : Continuous φ.hom)

/-- The continuous map on compact positive-degree finite-group homology induced
by a group homomorphism and a continuous coefficient morphism. -/
noncomputable def positiveHomologyMap (n : ℕ) :
    positiveHomology B hB n ⟶ positiveHomology C hC n := by
  unfold positiveHomology
  refine CompHausAddCommGrp.homologyMap
    (d₂ := differential B hB (n + 1)) (d₁ := differential B hB n)
    (e₂ := differential C hC (n + 1)) (e₁ := differential C hC n)
    (hd := differential_differential B hB n)
    (he := differential_differential C hC n)
    (p₂ := chainsMap B C f φ hφ (n + 2))
    (p₁ := chainsMap B C f φ hφ (n + 1))
    (p₀ := chainsMap B C f φ hφ n) ?_ ?_
  · intro x
    rw [differential_apply, chainsMap_apply, chainsMap_apply,
      differential_apply]
    change groupHomology.inhomogeneousChains.d C n
        ((groupHomology.chainsMap f φ).f (n + 1) x) =
      (groupHomology.chainsMap f φ).f n
        (groupHomology.inhomogeneousChains.d B n x)
    exact chainsMap_differential_raw_apply B C f φ n x
  · intro x
    rw [differential_apply, chainsMap_apply, chainsMap_apply,
      differential_apply]
    change groupHomology.inhomogeneousChains.d C (n + 1)
        ((groupHomology.chainsMap f φ).f (n + 2) x) =
      (groupHomology.chainsMap f φ).f (n + 1)
        (groupHomology.inhomogeneousChains.d B (n + 1) x)
    exact chainsMap_differential_raw_apply B C f φ (n + 1) x

end
end CompHausAddCommGrp.FiniteBar
end
