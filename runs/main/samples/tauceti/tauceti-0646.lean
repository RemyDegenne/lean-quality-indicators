public section

namespace TauCeti

universe u

variable (G : Type u) [Group G] [TopologicalSpace G]

variable {G} {N K : Subgroup G}

namespace IsTopCharacteristic

theorem sup (hN : IsTopCharacteristic G N) (hK : IsTopCharacteristic G K) :
    IsTopCharacteristic G (N ⊔ K) := by
  intro φ
  rw [Subgroup.map_sup, hN φ, hK φ]

end IsTopCharacteristic
end TauCeti
end
