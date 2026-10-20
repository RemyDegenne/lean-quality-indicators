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

@[simp]
lemma chainsMap_apply (n : ℕ) (x : chains B n) :
    chainsMap B C f φ hφ n x = (groupHomology.chainsMap f φ).f n x :=
  by rfl

end
end CompHausAddCommGrp.FiniteBar
end
