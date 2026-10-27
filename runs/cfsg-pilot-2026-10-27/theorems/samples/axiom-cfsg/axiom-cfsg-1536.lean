public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {M V Q : Subgroup G}

theorem Hyp79.conj_central (H : Hyp79 M V Q) (g : G) {u y : G} (hu : u ∈ conjSubgroup g V)
    (hy : y ∈ conjSubgroup g Q) : u * y = y * u := by
  rw [mem_conjSubgroup] at hu hy
  have h1 := H.V_central hu hy
  have e1 : u * y = g * ((g⁻¹ * u * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
  have e2 : y * u = g * ((g⁻¹ * y * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
  rw [e1, e2, h1]

end CFSG.RankThree.GF2n.Tim79
end
