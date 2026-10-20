public section

open Subgroup

open scoped commutatorElement

namespace TauCeti

universe u v w

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Functoriality

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable {K : Type w} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

variable (p) in
/-- **The graded map of a continuous homomorphism**: `f` carries `λ_k(G)` into `λ_k(H)`, so it
induces `gr_k(G) →+ gr_k(H)`. Its defining equation is `TauCeti.gradedMap_gradedMk`. -/
def gradedMap (f : G →* H) (hf : Continuous f) (k : ℕ) : gradedPiece p G k →+ gradedPiece p H k :=
  MonoidHom.toAdditive (QuotientGroup.map _ _
    ((f.comp (pLowerCentralSeries p G k).subtype).codRestrict (pLowerCentralSeries p H k)
      fun x => f.map_pLowerCentralSeries_le hf k ⟨x, x.2, rfl⟩)
    fun x hx => mem_comap.mpr (mem_subgroupOf.mpr
      (f.map_pLowerCentralSeries_le hf (k + 1) ⟨x, mem_subgroupOf.mp hx, rfl⟩)))

end Functoriality
end TauCeti
end
