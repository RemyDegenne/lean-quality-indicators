public section

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {ι : Type w} {κ η : Type*}

variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable {D : Type*} [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]

noncomputable section

variable (e : ι → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

variable [Fintype η] (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)

variable (degree : (κ → ℤ) →+ D)

theorem range_kostantRootSubgroupMatrix_le_upperUnitriangular_orderedWeightBasis
    (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
    {i : ι} {α : κ → ℤ} (hα : ∀ j, ⁅h j, e i⁆ = (α j : ℚ) • e i)
    (hdegree : 0 < degree α)
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    {A : Type*} [CommRing A] :
    (kostantRootSubgroupMatrix e h ρ M hM i hnil
      (orderedWeightBasis degree wt b) (A := A)).range ≤
        upperUnitriangularGroup (Fin (Fintype.card η)) A := by
  apply range_kostantRootSubgroupMatrix_le_upperUnitriangular e h ρ M hM
    (orderedWeightBasis degree wt b) (orderedWeight degree wt) i hnil
    (isCartanWeightVector_coe_orderedWeightBasis h ρ M b wt degree hwt) hα
  intro r s n hn hrs
  exact orderedWeight_lt_of_eq_add_nsmul degree wt hdegree hn hrs

end
end TauCeti.UniversalEnvelopingAlgebra
end
