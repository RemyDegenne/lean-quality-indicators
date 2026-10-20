namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed

set_option autoImplicit false

p2m_open

universe u

noncomputable section

namespace GoodReductionJacobian

namespace RelativeGroupLaw

namespace ClosedImage

p2m_open

section Topology

variable {X : Type*} [TopologicalSpace X]

theorem image_eq_of_image_subset [NoetherianSpace X] (r : X ≃ₜ X) {Z : Set X}
    (hZ : IsClosed Z) (h : r '' Z ⊆ Z) : r '' Z = Z := by
  by_contra hne
  let 𝒞 : Set (Closeds X) := {C | r '' (C : Set X) ⊂ C}
  have hZ𝒞 : (⟨Z, hZ⟩ : Closeds X) ∈ 𝒞 := HasSubset.Subset.ssubset_of_ne h hne
  obtain ⟨C₀, hC₀, hmin⟩ := (wellFounded_lt (α := Closeds X)).has_min 𝒞 ⟨_, hZ𝒞⟩
  have hC₁ : (⟨r '' (C₀ : Set X), r.isClosedMap _ C₀.2⟩ : Closeds X) ∈ 𝒞 := by
    change r '' (r '' (C₀ : Set X)) ⊂ r '' (C₀ : Set X)
    refine ⟨Set.image_mono hC₀.1, fun hle => hC₀.2 ?_⟩
    exact (Set.image_subset_image_iff r.injective).mp hle
  refine hmin _ hC₁ ?_
  change (r '' (C₀ : Set X)) ⊂ (C₀ : Set X) at hC₀
  exact hC₀

end Topology
end ClosedImage
end RelativeGroupLaw
end GoodReductionJacobian
end
end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
