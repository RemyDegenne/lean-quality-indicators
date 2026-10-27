public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer

open CFSG.Open CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.PFAppendixIII (rightConjugateElem)

open CFSG.RankThreeCoreUniqueness.Helpers

open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G : Type*} [Group G]

theorem internal_involution_hull_image_eq_class_closure
    (N : Subgroup G) (z : G) (hzN : z ∈ N) :
    (involutionPointHull (⟨z, hzN⟩ : N)).map N.subtype =
      Subgroup.closure (conjugacyWithin N z) := by
  rw [involutionPointHull, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨rightConjugateElem (⟨z, hzN⟩ : N) n, ⟨n, rfl⟩, rfl⟩

end CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
end
