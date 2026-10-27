namespace P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

namespace M3aGlue

section Transport

variable {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X] (φ : F ≃+* X.functionField)

noncomputable def locEquiv (z : X) : X.presheaf.stalk z ≃+* ↥(SemistableModel.localRing X φ z) :=
  RingEquiv.ofBijective (locHom φ z).rangeRestrict
    ⟨fun a b h => locHom_injective φ z (congrArg Subtype.val h), (locHom φ z).rangeRestrict_surjective⟩

end Transport
end M3aGlue
end P2MW.S_AlgebraicCurve_exists_finitePresentation_isLocalizationAtPrime_localRing_of_mem_smoothLocus
