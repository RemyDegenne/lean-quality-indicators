namespace P2MW.S_AlgebraicGeometry_isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed

set_option autoImplicit false

universe u

p2m_open

namespace KFEAux

open AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X]

theorem kumHom_preimage_eq_top (k : ℕ) (g : X.functionField) {V : X.Opens} (hη : genericPoint X ∈ V) :
    (kumHom X k g) ⁻¹ᵁ V = ⊤ := by
  apply le_antisymm le_top
  intro p _
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply]
  have hmem : X.fromSpecStalk (genericPoint X)
      (Spec.map (CommRingCat.ofHom (algebraMap X.functionField (Kum X k g))) p) ∈
      Set.range (X.fromSpecStalk (genericPoint X)) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hmem
  exact hmem.mem_open V.2 hη

end KFEAux
end P2MW.S_AlgebraicGeometry_isFinite_and_etale_fromNormalization_kummer_of_isIntegrallyClosed
