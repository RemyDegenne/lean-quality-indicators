public section

open CategoryTheory AlgebraicGeometry WithConv

namespace TauCeti.Comodule

universe u

variable {k H M : Type u} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [AddCommGroup M] [Module k M] [Comodule k H M]
  [Module.Finite k M]

/-- Rational translation on the locally closed projective orbit, with its full
scheme-theoretic image structure. -/
noncomputable def projectiveOrbitTranslation (m : M) (hm : Module.IsUnimodular k m)
    (g : WithConv (H →ₐ[k] k)) :
    projectiveOrbitScheme (H := H) m hm ≅ projectiveOrbitScheme (H := H) m hm where
  hom := orbitTranslationHom m hm g
  inv := orbitTranslationHom m hm g⁻¹
  hom_inv_id := by
    rw [← cancel_mono (projectiveOrbitι (H := H) m hm)]
    simp only [Category.assoc, orbitTranslationHom_ι, orbitTranslationHom_ι_assoc,
      projectivePointTranslation_inv_eq_symm, Iso.symm_hom, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  inv_hom_id := by
    rw [← cancel_mono (projectiveOrbitι (H := H) m hm)]
    simp only [Category.assoc, orbitTranslationHom_ι, orbitTranslationHom_ι_assoc,
      projectivePointTranslation_inv_eq_symm, Iso.symm_hom, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]

end TauCeti.Comodule
end
