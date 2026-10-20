public section

open CategoryTheory Opposite WithConv

open scoped CategoryTheory.MonObj

open AlgebraicGeometry MonObj MonoidalCategory

universe u

variable (R : Type u) [CommRing R]

namespace TauCeti

@[simp]
lemma hopfSpec_obj_mul_left (H : CommHopfAlgCat.{u} R) :
    μ[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
      (Opposite.op H)).X].left =
      eqToHom (hopfSpec_obj_tensor_X_left R H) ≫
        (pullbackSpecIso R H H).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R H)) ≫
        eqToHom (hopfSpec_obj_X_left R H).symm := by
  simpa only [Category.assoc] using
    (conj_eqToHom_iff_heq
      μ[((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
        (Opposite.op H)).X].left
      ((pullbackSpecIso R H H).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R H)))
      (hopfSpec_obj_tensor_X_left R H) (hopfSpec_obj_X_left R H)).2 (by
        rw [hopfSpec_obj_eq_asOver]
        exact heq_of_eq (AlgebraicGeometry.mul_spec_asOver_spec_left
          (R := CommRingCat.of R) (A := CommRingCat.of H)))

end TauCeti
end
