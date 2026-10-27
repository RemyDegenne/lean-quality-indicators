public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry MonObj

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace AbelianVariety

variable {K : Type u} [Field K]

noncomputable section

namespace prod

/-- Pair two homomorphisms with a common source to obtain a homomorphism into a product. -/
def lift {A B C : AbelianVariety K} (f : C ⟶ A) (g : C ⟶ B) :
    C ⟶ prod A B := by
  refine Hom.mk'
    (CartesianMonoidalCategory.lift (Hom.toOverHom f) (Hom.toOverHom g) ≫
      eqToHom (prod_toOver A B).symm) ?_ ?_
  · simp only [IsMonHom.one_hom_assoc, ← cancel_mono (eqToHom (prod_toOver A B)),
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, prod_one]
  · simp only [IsMonHom.mul_hom_assoc, ← cancel_mono (eqToHom (prod_toOver A B)),
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, prod_mul,
      tensorHom_comp_tensorHom_assoc]

end prod
end
end AbelianVariety
end AlgebraicGeometry
end TauCeti
end
