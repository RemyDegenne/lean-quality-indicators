set_option autoImplicit false

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

namespace SubalgebraStages

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]

variable {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)

@[reducible] noncomputable def specCone : Cone (specDiagram S) where
  pt := Spec (CommRingCat.of A)
  π := { app i := specLeg S i.unop
         naturality {i j} h := by
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
           exact (specLeg_specTrans S h.unop.le).symm }

end SubalgebraStages
end AlgebraicGeometry
