public section

open CategoryTheory

namespace FiniteGroupTateCohomology.Cyclic

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

@[simp]
lemma oddModelFunctor_obj (g : G) (A : Rep.{u} R G) :
    (oddModelFunctor g).obj A =
      (Rep.FiniteCyclicGroup.subCompNormHom A g).homology :=
  rfl

end FiniteGroupTateCohomology.Cyclic
end
