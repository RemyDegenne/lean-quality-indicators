@[expose] public section

noncomputable section

open CategoryTheory

open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-- The `algSpec` presentation of an affine target is isomorphic over the base
to its spectrum with the algebra-induced structure morphism. -/
def affineSpecHomOverTargetIso (A : Type u) [CommRing A] [Algebra R A] :
    (algSpec (.of R)).obj (.op (CommAlgCat.of R A)) ≅
      (Spec (.of A)).asOver (Spec (.of R)) :=
  Over.isoMk (Iso.refl (Spec (.of A))) (by
    change 𝟙 (Spec (.of A)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R A))
    exact Category.id_comp _)

end AlgebraicGeometry
end
end
