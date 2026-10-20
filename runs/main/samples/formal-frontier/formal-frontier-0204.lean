public section

open CategoryTheory

namespace FiniteGroupTateCohomology.Cyclic

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

@[simp]
lemma subCompNormHomMap_comp {A B C : Rep.{u} R G} (g : G)
    (f : A ⟶ B) (h : B ⟶ C) :
    subCompNormHomMap g (f ≫ h) = subCompNormHomMap g f ≫ subCompNormHomMap g h := by
  ext <;> simp [subCompNormHomMap]

end FiniteGroupTateCohomology.Cyclic
end
