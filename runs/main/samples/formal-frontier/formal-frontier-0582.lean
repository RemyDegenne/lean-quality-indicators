@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open TopologicalSpace

open scoped Simplicial

noncomputable section

universe u

namespace AlgebraicTopology

@[reassoc (attr := simp)]
theorem twoOpenMayerVietorisFromIntersection_comp_fromBiprod {X : TopCat.{u}}
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    twoOpenMayerVietorisFromIntersection U V n ≫
      twoOpenMayerVietorisFromBiprod U V hUV n = 0 := by
  simp only [twoOpenMayerVietorisFromIntersection,
    twoOpenMayerVietorisFromBiprod, Category.assoc, Iso.hom_inv_id_assoc]
  exact twoOpenMayerVietoris_comp_toSpace U V hUV n

end AlgebraicTopology
end
end
