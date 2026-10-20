@[expose] public section

open CategoryTheory Limits AlgebraicTopology Simplicial

namespace SphereOddDegree

/-- The `j`-th endpoint section `Sing X ⟶ Sing X × Δ[1]`. -/
noncomputable def sect (X : TopCat.{0}) (j : Fin 2) :
    TopCat.toSSet.obj X ⟶ TopCat.toSSet.obj X ⨯ Δ[1] :=
  Limits.prod.lift (𝟙 (TopCat.toSSet.obj X)) (vtx (TopCat.toSSet.obj X) j)

end SphereOddDegree
end
