@[expose] public section

open CategoryTheory Simplicial Limits AlgebraicTopology SSet

namespace SphereOddDegree

variable {X Y : TopCat.{0}} {f g : X ⟶ Y}

/-- **The singular prism operator (unconditional).** A homotopy of continuous maps
induces a chain homotopy between the induced integral singular chain maps.
It combines the project's singular cylinder (`prismHomotopy`) with the backported algebraic prism
`CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`. -/
noncomputable def singularChainHomotopyOfHomotopy
    {X Y : TopCat.{0}} {f g : X ⟶ Y} (H : ContinuousMap.Homotopy f.hom g.hom) :
    Homotopy (singularChainℤ.map f) (singularChainℤ.map g) :=
  ((prismHomotopy H).whiskerRight (sigmaConst.obj (ModuleCat.of ℤ ℤ))).toChainHomotopy

end SphereOddDegree
end
