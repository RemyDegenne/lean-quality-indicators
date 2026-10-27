public section

noncomputable section

open CategoryTheory Limits Metric

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C] (A : C)

/-- **The fundamental class of the circle**, with coefficients in an object `A` of an abelian
category with coproducts: the class `A ⟶ H₁(S¹; A)` of the standard loop `t ↦ (cos 2πt, sin 2πt)`.
It is the image of the relative class of the standard `1`-simplex of the interval `I¹` under the
loop, followed by the inverse of `H₁(S¹; A) ≅ H₁(S¹, {(1, 0)}; A)`
(`TauCeti.singularHomologyIsoOfSubsetSingleton`). The circle is oriented by this
parametrization, which is also the one with which double loops are read as maps from the circle in
`TauCeti.BasedTopologicalSpace.loopSpace2Homeomorph`. -/
def circleFundamentalClass :
    A ⟶ ((AlgebraicTopology.singularHomologyFunctor C 1).obj A).obj (TopCat.of Sphere1) :=
  cubeRelClass A ≫ TopPair.singularHomologyMap circleLoopPairHom A 1 ≫
    (singularHomologyIsoOfSubsetSingleton A 0 Sphere1.east).inv

end TauCeti
end
end
