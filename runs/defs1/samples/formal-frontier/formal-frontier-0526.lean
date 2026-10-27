@[expose] public section

universe a b c w p

open CategoryTheory Limits Opposite

open scoped Simplicial TensorProduct

namespace SSet

variable {A : Type a} {B : Type b} {C : Type c}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The normalized coefficient morphism, conjugated by the integral tensor
comparison. Only the morphism is conjugated; the tensor differential is unchanged. -/
@[no_expose]
noncomputable def tensorNormalizedChainComplexCoefficientMap (g : A →+ B) (S : SSet.{w}) :
    tensorNormalizedChainComplex.{a, w, max b p} A S ⟶
      tensorNormalizedChainComplex.{b, w, max a p} B S :=
  (tensorNormalizedChainIso.{a, w, max b p} A S).hom ≫
    (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w b p} A)))).nondegComplexMap
      (S.splitting.map (sigmaConst.obj (ModuleCat.of ℤ (ULift.{max w a p} B))))
      (Functor.whiskerLeft S (sigmaConst.map (liftedCoefficientMap.{a, b, max w p} g))) ≫
    (tensorNormalizedChainIso.{b, w, max a p} B S).inv

end SSet
end
