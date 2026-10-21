namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

theorem antisymmetricPairProjection_repr (k : Fin 2) (x : V.AntisymmetricPairAlgebra) (a : Fin W.dim) :
    W.model.basis.repr (V.antisymmetricPairProjection k x) a =
      (pi V.antisymmetricPairModels).basis.repr x (V.antisymmetricPairCoordinateIndex k a) :=
  productFinBasis_repr_component V.antisymmetricPairModels x (some k) a

end NativeSampleCorrelation
end Erdos3
end
end OAI
