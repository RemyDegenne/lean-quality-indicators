@[expose] public noncomputable section

open Filter

namespace ViscositySolns

variable {n : Nat} {g : Point n -> Real}

namespace PerronMethodExistenceTheorem

theorem strictBoundary_of_bentSourceOuterClosedBallGeometricSemijetLscSelectionPatch
    {C boundary : Set (Point n)} [LocallyCompactSpace C]
    {F : Operator n}
    (B : DirichletBarrierPair C boundary F g)
    (hcomparison :
      DirichletComparisonPrinciple C boundary F g)
    (hF : OperatorContinuous F)
    (hFell : DegenerateElliptic F)
    (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerTrace :
      BoundaryLowerTraceOn C boundary g B.lower)
    (hupperTrace :
      BoundaryUpperTraceOn C boundary g B.upper)
    (hne : ∀ x : Point n, x ∈ C ∪ boundary -> (nhdsWithin x C).NeBot)
    (hupperBddAbove : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· <= ·) B.upper)
    (hlowerBddBelow : ∀ x : Point n, x ∈ C ∪ boundary ->
      (nhdsWithin x C).IsBoundedUnder (· >= ·) B.lower)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallGeometricSemijetLscSelectionPatch
        C boundary F g B) :
    DirichletSolutionOn C boundary F g
      (upperEnvelope C (perronEnvelope C boundary F
        g B.lower B.upper)) :=
  of_perronFamily_top_and_bentSourceOuterClosedBallGeometricSemijetLscSelectionPatch
    B hcomparison hF hFell hFinv hCopen hlowerTrace hupperTrace hne
    hupperBddAbove hlowerBddBelow hpatch

end PerronMethodExistenceTheorem
end ViscositySolns
end
