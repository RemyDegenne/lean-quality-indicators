public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

local notation "Γ" => zigzagAlgebraInternalGrading k G

local notation "U" => zigzagGradedBraidBimodule k G

local notation "F" => zigzagBimoduleTensor k G

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

/-- The inverse graded braid complex followed by the braid complex is homotopy
equivalent to the regular graded zigzag bimodule in cochain degree zero. -/
def zigzagBraidInverseTensorComplexHomotopyEquiv (i : V) :
    HomotopyEquiv
      (HomologicalComplex.mapBifunctor (zigzagBraidInverseComplex k G i) (zigzagBraidComplex k G i)
        F (ComplexShape.up ℤ))
      ((HomologicalComplex.single
        (GradedModuleCat.{max u w} (zigzagEnvelopingGrading k G).piece)
        (ComplexShape.up ℤ) 0).obj (zigzagGradedBimodule k G)) :=
  (Contraction.ThreeTermCancellationData.toContraction
    (reverseCancellationData k G i)).homotopyEquiv.symm

end TauCeti
end
end
