public section

noncomputable section

namespace TauCeti

open CategoryTheory

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]

attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

local notation "F" => zigzagBimoduleTensor k G

local notation "Z" => zigzagGradedBimodule k G

local notation "U" => zigzagGradedBraidBimodule k G

local notation "B" => zigzagBraidComplex k G

local notation "B'" => zigzagBraidInverseComplex k G

local notation "c" => ComplexShape.up ℤ

local notation "T" => zigzagBraidInverseComplexTensor k G

@[reassoc (attr := simp)]
theorem ιMapBifunctor_zigzagBraidInverseTensorXOneIso_hom (i : V) :
    HomologicalComplex.ιMapBifunctor (B i) (B' i) F c 0 1 1 (by simp) ≫
        (zigzagBraidInverseTensorXOneIso k G i).hom =
      ((((F).flip.obj ((B' i).X 1)).mapIso (zigzagBraidComplexXIso₁ k G i) ≪≫
        ((F).obj Z).mapIso (zigzagBraidInverseComplexXIso₁ k G i)) ≪≫
          zigzagBimoduleLeftUnitor k G ((GradedModuleCat.shiftFunctor (-2)).obj (U i))).hom := by
  simp only [zigzagBraidInverseTensorXOneIso, Iso.trans_hom,
    HomologicalComplex.ι_mapBifunctorSingleSummandIso_hom_assoc, inverseTensorRightIso,
    Category.assoc]

end TauCeti
end
end
