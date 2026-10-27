public section

open CategoryTheory Limits MonoidalCategory CochainComplex.HomComplex

namespace TauCeti

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  (F G K : CochainComplex C ℤ)

/-- **Composition of cochains is a closed degree-zero map.**  It assembles into a morphism of
cochain complexes of `R`-modules out of the tensor product; the differential of a composite is
computed by the Leibniz rule, which is precisely the condition for this to be a chain map. -/
noncomputable def linearHomComplexComp :
    linearHomComplex R G K ⊗ linearHomComplex R F G ⟶ linearHomComplex R F K where
  f j := HomologicalComplex.mapBifunctorDesc (cochainCompTensor R F G K · · j ·)
  comm' j j' hjj' := by
    replace hjj' : j + 1 = j' := hjj'
    subst hjj'
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    exact (cochainCompTensor_d R F G K p q j h).symm

end TauCeti
end
