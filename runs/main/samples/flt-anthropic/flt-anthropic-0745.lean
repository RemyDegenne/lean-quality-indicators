namespace P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_smoothingOperator_eq_archConvN_and_exists_levelSet_subset

attribute [-instance] instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm Matrix MeasureTheory Topology Filter TopologicalSpace

namespace LanglandsTunnell

namespace CubicInduction

namespace ArchConvCalculus

p2m_open

attribute [local instance] secondCountableTopology_adeleRing

attribute [local instance] secondCountableTopology_prodAdele

attribute [local instance] secondCountableTopology_infiniteAdeleRing secondCountableTopology_finiteAdeleRing

attribute [local instance] secondCountableTopology_adelicGL secondCountableTopology_ginf secondCountableTopology_gf

scoped instance locallyCompactSpace_matrix_finiteAdeleRing :
    LocallyCompactSpace (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 3 → Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ))

scoped instance t2Space_matrix_finiteAdeleRing : T2Space (Matrix (Fin 3) (Fin 3) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :=
  inferInstanceAs (T2Space (Fin 3 → Fin 3 → FiniteAdeleRing (𝓞 ℚ) ℚ))

attribute [local instance] locallyCompactSpace_gf

attribute [local instance] gfMeasurableSpace

attribute [local instance] gfBorelSpace

attribute [local instance] isHaarMeasure_muFin

attribute [local instance] ginfMeasurableSpace ginfBorelSpace locallyCompactSpace_ginf isHaarMeasure_μ

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

attribute [local instance] isHaarMeasure_prod

attribute [local instance] isHaarMeasure_productHaar

theorem measurableSet_levelSet {K' : (p : HeightOneSpectrum (𝓞 ℚ)) → Subgroup (GL (Fin 3) (p.adicCompletion ℚ))}
    (hK' : IsLevelDatum K') : MeasurableSet (levelSet K') :=
  (isOpen_levelSet hK').measurableSet

end ArchConvCalculus
end CubicInduction
end LanglandsTunnell
end
end P2MW.S_LanglandsTunnell_CubicInduction_SlabL2_smoothingOperator_eq_archConvN_and_exists_levelSet_subset
