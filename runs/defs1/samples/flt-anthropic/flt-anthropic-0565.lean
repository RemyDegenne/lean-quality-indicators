namespace P2MW.S_CerednikDrinfeld_QM_exists_flat_family_lift_of_formallyEtale_of_locallyOfFiniteType

attribute [-instance] CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace FpqcLocalLiftGen

section Ring

variable {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (r : ℕ) (C : Type) [CommRing C] [Algebra 𝒪 C]

abbrev Rch : Type := chartERing C (algebraMap 𝒪 C π) r

end Ring
end FpqcLocalLiftGen
end P2MW.S_CerednikDrinfeld_QM_exists_flat_family_lift_of_formallyEtale_of_locallyOfFiniteType
