namespace P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal

set_option autoImplicit false

open MeasureTheory NumberField

open IsDedekindDomain

open scoped TensorProduct

open scoped TensorProduct.RightActions

open scoped Matrix

noncomputable section

namespace EllGermBridge

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

scoped instance secondCountable_localGL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

section Integrality

theorem two_ne_zero_adicCompletion : (2 : v.adicCompletion K) ≠ 0 := by
  intro h
  apply (two_ne_zero : (2 : K) ≠ 0)
  apply (algebraMap K (v.adicCompletion K)).injective
  rw [map_ofNat, map_zero, h]

end Integrality
end EllGermBridge
end
end P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
