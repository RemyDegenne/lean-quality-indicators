namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap

set_option autoImplicit false

open scoped TensorProduct

open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

namespace B25TG

section SemilinearGen

variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
  {A : Type} [CommRing A] [Algebra 𝒪 A] [Algebra B A]
  {C : Type} [CommRing C] [Algebra 𝒪 C] [Algebra B C]
  {M : Type} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower B A M]
  {N : Type} [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]

def linB (φ : A →ₐ[𝒪] C) (hφ : ∀ b, φ (algebraMap B A b) = algebraMap B C b) (τ : M →ₛₗ[(φ : A →+* C)] N) :
    M →ₗ[B] N where
  toFun := τ
  map_add' a b := map_add τ a b
  map_smul' b m := by
    rw [← algebraMap_smul A b m, LinearMap.map_smulₛₗ]
    show φ (algebraMap B A b) • τ m = b • τ m
    rw [hφ, algebraMap_smul]

end SemilinearGen
end B25TG
end P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap
