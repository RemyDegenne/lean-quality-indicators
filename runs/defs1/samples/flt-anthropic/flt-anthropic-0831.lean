namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule

set_option autoImplicit false

universe u

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 6400000

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

set_option linter.unusedTactic false

noncomputable section

noncomputable section

open CategoryTheory Opposite MvPolynomial HomogeneousLocalization TopologicalSpace

namespace AlgebraicGeometry

namespace ProjSpace

namespace GMSec

p2m_open

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (π : X ⟶ Spec (.of A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

section Build

variable [IsFinite φ]

scoped instance : Fintype (Gens φ) := by unfold Gens; infer_instance

def psi0 : ProjSpaceCech.GradedModule.Hom (Fgen φ π) (twistGradedModule φ π) where
  toLinearMap := psi0Lin φ π
  mem_grade d v hv := by
    rw [psi0Lin_apply]
    refine Submodule.sum_mem _ fun t _ => ?_
    exact ProjSpaceCech.GradedModule.evalLin_mem_grade _ (genFrac_num_mem φ π (gen φ t)) (hv t (Set.mem_univ t))
  xMul_comm j := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, psi0Lin_apply, psi0Lin_apply, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    exact ProjSpaceCech.GradedModule.evalLin_X_mul _ _ j (v t)

end Build
end GMSec
end ProjSpace
end AlgebraicGeometry
end
end
end P2MW.S_AlgebraicGeometry_ProjSpace_exists_isFG_hom_injective_saturated_twistGradedModule
