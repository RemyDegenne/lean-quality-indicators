namespace P2MW.S_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective

set_option autoImplicit false

set_option linter.unusedSectionVars false

set_option linter.unusedVariables false

noncomputable section

universe u

namespace P2mSchlessingerTangent

open IsLocalRing

variable {O : Type u} [CommRing O] [IsLocalRing O]

section tsze

variable (O)

variable (M : Type u) [AddCommGroup M] [Module (ResidueField O) M] [Module (ResidueField O)ᵐᵒᵖ M]
  [IsCentralScalar (ResidueField O) M] [Module O M] [IsScalarTower O (ResidueField O) M]
  [IsScalarTower O (ResidueField O)ᵐᵒᵖ M]

variable (N : Type u) [AddCommGroup N] [Module (ResidueField O) N] [Module (ResidueField O)ᵐᵒᵖ N]
  [IsCentralScalar (ResidueField O) N] [Module O N] [IsScalarTower O (ResidueField O) N]
  [IsScalarTower O (ResidueField O)ᵐᵒᵖ N]

variable (P : Type u) [AddCommGroup P] [Module (ResidueField O) P] [Module (ResidueField O)ᵐᵒᵖ P]
  [IsCentralScalar (ResidueField O) P] [Module O P] [IsScalarTower O (ResidueField O) P]
  [IsScalarTower O (ResidueField O)ᵐᵒᵖ P]

variable {M N P}

def inlO : ResidueField O →ₐ[O] TrivSqZeroExt (ResidueField O) M :=
  { TrivSqZeroExt.inlHom (ResidueField O) M with
    commutes' := fun o => rfl }

end tsze
end P2mSchlessingerTangent
end
end P2MW.S_IsLocalRing_exists_trivSqZeroExt_forall_exists_algHom_dualNumber_of_forall_pullback_surjective_of_tangent_injective
