namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace RG3aAux

section T

variable {X₀ : Scheme.{0}} (𝒰 : X₀.OrderedAffineCover)

theorem κ_inv (i j : 𝒰.ι) : (κ 𝒰 i j).inv = X₀.homOfLE (O_comm_le 𝒰 j i) := rfl

end T
end RG3aAux
end P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_glued_of_overlap_isos_of_forall_base_eq
