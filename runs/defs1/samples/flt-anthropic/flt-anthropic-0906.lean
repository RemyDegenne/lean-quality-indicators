namespace P2MW.S_Module_exists_mumfordTruncation_of_flat_complex

set_option autoImplicit false

universe u

open scoped TensorProduct

noncomputable section

namespace TwoChartCech

namespace Mumford

namespace NTerm

p2m_open

section ThreeStep

variable {R : Type u} [CommRing R]

variable {C0 C1 C2 : Type u} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]
  [AddCommGroup C2] [Module R C2]

variable (d0 : C0 →ₗ[R] C1) (d1 : C1 →ₗ[R] C2) (hsq : d1 ∘ₗ d0 = 0)

variable [Module.Finite R (C2 ⧸ LinearMap.range d1)]

def kerToK0 : LinearMap.ker d1 →ₗ[R] K0 d1 :=
  LinearMap.codRestrict (K0 d1) ((LinearMap.inl R C1 _).comp (LinearMap.ker d1).subtype)
    (fun x => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.coprod_apply, map_zero,
        add_zero, Submodule.coe_subtype]
      exact x.2)

end ThreeStep
end NTerm
end Mumford
end TwoChartCech
end
end P2MW.S_Module_exists_mumfordTruncation_of_flat_complex
