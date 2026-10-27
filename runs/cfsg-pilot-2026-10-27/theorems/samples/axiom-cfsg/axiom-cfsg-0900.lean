public section

set_option linter.unusedSectionVars false

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

namespace Asc77

namespace S24B

namespace Ctx8Frame

section

open CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

open CFSG.ClassicalInvolution.Disconnected.AschTight (HypOmegaGen)

open scoped Pointwise

open CFSG.ClassicalInvolution.Asc77.S24

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8Frame Ω K K' W S R R' z u)

theorem conj_t_zpow (n : ℤ) :
    C.D.x₃ ^ n * C.D.F.ρ'.r * (C.D.x₃ ^ n)⁻¹ = C.D.x₂ ^ (-n) * C.D.F.ρ'.r := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S24.conj_t_zpow_of C.D.t₃ C.D.comm23 n

end
end Ctx8Frame
end S24B
end Asc77
end CFSG.ClassicalInvolution.Q3.Q3T8
end
