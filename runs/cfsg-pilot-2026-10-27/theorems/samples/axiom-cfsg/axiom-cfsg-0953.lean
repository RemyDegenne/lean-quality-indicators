public section

set_option linter.unusedSectionVars false

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77

open CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected

namespace S24B

open CFSG.ClassicalInvolution.Asc77.S24B

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace Ctx8

open CFSG.ClassicalInvolution.Asc77.S24B.Ctx8

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (C : Asc77.S24B.Ctx8 Ω K K' W S R R' z u)

theorem orderOf_x₁ : orderOf C.D.x₁ = 4 := by rw [C.D.o₁, C.m_eq_one]

end Ctx8
end S24B
end Asc77
end
end CFSG.ClassicalInvolution.Q3.Q3T8
end
