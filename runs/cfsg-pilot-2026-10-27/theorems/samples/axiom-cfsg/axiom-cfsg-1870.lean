public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace Setup

variable {G : Type} [Group G] [Finite G] {S : Setup G}

section Certs

namespace Phi1

variable {c : Ctx S} {a₁ v v₁ φ₁ : G} (hφ : Phi1 c φ₁) (h : Sec4Hyp c a₁ v v₁)

include hφ h in
theorem phi2_orderOf : orderOf (cj φ₁ v) = 3 :=
  orderOf_eq_prime (hφ.phi2_cube h) (hφ.phi2_ne_one)

end Phi1
end Certs
end Setup
end CFSG.Sporadic.Recognition.JankoWong
end
