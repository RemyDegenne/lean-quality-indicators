public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Equiv Equiv.Perm Subgroup CFSG.GH74 CFSG.GH74.GLS CFSG.Open

namespace Setup

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {S : Setup G} (c : Ctx S)

theorem NH_inf_CP_le_CPH : c.NH ⊓ c.CP ≤ c.CPH := fun _ hy => ⟨hy.2, hy.1.2⟩

end Ctx
end Setup
end CFSG.Sporadic.Recognition.JankoWong
end
