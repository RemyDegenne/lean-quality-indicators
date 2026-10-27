namespace P2MW.S_HeckeEis_finrank_coeffH1par_top_add_le

set_option autoImplicit false

set_option maxHeartbeats 800000

set_option synthInstance.maxHeartbeats 80000

noncomputable section

namespace HeckeEis

namespace UASol

p2m_open

open scoped MatrixGroups

open ModularGroup

def eU : ↥Gt := ⟨S * T, Subgroup.mem_top _⟩

end UASol
end HeckeEis
end
end P2MW.S_HeckeEis_finrank_coeffH1par_top_add_le
