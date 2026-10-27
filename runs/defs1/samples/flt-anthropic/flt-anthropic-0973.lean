namespace P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one

set_option autoImplicit false

set_option linter.unusedSectionVars false

open Subgroup SimpleGraph

namespace GroupTheory

namespace BassSerre

p2m_open

variable {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)]

abbrev Vertex : Type _ :=
  (i : ι) × (CoprodI G ⧸ (Monoid.CoprodI.of (M := G) (i := i)).range)

end BassSerre
end GroupTheory
end P2MW.S_Monoid_CoprodI_finrank_addMonoidHom_add_card_orbitRelQuotient_le_index_add_one
