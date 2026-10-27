namespace P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup

set_option autoImplicit false

noncomputable section

p2m_open

namespace CerednikDrinfeld

p2m_open

namespace Mumford

p2m_open

namespace I4a

variable {G : Type} [Group G] {W : Type} [MulAction G W] {𝒯 : SimpleGraph W} [GraphAction G 𝒯]
  {Γ' : Subgroup G} [GraphAction (↥Γ') 𝒯]

variable (G Γ') in

def piq : QuotEdge (↥Γ') 𝒯 → QuotEdge G 𝒯 :=
  Quotient.map' id (fun _ _ h => by obtain ⟨γ, h⟩ := h; exact ⟨(γ : G), h⟩)

end I4a
end Mumford
end CerednikDrinfeld
end
end P2MW.S_CerednikDrinfeld_Mumford_exists_finiteHom_quotientDegeneracyData_of_subgroup
