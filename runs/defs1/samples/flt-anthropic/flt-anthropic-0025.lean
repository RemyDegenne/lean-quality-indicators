namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree

set_option autoImplicit false

universe u

noncomputable section

namespace B28U3

section Transfer

p2m_open

variable {p : ℕ} [hp : Fact p.Prime] {B : Type} [CommRing B] {j : CerednikDrinfeld.Zp2 p →+* B}

section S

variable (D D' : GradedCartierModuleData p B j) (γ : Fin 2 → D.M) (γ' : Fin 2 → D'.M)

def S (K : ℕ) : Set (D.M × D'.M) :=
  {q | ∃ (c : ℕ → Fin 2 → B) (h : D.M) (h' : D'.M),
    q.1 = ev D γ K c + (⇑D.verschiebung)^[K] h ∧ q.2 = ev D' γ' K c + (⇑D'.verschiebung)^[K] h'}

end S
end Transfer
end B28U3
end
end P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_bijective_map_eq_of_hasStructureConstants_of_torsionFree
