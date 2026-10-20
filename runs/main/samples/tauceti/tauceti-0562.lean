public section

namespace TauCeti

open _root_.Subgroup

variable {p : ℕ} {G H : Type*} [Group G] [Group H]

section OfSylow

variable (s : G) (P : Sylow p (centralizer ({s} : Set G)))

@[simp]
theorem coe_pFreePartHom_apply [Fact p.Prime] (hs : ¬ p ∣ orderOf s)
    (x : ↥(pElementaryOfSylow s P)) : (pFreePartHom s P hs x : G) = pFreePart p (x : G) :=
  (rfl)

end OfSylow
end TauCeti
end
