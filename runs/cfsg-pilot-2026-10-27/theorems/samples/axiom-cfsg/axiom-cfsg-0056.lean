public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S1417

section Setup

variable {G : Type} [Group G] [Finite G] {T Mc : Subgroup G}

theorem omegaOneCenterOf_inf_eq {T V : Subgroup G} (hVe : IsElemAbelian 2 V) (hVT : V ≤ T) :
    omegaOneCenterOf (thompsonJ T) ⊓ V = V ⊓ Subgroup.centralizer (thompsonJ T : Set G) := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.2, ?_⟩
    have : omegaOneCenterOf (thompsonJ T) ≤ Subgroup.centralizer (thompsonJ T : Set G) :=
      (Subgroup.closure_le _).2 fun z hz => hz.1.2
    exact this hx.1
  · intro x hx
    refine ⟨?_, hx.1⟩
    rw [omegaOneCenterOf, ← omegaOneCenterOf, ← (omegaOne_centralizer_thompsonJ T).1]
    exact Subgroup.subset_closure ⟨⟨hVT hx.1, hx.2⟩, hVe.2 x hx.1⟩

end Setup
end S1417
end CFSG.Quasithin
end
