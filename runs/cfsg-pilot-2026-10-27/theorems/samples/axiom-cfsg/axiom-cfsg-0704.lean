public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {z : G}

omit [Finite G] in
theorem mem_liftToSylow_iff (hz : IsCentralInvolution (S : Subgroup G) z)
    {X : Subgroup (EscapingQuotient z)} (s : (S : Subgroup G)) :
    (s : G) ∈ liftToSylow hz X ↔ sylowBar hz s ∈ X := by
  rw [mem_liftToSylow]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨s.2, h⟩⟩

end CFSG.ProperTwoGeneratedCore.Lemma37
end
