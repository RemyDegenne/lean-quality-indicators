public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResRowAt.smallE6_prime_three {G : Type} [Group G] {p : ℕ}
    {J X : Subgroup G} (hrow : GGResRowAt ggRowTwoNodeSmallE6 p J X) : p = 3 := by
  obtain ⟨labJ, labX, _, _, _, _, ⟨hRow, _⟩, htag⟩ := hrow
  rcases hRow with ⟨_, _, _, hX⟩ | ⟨_, _, _, hX⟩ | ⟨_, hp, _, _⟩ | ⟨_, hp, _, _⟩
  · subst hX
    simp at htag
  · subst hX
    simp at htag
  · exact hp
  · exact hp

end CFSG.StandardType
end
