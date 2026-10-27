public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

open CFSG.Quasithin.Stroth.G5 CFSG.LieType.BorelTits CFSG.GH74.Uniqueness.Bender

variable {G : Type} [Group G] [Finite G]

variable {L1 L2 S : Subgroup G}

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem Gw_sub_one_add_one (c : ℤ) :
    t.Gw (c - 1) (c + 1) = t.Gv (c - 1) ⊓ t.Gv c ⊓ t.Gv (c + 1) := by
  ext y
  rw [mem_inf, mem_inf]
  constructor
  · intro hy
    exact ⟨⟨mem_win_iff.mp hy (c - 1) (by omega) (by omega),
      mem_win_iff.mp hy c (by omega) (by omega)⟩,
      mem_win_iff.mp hy (c + 1) (by omega) (by omega)⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact mem_win_iff.mpr fun i h1' h2' => by
      rcases (show i = c - 1 ∨ i = c ∨ i = c + 1 by omega) with rfl | rfl | rfl
      · exact h1
      · exact h2
      · exact h3

end Track
end CFSG.Quasithin.Stroth.Rq
end
