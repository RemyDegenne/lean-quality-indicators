public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

open CFSG.Assembly.RankThreeEven (projSL)

open Matrix

open scoped MatrixGroups

namespace Item424Res2

open Res423Two Item434CharThree

theorem exists_pow_four_of_map_eq {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {D : Subgroup X} {F : Subgroup Y} (hDF : D.map e.toMonoidHom = F)
    (hF : ∃ ρ ∈ autIn (⊤ : Subgroup Y) F, ρ ^ 4 = 1 ∧ ρ ^ 2 ≠ 1) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨ρ, hρ, h4, h2⟩ := hF
  have f := Sporadic.autInTopCongr e D
  rw [hDF] at f
  refine exists_pow_four_of_mulEquiv f (m := ⟨ρ, hρ⟩) ?_ ?_
  · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h4)
  · intro h
    exact h2 (by simpa using congrArg Subtype.val h)

end Item424Res2
end CFSG.RankThree.PartTwo.Sec4
end
