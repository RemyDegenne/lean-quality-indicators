public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.Assembly.RankThreeEven (projSL)

open CFSG.RankThree.PartTwo.Sec11.LSSolvableProof (card_projSL_two_even isSimpleGroup_projSL)

open scoped commutatorElement

theorem false_of_frattini_section_four
    {G : Type} [Group G] [Finite G]
    {Q : Type*} [Group Q] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3) {P : Subgroup G} (ρ : P →* Q) {j : P}
    (hj : IsPGroup p (Subgroup.zpowers j)) {S B : Subgroup Q}
    (hSj : S ≤ Subgroup.centralizer {ρ j}) (hSρ : S ≤ ρ.range) (hB : Group.IsSolvable B)
    (hcent : ∀ x ∈ Subgroup.centralizer {j}, ρ x ∈ B) (e : S ≃* projSL 2 (GaloisField 2 4)) :
    False :=
  false_of_frattini_section_of_minDegree hp2 hloc ρ hj hSj hSρ hB hcent (by norm_num) e
    (l2EvenSolvableMinDegree_four p hp2)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
end
