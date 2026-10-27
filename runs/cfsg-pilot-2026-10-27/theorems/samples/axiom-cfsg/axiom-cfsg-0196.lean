attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

open P51 (V e)

open S36 (hypF hypU hypA dot)

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

section Words

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) {g : Fin 3 → G}
  (hgH : ∀ i, g i ∈ H₅₂ b b₁ b₂ b₃ s₀) (hg : ∀ i v, g i * h5.ε v * (g i)⁻¹ = h5.ε (S52.gf i v))

include hg in
theorem FF81Sec5.conjBy_hyp {w : List (Fin 3)} {r i : Fin 13} (hw : S55.Carries w r i) :
    conjBy (S55.wel g w) (S55.hyp h5.εA r) = S55.hyp h5.εA i := by
  have hle : conjBy (S55.wel g w) (S55.hyp h5.εA r) ≤ S55.hyp h5.εA i := by
    rw [S55.hyp, Q42.conjBy_closure_pair, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · rw [h5.wel_εA hg]; exact (h5.coordA.mem_hyp i _).2 hw.1
    · rw [h5.wel_εA hg]; exact (h5.coordA.mem_hyp i _).2 hw.2
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_conjBy, h5.coordA.card_hyp, h5.coordA.card_hyp]

end Words
end CFSG.RankThree.PartTwo.Sec21.FF81
end
