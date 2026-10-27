public section

namespace CFSG.RankThree.GF2n.Smith81.U6Cube

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix exteriorPower CFSG.LieType.Universal.Unitary
  CFSG.ClassicalGroups.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

theorem pt0_eq :
    pt0 K = cubeBasis K (tripleSet 0 2 4 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 0 2 5 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 0 3 4 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 0 3 5 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 1 2 4 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 1 2 5 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 1 3 4 (by decide) (by decide) (by decide)) +
      cubeBasis K (tripleSet 1 3 5 (by decide) (by decide) (by decide)) := by
  unfold pt0
  simp only [ι3_add_fst, ι3_add_snd, ι3_add_thd]
  rw [e_triple_eq 0 2 4 (by decide) (by decide), e_triple_eq 0 2 5 (by decide) (by decide),
    e_triple_eq 0 3 4 (by decide) (by decide), e_triple_eq 0 3 5 (by decide) (by decide),
    e_triple_eq 1 2 4 (by decide) (by decide), e_triple_eq 1 2 5 (by decide) (by decide),
    e_triple_eq 1 3 4 (by decide) (by decide), e_triple_eq 1 3 5 (by decide) (by decide)]
  abel

end CFSG.RankThree.GF2n.Smith81.U6Cube
end
