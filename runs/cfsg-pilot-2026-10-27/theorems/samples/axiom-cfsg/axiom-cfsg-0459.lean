public section

namespace CFSG.RankThree.PartOne.OutStructure

open Matrix Subgroup QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration

open scoped commutatorElement

section Models

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit

open scoped Pointwise

theorem outPNice_POmegaMinus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    {n m : ℕ} (hn : 4 ≤ n) (h : StatedClassicalModel X .POmegaMinus n 2 m) : OutPNice p X := by
  obtain ⟨-, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := id h
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K n hn b c
    hirr
  exact OutPNice.of_mulEquiv (coordinateMinusWitnessEquiv K (by omega) b c e)
    (outPNice_of_image_top _ hnd hT hp hp2 htop)

end Models
end CFSG.RankThree.PartOne.OutStructure
end
