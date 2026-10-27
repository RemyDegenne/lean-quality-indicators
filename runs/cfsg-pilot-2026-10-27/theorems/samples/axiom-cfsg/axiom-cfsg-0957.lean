public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

section Orthogonal

open CFSG.Open CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData

open CFSG.RankThree.Classical.SteinbergBY

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter

open CFSG.HardMathSupport.Lang.Proving

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (mem_E_of_pow_eq_one_omega
  mem_inner_of_mem_D_omega)

theorem exists_conj_of_pow_prime_omegaOdd_three {G : Type} [Group G] {n : ℕ}
    (hG : StatedClassicalModel G .POmegaOdd n 3 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (β : MulAut G) (hβ : β ^ p = 1) : ∃ a, β = MulAut.conj a := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n 3 1 hG K hK e
  set e' := coordinateOddWitnessEquiv K e
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) := Finite.of_equiv _ e'.toEquiv
  haveI : Fact p.Prime := ⟨hp⟩
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hE := mem_E_of_pow_eq_one_omega hgates hp (Or.inl (by omega)) hβ'
  by_cases hD : MulAut.congr e' β ∈ (linearConjugationHom (coordinateQuadOdd n K)).range
  · obtain ⟨t, ht⟩ := mem_inner_of_mem_D_omega hgates hp (by omega) hD hβ'
    exact exists_conj_of_congr e' β ⟨t, ht.symm⟩
  · have hord : orderOf (MulAut.congr e' β) = p :=
      orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd
      (Or.inl rfl) n 3 1 p hG hp (by omega) K hK e _ hE hD hord
    exact absurd (Nat.le_of_dvd one_pos hdesc.1) (by omega)

end Orthogonal
end CFSG.LocalAnalysis.GLTheoremA.S2019
end
