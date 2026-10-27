public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Lin

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank

open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open CFSG.ClassicalGroups.UnitaryFlag

open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv psl_two_normal_form
  nonempty_mulEquiv_psl_of_lieModel nonempty_mulEquiv_primeFormP_of_lieModel')

theorem psu_component_cases {J : Type} [Group J] {n p f : ℕ} (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible .PSU n p f) (hm : Blueprint.LieModel J .PSU n p f)
    {α : MulAut J} (hα : orderOf α = 2) {Kc : Subgroup (fixedSubgroup α)}
    (hKc : IsComponent Kc) : ComponentCases p (linUTuples n f) Kc := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ p ^ f = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq (MulAut.congr ψ α)
  have hff : primeFormFieldFactor h hC hn hq (MulAut.congr ψ α) = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one (MulAut.congr ψ α)
    rw [hβ] at h1
    rw [h1, map_one]
  refine componentCases_of_component_equiv (fixedSubgroupCongrEquiv ψ α) (fun N hN => ?_) hKc
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · have hAα : MulAut.congr ψ α = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    have hord : orderOf (primeFormConjHom h _ A) = 2 := hAα ▸ hβ
    exact componentCases_of_component_equiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAα))
      (fun N' hN' => ComponentCases.mono (fun x hx => Or.inl hx)
        (inner_psu_component_cases h hp2 hadm A hord hN')) hN
  · have hord : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 := hAφ ▸ hβ
    exact componentCases_of_component_equiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAφ.symm))
      (fun N' hN' => Or.inr ((graph_psu_component_models h hp2 hadm A φ hφ hord hN').mono
        fun x hx => Or.inr hx)) hN

end CFSG.ComponentClassification.CatLeafProof.X10Lin
end
