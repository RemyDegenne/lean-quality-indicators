public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KLCE CFSG.RankThree.PartOne.KD4T

section Main

theorem ggTorusNoLine_E8Plus_largePrime {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hlarge : ¬ GGNbrExcPlusSmallPrimeE7E8 p) :
    GGTorusNoLine p 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have h3 : p ≠ 3 := fun h => hlarge (Or.inl h)
  have h5 : p ≠ 5 := fun h => hlarge (Or.inr h)
  have h11 : 11 ≤ p :=
    ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one hp hp2 (hK ▸ hpq) h3 h5
  have := TableBExc.finite_recipeGroup .E8 K
  set e := TableBExc.recipeEquiv .E8 K with he_def
  have hT : SylowTorus (TableBExc.RecipeGroup .E8 K) p 8 :=
    (ExcFramesHalf.sylowTorus_E8_half K hp h11 hpq).of_mulEquiv e.symm
  refine ggTorusNoLine_of_scNoLine hp (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (fun φ hφ _ => TableBExc.idImage_subset_inn_E8 K hφ)
    (ExcSplitL.ggCenterPrime_recipe_E8 hp hp2) ?_
  refine ggSCNoLine_of_sylowTorus_frame hp hp2 hpq hT
    (fun i => e.symm.toMonoidHom.comp (TableBExcTwo.rho K TableBExcTwo.frameE8 i))
    (fun i => ?_) (fun i j hij A B => ?_) (fun i => ?_) 7
  · exact e.symm.injective.comp (TableBExcTwo.rho_injective _ i)
  · exact (TableBExcTwo.commute_rho _ hij A B).map e.symm.toMonoidHom
  · obtain ⟨j, hji, g, hg⟩ := ExcPlusLargeE8.exists_conj_rho_E8 (K := K) i
    refine ⟨j, hji, e.symm g, fun A => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_inv, ← map_mul, hg]

end Main
end CFSG.StandardType
end
