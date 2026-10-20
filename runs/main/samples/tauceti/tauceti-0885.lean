public section

namespace Nat.Partition

open TauCeti Equiv Finset

theorem character_indFDRep_trivial_parts_two_one_one_eq_sum {k : Type*} [Field k]
    (μ : Nat.Partition 4) (hμ : μ.parts = {2, 1, 1}) (g : Perm (Fin 4)) :
    (indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))).character g =
      ((symmetricGroupFourCharacterTable ⟨0, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨2, by decide⟩ (symmetricGroupFourClassData.index g) +
        2 * symmetricGroupFourCharacterTable ⟨3, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨4, by decide⟩
          (symmetricGroupFourClassData.index g) : ℤ) : k) := by
  let A := indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))
  have hg := ClassFunction.eq_of_isConj (ClassFunction.ofCharacter A.ρ)
    (symmetricGroupFourClassData.isConj_rep_index g)
  simp only [ClassFunction.ofCharacter_apply] at hg
  have ha : A.character (symmetricGroupFourClassData.rep (symmetricGroupFourClassData.index g)) =
      A.character g := hg
  rw [← ha, character_indFDRep_trivial_parts_two_one_one μ hμ]
  generalize symmetricGroupFourClassData.index g = j
  have hc : ∀ j : SymmetricGroupFourClassIndex,
      symmetricGroupFourCharacterTable ⟨0, by decide⟩ j +
        symmetricGroupFourCharacterTable ⟨2, by decide⟩ j +
        2 * symmetricGroupFourCharacterTable ⟨3, by decide⟩ j +
        symmetricGroupFourCharacterTable ⟨4, by decide⟩ j =
      (![12, 2, 0, 0, 0] : Fin 5 → ℤ) (j.cast numClasses_symmetricGroupFourClassData) := by
    simp only [symmetricGroupFourCharacterTable_apply]
    intro j
    fin_cases j <;> decide
  rw [hc]
  fin_cases j <;> norm_num [Fin.cast, Matrix.cons_val]

end Nat.Partition
end
