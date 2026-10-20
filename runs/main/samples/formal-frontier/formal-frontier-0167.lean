@[expose] public section

universe u

namespace FreeGroupBasis

variable {G : Type u} [Group G]

local notation "indexTwoCoefficients" =>
  (![![Multiplicative.ofAdd 1, 1], ![1, Multiplicative.ofAdd 1],
    ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]] :
      Fin 3 → Fin 2 → Multiplicative (ZMod 2))

variable (b : FreeGroupBasis (Fin 2) G)

theorem ne_one_iff_existsUnique_indexTwoCharacter (χ : G →* Multiplicative (ZMod 2)) :
    χ ≠ 1 ↔ ∃! c : Fin 3, χ = b.indexTwoCharacter c := by
  constructor
  · intro hχ
    have hvalues : ∀ z : Multiplicative (ZMod 2),
        z = 1 ∨ z = Multiplicative.ofAdd (1 : ZMod 2) := by decide
    obtain ⟨c, hc⟩ : ∃ c : Fin 3, χ = b.indexTwoCharacter c := by
      rcases hvalues (χ (b 0)) with hzero | hzero <;>
        rcases hvalues (χ (b 1)) with hone | hone
      · exact (hχ (b.ext_hom χ 1 (by
          intro i
          fin_cases i <;> simpa using (by assumption)))).elim
      · refine ⟨1, b.ext_hom χ (b.indexTwoCharacter 1) ?_⟩
        intro i
        fin_cases i <;> simpa using (by assumption)
      · refine ⟨0, b.ext_hom χ (b.indexTwoCharacter 0) ?_⟩
        intro i
        fin_cases i <;> simpa using (by assumption)
      · refine ⟨2, b.ext_hom χ (b.indexTwoCharacter 2) ?_⟩
        intro i
        fin_cases i <;> simpa using (by assumption)
    refine ⟨c, hc, ?_⟩
    intro d hd
    exact b.indexTwoCharacter_injective (hd.symm.trans hc)
  · rintro ⟨c, hc, _⟩
    rw [hc]
    exact b.indexTwoCharacter_ne_one c

end FreeGroupBasis
end
