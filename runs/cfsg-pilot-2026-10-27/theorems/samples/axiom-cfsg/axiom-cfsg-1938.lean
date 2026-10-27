public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace Round12Cl

theorem BC {p l n : ℕ} {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C)
    (h : GGTableBNbrInnerRound12Label p ⟨t, l, n⟩) : False := by
  obtain ⟨-, hBC, -, -, -, hSp, -, -, -, -, -, -, hNsVac⟩ := h.parts
  by_cases hq : p ∣ 2 ^ n - 1
  · exact hBC ⟨ht, hq⟩
  · by_cases hq1 : p ∣ 2 ^ n + 1
    · exact hSp ⟨ht, hq1⟩
    · exact hNsVac (Or.inl ⟨ht, hq, hq1⟩)

end Round12Cl
end CFSG.StandardType
end
