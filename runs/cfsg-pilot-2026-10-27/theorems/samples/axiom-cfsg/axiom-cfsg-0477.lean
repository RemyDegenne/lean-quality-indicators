public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G]

namespace GHSylow

variable (D : GHSylow G)

theorem conj_t_S {c : G} (hc : c ∈ (D.S : Subgroup G)) :
    c⁻¹ * D.t * c = D.t ∨ c⁻¹ * D.t * c = D.t * D.z := by
  obtain ⟨c', rfl⟩ := D.exists_toG hc
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  rcases SE.conj_invRep1 c' with h | h <;> rw [h]
  · exact Or.inl rfl
  · exact Or.inr rfl

end GHSylow
end CFSG.ComponentClassification.GHarris
end
