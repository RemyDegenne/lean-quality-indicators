public section

namespace CFSG.QuasithinUnique.Borel252

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique.Fin257

section Data

variable {M : Type} [Group M] {U R₁ R₂ : Subgroup M}

theorem BorelData.charTwo₂ (h : BorelData M U R₁ R₂) :
    CharTwo (Subgroup.normalizer (R₂ : Set M)) := by
  unfold CharTwo
  rw [h.core₂]
  intro x hx
  obtain ⟨-, hxc⟩ := Subgroup.mem_inf.mp hx
  exact h.cent₂ x fun r hr => (Subgroup.mem_centralizer_iff.mp hxc r hr).symm

end Data
end CFSG.QuasithinUnique.Borel252
end
