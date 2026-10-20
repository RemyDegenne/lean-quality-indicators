public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

open scoped NumberField NumberField.AdeleRing

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

theorem ideleCongrOneSubgroup_inf_ideleCongruenceSubgroup_one (𝔪 : Modulus K) :
    ideleCongrOneSubgroup 𝔪 ⊓ ideleCongruenceSubgroup (Modulus.one K) =
      ideleCongruenceSubgroup 𝔪 := by
  ext x
  rw [Subgroup.mem_inf, mem_ideleCongruenceSubgroup_one_iff]
  exact ⟨fun ⟨hx, h⟩ ↦ ⟨fun v _ ↦ h v, hx⟩,
    fun hx ↦ ⟨hx.2, ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx⟩⟩

end TauCeti.GlobalNumberFields
end
end
