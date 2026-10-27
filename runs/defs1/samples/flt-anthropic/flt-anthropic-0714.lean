set_option autoImplicit false

open Function

universe u v w u' v' w'

namespace Deformation

namespace HondaSystem.Examples

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime]

noncomputable def mult : HondaSystem (p : 𝓞) 𝓞 where
  toDieudonneDatum := DieudonneDatum.multOne (p : 𝓞)
  L := ⊤
  sh1_le x _ hx := by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, Submodule.mem_top, rfl⟩
  sh1_ge y _ := ⟨y, rfl⟩
  sh2' := sup_top_eq _
  sh3 x _ hx := hx

end HondaSystem.Examples
end Deformation
