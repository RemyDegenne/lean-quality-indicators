@[expose] public section

open Set Function Complex

open UpperHalfPlane hiding I

open scoped Real

local notation "𝕢" => Periodic.qParam

local notation "ℍₒ" => upperHalfPlaneSet

namespace ModularForm

scoped[ModularForm] notation "η" => eta

lemma logDeriv_one_sub_cexp (r : ℂ) : logDeriv (fun z ↦ 1 - r * cexp z) =
    fun z ↦ -r * cexp z / (1 - r * cexp z) := by
  ext z
  simp [logDeriv]

end ModularForm
end
