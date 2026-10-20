@[expose] public section

universe u v

open CategoryTheory

universe uS

namespace KTheory.K0

section FieldRingEquivalence

variable (K : Type u) [hK : Field K]

theorem finrankRingEquiv_comp_ofClass :
    (finrankRingEquiv K).toAddMonoidHom.comp (ofClass K) =
      (Int.ofNatHom : ℕ →+ ℤ).comp (ProjectiveClass.finrankHom K) := by
  rw [finrankRingEquiv_toAddMonoidHom, finrankHom_comp_ofClass]

end FieldRingEquivalence
end KTheory.K0
end
