namespace P2MW.S_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw

set_option autoImplicit false

set_option maxHeartbeats 4000000

set_option synthInstance.maxHeartbeats 1600000

open scoped NNReal

open Polynomial

namespace Ws26T4

open ExtCitation.LocalLevel IsLocalRing

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

scoped instance isScalarTower_int : IsScalarTower ℤ_[q] Kw (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem isLocalHom_algebraMap_intClosure [IsLocalRing (integralClosure ℤ_[q] Kw)] :
    IsLocalHom (algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw)) := by
  refine ⟨fun z hz => ?_⟩

  have hu : IsUnit (intClosureEquivRw q Kw (algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw) z)) :=
    hz.map (intClosureEquivRw q Kw)
  have h1 := norm_eq_one_of_isUnit q Kw hu
  rw [coe_intClosureEquivRw] at h1
  have h2 : ((algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw) z : Kw) : PadicAlgCl q)
      = algebraMap ℚ_[q] (PadicAlgCl q) (z : ℚ_[q]) := rfl
  rw [h2, PadicAlgCl.norm_extends] at h1
  exact PadicInt.isUnit_iff.mpr h1

end Ws26T4
end P2MW.S_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw
