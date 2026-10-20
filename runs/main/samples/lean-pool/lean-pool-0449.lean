@[expose] public noncomputable section

open Filter

open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

theorem viscositySubsolution_iff_testFunctionSubsolution
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} :
    ViscositySubsolution C F u <-> TestFunctionSubsolution C F u := by
  constructor
  · rintro ⟨husc, hjet⟩
    refine ⟨husc, ?_⟩
    intro x hx J φ h_le hφ
    exact hjet x hx J
      (superjet_of_eventually_le_of_hasSecondOrderExpansionWithinAtValue h_le hφ)
  · rintro ⟨husc, htest⟩
    refine ⟨husc, ?_⟩
    intro x hx J hJ
    rcases
      (superjet_iff_exists_eventually_le_hasSecondOrderExpansionWithinAtValue.mp hJ) with
      ⟨φ, h_le, hφ⟩
    exact htest x hx J φ h_le hφ

end ViscositySolns
end
