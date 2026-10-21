namespace OAI

open Set Function Metric Filter Asymptotics Bornology

open scoped Topology OnePoint

noncomputable section

namespace CircleDomainRigidity

namespace FiniteJordanConfiguration

variable {I : Type*} [Finite I]

lemma selected_cap_eq (C : FiniteJordanConfiguration I) (schedule : ℕ → I) (n : ℕ) :
    FiniteTransfer.closedTerminalCap ((iterate C schedule (n+1)).hole (schedule n))=
      ((↑) : ℂ → Sphere) '' closedBall (selectedCenter C schedule n) (selectedRadius C schedule n) := by
  change ((↑) : ℂ → Sphere) '' closure (jordanInterior
    ((chosenStep (iterate C schedule n) (schedule n)).target.hole (schedule n))) = _
  rw [(chosenStep (iterate C schedule n) (schedule n)).selected]
  change ((↑) : ℂ → Sphere) '' closure (ball (selectedCenter C schedule n)
    (selectedRadius C schedule n)) = _
  rw [closure_ball _ (selectedRadius_pos C schedule n).ne']

end FiniteJordanConfiguration
end CircleDomainRigidity
end
end OAI
