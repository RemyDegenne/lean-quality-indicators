namespace P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio

set_option Elab.async false

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section DeskModule19

set_option autoImplicit false

noncomputable section

open Matrix FLT.EKAverage FLT.SmoothVectors

namespace FLT

namespace PrincipalSeriesGL2Padic

p2m_open

open LocalNewvector

namespace PSCarrier

namespace G

open LocalNewvector LocalNewvector.PSCarrier

variable (p : ℕ) [Fact p.Prime] (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)

p2m_reactivate

section ExtCells

theorem eq_zero_of_cells {f : PSCarrier p μ₁ μ₂}
    (hN : ∀ y : ℚ_[p], toFn p μ₁ μ₂ f (lowerUnip p y) = 0)
    (hw : toFn p μ₁ μ₂ f (weyl p) = 0) :
    f = 0 :=
  ext_cells p μ₁ μ₂ (fun y => (hN y).trans rfl) (hw.trans rfl)

end ExtCells
end G
end PSCarrier
end PrincipalSeriesGL2Padic
end FLT
end
end DeskModule19
end P2MW.S_LocalNewvector_PSCarrier_isIrreducibleGLRep_of_hasCharConductor_of_ratio
