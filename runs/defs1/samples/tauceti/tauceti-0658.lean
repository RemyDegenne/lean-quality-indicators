public section

noncomputable section

open LaurentPolynomial

namespace TauCeti

namespace OrientedPDCode

variable {n m : ℕ}

section Relabel

variable (D : OrientedPDCode n) (half : Fin (4 * n) ≃ Fin (4 * m)) (cross : Fin n ≃ Fin m)

/-- **Relabelling keeps the Alexander module**: the generator of a half-edge of the relabelled
code corresponds to the generator of its old name. -/
def alexanderModuleRelabelEquiv :
    (D.relabel half cross).AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] D.AlexanderModule :=
  LinearEquiv.ofLinearMap (relabelHom D half cross) (relabelInvHom D half cross)
    (by ext (h | j) <;> simp [relabelHom_alexanderGenerator, relabelInvHom_alexanderGenerator])
    (by ext (h | j) <;> simp [relabelHom_alexanderGenerator, relabelInvHom_alexanderGenerator])

end Relabel
end OrientedPDCode
end TauCeti
end
end
