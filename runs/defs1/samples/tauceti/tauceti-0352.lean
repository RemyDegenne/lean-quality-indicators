public section

namespace TauCeti

open ContCohomology Multiplicative Subgroup

attribute [local instance 2000] Ring.toAddCommGroup

variable (p : ℕ) [Fact p.Prime]

section Presentation

/-- **`⟨x₁, x₂ ∣ (x₁, x₂)⟩ ≃ₜ* ℤ_p × ℤ_p`**, the exponent-sum isomorphism: the generator `xᵢ` goes
to the coordinate vector `eᵢ` (`TauCeti.presentedProPEquivPiPadicInt_of`). -/
noncomputable def presentedProPEquivPiPadicInt :
    presentedProP p (Fin 2) {demushkinWordNeTwo 0 2 (freeProPGen p 2)} ≃ₜ*
      Multiplicative (Fin 2 → ℤ_[p]) :=
  (presentedProP.congrOfClosureEq (by
    rw [topologicalClosure_normalClosure_demushkinWordNeTwo_zero_two,
      (freeProP.exponentSum p (Fin 2)).topologicalClosure_normalClosure_ker])).trans
    (presentedProP.equivOfSurjective (freeProP.exponentSum p (Fin 2))
      (freeProP.exponentSum_surjective p (Fin 2)))

end Presentation
end TauCeti
end
