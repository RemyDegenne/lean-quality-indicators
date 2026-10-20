namespace P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm

set_option autoImplicit false

noncomputable section

namespace W0A

open ModularCurve IntermediateField

local notation "Qb" => AlgebraicClosure ℚ

section Aut

variable (F : IntermediateField ℚ (LaurentSeries ℚ)) {L : Type} [Field L] [CharZero L]
  (ιA : L →+* Qb)
  (ψ : ↥(laurentBaseChange Qb F) ≃ₐ[Qb] ↥(laurentBaseChange Qb F))
  (hψ : ∀ τ : Qb ≃ₐ[ℚ] Qb, (∀ x : L, τ (ιA x) = ιA x) →
      ∀ g : ↥(laurentBaseChange Qb F), ψ (arithmeticGalois F τ • g) = arithmeticGalois F τ • ψ g)

@[scoped simp] theorem emb_descend (f : ↥(laurentBaseChange L F)) :
    emb F ιA (descend F ιA ψ hψ f) = ψ (emb F ιA f) := emb_descendFun F ιA ψ hψ f

end Aut
end W0A
end
end P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_coeffMap_eq_of_arithmeticGalois_comm
