namespace P2MW.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed

set_option maxHeartbeats 3200000

universe u v w

namespace W2G9

section AbsoluteGalois

theorem existsUnique_algHom_realizing_pointsMap_of_etale_absoluteGaloisGroup
    {K : Type*} [Field K] [CharZero K]
    {B : Type u} {C : Type v} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Algebra.Etale K B] [Algebra.Etale K C]
    (Φ : (C →ₐ[K] AlgebraicClosure K) → (B →ₐ[K] AlgebraicClosure K))
    (hΦ : ∀ (γ : Field.absoluteGaloisGroup K) (χ : C →ₐ[K] AlgebraicClosure K),
      Φ ((AlgEquiv.toAlgHom γ).comp χ) = (AlgEquiv.toAlgHom γ).comp (Φ χ)) :
    ∃! ψ : B →ₐ[K] C, ∀ χ : C →ₐ[K] AlgebraicClosure K, χ.comp ψ = Φ χ := by
  haveI : IsGalois K (AlgebraicClosure K) := ⟨⟩
  exact existsUnique_algHom_realizing_equivariant_pointsMap_of_etale Φ
    (fun γ χ => hΦ γ χ)

end AbsoluteGalois
end W2G9
end P2MW.S_AlgHom_exists_algEquiv_comp_eq_of_isAlgClosed
