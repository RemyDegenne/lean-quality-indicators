namespace P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient

open scoped TensorProduct

open IsLocalRing Module Polynomial

namespace LCMazur

namespace OrdQ

section Unique

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]

variable [IsLocalRing A] [Module.Free A V] [Module.Finite A V] {φ : End A V} {α β : A}

theorem span_singleton_eq_range_ordProj (h2 : finrank A V = 2)
    (hφ : φ.charpoly = (X - C α) * (X - C β)) (hu : IsUnit (α - β)) {w : V}
    (hw : ∀ v, φ v - β • v ∈ A ∙ w) : (A ∙ w) = LinearMap.range (ordProj φ α β) := by
  obtain ⟨b, hb⟩ := exists_basis_range_ordProj h2 hφ hu
  have hle : LinearMap.range (ordProj φ α β) ≤ A ∙ w := by
    rintro _ ⟨v, rfl⟩
    rw [ordProj_apply]
    exact Submodule.smul_mem _ _ (hw v)
  rw [hb] at hle ⊢
  exact (span_basis_eq_of_le b 0 hle).symm

end Unique
end OrdQ
end LCMazur
end P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_quotient
