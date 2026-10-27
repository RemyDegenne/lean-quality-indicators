public section

namespace CFSG.StandardType

open CFSG.Assembly

section Chev

variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K]

theorem chevFieldImage_eq_one_of_card_two (hK : Nat.card K = 2) (H : Subgroup (LargeEvenChevGL A K))
    {φ : MulAut (LargeEvenCenterQuot H)} (hφ : φ ∈ LargeEvenChevFieldImage A K H) : φ = 1 := by
  obtain ⟨σ, hσ⟩ := hφ
  ext y
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective y
  have := hσ h h (largeEvenEntrywise_of_forall_eq _ (ringEquiv_apply_eq_of_card_two hK σ) _).symm
  simpa using this

end Chev
end CFSG.StandardType
end
