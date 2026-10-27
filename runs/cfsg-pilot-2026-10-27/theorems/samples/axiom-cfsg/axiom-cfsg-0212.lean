public section

namespace CFSG.Quasithin.D4Hex

open CFSG.Quasithin.H13.F431.G2Two

variable {G : Type} [Group G] [Finite G]

theorem card_abelian_le_32 {z : G} {Q A : Subgroup G} (hQcard : Nat.card Q = 512)
    (hQcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z)
    (hQZ : ∀ w ∈ Q, (∀ q ∈ Q, q * w = w * q) → w = 1 ∨ w = z) (hAQ : A ≤ Q)
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : Nat.card A ≤ 32 := by
  have h := card_sq_le_two_mul_of_abelian hQcomm hQZ hAQ hA
  rw [hQcard] at h
  by_contra hgt
  push Not at hgt
  nlinarith

end CFSG.Quasithin.D4Hex
end
