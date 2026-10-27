public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.RankOne

open scoped Pointwise

section Bender

variable {Y : Type*} [Group Y]

theorem not_isCyclic_of_mul_self {P : Subgroup Y} (hexp : ∀ a ∈ P, a * a = 1)
    (hq : 4 ≤ Nat.card P) : ¬ IsCyclic P := by
  intro hcyc
  have h := Monoid.exponent_dvd_of_forall_pow_eq_one (G := P) (n := 2) fun a =>
    Subtype.ext (by simpa [pow_two] using hexp a a.2)
  rw [IsCyclic.exponent_eq_card] at h
  have := Nat.le_of_dvd two_pos h
  omega

end Bender
end CFSG.Timmesfeld.Bridge
end
