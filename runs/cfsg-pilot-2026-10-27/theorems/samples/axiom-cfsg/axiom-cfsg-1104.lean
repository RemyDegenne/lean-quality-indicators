public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup CFSG.GH74.GLS

variable {X : Type} [Group X]

theorem oddResidualIn_eq_oPrimeResidualOf (Y : Subgroup X) :
    FooteLit.oddResidualIn Y = oPrimeResidualOf 2 Y := by
  unfold FooteLit.oddResidualIn oPrimeResidualOf oPrimeResidual
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, k, hk⟩
    refine ⟨⟨x, hx⟩, ⟨k, Subtype.ext ?_⟩, rfl⟩
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hk, pow_orderOf_eq_one]
  · rintro ⟨y, ⟨k, hk⟩, rfl⟩
    refine ⟨y.2, ?_⟩
    have hdvd : orderOf (y : X) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← Subgroup.coe_pow, hk, Subgroup.coe_one])
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩

end CFSG.ComponentClassification.Sol78
end
