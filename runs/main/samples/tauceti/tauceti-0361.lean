public section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p] [PerfectRing R p]

local notation "𝕎" => WittVector p

@[simp]
theorem zero_teichmullerCoeff (n : ℕ) : (0 : 𝕎 R).teichmullerCoeff n = 0 := by
  simp [teichmullerCoeff_eq_iff, zero_pow (pow_ne_zero n hp.out.ne_zero)]

end WittVector
end
