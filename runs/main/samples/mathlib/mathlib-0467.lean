public section

open scoped Int

variable {M : Type*}

namespace Units

variable [Monoid M]

lemma conj_pow' (u : Mˣ) (x : M) (n : ℕ) :
    ((↑u⁻¹ : M) * x * (u : M)) ^ n = (↑u⁻¹ : M) * x ^ n * (u : M) := u⁻¹.conj_pow x n

end Units
end
