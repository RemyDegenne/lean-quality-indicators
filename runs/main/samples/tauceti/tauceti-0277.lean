public section

namespace TauCeti

variable {R : Type*} [Ring R]

section Pi

variable {ι : Type*} (A : ι → Type*) [∀ i, Ring (A i)]

@[simp]
theorem coe_centralIdempotentsPiEquiv_apply (e : centralIdempotents (∀ i, A i)) (i : ι) :
    (centralIdempotentsPiEquiv A e i : A i) = (e : ∀ i, A i) i := (rfl)

end Pi
end TauCeti
end
