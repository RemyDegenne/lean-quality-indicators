@[expose] public section

namespace Pi

variable (ι : Type*)

variable {R : Type*}

variable (A : ι → Type*)

variable [CommSemiring R] [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)]

@[simp]
theorem algebraMap_apply (a : R) (i : ι) : algebraMap R (Π i, A i) a i = algebraMap R (A i) a :=
  rfl

end Pi
end
