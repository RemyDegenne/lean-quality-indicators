@[expose] public section

variable {M : Type*}

section Prime

variable [CommMonoidWithZero M]

@[simp]
theorem not_prime_one : ¬Prime (1 : M) := fun h => h.not_isUnit isUnit_one

end Prime
end
