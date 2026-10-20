@[expose] public section

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open Module

open scoped nonZeroDivisors Polynomial

section IsDedekindDomain

variable {R A}

variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal

variable {K}

lemma FractionalIdeal.mul_inf (I J K : FractionalIdeal A⁰ K) : I * (J ⊓ K) = I * J ⊓ I * K :=
  mul_inf₀ (zero_le _) _ _

end IsDedekindDomain
end
