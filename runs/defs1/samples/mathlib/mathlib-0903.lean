@[expose] public section

open Module

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b "," c "]" =>
    QuaternionAlgebra R a b c

@[inherit_doc]
scoped[Quaternion] notation "ℍ[" R "," a "," b "]" => QuaternionAlgebra R a 0 b

namespace QuaternionAlgebra

open scoped Quaternion

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

section Zero

variable [Zero R]

/-- The imaginary part of a quaternion.

Note that unless `c₂ = 0`, this definition is not particularly well-behaved;
for instance, `QuaternionAlgebra.star_im` only says that the star of an imaginary quaternion
is imaginary under this condition. -/
def im (x : ℍ[R,c₁,c₂,c₃]) : ℍ[R,c₁,c₂,c₃] :=
  ⟨0, x.imI, x.imJ, x.imK⟩

end Zero
end QuaternionAlgebra
end
