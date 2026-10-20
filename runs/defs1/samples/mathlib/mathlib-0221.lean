@[expose] public section

open IsLocalization Pointwise nonZeroDivisors

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]

variable [Algebra R P]

/-- An element of `S` such that `I.den • I = I.num`, see `FractionalIdeal.num` and
`FractionalIdeal.den_mul_self_eq_num`. -/
noncomputable def den (I : FractionalIdeal S P) : S :=
  ⟨I.2.choose, I.2.choose_spec.1⟩

end FractionalIdeal
end
