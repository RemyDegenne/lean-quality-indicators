public section

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The `n`-th symmetric power of an object of `ModuleCat R`: the degree-`n` homogeneous
submodule of its symmetric algebra. -/
abbrev symmetricPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ModuleCat.of R (TauCeti.SymmetricAlgebra.homogeneousSubmodule R M n)

end ModuleCat
end
