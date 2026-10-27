@[expose] public section

universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [CommRing R]

/-- The exterior power of an object in `ModuleCat R`. -/
def exteriorPower (M : ModuleCat.{v} R) (n : ℕ) : ModuleCat.{max u v} R :=
  ↧(⋀[R]^n M)

end ModuleCat
end
