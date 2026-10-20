public section

namespace TauCeti

namespace zHat

universe u

open Additive

@[simp]
theorem ofMul_ofInt (z : Multiplicative ℤ) :
    ofMul ((ofInt : Multiplicative ℤ →* zHat.{u}) z) = (z.toAdd : Additive zHat.{u}) := by
  rw [← ofAdd_toAdd z, ofInt_ofAdd, ← toMul_intCast, ofMul_toMul, toAdd_ofAdd]

end zHat
end TauCeti
end
