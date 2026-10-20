public section

open Matrix Matrix.SpecialLinearGroup HeckeRing HeckeCosetModule

namespace HeckeRing.GLn

variable (n : ℕ)

variable [NeZero n]

/-- The integral Hecke ring of `GL_n` is commutative. -/
@[instance_reducible]
noncomputable def commSemiringIntegralHeckeRing : CommSemiring (IntegralHeckeRing n) :=
  commSemiringHeckeRing n ℤ

end HeckeRing.GLn
end
