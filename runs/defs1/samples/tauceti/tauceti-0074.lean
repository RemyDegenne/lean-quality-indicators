public section

noncomputable section

open Equiv Equiv.Perm Polynomial

namespace TauCeti

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-- A resolvent item: `a` is an integral root of the quintic resolvent sextic and the sextic has
nonzero discriminant. The latter condition is precisely the separation evidence needed to read
the root as an upper bound on the Galois image. -/
def HasSexticRoot (f : ℤ[X]) (a : ℤ) : Prop :=
  (resolventSextic f).eval a = 0 ∧ (resolventSextic f).discr ≠ 0

end TauCeti
end
end
