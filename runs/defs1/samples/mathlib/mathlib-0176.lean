@[expose] public section

variable (M : Type*) [Monoid M]

open Polynomial

section CommRing

variable (G : Type*) [Group G] [Fintype G]

variable (R : Type*) [CommRing R] [MulSemiringAction G R]

open MulAction

/-- the product of `(X - g • x)` over distinct `g • x`. -/
noncomputable def prodXSubSMul (x : R) : R[X] :=
  letI := Classical.decEq R
  (Finset.univ : Finset (G ⧸ MulAction.stabilizer G x)).prod fun g ↦
    Polynomial.X - Polynomial.C (ofQuotientStabilizer G x g)

end CommRing
end
