namespace P2MW.S_CerednikDrinfeld_exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

noncomputable section

namespace EDB

section L5

variable {Onr R C : Type} [CommRing Onr] [CommRing R] [Field C] [Algebra Onr R] [Algebra R C]
  (π' : Onr) (q : ℕ)

variable {π' q}

theorem L5RatRep.of_algebraMap (r : Onr) :
    L5RatRep (R := R) (C := C) π' q (algebraMap Onr (chartERing Onr π' q) r) :=
  L5RatRep.of_const _ (algebraMap R C (algebraMap Onr R r)) fun x => by rw [AlgHom.commutes]

end L5
end EDB
end
end P2MW.S_CerednikDrinfeld_exists_linearPieces_eq_chartUnitLocus_of_cerednikDrinfeld_quotient
