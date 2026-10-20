namespace P2MW.S_CerednikDrinfeld_exists_mem_holOn_apply_toOmega_eq_of_chartMap_of_cerednikDrinfeld_quotient

set_option autoImplicit false

open scoped TensorProduct MatrixGroups

open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

noncomputable section

namespace EDB

section L5

variable {Onr R C : Type} [CommRing Onr] [CommRing R] [Field C] [Algebra Onr R] [Algebra R C]
  (π' : Onr) (q : ℕ)

def L5RatRep (a : chartERing Onr π' q) : Prop :=
  ∃ ρ : Omega.RatPair C, ∀ x : chartERing Onr π' q →ₐ[Onr] R,
    ρ.den.eval (algebraMap R C (x (chartERing.ξ Onr π' q))) ≠ 0 ∧
    ρ.evalAt (algebraMap R C (x (chartERing.ξ Onr π' q))) = algebraMap R C (x a)

end L5
end EDB
end
end P2MW.S_CerednikDrinfeld_exists_mem_holOn_apply_toOmega_eq_of_chartMap_of_cerednikDrinfeld_quotient
