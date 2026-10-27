public section

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

noncomputable local instance commSemiringIntegralHeckeRingLocal [NeZero n] :
    CommSemiring (IntegralHeckeRing n) :=
  { (HeckeCosetModule.instSemiringHeckeRing ℤ : Semiring (IntegralHeckeRing n)) with
    mul_comm := HeckeCosetModule.mul_comm_of_antiInvolution ℤ (transposeAntiInvolution n)
      (transposeAntiInvolution_onHeckeCoset_eq_self n) }

section TGen

variable (p : ℕ) (hp : p.Prime)

variable [NeZero n]

include hp in
/-- The k-th generator of pLocalSubring: `T(1,...,1,p,...,p)` with `k+1` entries of `p`. -/
noncomputable def heckeGen (k : Fin n) : IntegralHeckeRing n :=
  diagElem (heckeGenDiag n p k)

end TGen
end HeckeRing.GLn
end
