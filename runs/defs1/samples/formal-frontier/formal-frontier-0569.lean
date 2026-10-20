@[expose] public section

open scoped TrivSqZeroExt

namespace SymmetricAlgebra

universe uR uM uN

variable {R : Type uR} {M : Type uM}

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The quotient equivalence identifies the cotangent ideal with the square-zero kernel,
as modules over the base ring. -/
noncomputable def cotangentIdealEquivKerIdeal :
    (augmentationIdeal (R := R) (M := M)).cotangentIdeal ≃ₗ[R]
      TrivSqZeroExt.kerIdeal R M := by
  let equiv := squareZeroQuotientEquiv (R := R) (M := M)
  apply equiv.toLinearEquiv.ofSubmodules
    ((augmentationIdeal (R := R) (M := M)).cotangentIdeal.restrictScalars R)
    ((TrivSqZeroExt.kerIdeal R M).restrictScalars R)
  apply Submodule.ext
  intro value
  rw [← squareZeroQuotientEquiv_cotangentIdeal (R := R) (M := M)]
  exact (Ideal.mem_map_iff_of_surjective equiv.toRingHom equiv.surjective).symm

end SymmetricAlgebra
end
