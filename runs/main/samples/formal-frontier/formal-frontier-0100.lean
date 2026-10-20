@[expose] public section

open scoped TrivSqZeroExt

namespace SymmetricAlgebra

universe uR uM uN

variable {R : Type uR} {M : Type uM}

variable [CommRing R] [AddCommGroup M] [Module R M]

@[simp] theorem cotangentIdealEquivKerIdeal_apply
    (x : (augmentationIdeal (R := R) (M := M)).cotangentIdeal) :
    ((cotangentIdealEquivKerIdeal (R := R) (M := M) x :
      TrivSqZeroExt.kerIdeal R M) : TrivSqZeroExt R M) =
      squareZeroQuotientEquiv (R := R) (M := M) x :=
  rfl

end SymmetricAlgebra
end
