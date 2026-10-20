public section

open scoped TensorProduct

universe u v

variable {R ι : Type u} {M : Type v}

namespace SymmetricPower

section CommSemiring

variable [CommSemiring R]

variable [AddCommMonoid M] [Module R M]

/-- A linear map induces a linear map on every symmetric tensor power. -/
noncomputable def map {N : Type*} [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    Sym[R] ι M →ₗ[R] Sym[R] ι N where
  toFun :=
    (addConGen (Rel R ι M)).lift
      ((mk R ι N).toAddMonoidHom.comp
        (PiTensorProduct.map fun _ : ι => f).toAddMonoidHom)
      (map_rel f)
  map_add' := map_add _
  map_smul' r x := AddCon.induction_on x fun x => by
    exact congrArg (mk R ι N) ((PiTensorProduct.map fun _ : ι => f).map_smul r x)

end CommSemiring
end SymmetricPower
end
