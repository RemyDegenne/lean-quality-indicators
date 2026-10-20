set_option warningAsError true

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR uS uT

@[simp]
lemma mapRingHom_scalar {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    (f : R →+* S) (unit : Rˣ) :
    mapRingHom f (scalar ι unit) = scalar ι (Units.map f unit) := by
  apply Units.ext
  ext i j
  simp [mapRingHom_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

end Matrix.GeneralLinearGroup
end
