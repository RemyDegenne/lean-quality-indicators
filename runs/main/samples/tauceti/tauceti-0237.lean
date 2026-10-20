public section

open Module

namespace TauCeti.IntegralLattice

universe u v w x y z

variable {V : Type u} {W : Type v}

variable [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

section Isometry

variable {X : Type w} {Y : Type x} {U : Type y} {Z : Type z}

variable [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]

variable [AddCommGroup U] [Module ℚ U] [AddCommGroup Z] [Module ℚ Z]

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W}

variable {L' : IntegralLattice X} {M' : IntegralLattice Y}

@[simp]
theorem orthogonalSumComm_symm (L : IntegralLattice V) (M : IntegralLattice W) :
    (orthogonalSumComm L M).symm = orthogonalSumComm M L := by
  apply Isometry.ext
  intro p
  rw [Isometry.coe_symm, orthogonalSumComm_apply]
  simp only [orthogonalSumComm, LinearEquiv.symm_prodComm,
    LinearEquiv.prodComm_apply]
  rfl

end Isometry
end Isometry
end TauCeti.IntegralLattice
end
