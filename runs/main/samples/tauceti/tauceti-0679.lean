public section

open WithConv

namespace TauCeti

open DynkinType

namespace Symplectic

open GLSymplecticFin

universe u v

variable {m : ℕ}

@[simp]
theorem diagonalRootDatum_root_positiveLong (i : Fin m) :
    (diagonalRootDatum.{u} m).root (.positiveLong i) = Finsupp.single (ULift.up i) 2 := by
  rw [diagonalRootDatum_root, RootSubgroupIndex.equivTypeCIndex_positiveLong,
    root_typeCIndexEquiv_of_not_lt (lt_irrefl i), map_add, characterEquiv_signedWeight]
  simp only [Bool.false_eq_true, ↓reduceIte, one_smul]
  rw [← Finsupp.single_add, one_add_one_eq_two]

end Symplectic
end TauCeti
end
