@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [LinearOrder ι] (R : Type u) [CommRing R]

namespace UpperTriangularGroup

variable {ι : Type u} [Fintype ι] [LinearOrder ι]

variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]

/-- Project an upper-triangular matrix to its invertible diagonal. -/
def diagonal : UpperTriangularGroup ι R →* DiagonalGroup ι R where
  toFun matrix := (DiagonalGroup.unitsEquiv (R := R)).symm
    (fun row => (isUnit_entry matrix row).unit)
  map_one' := by
    apply DiagonalGroup.ext
    intro row
    change ((DiagonalGroup.unitsEquiv (R := R)).symm
      (fun index : ι => (isUnit_entry (1 : UpperTriangularGroup ι R) index).unit)).1 row row =
      (1 : DiagonalGroup ι R).1 row row
    simp [DiagonalGroup.unitsEquiv_symm_apply]
  map_mul' left right := by
    apply DiagonalGroup.ext
    intro row
    change ((DiagonalGroup.unitsEquiv (R := R)).symm
      (fun index : ι => (isUnit_entry (left * right) index).unit)).1 row row =
      ((DiagonalGroup.unitsEquiv (R := R)).symm
        (fun index : ι => (isUnit_entry left index).unit) *
        (DiagonalGroup.unitsEquiv (R := R)).symm
        (fun index : ι => (isUnit_entry right index).unit)).1 row row
    rw [← map_mul (DiagonalGroup.unitsEquiv (R := R)).symm]
    simp only [DiagonalGroup.unitsEquiv_symm_apply, IsUnit.unit_spec]
    exact UnitriangularCoordinateRing.upper_mul_diag left.2 right.2 row

end UpperTriangularGroup
end Matrix
end
end
