@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [LinearOrder ι] (R : Type u) [CommRing R]

namespace UpperTriangularGroup

variable {ι : Type u} [Fintype ι] [LinearOrder ι]

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The U-first product map, whose multiplication uses diagonal conjugation. -/
def semidirHom :
    (UnitriangularGroup ι R ⋊[diagonalAction (ι := ι) (R := R)] DiagonalGroup ι R) →*
      UpperTriangularGroup ι R :=
  SemidirectProduct.lift UnitriangularGroup.inUpperTriangular diagonalSection (by
    intro diag
    apply MonoidHom.ext
    intro unit
    exact inUpperTriangular_diagonalAction diag unit)

end UpperTriangularGroup
end Matrix
end
end
