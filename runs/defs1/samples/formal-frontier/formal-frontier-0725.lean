@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [LinearOrder ι] (R : Type u) [CommRing R]

namespace UpperTriangularGroup

variable {ι : Type u} [Fintype ι] [LinearOrder ι]

variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]

/-- Apply a ring homomorphism to each matrix entry. -/
def map (ringHom : R →+* S) : UpperTriangularGroup ι R →* UpperTriangularGroup ι S where
  toFun matrix := ⟨GeneralLinearGroup.map ringHom matrix.1, matrix.2.map ringHom⟩
  map_one' := by
    apply Subtype.ext
    exact (GeneralLinearGroup.map ringHom).map_one
  map_mul' left right := by
    apply Subtype.ext
    exact (GeneralLinearGroup.map ringHom).map_mul left.1 right.1

end UpperTriangularGroup
end Matrix
end
end
