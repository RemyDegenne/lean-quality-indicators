@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [LinearOrder ι] (R : Type u) [CommRing R]

namespace UpperTriangularGroup

variable {ι : Type u} [Fintype ι] [LinearOrder ι]

variable {R S Q : Type u} [CommRing R] [CommRing S] [CommRing Q]

/-- Inclusion into the native matrix general linear group. -/
def inclusion : UpperTriangularGroup ι R →* GeneralLinearGroup ι R :=
  (upperTriangularSubgroup ι R).subtype

end UpperTriangularGroup
end Matrix
end
end
