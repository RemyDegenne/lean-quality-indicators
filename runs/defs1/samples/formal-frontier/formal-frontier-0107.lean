@[expose] public section

noncomputable section

universe u

namespace Matrix

variable (ι : Type u) [Fintype ι] [LinearOrder ι] (R : Type u) [CommRing R]

namespace UpperTriangularGroup

variable {ι : Type u} [Fintype ι] [LinearOrder ι]

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Diagonal conjugation on the existing unitriangular group, transported
through Mathlib's normalizer action and `MulAut.congr`. The entrywise weight
is `dᵢ * uᵢⱼ * dⱼ⁻¹`; normality in all of GL is not claimed. -/
def diagonalAction : DiagonalGroup ι R →* MulAut (UnitriangularGroup ι R) :=
  (MulAut.congr (kernelEquiv (ι := ι) (R := R)).symm).toMonoidHom.comp
    (((diagonal (ι := ι) (R := R)).ker.normalizerMonoidHom).comp
      ((diagonalSection (ι := ι) (R := R)).codRestrict _
        (fun _ => by simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top])))

end UpperTriangularGroup
end Matrix
end
end
