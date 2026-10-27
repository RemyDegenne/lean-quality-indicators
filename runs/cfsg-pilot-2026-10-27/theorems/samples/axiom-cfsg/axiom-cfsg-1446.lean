public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

open scoped commutatorElement

section FFJ

variable {V : Type*} [CommGroup V]

theorem ffJ_ffJ (X : Subgroup (MulAut V)) : ffJ (ffJ X) = ffJ X :=
  le_antisymm (iSup₂_le fun _ hA => B6.le_ffJ ⟨hA.1.trans (B6.ffJ_le X), hA.2⟩)
    (iSup₂_le fun _ hA => B6.le_ffJ ⟨B6.le_ffJ hA, hA.2⟩)

end FFJ
end CFSG.Quasithin.EmptyFaithfulMultiple
end
