public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Tail

theorem nonempty_equiv_of_natural_zmod {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥H}
    (hπ : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H U Z π) :
    Nonempty (↥H ≃* ↥(StatedSL 3 (ZMod 2))) :=
  ⟨(MulEquiv.ofBijective π ⟨injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩).symm⟩

end Tail
end FFC
end CFSG.Quasithin
end
