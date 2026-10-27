public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.Vol2.Ch10.SecA CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

section Convert

variable {Y : Type} [Group Y]

theorem lred3_four_of_hatM22 (hY : CFSG.IsQuasisimple Y) {Γ₀ : Type} [Group Γ₀]
    (hhat : IsHat Γ₀ ↥CFSG.Open.quasithinM22) (π : Γ₀ →* Y) (hπ : Function.Surjective π) :
    FourList (Y ⧸ Subgroup.center Y) := by
  obtain ⟨e⟩ := lred3_cq_of_quasisimple hhat.1 hY π hπ
  obtain ⟨f⟩ := hhat.2.2
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨(e.symm.trans f).trans (MulEquiv.subgroupCongr
      (by rfl : CFSG.Open.quasithinM22 = CFSG.Blueprint.NativeSporadic.M22))⟩))))))))

end Convert
end CFSG.Quasithin
end
