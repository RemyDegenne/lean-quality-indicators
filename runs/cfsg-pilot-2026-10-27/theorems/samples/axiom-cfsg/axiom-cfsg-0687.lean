public section

namespace CFSG.ABGTheoremB.V56

open CFSG.ABGLocalTools

open scoped Pointwise

variable {G : Type*} [Group G]

theorem isPGroup_thompsonCenter {p : ℕ} {U : Subgroup G} (hU : IsPGroup p U) :
    IsPGroup p (CFSG.thompsonCenter U) :=
  hU.to_le (CFSG.thompsonCenter_le U)

end CFSG.ABGTheoremB.V56
end
