public section

namespace CFSG.Quasithin.H13

namespace L211L

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo Matrix

open scoped MatrixGroups

section Model

local instance fact11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

theorem sabc_eleven : (sj1 * sj0 * sc) ^ 11 = 1 := Subtype.ext (by decide)

end Model
end L211L
end CFSG.Quasithin.H13
end
