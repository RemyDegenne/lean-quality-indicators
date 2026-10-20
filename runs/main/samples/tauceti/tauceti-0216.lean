public section

open scoped LaurentSeries

namespace TauCeti.Place

variable {k F : Type*} [Field k] [Field F] [Algebra k F] (P : Place k F)

variable [Algebra.IsSeparable k P.ResidueField]

variable {t : F} (ht : P.ord t = 1)

theorem residueResidueField_apply (z : F) :
    P.residueResidueField ht z = (P.laurentSeriesExpansionResidueField ht z).coeff (-1) := (rfl)

end TauCeti.Place
end
