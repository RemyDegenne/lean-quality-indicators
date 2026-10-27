public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace Conf

variable (K : Conf S T₁)

theorem pN_eq_of {n : X} (hn : n ∈ K.NR) {i j : Fin 8} (h : ∀ e ∈ K.Ex i, n * e * n⁻¹ ∈ K.Ex j) :
    K.pN hn i = j := K.pi_eq_of _ h

end Conf
end KD8c
end CFSG.ComponentClassification.HSFLit
end
