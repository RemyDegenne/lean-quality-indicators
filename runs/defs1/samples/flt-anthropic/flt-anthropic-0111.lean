namespace P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

set_option linter.unusedSectionVars false

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

set_option autoImplicit false

p2m_open

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

namespace OrderedAffineCoverOf

namespace Acyclic

p2m_open

universe u

section AltImg

variable {V : Scheme.{u}} {W : V.Opens} (K : Scheme.OrderedAffineCoverOf W)

def altInsert {i : ℕ} (s : K.Idx i) (j : K.ι)
    (hj : j ∉ altImg K s) : K.Idx (i + 1) :=
  altOfFinset K (insert j (altImg K s))
    (by rw [Finset.card_insert_of_notMem hj, card_altImg])

end AltImg
end Acyclic
end OrderedAffineCoverOf
end Scheme
end AlgebraicGeometry
end
end P2MW.S_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_ker_d_zero_eq_range_aug
