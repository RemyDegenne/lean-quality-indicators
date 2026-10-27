public section

open MulAction

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

variable {s : G} {H K : Subgroup G}

variable (s H K) in
/-- The inclusion of the Mackey subgroup into `sHs⁻¹`, along which the conjugate representation
`{}^s A` is restricted. -/
def mackeyToConjH : mackeySubgroup s H K →* (MulAut.conj s • H : Subgroup G) :=
  Subgroup.inclusion mackeySubgroup_le_conj

end TauCeti
end
