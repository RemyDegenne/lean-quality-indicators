namespace OAI

noncomputable section

open CategoryTheory

open scoped BigOperators

open CategoryTheory Finsupp

open CategoryTheory Finsupp MonoidalCategory

open scoped BigOperators Matrix

open scoped Matrix

namespace CoboundaryExpanders.Actions

universe u

variable {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]

@[simp] theorem induced_id (j : ℕ) : induced (k := k) (MonoidHom.id G) j = 𝟙 _ :=
  groupHomology.map_id j

end CoboundaryExpanders.Actions
end
end OAI
