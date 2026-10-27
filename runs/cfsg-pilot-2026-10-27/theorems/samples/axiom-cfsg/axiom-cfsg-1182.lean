public section

namespace CFSG.Quasithin

open scoped Pointwise

section Transport

variable {B : Type*} [Group B] (X : Subgroup B) (e : ↥X ≃* D33)

theorem omsh_exists_elt {x : B} (hx : x ∈ X) : ∃ d : D33, omshφ X e d = x :=
  ⟨e ⟨x, hx⟩, omshφ_eq X e hx⟩

end Transport
end CFSG.Quasithin
end
