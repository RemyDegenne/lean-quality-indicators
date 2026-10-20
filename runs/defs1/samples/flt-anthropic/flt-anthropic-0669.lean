namespace P2MW.S_ValuationSubring_exists_admissible_smallConstants_stable_of_eq_two

set_option autoImplicit false

open IsLocalRing

open scoped Pointwise

namespace ConstAdm

local notation "ℚ̄" => AlgebraicClosure ℚ

def incl (A : ValuationSubring ℚ̄) (k₀ : IntermediateField ℚ ℚ̄) :
    ↥(A.comap (algebraMap ↥k₀ ℚ̄)) →+* ↥A :=
  { toFun := fun x => ⟨((x : ↥k₀) : ℚ̄), x.2⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

end ConstAdm
end P2MW.S_ValuationSubring_exists_admissible_smallConstants_stable_of_eq_two
