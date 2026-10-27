namespace P2MW.S_groupCohomology_inf_injective_and_exact_of_isZero_res

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep

set_option maxHeartbeats 3200000

noncomputable section

namespace P2mS26IR

open CategoryTheory CategoryTheory.Limits Representation

variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G) [S.Normal]

def P (q : ℕ) (A : Rep.{u} k G) : Prop :=
  Function.Injective (inf S A q).hom ∧
    ∀ x : groupCohomology A q, (res S A q).hom x = 0 → ∃ y, (inf S A q).hom y = x

end P2mS26IR
end
end P2MW.S_groupCohomology_inf_injective_and_exact_of_isZero_res
