public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.ABGLocalTools

open scoped commutatorElement

namespace Facts

section Core1

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G}

theorem false_of_mem_inf (F : Facts A) {x : G} (hx2 : orderOf x = 2) (hxA : x ∈ A)
    (hxK : x ∈ centralizer (A : Set G)) : False := by
  have h1 : 2 ∣ Nat.card ↥(A ⊓ centralizer (A : Set G)) := by
    have := Subgroup.orderOf_dvd_natCard (A ⊓ centralizer (A : Set G)) ⟨hxA, hxK⟩
    rwa [hx2] at this
  exact (Nat.not_even_iff_odd.2 F.odd_inf) (even_iff_two_dvd.2 h1)

end Core1
end Facts
end CFSG.OddStandard.Seitz77
end
