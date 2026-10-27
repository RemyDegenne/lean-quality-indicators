public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.Model

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

open Certificates.TitsAschbacherParrott Certificates.TitsAschbacherSecFour
  Certificates.TitsAschbacherE32

open CFSG.Quasithin (tπ twoF4H twoF4N)

theorem hatE_long_or_short
    {e : Equiv.Perm (Fin 1755)} (he : e ∈ hatE) (he1 : e ≠ 1) : IsLong e ∨ IsShort e := by
  obtain ⟨m, hm, rfl⟩ := mem_hatE_iff.1 he
  have h1 : 1 ≤ m := by
    by_contra h0
    exact he1 (by rw [show m = 0 by omega, elt_values.1])
  rcases Nat.lt_or_ge (eTag m) 2 with h | h
  · exact Or.inl ((eElt_long_short hm h1).1 (by omega))
  · exact Or.inr ((eElt_long_short hm h1).2 (le_antisymm (eTag_facts.2.1 m hm) h))

end CFSG.LocalAnalysis.EvenBN.Tits.Model
end
