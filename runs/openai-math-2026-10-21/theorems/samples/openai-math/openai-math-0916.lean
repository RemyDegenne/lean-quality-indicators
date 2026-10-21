namespace OAI

section

open Finset

open scoped ComplexConjugate BigOperators

namespace SquareDifference

section PrimaryCoefficient

variable {I : Type*} [Fintype I] [DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)
  (q : ℕ) [NeZero q]
  (hq : q∣∏i, primaryModulus q (p i))

lemma primary_root_sieve_square_zero (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (H : ℝ)
    (hH : ((∏i∈primaryActive p q\R, p i : ℕ) : ℝ)≤H)
    (i : I) (hi : i∉R) (hqi : p i∣q) (hpi : p i≠2)
    (hei : primaryModulus q (p i)≠p i) :
    truncatedSieveMean univ p H
      (rootSieveA p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R c
        (primaryCoordinateChar p hinj q hq ψ))
      (rootSieveB p (fun i => primaryModulus q (p i)) (fun i => prime_dvd_primaryModulus q (p i)) R
        (primaryCoordinateChar p hinj q hq ψ))=0 := by
  exact rootSieve_zero_of_squarefactor p (fun i => primaryModulus q (p i))
    (fun i => prime_dvd_primaryModulus q (p i)) R c (primaryCoordinateChar p hinj q hq ψ)
    univ (primaryActive p q) (subset_univ _) H
    (fun j _ hj => primaryCoordinateChar_trivial p hinj q hq ψ j (by simpa only [mem_primaryActive] using hj)) hH i
    (mem_sdiff.mpr ⟨(mem_primaryActive p q i).mpr hqi,hi⟩) hpi
    ((primaryModulus_eq_or_square q (p i)).resolve_left hei)
    (primaryCoordinateChar_primitive p hinj q hq ψ hψ i hqi)

end PrimaryCoefficient
end SquareDifference
end
end OAI
