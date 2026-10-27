public section

namespace CFSG

namespace FiveTransitive.Degree68LargePrimeFreeCore

open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ¬ 7 ∣ Nat.card P) (s : Set X) (hs : s.ncard = 5)
    (p : ℕ) (hp : p.Prime) (hlarge : 11 ≤ p) : ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  by_cases hsmall : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29
  · exact small_not_dvd_five_fixer p hp hsmall P hcard h5 hnotAlt hseven s hs
  by_cases h31 : p = 31
  · subst p
    exact Degree68LargePrimeThirtyOne.not_dvd_five_fixer P hcard h5 hnotAlt s hs
  have h32 : 32 ≤ p := by
    by_contra hn
    have hu : p ≤ 31 := by omega
    interval_cases p <;> norm_num at *
  let sf := s.toFinite.toFinset
  have he : (sf : Set X) = s := s.toFinite.coe_toFinset
  have hsf : sf.card = 5 := by rw [← Set.ncard_coe_finset,he]; exact hs
  have hh := Degree68LargePrimeLong.long_not_dvd_five_fixer P hcard h5 hnotAlt sf hsf p hp h32
  rwa [he] at hh

end FiveTransitive.Degree68LargePrimeFreeCore
end CFSG
end
