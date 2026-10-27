public section

open CategoryTheory CategoryTheory.Limits

namespace FiniteGroupTateCohomology

universe u

variable {R G : Type u} [CommRing R] [CommGroup G] [Fintype G]

namespace Cyclic

variable (A : Rep.{u} R G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Tate cohomology in every even integer degree, compared coherently with
`A --N--> A --(g - 1)--> A`. -/
noncomputable def tateCohomologyIsoEven (n : ℤ) (hn : Even n) :
    tateCohomology A n ≅ evenModel A g := by
  cases n with
  | ofNat i =>
      cases i with
      | zero =>
          exact tateIsoEvenZero (R := R) (G := G) A g hg
      | succ i =>
          have hi_even : Even (i + 1) := (Int.even_coe_nat (i + 1)).mp hn
          letI : NeZero (i + 1) := ⟨Nat.succ_ne_zero i⟩
          exact tateIsoEvenPositive A g hg (i + 1) hi_even
  | negSucc i =>
      change Even (-(i + 1 : ℤ)) at hn
      have hi_succ_even : Even (i + 1) :=
        (Int.even_coe_nat (i + 1)).mp (even_neg.mp hn)
      have hi_odd : Odd i :=
        Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hi_succ_even)
      letI : NeZero i := ⟨by
        intro h
        subst i
        exact Nat.not_odd_zero hi_odd⟩
      exact tateIsoEvenNegative A g hg i hi_odd

end Cyclic
end FiniteGroupTateCohomology
end
