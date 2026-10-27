public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148PtRes

open Equiv Equiv.Perm

open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

open CFSG.ComponentClassification

theorem eq_one_of_fixed_alternating_six {τ : MulAut (alternatingGroup (Fin 6))}
    (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {g : alternatingGroup (Fin 6)} (hg : τ g = g) {k : ℕ}
    (hgk : g ^ k = 1) (hk3 : Nat.Coprime k 3) : g = 1 := by
  obtain ⟨h, rfl⟩ := mem_inner_of_pow_three hτ3
  have hinj := CatalogueSchreierAlternating.DegreeSix.inner_conjugation_injective
  have hh3 : h ^ 3 = 1 := hinj (by rw [map_pow, hτ3, map_one])
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hτ1 (map_one _)
  have hgh : g * h = h * g := by
    have h1 : h * g * h⁻¹ = g := hg
    calc g * h = h * g * h⁻¹ * h := by rw [h1]
      _ = h * g := by group
  have hx3 : (h : Perm (Fin 6)) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hh3, Subgroup.coe_one]
  have hx1 : (h : Perm (Fin 6)) ≠ 1 := fun he => hh1 (Subtype.ext he)
  have hgx : (g : Perm (Fin 6)) * h = h * g := congrArg Subtype.val hgh
  have hg3 : (g : Perm (Fin 6)) ^ 3 = 1 :=
    pow_three_eq_one_of_commute_six hx3 hx1 (mem_alternatingGroup.mp g.2) hgx
  have hg3' : g ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hg3, Subgroup.coe_one])
  have hd : orderOf g ∣ Nat.gcd k 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hgk) (orderOf_dvd_of_pow_eq_one hg3')
  rw [hk3, Nat.dvd_one] at hd
  exact orderOf_eq_one_iff.mp hd

end CFSG.RankThree.PartTwo.Sec14.Item148PtRes
end
