public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th Native Max3

open CFSG.Sporadic.Recognition.PresentedWords

section Basic

theorem imgGL_mem_J {k : ℕ} (hk : k < 8) : Bridge.Th.imgGL k ∈ J := by
  have hJ : J ≤ Bridge.Th.φ.range := Bridge.Th.J_le_range
  have hcard : Nat.card Bridge.Th.φ.range ≤ Nat.card J := by
    have hfinP : Finite Bridge.Th.pres.Group := by
      change Finite TauCeti.SporadicName.Th.Group
      exact CFSG.Sporadic.Presentation.Th.finite_card_le.1
    letI := hfinP
    have h1 : Nat.card Bridge.Th.φ.range ≤ Nat.card Bridge.Th.pres.Group :=
      Nat.card_le_card_of_surjective Bridge.Th.φ.rangeRestrict
        (MonoidHom.rangeRestrict_surjective _)
    have h2 : Nat.card Bridge.Th.pres.Group ≤ 90745943887872000 := by
      change Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000
      exact CFSG.Sporadic.Presentation.Th.finite_card_le.2
    exact h1.trans (h2.trans Bridge.Th.card_J.symm.le)
  have heq : J = Bridge.Th.φ.range := Subgroup.eq_of_le_of_card_ge hJ hcard
  rw [heq]
  exact Bridge.Th.imgGL_mem_range k

end Basic
end CFSG.Sporadic.Th.Recog
end
