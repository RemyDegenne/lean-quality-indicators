public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW

open CFSG.RankThree.PartOne (omegaOneCenterIn)

open scoped commutatorElement

variable {G : Type} [Group G]

namespace Gomi47

variable [Finite G]

omit [Finite G] in
theorem good47_of_no_gomiE' (hF : Gomi46Facts G) {P : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (hPN : ∀ H : Subgroup G, GomiH H → H ≤ P → P ≤ Subgroup.normalizer (H : Set G))
    (hno : ∀ E₁ E₂ : Subgroup G, ¬ GomiE' P E₁ E₂) : Good47 P := by
  intro Di Dj R hDi hDj hne hR
  have hPi := hPN Di hDi.1.1 hDi.1.2
  have hPj := hPN Dj hDj.1.1 hDj.1.2
  have hpair : GomiE P Di Dj :=
    ⟨hDi, hDj, hne, by rw [inf_eq_left.2 hPi, inf_eq_left.2 hPj], Or.inl ⟨hPi, hPj⟩⟩
  have h1 : ∃ Q₁ Q₂ : Subgroup G, IsOtherSylow P Di Q₁ ∧ IsOtherSylow P Dj Q₂ ∧
      (omegaOneCenterIn Q₁ ≤ Dj ∨ omegaOneCenterIn Q₂ ≤ Di) := by
    by_contra hcon
    push Not at hcon
    exact hno Di Dj ⟨hpair, fun Q₁ Q₂ h₁ h₂ => hcon Q₁ Q₂ h₁ h₂⟩
  obtain ⟨Q₁, Q₂, h₁, h₂, hor⟩ := h1
  have hiff := hF.l45_three P Di Dj Q₁ Q₂ hP hpair h₁ h₂
  have hX₂ : omegaOneCenterIn Q₂ ≤ Di := hor.elim hiff.1 id
  exact (hF.l45_three P Di Dj R Q₂ hP hpair hR h₂).2 hX₂

end Gomi47
end CFSG.CGT.PushingUpLit.C2L
end
