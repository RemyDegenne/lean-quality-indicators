public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG (conjugate)

open CFSG.Open

open CFSG.ComponentClassification

open scoped commutatorElement

section FourGroup

open CFSG.ComponentClassification.AschbacherKnownGroup (IsFourGroup)

variable {G : Type} [Group G] [Finite G]

theorem exists_fourGroup_of_two_le_pRank {X : Subgroup G} (h : 2 ≤ Open.pRank 2 X) :
    ∃ V : Subgroup G, V ≤ X ∧ IsFourGroup V := by
  obtain ⟨E, hEX, hE, hcard⟩ := SectionRank.exists_pRank (by norm_num : 1 < 2) X
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ^ 2 ∣ Nat.card E := by rw [hcard]; exact pow_dvd_pow 2 h
  obtain ⟨V₀, hV₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have hEc := hE.1
  refine ⟨V₀.map E.subtype, (Subgroup.map_subtype_le V₀).trans hEX,
    ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨a₀, -, ha⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨b₀, -, hb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← ha, ← hb]
    exact congrArg Subtype.val (mul_comm' a₀ b₀)
  · obtain ⟨x₀, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact hE.2 x₀ x₀.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hV₀]
    norm_num

end FourGroup
end CFSG.CGT.PushingUpLit.CGT6.Nine7
end
