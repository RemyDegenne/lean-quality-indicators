public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open

open CFSG.Blueprint.Chevalley (Tag)

section Leaves

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

theorem lower_E8_one
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hc : orderOf ((2 : ZMod p) ^ f) = 1) : p ^ 8 ≤ Nat.card B := by
  obtain ⟨K, _, _, _, hK, ⟨θ⟩⟩ := exists_recipe_equiv
    (h.model.chevalleyExceptionalModel (by decide)).2
  have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact dvd_two_pow_sub_one h.prime hc
  exact h.pow_le_card_of_torusLift θ (TableBExc.ggTorusLift_E8 h.prime h.ne_two hpq)

end Leaves
end CFSG.StandardType.TableCRes
end
