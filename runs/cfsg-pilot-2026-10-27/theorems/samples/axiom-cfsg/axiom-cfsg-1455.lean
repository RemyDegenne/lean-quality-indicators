public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.B.Classical.E6Adjoint

open CFSG.Monster.Existence.StdOdd.P5 (E5 GL5 M5 rk refl reflGL genA genB Pbar IsExt)

open CFSG.LieType.Chevalley.C2E6Std (card_stdGroup)

theorem exists_sylow_isExt_fixDim :
    ∃ (P : Sylow 3 Rgrp) (E : Subgroup P) (ι : E ≃* Multiplicative E5) (ρ : P →* GL5),
      IsExt Pbar E ι ρ ∧
        (∀ x : E5, fixDim (((ι.symm (Multiplicative.ofAdd x) : E) : P) : Rgrp) = 6 + rk x) ∧
        (∀ e : E, fixDim (((e : P) : Rgrp)) = 6 + rk (P5.ivec E ι e)) := by
  obtain ⟨T, E, ι, ρ, h, h1, h2⟩ := exists_isExt_stdGroup_fixDim
  have hcard : Nat.card T = 3 ^ 9 := h.pbar_card
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite Rgrp := Nat.finite_of_card_ne_zero (by rw [card_stdGroup]; norm_num)
  exact ⟨Sylow.ofCard T (by rw [hcard, sylowThree_card_factorization]), E, ι, ρ, h, h1, h2⟩

end CFSG.Monster.Existence.StdOdd.Cert
end
