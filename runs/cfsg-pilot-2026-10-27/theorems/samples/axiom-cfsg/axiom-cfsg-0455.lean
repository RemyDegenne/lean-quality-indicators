public section

namespace CFSG.Quasithin.RuType.A65

open CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {G : Type*} [Group G]

variable [Finite G]

theorem card_centralizer_mul_eq (z t : G) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) *
        Nat.card {v : G // IsConj t v ∧ v * z = z * v} =
      Nat.card (Subgroup.centralizer ({z} : Set G)) *
        Nat.card {u : G // IsConj z u ∧ u * t = t * u} := by
  have hz := card_centralizer_mul_card_conjugatesOf z
  have ht := card_centralizer_mul_card_conjugatesOf t
  have hdc := card_conj_mul_card_comm z t
  have hzc : Nat.card (conjugatesOf z) = Nat.card {u : G // IsConj z u} := rfl
  have htc : Nat.card (conjugatesOf t) = Nat.card {v : G // IsConj t v} := rfl
  rw [hzc] at hz
  rw [htc] at ht
  have hpos : 0 < Nat.card {u : G // IsConj z u} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨z, IsConj.refl z⟩⟩, inferInstance⟩
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card (Subgroup.centralizer ({t} : Set G)) *
        Nat.card {v : G // IsConj t v ∧ v * z = z * v} * Nat.card {u : G // IsConj z u} =
      Nat.card (Subgroup.centralizer ({t} : Set G)) * (Nat.card {u : G // IsConj z u} *
        Nat.card {v : G // IsConj t v ∧ v * z = z * v}) := by ring
    _ = Nat.card (Subgroup.centralizer ({t} : Set G)) * Nat.card {v : G // IsConj t v} *
        Nat.card {u : G // IsConj z u ∧ u * t = t * u} := by rw [hdc]; ring
    _ = Nat.card (Subgroup.centralizer ({z} : Set G)) * Nat.card {u : G // IsConj z u} *
        Nat.card {u : G // IsConj z u ∧ u * t = t * u} := by rw [ht, hz]
    _ = Nat.card (Subgroup.centralizer ({z} : Set G)) *
        Nat.card {u : G // IsConj z u ∧ u * t = t * u} * Nat.card {u : G // IsConj z u} := by
      ring

end CFSG.Quasithin.RuType.A65
end
