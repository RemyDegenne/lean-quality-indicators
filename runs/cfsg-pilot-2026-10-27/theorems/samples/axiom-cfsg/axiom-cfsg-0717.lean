public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup

open scoped commutatorElement Pointwise

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem yamada_3_1 : (∃ P : Sylow 2 X, (P : Subgroup X) = d.S) ∧ Nat.card d.S = q ^ 12 ∧
    (d.S : Set X) = (d.U₁ : Set X) * (d.U₂ : Set X) * (d.U₃ : Set X) * (d.U₄ : Set X) *
      (d.U₅ : Set X) * (d.U₆ : Set X) ∧
    ∀ g ∈ d.S, ∃! a, d.nf a = g := by
  refine ⟨d.exists_sylow_eq_S, d.card_S, ?_, fun g hg => ?_⟩
  · ext g
    rw [SetLike.mem_coe, d.mem_S]
    constructor
    · rintro ⟨⟨a₁, a₂, a₃, a₄, a₅, a₆⟩, rfl⟩
      exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul
        (Set.mul_mem_mul ⟨a₁, rfl⟩ ⟨a₂, rfl⟩) ⟨a₃, rfl⟩) ⟨a₄, rfl⟩) ⟨a₅, rfl⟩) ⟨a₆, rfl⟩
    · rintro ⟨_, ⟨_, ⟨_, ⟨_, ⟨_, ⟨a₁, rfl⟩, _, ⟨a₂, rfl⟩, rfl⟩, _, ⟨a₃, rfl⟩, rfl⟩, _,
        ⟨a₄, rfl⟩, rfl⟩, _, ⟨a₅, rfl⟩, rfl⟩, _, ⟨a₆, rfl⟩, rfl⟩
      exact ⟨(a₁, a₂, a₃, a₄, a₅, a₆), rfl⟩
  · obtain ⟨a, ha⟩ := d.mem_S.1 hg
    exact ⟨a, ha, fun b hb => d.nf_injective (hb.trans ha.symm)⟩

end TrialityD4Data
end CFSG.LocalAnalysis.EvenBN.TrialityD4
end
