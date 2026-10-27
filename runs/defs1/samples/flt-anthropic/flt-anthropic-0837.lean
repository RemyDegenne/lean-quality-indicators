namespace P2MW.S_M4aHerbrand_sUnitQuot_fixedRank_eq

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section Fold_DenominatorClearing

namespace M4aLocalCFT

universe u

open AddSubgroup

variable {A B V : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup V]

p2m_reactivate

section Gates

noncomputable def intSwapPair : HerbrandPair (ℤ × ℤ) where
  derive :=
    { toFun := fun p => (p.2 - p.1, p.1 - p.2)
      map_zero' := by
        show ((0 : ℤ) - 0, (0 : ℤ) - 0) = (0, 0)
        simp
      map_add' := fun p q => by
        show (p.2 + q.2 - (p.1 + q.1), p.1 + q.1 - (p.2 + q.2))
          = (p.2 - p.1 + (q.2 - q.1), p.1 - p.2 + (q.1 - q.2))
        rw [Prod.mk.injEq]
        exact ⟨by ring, by ring⟩ }
  norm :=
    { toFun := fun p => (p.1 + p.2, p.1 + p.2)
      map_zero' := by
        show ((0 : ℤ) + 0, (0 : ℤ) + 0) = (0, 0)
        simp
      map_add' := fun p q => by
        show (p.1 + q.1 + (p.2 + q.2), p.1 + q.1 + (p.2 + q.2))
          = (p.1 + p.2 + (q.1 + q.2), p.1 + p.2 + (q.1 + q.2))
        rw [Prod.mk.injEq]
        exact ⟨by ring, by ring⟩ }
  derive_norm := fun p => by
    show ((p.1 + p.2) - (p.1 + p.2), (p.1 + p.2) - (p.1 + p.2)) = (0, 0)
    simp
  norm_derive := fun p => by
    show ((p.2 - p.1) + (p.1 - p.2), (p.2 - p.1) + (p.1 - p.2)) = (0, 0)
    rw [Prod.mk.injEq]
    exact ⟨by ring, by ring⟩

end Gates
end M4aLocalCFT
end Fold_DenominatorClearing
end P2MW.S_M4aHerbrand_sUnitQuot_fixedRank_eq
