public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace ZeroCrossedMass

open CrossFamilyProjection DisjointCoherentFamilies MultipleRemainderProjection
  NormalInducedFamily

theorem mul_normalMass_le {L : Type*} [Group L] [Finite L] (H : Subgroup L) {c : ℝ}
    (hch : c ≤ (Nat.card H : ℝ)) :
    c * normalMass H ≤ ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
  have h1 := one_le_natCard H
  have he : (0 : ℝ) ≤ (H.index : ℝ) := Nat.cast_nonneg _
  have hpos : (0 : ℝ) < (Nat.card H : ℝ) := by linarith
  have hrw : c * normalMass H
      = (c / (Nat.card H : ℝ)) * (((Nat.card H : ℝ) - 1) / (H.index : ℝ)) := by
    rw [normalMass_eq]; ring
  rw [hrw]
  have h2 : c / (Nat.card H : ℝ) ≤ 1 := (div_le_one hpos).2 hch
  have h3 : (0 : ℝ) ≤ ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := div_nonneg (by linarith) he
  nlinarith

end ZeroCrossedMass
end CFSG.FeitThompson
end
