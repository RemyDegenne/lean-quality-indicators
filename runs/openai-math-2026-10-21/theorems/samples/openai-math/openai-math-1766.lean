namespace OAI

section

section

namespace DilutedSpinGlass.PrescribedTree

open scoped BigOperators Classical

variable {L : ℕ}

theorem shiftedCharge_relative_bound (hL : 0 < L) (Q : Finset ℕ)
    (T S : PrescribedTree L) (k : ℕ) (a b : T.Leaf) (hab : a ≠ b)
    (η : ℝ) (hη : 0 < η) (hr : BranchRegular T (grid L 0 L) η)
    (hb : branchingCount T (fun _ => True) = branchingCount T (· ∈ Q)+1) :
    shiftedCharge Q T S k /
        |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}| ≤
      chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k
        (branchingCount T (· ∈ Q)) / η^(branchExcess T) := by
  let J := |partialKappa T (grid L 0 L) Finset.univ / partialKappa T (grid L 0 L) {b,a}|
  let A := chargeBound (2*(leaves S+k:ℕ)) ((Q.card:ℝ)*(leaves S+k:ℕ)) k
    (branchingCount T (· ∈ Q))
  let D := (L:ℝ)⁻¹^(branchingCount T (· ∈ Q))
  let E := η^(branchExcess T)
  have hD : 0 < D := pow_pos (inv_pos.mpr (Nat.cast_pos.mpr hL)) _
  have hE : 0 < E := pow_pos hη _
  have hA : 0 ≤ A := chargeBound_nonneg (by positivity) (by positivity) _ _
  have hlo : D*E ≤ J := protectedKappa_grid_lower hL T a b hab η hη.le hr _ hb
  have hJ : 0 < J := (mul_pos hD hE).trans_le hlo
  change A*D/J ≤ A/E
  apply (div_le_div_iff₀ hJ hE).mpr
  have hh := mul_le_mul_of_nonneg_left hlo hA
  nlinarith [hh]

end DilutedSpinGlass.PrescribedTree
end
end
end OAI
