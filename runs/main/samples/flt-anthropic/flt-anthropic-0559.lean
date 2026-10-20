namespace P2MW.S_HeckeEis_le_finrank_fixed_S_and_ST_binaryFormRepSL

set_option autoImplicit false

set_option maxHeartbeats 1600000

set_option synthInstance.maxHeartbeats 160000

open scoped MatrixGroups

open MvPolynomial

namespace UH1

theorem bvec_mem (c₁ c₂ : ℂ) (n a : ℕ) (ha : a ≤ n) : bvec c₁ c₂ n a ∈ HeckeEis.BinaryForm ℂ n := by
  rw [MvPolynomial.mem_homogeneousSubmodule, bvec]
  have h := ((isHomogeneous_lin c₁).pow a).mul ((isHomogeneous_lin c₂).pow (n - a))
  rwa [one_mul, one_mul, Nat.add_sub_cancel' ha] at h

end UH1
end P2MW.S_HeckeEis_le_finrank_fixed_S_and_ST_binaryFormRepSL
