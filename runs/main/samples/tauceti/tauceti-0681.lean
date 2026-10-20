public section

noncomputable section

open Unitary

open scoped InnerProductSpace

namespace Matrix.IsHermitian

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι 𝕜}
  (hB : B.IsHermitian)

include hB

theorem one_sub_smul_eq_conjStarAlgAut_diagonal (c : 𝕜) :
    1 - c • B =
      conjStarAlgAut 𝕜 _ hB.eigenvectorUnitary
        (diagonal fun j => 1 - c * (hB.eigenvalues j : 𝕜)) := by
  have h : (diagonal fun j => 1 - c * (hB.eigenvalues j : 𝕜)) =
      1 - c • diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
    simp [← diagonal_one, ← diagonal_sub, ← diagonal_smul, Pi.smul_def]
  rw [h, map_sub, map_one, map_smul, ← hB.spectral_theorem]

end Matrix.IsHermitian
end
end
