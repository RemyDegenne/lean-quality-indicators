public section

namespace CFSG.Monster.B.Pinned

open Bin Primes.Native

section RepGroup

variable {G : Type*} [Group G] {n : ℕ} {f : G →* Matrix (Fin n) (Fin n) (ZMod 2)}

theorem rep_inv {X Y : Mat} {g : G} (hX : Rep f X g) (hY : Y.size ≤ n)
    (h : (mulP n X Y == idMat n) = true) : Rep f Y g⁻¹ := by
  refine ⟨hY, ?_⟩
  have e := cmat_eq_of_beq (n := n) h
  rw [cmat_mulP _ _ _ hY, cmat_idMat, hX.2] at e
  calc cmat n Y = f (g⁻¹ * g) * cmat n Y := by rw [inv_mul_cancel, map_one, one_mul]
    _ = f g⁻¹ * (f g * cmat n Y) := by rw [map_mul, mul_assoc]
    _ = f g⁻¹ := by rw [e, mul_one]

end RepGroup
end CFSG.Monster.B.Pinned
end
