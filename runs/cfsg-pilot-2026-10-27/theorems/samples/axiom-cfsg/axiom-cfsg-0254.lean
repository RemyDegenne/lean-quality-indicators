public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

section Block

variable {K : Type*} [Field K] {n : ℕ}

theorem det_submatrix_of_agrees_one {r : ℕ} {e : Fin r → Fin n} (he : Function.Injective e)
    {J : Finset (Fin n)} (hJ : ∀ i, i ∈ J ↔ i ∈ Set.range e) {M : Matrix (Fin n) (Fin n) K}
    (hM : ∀ i j, (i ∉ J ∨ j ∉ J) → M i j = (1 : Matrix (Fin n) (Fin n) K) i j) :
    (M.submatrix e e).det = M.det := by
  classical
  rw [M.twoBlockTriangular_det' (fun s => s ∈ Set.range e) fun a ha b hb => by
    rw [hM a b (Or.inr fun h => hb ((hJ b).1 h)),
      one_apply_ne (show a ≠ b from fun h => hb (h ▸ ha))]]
  have h1 : M.toSquareBlockProp (fun s => s ∉ Set.range e) = 1 := by
    ext ⟨a, ha⟩ ⟨b, hb⟩
    rw [toSquareBlockProp, Matrix.toBlock_apply, hM a b (Or.inl fun h => ha ((hJ a).1 h)),
      one_apply, one_apply]
    simp only [Subtype.mk.injEq]
  rw [h1, det_one, mul_one]
  convert det_submatrix_equiv_self (Equiv.ofInjective e he)
    (M.toSquareBlockProp fun s => s ∈ Set.range e) using 2
  rfl

end Block
end CFSG.SeitzReduction.LinearPilot
end
