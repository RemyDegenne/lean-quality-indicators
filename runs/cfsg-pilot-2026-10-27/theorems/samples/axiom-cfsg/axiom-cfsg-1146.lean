public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Equiv

section Finish

variable {K : Type*} [Group K]

theorem finish_swap_model (α : MulAut K) (φ : K ≃* ↥A6Models.psl29) (a : P10)
    (hφ : ∀ k : K, ((φ (α k) : ↥A6Models.psl29) : P10) = a * ((φ k : ↥A6Models.psl29) : P10) * a⁻¹)
    {y : P10} (hy : y ∈ A6Models.psl29) (hay : a * y = y * A6Models.tFrob) :
    ∃ φ' : K ≃* ↥A6Models.psl29, ∀ k : K, ((φ' (α k) : ↥A6Models.psl29) : P10) =
      A6Models.tFrob * ((φ' k : ↥A6Models.psl29) : P10) * A6Models.tFrob⁻¹ := by
  let yy : ↥A6Models.psl29 := ⟨y, hy⟩
  let φ' : K ≃* ↥A6Models.psl29 := φ.trans (MulAut.conj yy⁻¹)
  refine ⟨φ', fun k => ?_⟩
  have hφ' : ∀ k : K, ((φ' k : ↥A6Models.psl29) : P10) = y⁻¹ * ((φ k : ↥A6Models.psl29) : P10) * y := by
    intro k
    show ((yy⁻¹ * φ k * yy⁻¹⁻¹ : ↥A6Models.psl29) : P10) = _
    simp [yy]
  rw [hφ', hφ', hφ k]
  have h1 : a = y * A6Models.tFrob * y⁻¹ := by
    calc a = a * y * y⁻¹ := by group
      _ = y * A6Models.tFrob * y⁻¹ := by rw [hay]
  rw [h1]
  group

end Finish
end CFSG.QuasithinUnique.DoubleA3
end
