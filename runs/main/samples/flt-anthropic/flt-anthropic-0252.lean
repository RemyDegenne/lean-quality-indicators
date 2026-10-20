namespace P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise

open QuaternionAlgebra

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise

open QuaternionAlgebra

noncomputable section

namespace QMHecke12

variable {a b : ℚ}

section Forward

variable {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
  (hB : IsIndefiniteRamifiedExactlyAt a b q q')
  (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
  (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
  (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime)

include hqq' hB hΛ hι hℓ in

theorem exists_generator (M : Submodule ℤ (Fin 2 → ℂ))
    (hMle : M ≤ qmPeriodLattice ι Λ τ)
    (hMℓ : ∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M)
    (hMst : ∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M)
    (hMidx : M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2) :
    ∃ s₁ ∈ Λ, nrd s₁ = (ℓ : ℚ) ∧ ∀ v : Fin 2 → ℂ, v ∈ M ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * s₁) = v := by
  classical
  have hO : IsOrder Λ := hΛ.isOrder
  obtain ⟨ha, hb⟩ := ne_zero_of_hB hB
  have hinj : Function.Injective (qmPeriodMap ι τ) :=
    (QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span hO ha hb ι τ).1
  set φ := qmPeriodMap ι τ with hφ

  let J : Submodule ℤ ℍ[ℚ, a, b] := Λ ⊓ M.comap φ
  have memJ : ∀ x, x ∈ J ↔ x ∈ Λ ∧ φ x ∈ M := fun x => Iff.rfl
  have hJΛ : J ≤ Λ := inf_le_left
  have hℓJ : ∀ y ∈ Λ, (ℓ : ℤ) • y ∈ J := fun y hy =>
    (memJ _).2 ⟨Λ.smul_mem _ hy, by rw [map_zsmul]; exact hMℓ _ (Submodule.mem_map_of_mem hy)⟩
  have hleft : ∀ m ∈ Λ, ∀ x ∈ J, m * x ∈ J := fun m hm x hx =>
    (memJ _).2 ⟨hO.mul_mem hm ((memJ x).1 hx).1, by rw [hφ, qmPeriodMap_mul]; exact hMst m hm _ ((memJ x).1 hx).2⟩
  have hJmap : J.map φ = M := by
    apply le_antisymm
    · rintro v ⟨x, hx, rfl⟩; exact ((memJ x).1 hx).2
    · intro v hv
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_map.1 (hMle hv))
      exact ⟨x, (memJ x).2 ⟨hx, hv⟩, rfl⟩
  have hidx : J.toAddSubgroup.relIndex Λ.toAddSubgroup = ℓ ^ 2 := by
    rw [← AddSubgroup.relIndex_map_map_of_injective J.toAddSubgroup Λ.toAddSubgroup (f := φ.toAddMonoidHom) hinj,
      ← map_toAddSubgroup, ← map_toAddSubgroup, hJmap]
    exact hMidx
  obtain ⟨s₀, hs₀, hn₀, hJ⟩ :=
    QuaternionAlgebra.IsMaximalOrder.exists_nrd_eq_forall_mem_iff_exists_mul_of_relIndex_eq_sq_of_isIndefiniteRamifiedExactlyAt
      hqq' hB Λ hΛ ℓ hℓ J hJΛ hℓJ hleft hidx

  have key : ∃ s₁ ∈ Λ, nrd s₁ = (ℓ : ℚ) ∧ ∀ x : ℍ[ℚ, a, b], x ∈ J ↔ ∃ m ∈ Λ, x = m * s₁ := by
    rcases hn₀ with hn₀ | hn₀
    · exact ⟨s₀, hs₀, hn₀, hJ⟩
    · obtain ⟨u, ⟨hu, v, hv, huv, hvu⟩, hnu⟩ := QuaternionAlgebra.IsMaximalOrder.exists_isUnitOf_nrd_eq_neg_one hB Λ hΛ
      refine ⟨u * s₀, hO.mul_mem hu hs₀, by rw [QuaternionAlgebra.nrd_mul, hnu, hn₀]; ring, fun x => (hJ x).trans ?_⟩
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m * v, hO.mul_mem hm hv, by rw [mul_assoc, ← mul_assoc v, hvu, one_mul]⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨m * u, hO.mul_mem hm hu, by rw [mul_assoc]⟩
  obtain ⟨s₁, hs₁, hn₁, hJ₁⟩ := key
  refine ⟨s₁, hs₁, hn₁, fun v => ?_⟩
  constructor
  · intro hv
    obtain ⟨x, hx, rfl⟩ := (Submodule.mem_map.1 (hMle hv))
    obtain ⟨m, hm, rfl⟩ := (hJ₁ x).1 ((memJ x).2 ⟨hx, hv⟩)
    exact ⟨m, hm, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ((memJ _).1 ((hJ₁ _).2 ⟨y, hy, rfl⟩)).2

end Forward
end QMHecke12
end
end P2MW.S_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq
