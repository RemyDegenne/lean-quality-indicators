namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat

set_option autoImplicit false

set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace W2C2

section FlatTorsion

open scoped TensorProduct in

theorem smul_pow_eq_zero_imp_of_flat'
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (hπ : ∀ s : 𝒪, π * s = 0 → s = 0) (k : ℕ)
    (M : Type) [AddCommGroup M] [Module (𝒪 ⧸ Ideal.span {π ^ k}) M] [Module.Flat (𝒪 ⧸ Ideal.span {π ^ k}) M]
    (j : ℕ) (hj : j ≤ k) (y : M) (hy : (Ideal.Quotient.mk (Ideal.span {π ^ k}) π) ^ j • y = 0) :
    ∃ z : M, y = (Ideal.Quotient.mk (Ideal.span {π ^ k}) π) ^ (k - j) • z := by
  classical
  have hreg : ∀ (i : ℕ) (u v : 𝒪), π ^ i * u = π ^ i * v → u = v := by
    intro i
    induction i with
    | zero => intro u v h; simpa using h
    | succ i ih =>
      intro u v h
      apply ih
      have h' : π * (π ^ i * u - π ^ i * v) = 0 := by
        rw [mul_sub, ← mul_assoc, ← mul_assoc, ← pow_succ', h, sub_self]
      exact sub_eq_zero.1 (hπ _ h')
  set A := 𝒪 ⧸ Ideal.span {π ^ k} with hA
  set ϖ : A := Ideal.Quotient.mk (Ideal.span {π ^ k}) π with hϖ
  let f : A →ₗ[A] A := LinearMap.lsmul A A (ϖ ^ (k - j))
  let g : A →ₗ[A] A := LinearMap.lsmul A A (ϖ ^ j)
  have hfg : Function.Exact f g := by
    intro x
    constructor
    · intro hx
      obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hx' : Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ j * x₀) = 0 := by
        have : g (Ideal.Quotient.mk _ x₀) = ϖ ^ j * Ideal.Quotient.mk _ x₀ := rfl
        rw [← map_pow, ← map_mul] at this; rw [← this]; exact hx
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx'
      obtain ⟨c, hc⟩ := hx'
      have hx₀ : x₀ = c * π ^ (k - j) := by
        have : π ^ j * x₀ = π ^ j * (c * π ^ (k - j)) := by
          rw [← hc, mul_comm c, mul_comm c, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]
        exact hreg j _ _ this
      refine ⟨Ideal.Quotient.mk (Ideal.span {π ^ k}) c, ?_⟩
      show ϖ ^ (k - j) • Ideal.Quotient.mk (Ideal.span {π ^ k}) c = Ideal.Quotient.mk (Ideal.span {π ^ k}) x₀
      rw [hx₀, smul_eq_mul, hϖ, ← map_pow, ← map_mul, mul_comm]
    · rintro ⟨w, rfl⟩
      show ϖ ^ j • (ϖ ^ (k - j) • w) = 0
      rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj, hϖ, ← map_pow,
        show Ideal.Quotient.mk (Ideal.span {π ^ k}) (π ^ k) = 0 from Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl),
        zero_mul]
  have hex := Module.Flat.lTensor_exact M hfg
  have h1 : LinearMap.lTensor M g (y ⊗ₜ[A] (1 : A)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    show y ⊗ₜ[A] (ϖ ^ j • (1 : A)) = 0
    rw [← TensorProduct.smul_tmul, hy, TensorProduct.zero_tmul]
  obtain ⟨t, ht⟩ := (hex _).1 h1
  refine ⟨TensorProduct.rid A M t, ?_⟩
  have key : ∀ u : M ⊗[A] A, TensorProduct.rid A M (LinearMap.lTensor M f u) = ϖ ^ (k - j) • TensorProduct.rid A M u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul m b =>
      rw [LinearMap.lTensor_tmul]
      show TensorProduct.rid A M (m ⊗ₜ[A] (ϖ ^ (k - j) • b)) = ϖ ^ (k - j) • TensorProduct.rid A M (m ⊗ₜ[A] b)
      rw [TensorProduct.rid_tmul, TensorProduct.rid_tmul, smul_smul, smul_eq_mul]
    | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, smul_add]
  rw [← key, ht, TensorProduct.rid_tmul, one_smul]

end FlatTorsion
end W2C2
end P2MW.S_AlgebraicGeometry_exists_ringEquiv_quotient_sections_of_isPullback_of_flat
