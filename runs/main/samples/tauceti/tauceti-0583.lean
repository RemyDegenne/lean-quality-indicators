public section

open scoped TensorProduct

namespace TauCeti

universe uR uM

variable {R : Type uR} {M : Type uM} [CommRing R] [AddCommMonoid M] [Module R M]

namespace ReducedTensorWords

theorem component_gradedCoderiv_of_eq_zero (G : InternalGrading R M)
    (F : ReducedTensorWords R M →ₗ[R] M) (q : ℤ) (c : ℕ)
    (hF : ∀ n : {n : ℕ // 0 < n}, c + 1 < n.1 → F ∘ₗ of R M n = 0)
    (k n : {n : ℕ // 0 < n}) (hn : k.1 + 1 + c ≤ n.1)
    (z : TensorPower R n.1 M) :
    component R M k (gradedCoderiv G F q (of R M n z)) = 0 := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod a x =>
      simp only [map_smul]
      suffices h : component R M k
          (gradedCoderiv G F q (of R M n (PiTensorProduct.tprod R x))) = 0 by
        rw [h, smul_zero]
      rw [gradedCoderiv_of_tprod, map_sum]
      apply Finset.sum_eq_zero
      intro p hp
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro d hd
      by_cases hfit : 0 < d ∧ p + d ≤ n.1
      · by_cases hdc : c + 1 < d
        · have hzero : F (subword R x p d) = 0 := by
            rw [subword_eq_of_tprod R x hfit.1 hfit.2]
            exact LinearMap.congr_fun (hF ⟨d, hfit.1⟩ hdc) _
          rw [hzero, splice_zero, map_zero]
        · rw [splice_eq_of_tprod R _ _ hfit.1 hfit.2 (by omega)]
          apply component_of_of_ne
          intro heq
          have := congrArg Subtype.val heq
          dsimp only at this
          omega
      · rw [splice_eq_zero_of_not_fits R _ _ hfit, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

end ReducedTensorWords
end TauCeti
end
