namespace P2MW.S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff

set_option autoImplicit false

open PDivisibleGroup Coalgebra WithConv

p2m_open_scoped

namespace PDivCharDiff

section Test

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]

variable {A : Type} [AddCommGroup A] [Module R A]

theorem T_sum_coord {ι : Type} [Fintype ι] (b : Module.Basis ι R A) (lam : Module.Dual R A →ₗ[R] S)
    (φ : Module.Dual R A) : T S φ (∑ i, lam (b.coord i) ⊗ₜ[R] b i) = lam φ := by
  rw [map_sum]
  simp_rw [T_tmul, ← map_smul lam]
  rw [← map_sum, Module.Basis.sum_dual_apply_smul_coord]

end Test
end PDivCharDiff
end P2MW.S_PDivisibleGroup_CartierDuality_charElem_mul_and_charDiff_mul_and_lTensor_cotangentMap_charDiff
