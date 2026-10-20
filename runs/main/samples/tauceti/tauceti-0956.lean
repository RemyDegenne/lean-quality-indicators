public section

open scoped TensorProduct

namespace TauCeti.ComoduleAlgebra

universe u v w x y

section Semiring

variable {R : Type u} {H : Type v} {A : Type w} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [CommSemiring A] [Algebra R A] [ComoduleAlgebra R H A]
  {B : Type x} [CommSemiring B] [Algebra R B] [Algebra B A] [IsScalarTower R B A]
  (B' : Type y) [CommSemiring B'] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']

variable {B'}

variable (B')

theorem galoisMap_baseChange_bijective (hB : ∀ b : B, algebraMap B A b ∈ coinvariants R H A)
    (h : Function.Bijective (galoisMap B hB)) :
    letI := baseChange B' hB
    Function.Bijective (galoisMap B' (algebraMap_mem_coinvariants_baseChange hB)) := by
  let := baseChange B' hB
  rw [coe_galoisMap_baseChange, EquivLike.comp_bijective, EquivLike.bijective_comp]
  exact (LinearEquiv.ofBijective (((galoisMap B hB).restrictScalars B).toLinearMap)
    (by simpa using h)).lTensor B' |>.bijective

end Semiring
end TauCeti.ComoduleAlgebra
end
