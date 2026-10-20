namespace P2MW.S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

namespace P2MMultE

open scoped TensorProduct

section DualSide

variable {F : Type*} [Field F] {A : Type*} [CommRing A] [HopfAlgebra F A] [Module.Finite F A]

variable {L : Type*} [Field L] [Algebra F L]

variable {S : Submonoid (WithConv (A →ₐ[F] L))}

theorem toDualQ_one (h : PtHyp S) (q : QS S) : toDualQ h 1 q = counitQ h q := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [toDualQ_mk, Subalgebra.coe_one, CartierDual.one_apply, counitQ_mk]

end DualSide
end P2MMultE
end P2MW.S_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints
