namespace P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace HopfAlgebra

p2m_open

namespace HopfIdealQuotient

variable {F : Type u} [Field F] {A : Type v} [CommRing A] [HopfAlgebra F A] (I : Ideal A)
  (hcomul : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)
      (Coalgebra.comul (R := F) a) = 0)
  (hcounit : ∀ a ∈ I, Coalgebra.counit (R := F) a = 0)
  (hanti : ∀ a ∈ I, HopfAlgebraStruct.antipode (R := F) a ∈ I)

local notation "Q" => A ⧸ I

local notation "mk" => Ideal.Quotient.mkₐ F I

noncomputable def antipodeAlgHom : A →ₐ[F] A :=
  AlgHom.ofLinearMap (HopfAlgebraStruct.antipode (R := F))
    (HopfAlgebra.antipode_one (R := F) (A := A))
    (fun a b => by rw [HopfAlgebra.antipode_mul, mul_comm])

end HopfIdealQuotient
end HopfAlgebra
end P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
