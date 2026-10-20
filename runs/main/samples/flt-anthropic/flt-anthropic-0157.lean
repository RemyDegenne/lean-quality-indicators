namespace P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup

noncomputable section

open scoped TensorProduct

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

open scoped TensorProduct

open WithConv

namespace QH

p2m_reactivate

section Quot

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [HopfAlgebra R A] (I : Ideal A)
  (h₁ : ∀ a ∈ I, Coalgebra.counit (R := R) a = 0)
  (h₂ : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) a) = 0)
  (h₃ : ∀ a ∈ I, HopfAlgebra.antipode R a ∈ I)

local notation "mkA" => Ideal.Quotient.mkₐ R I

@[scoped simp] lemma qComul_mk (a : A) :
    qComul I h₂ (Ideal.Quotient.mk I a) =
      Algebra.TensorProduct.map mkA mkA (Coalgebra.comul (R := R) a) :=
  Ideal.Quotient.lift_mk I _ _

end Quot
end QH
end
end P2MW.S_HopfAlgebra_exists_finiteFlat_bialgHom_surjective_points_equiv_of_stable_subgroup
