namespace P2MW.S_Rep_nonempty_iso_indBot_trivial_of_isPGroup

set_option autoImplicit false

universe u

p2m_open

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

noncomputable section

namespace P2mS26K1

open Representation

section model

variable {k G : Type*} [CommRing k] [Group G]

variable {A : Type*} [AddCommGroup A] [Module k A] (ρ : Representation k (⊥ : Subgroup G) A)

p2m_open

noncomputable def E [DecidableEq G] : (G →₀ A) ≃ₗ[k] Representation.IndV (⊥ : Subgroup G).subtype ρ :=
  (finsuppScalarLeft k A G).symm.trans <|
    (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv k).symm (LinearEquiv.refl k A)).trans
      ((Submodule.quotEquivOfEqBot _ (ker_tprod_bot_eq_bot ρ)).symm :
        (MonoidAlgebra k G ⊗[k] A) ≃ₗ[k] Representation.Coinvariants (V := MonoidAlgebra k G ⊗[k] A)
          (Representation.tprod ((Representation.leftRegular k G).comp (⊥ : Subgroup G).subtype) ρ))

end model
end P2mS26K1
end
end P2MW.S_Rep_nonempty_iso_indBot_trivial_of_isPGroup
