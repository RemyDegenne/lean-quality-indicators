namespace P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct

p2m_reactivate

p2m_reactivate

p2m_reactivate

section P13_E_INTEGRAL

set_option autoImplicit false

set_option maxHeartbeats 6400000

set_option synthInstance.maxHeartbeats 1600000

p2m_reactivate

namespace P2MMultE

open scoped TensorProduct

section Restriction

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]

variable {F : Type} [Field F] [Algebra O F] [IsFractionRing O F]

variable {A : Type} [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
  [Coalgebra.IsCocomm O A]

variable {L : Type} [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]

variable {S S' : Submonoid (WithConv (F ⊗[O] A →ₐ[F] L))}

noncomputable def resE (h : IPtHyp S) (h' : IPtHyp S') (hle : S ≤ S') (ψ : ptsE h') : ptsE h :=
  WithConv.toConv (ψ.ofConv.comp (inclES h h' hle))

end Restriction
end P2MMultE
end P13_E_INTEGRAL
end P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two
